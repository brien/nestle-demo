using System;
using System.Collections.Generic;
using System.Data;
using System.Windows.Forms;
using TestSimpleRNG;

namespace Junction
{
    public sealed class GeneticAlgorithmSchedulingCS
    {
        private const double UNCONSTRAINED_TIME = 999999; // An arbitrary amount of time to add in decimal hours to create an unconstrained condition

        //Create a bit flag enumeration for allergens
        [Flags]
        public enum Allergens
        {
            None = 0,
            //Wheat = 1,
            //Milk = 2,
            //Soy = 4,
            Cat_16 = 1,
            Cat_2 = 2,
            Cat_8 = 4,
            Sesame = 8,
            Sulfite = 16,
            Eggs = 32,
            Fish = 64,
            Peanuts = 128,
            Nuts = 256
        }

        char[] AllergenList = new char[] { 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I' };

        // Flag to control the creation of delay jobs:
        public bool doGenerateDelay;
        // Run the refactored GA or the original Nestle Demo?
        public bool runRefactored;
        // Or Run the new GA (originally called constrained, no longer accurate description)?
        public bool runConstrained;

        //private double[] ProdRunTime;
        private double[] JobRunTime;
        private String[] ProductName;
        private int[] BOMItemIndex; //Used to hold the index from the product to the BOMItem list
        private System.Collections.Hashtable ProductNumberHash;
        private string[] AllergensInProduct;
        private double[,] ChangeOver;
        private double[,] ChangeOverPenalties;
        private int[] JobsToSchedule;
        private double[] OrderQty;
        private object[,] ScheduleResult;
        private int[,] Offspring;
        private int[,] Population;
        private double[] Priority; //The due time in decimal hours
        private double[] EarlyStart; //Earliest start time in decimal hours
        private double[] FitnessArray;
        private DateTime[] productionEndTime;
        private String[] ResourceName;
        private double[] ProdEndTime;
        private DateTime[] productionStartTime;
        private double[] ProdStartTime;
        private int[] StartProduct;
        private double[] RLCMin; //Minimum Resource Late Cost
        private double[] RLCMax; //Maximum Resource Late Cost
        private double[] RLCRatePerHour; //increase in late cost for each hour late
        private double[] MinLateCost;
        private double[] MaxLateCost;
        private double[] LateCostPerHour;
        private double[] MinEarlyCost;
        private double[] MaxEarlyCost;
        private double[] EarlyCostPerHour;
        private double[] MaxVolume;
        private double[] MinVolume;
        private double[] MaxFlowIn;
        private double[] MaxFlowOut;
        private int[] MaxInputs;
        private int[] MaxOutputs;
        public enum ResourceTypes
        {
            Batch = 0,
            Flow = 1,
            Tank = 2,
        }
        private ResourceTypes[] ResourceType;

        private List<BOMItem> BOMItems = new List<BOMItem>();

        public bool[] ConstrainedStart { get; set; }

        public GeneticOptimizer.GA GA;
        public ConstrainedGeneticOptimizer.ConstrainedGA CGA;


        private int NumberOfRealJobs;
        //todo   get an improvement over DelayIndex
        private int DelayIndex = -1; //Initialize to a negative value so that we can tell if there is not a delay product.
        private DataSet masterData;


        public bool ValidDataInput { get; set; }
        public bool ShowStatusWhileRunning { get; set; }
        public int NumberOfResources { get; set; }
        public double TotalTime { get; private set; }
        public int NumberOfResourceLateJobs { get; private set; }
        public int NumberOfServiceLateJobs { get; private set; }
        public int NumberOfResourceFeasibilityViolations { get; private set; }
        public int NumberOfBOMViolations { get; private set; }
        public int NumberOfEarlyStartViolations { get; private set; }
        public double RunTime { get; private set; }
        public double ChangeOverTime { get; private set; }
        public DataSet ScheduleDataSet { get; private set; }
        public bool IsFeasible { get; private set; }
        //public double LateCost { get; set; }
        public double BOMPenaltyCost { get; set; }
        public double ResourceNotFeasible { get; set; }
        public double ResourcePref { get; set; }
        public double[,] ResourcePreference;
        public double WashTime { get; set; }
        //public double RinseTime { get; set; }

        public DataSet MasterData
        {
            get
            {
                return masterData;
            }
            set
            {
                masterData = value;
                SetResourceData(masterData.Tables["Resources"]);
                SetProdData(masterData.Tables["Products"]);
                SetConstrainedStartData(masterData.Tables["Resources"]);
                SetChangeOverData(masterData.Tables["Change Over"]);
                SetChangeOverPenaltyData(MasterData.Tables["Change Over Penalties"]);
                SetOrderData(masterData.Tables["Orders"]);
                SetBOMData(masterData.Tables["BOMItems"]);
            }
        }


        private void FindBulls(int numBulls, ref int[] Bulls)
        {
            int iMax = Population.GetUpperBound(0);
            bool[] IsBull = new bool[iMax];
            int BestIndex;
            double[] SortedFitnessArray = new double[iMax];
            int[] FitnessIndex = new int[iMax];

            if (numBulls == 1)
            {
                BestIndex = FindBestIndex();
                Bulls[0] = BestIndex;
                IsBull[BestIndex] = true;
            }
            else
            {
                for (int i = 0; i < iMax; i++)
                {
                    //Set up an array of pointers to use for sorting
                    FitnessIndex[i] = i;
                    SortedFitnessArray[i] = FitnessArray[i];
                }
                //sort the array to find the bulls
                Array.Sort(SortedFitnessArray, FitnessIndex);
                for (int i = 0; i < (numBulls - 1); i++)
                {
                    Bulls[i] = FitnessIndex[i];
                }
            }
        }

        private int FindBestIndex()
        {
            int iMax = Population.GetUpperBound(0);
            int BestIndex = -1;
            double Best = 9999999.0;
            double Current;
            for (int i = 0; i < iMax; i++)
            {
                Current = FitnessArray[i];
                if (Best > Current)
                {
                    Best = Current;
                    BestIndex = i;
                }
            }
            return BestIndex;
        }

        private double CalcFitness(ref int[,] PopulationArray, int Member)
        {
            double Time = ProdStartTime[0];
            double NonDelayTime = Time; //Added 3/24 to elim delay time
            double JobStartTime, JobEndTime;
            double Fitness;
            double SumOfServiceEarlyPenalties = 0;
            double SumOfServiceLatePenalties = 0;
            double SumOfResourceLatePenalties = 0;
            double BOMPenalties = 0;
            int Previous = -1;
            bool ScheduleViolationBOM = false;
            bool ScheduleViolationResourceLate = false;
            bool ScheduleViolationOrderLate = false;
            bool ScheduleViolationResourceFeasiblilty = false;
            bool ScheduleViolationEarlyTime = false;
            double LateTime, EarlyTime;
            int CurrentProd;
            double TotalTimeAllResources = 0;
            int CurrentJob;
            double ResourcePrefPenalties = 0;
            double SumOfChangeOverPenalties = 0;
            double EarlyStartFactor = 0;

            // List of production orders to support calculation of BOM Item requirements
            List<ProdSchedule> pSched = new List<ProdSchedule>();


            for (int Resource = 0; Resource < NumberOfResources; Resource++)
            {
                Time = ProdStartTime[Resource];
                NonDelayTime = Time; // added to eliminate delay orders

                if (ConstrainedStart[Resource])
                {
                    Previous = StartProduct[Resource];
                }
                else
                {
                    Previous = -1;
                }
                // Calculate the time for the following jobs
                int FirstGeneInResource = NumberOfRealJobs * Resource;
                int LastGeneInResource = (NumberOfRealJobs * (Resource + 1)) - 1;
                double co, cop;
                for (int i = FirstGeneInResource; i <= LastGeneInResource; i++)
                {
                    CurrentJob = PopulationArray[Member, i];
                    CurrentProd = JobsToSchedule[CurrentJob];
                    if (Previous != -1 & CurrentProd != -1)
                    {
                        co = ChangeOver[Previous, CurrentProd];
                        cop = ChangeOverPenalties[Previous, CurrentProd];
                    }
                    else
                    {
                        co = 0;
                        cop = 0;
                    }
                    // Change code to eliminate Delay Jobs from the fitness calculation as well as slack jobs
                    // Delay jobs are being coded manually as product 9999
                    //ToDo enhance input to give a better spread on delay jobs vs adding products and orders for delays. Get rid of the 9999 comparison.
                    //if (CurrentProd != -1)  Changed on 3/24/2012
                    if (CurrentProd != -1)
                    {

                        //This is a real job so process it
                        if (Previous == -1)
                        {
                            //First job on the resource was a slack job
                            JobStartTime = Time;
                            Time += JobRunTime[CurrentJob];
                            JobEndTime = Time;
                        }
                        else
                        {
                            //we have a real job in the previous variable
                            JobStartTime = Time;
                            Time += JobRunTime[CurrentJob] + co;
                            JobEndTime = Time;
                            // Find last non delay time on the resource

                        }
                        if (CurrentProd != DelayIndex)
                        {
                            //Used to find the last real job running on a resource
                            NonDelayTime = Time;
                            //Used to encourage jobs to start as soon as possible
                            //Todo  Turn Early start factor into a configurable factor (by resorce?)
                            EarlyStartFactor += JobStartTime;
                        }

                        Previous = JobsToSchedule[CurrentJob];

                        //Calculate Service Early Cost
                        EarlyTime = EarlyStart[CurrentJob];
                        if (JobStartTime < EarlyTime & EarlyTime != 0.0)
                        {
                            SumOfServiceEarlyPenalties += Math.Min(MaxEarlyCost[CurrentJob], MinEarlyCost[CurrentJob] + EarlyCostPerHour[CurrentJob] * (EarlyTime - (JobStartTime)));
                            ScheduleViolationEarlyTime = true;
                        }

                        //Calculate Service Late Cost
                        LateTime = Priority[CurrentJob];
                        if (Time > LateTime)
                        {
                            SumOfServiceLatePenalties += Math.Min(MaxLateCost[CurrentJob], MinLateCost[CurrentJob] + LateCostPerHour[CurrentJob] * (JobEndTime - Priority[CurrentJob]));
                            ScheduleViolationOrderLate = true;
                        }

                        //Calculate Resource Late Cost
                        if (Time > ProdEndTime[Resource])
                        {
                            SumOfResourceLatePenalties += Math.Min(RLCMax[Resource], RLCMin[Resource] + RLCRatePerHour[Resource] * (Time - ProdEndTime[Resource]));
                            ScheduleViolationResourceLate = true;
                        }

                        // Add the resource preference penalties
                        ResourcePrefPenalties += ResourcePreference[CurrentProd, Resource];
                        if (ResourcePreference[CurrentProd, Resource] == ResourceNotFeasible)
                        {
                            ScheduleViolationResourceFeasiblilty = true;
                        }

                        //Sum up the changeover penalties
                        SumOfChangeOverPenalties += cop;

                        //Build the output schedule for BOM Items
                        //First create a new production schedule item
                        ProdSchedule p = new ProdSchedule(CurrentProd, JobStartTime, JobEndTime, OrderQty[CurrentJob]);
                        //Second, add the new schedule item to the list
                        pSched.Add(p);
                    }
                }
                // Calculate the total production time required
                //TotalTimeAllResources += Time - ProdStartTime[Resource]; 
                TotalTimeAllResources += NonDelayTime - ProdStartTime[Resource];
            }

            //Get ready to check for BOM violations
            if (BOMItems.Count > 0) //This is purely a speed enhancement to skip this section if there are no BOM items.
            {
                List<ProdSchedule> ComponentSchedule = new List<ProdSchedule>();
                foreach (ProdSchedule ps in pSched)
                {
                    //Find out if the item has components
                    int bIdx = BOMItemIndex[ps.Product];
                    if (bIdx == -1) continue;
                    int cIdx = -1;
                    BOMItem bi = BOMItems[bIdx];
                    foreach (int component in bi.Components)
                    {
                        cIdx++;
                        //add the demand of the component quantity to the schedule
                        double ComponentDemand = -(ps.OrderQty * bi.Percent[cIdx]);
                        //Note: StartTime is used twice in the line below. This is not a mistake.
                        //Component demand is not a real scheduled job.
                        //This simplification makes sure the demand occurs at the start of the parent job.
                        //Adding .0001 keeps the posting sequence = (debit inventory first at any given time then credit)
                        ProdSchedule cd = new ProdSchedule(component, ps.StartTime, ps.StartTime + 0.0001, ComponentDemand);
                        ComponentSchedule.Add(cd);
                    }

                }
                pSched.AddRange(ComponentSchedule);
                pSched.Sort();
                int pProd = -99; // set up a variable to hold the previous product
                double pQty = 0; //set up a variable to hold the previous quantity

                //Calculate the available quantities
                foreach (ProdSchedule ps in pSched)
                {
                    // Calculate the penalty
                    if (pProd == ps.Product)
                    {
                        pQty += ps.OrderQty;
                        ps.AvailableQuantity = pQty;
                    }
                    else
                    {
                        pQty = ps.OrderQty;
                        pProd = ps.Product;
                        ps.AvailableQuantity = pQty;
                    }
                    if (ps.AvailableQuantity < 0.0)
                    {
                        BOMPenalties += BOMPenaltyCost;
                        ScheduleViolationBOM = true;
                    }
                }
            }

            if (!(ScheduleViolationBOM | ScheduleViolationResourceLate | ScheduleViolationOrderLate | ScheduleViolationResourceFeasiblilty | ScheduleViolationEarlyTime))
            {
                IsFeasible = true;
            }

            //Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
            //    + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties; 
            Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
             + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties + EarlyStartFactor;

            return Fitness;
        }

        private void CalcTime(ref object[,] Schedule, int TimeColumn, int SetupColumn, int[] genes, double[] delayTimes)
        {
            //Calculates Time Only - For Fitness use the the CalcFitness method
            double Time = ProdStartTime[0];
            int PreviousProd = -1;
            int CurrentProd;

            //Clear the global time variables
            TotalTime = 0;
            RunTime = 0;
            ChangeOverTime = 0;

            //Calculate the time for the following jobs
            for (int Resource = 0; Resource < NumberOfResources; Resource++)
            {
                if (ConstrainedStart[Resource])
                {
                    PreviousProd = StartProduct[Resource];
                }
                else
                {
                    PreviousProd = -1;
                }
                Time = ProdStartTime[Resource];
                //Split the gene string into resources
                int FirstGeneInResource = NumberOfRealJobs * Resource;
                int LastGeneInResource = (NumberOfRealJobs * (Resource + 1)) - 1;

                for (int i = FirstGeneInResource; i <= LastGeneInResource; i++)
                {
                    //int CurrentJob = (int)Schedule[0, i];
                    //CurrentProd = (int)Schedule[1, i];

                    int CurrentJob = genes[i]; // Population[BestIndex, i];
                    CurrentProd = JobsToSchedule[CurrentJob];

                    double co = 0;

                    if (PreviousProd != -1 & CurrentProd != -1)
                    {
                        co = ChangeOver[PreviousProd, CurrentProd];
                    }
                    Schedule[SetupColumn, i] = co;
                    if (CurrentProd != -1)
                    {
                        Time += JobRunTime[CurrentJob] + co + delayTimes[CurrentJob];
                        Schedule[TimeColumn, i] = Time;
                        //Update the global variables for time and late jobs
                        RunTime += JobRunTime[CurrentJob] + delayTimes[CurrentJob];
                        ChangeOverTime += co;
                        //Set the previous = current for the next loop
                        PreviousProd = CurrentProd;
                    }
                    else
                    {
                        Schedule[TimeColumn, i] = Time;
                    }
                }
                TotalTime += Time - ProdStartTime[Resource];
                //Reset the variables for the next resource
                PreviousProd = -1;
            }
        }
        private void CalcTime(ref object[,] Schedule, int TimeColumn, int SetupColumn, int BestIndex)
        {
            //Calculates Time Only - For Fitness use the the CalcFitness method
            double Time = ProdStartTime[0];
            int PreviousProd = -1;
            int CurrentProd;

            //Clear the global time variables
            TotalTime = 0;
            RunTime = 0;
            ChangeOverTime = 0;

            //Calculate the time for the following jobs
            for (int Resource = 0; Resource < NumberOfResources; Resource++)
            {
                if (ConstrainedStart[Resource])
                {
                    PreviousProd = StartProduct[Resource];
                }
                else
                {
                    PreviousProd = -1;
                }
                Time = ProdStartTime[Resource];
                //Split the gene string into resources
                int FirstGeneInResource = NumberOfRealJobs * Resource;
                int LastGeneInResource = (NumberOfRealJobs * (Resource + 1)) - 1;

                for (int i = FirstGeneInResource; i <= LastGeneInResource; i++)
                {
                    //int CurrentJob = (int)Schedule[0, i];
                    //CurrentProd = (int)Schedule[1, i];

                    int CurrentJob = Population[BestIndex, i];
                    CurrentProd = JobsToSchedule[CurrentJob];

                    double co = 0;

                    if (PreviousProd != -1 & CurrentProd != -1)
                    {
                        co = ChangeOver[PreviousProd, CurrentProd];
                    }
                    Schedule[SetupColumn, i] = co;
                    if (CurrentProd != -1)
                    {
                        Time += JobRunTime[CurrentJob] + co;
                        Schedule[TimeColumn, i] = Time;
                        //Update the global variables for time and late jobs
                        RunTime += JobRunTime[CurrentJob];
                        ChangeOverTime += co;
                        //Set the previous = current for the next loop
                        PreviousProd = CurrentProd;
                    }
                    else
                    {
                        Schedule[TimeColumn, i] = Time;
                    }
                }
                TotalTime += Time - ProdStartTime[Resource];
                //Reset the variables for the next resource
                PreviousProd = -1;
            }
        }


        private void CreatePopulation(int NumberOfNonRandomOffspring)
        {
            int iMax = Population.GetUpperBound(0);  //members of the population
            int jMax = Population.GetUpperBound(1) + 1;   //number of jobs (chromosomes) in the population
            Random Rand = new Random();
            int[] NewMember = new int[jMax];
            double[] RandomArray = new double[jMax];

            //First set up the non-random offspring using a hueristic
            //The purpose of this is to create good starting point(s) in order to reduce the number of search generations required
            //If multiple resources are in use, this will not create any non-random offspring and will return a zero
            NumberOfNonRandomOffspring = CreateNonRandom(NumberOfNonRandomOffspring);

            //Create the random population members
            for (int i = NumberOfNonRandomOffspring; i <= iMax; i++)
            {
                for (int j = 0; j < jMax; j++)
                {
                    NewMember[j] = j;
                    RandomArray[j] = Rand.NextDouble();
                }
                Array.Sort(RandomArray, NewMember);
                for (int j = 0; j < jMax; j++)
                {
                    Population[i, j] = NewMember[j];
                }
            }
            // Set the FitnessArray for the new members
            for (int i = 0; i <= iMax; i++)
            {
                FitnessArray[i] = CalcFitness(ref Population, i);
            }
        }


        private void Mutate(int Individual, double MutationProbability, ref int[,] Offspring)
        {
            int GeneCount = Offspring.GetUpperBound(1) + 1;
            Random Mutation = new Random();

            MutationProbability = MutationProbability * Mutation.NextDouble();

            int CurrentJob, RandomIndex;

            for (int j = 0; j < GeneCount; j++)
            {
                if (Mutation.NextDouble() < MutationProbability)
                {
                    //Swap the current gene with another in the string
                    CurrentJob = Offspring[Individual, j];
                    RandomIndex = (int)(Mutation.NextDouble() * (double)GeneCount);
                    Offspring[Individual, j] = Offspring[Individual, RandomIndex];
                    Offspring[Individual, RandomIndex] = CurrentJob;
                }
            }
        }

        private int CreateNonRandom(int iNumToCreate)
        //The subroutine returns the number of non-random strings created.
        //This routine only works for single production resources. Exit if more than one production resource is in use.
        {
            //This algorithm has not been developed to support multiple production resources.
            if (NumberOfResources > 1)
            {
                return 0;
            }

            Random RandNum = new Random();
            int StartPoint = -1;
            int Previous;
            int iMax = JobsToSchedule.GetUpperBound(0) + 1;
            int jMax = Population.GetUpperBound(1) + 1;

            for (int i = 0; i < iNumToCreate; i++)
            {
                bool Found = false;
                bool[] AlreadyUsed = new bool[iMax];
                double ChangeTime;
                //Check to see if this is a constrained start on the first non-random string
                if (i == 0 & ConstrainedStart[0])
                {
                    //Select the start point that contains a product that is currently running
                    for (int k = 0; k < iMax; k++)
                    {
                        if (JobsToSchedule[k] == StartProduct[0])
                        {
                            StartPoint = k;
                        }
                    }
                    if (StartPoint == -1)
                    {
                        //If the starting product wasn't in the mix, then pick a random start point.
                        StartPoint = Convert.ToInt32(((double)iMax * RandNum.NextDouble()));
                    }
                }
                else
                {
                    StartPoint = Convert.ToInt32(((double)iMax * RandNum.NextDouble()));
                }

                Previous = StartPoint;
                AlreadyUsed[StartPoint] = true;
                //put the startpoint into the population
                Population[i, 0] = StartPoint;
                //Fill out the remaining jobs in this gene sequence
                for (int j = 1; j < jMax; j++)
                {
                    Found = false;
                    for (int k = 0; k < jMax; k++) //need to check all of the possible jobs to schedule
                    {
                        //try to find the next job with 0 setup cost
                        if (!AlreadyUsed[k])
                        {
                            //check the setup time
                            ChangeTime = ChangeOver[JobsToSchedule[Previous], JobsToSchedule[k]];
                            if (ChangeTime == 0)
                            {
                                Population[i, j] = k;
                                Found = true;
                                Previous = k;
                                AlreadyUsed[k] = true;
                                break;
                            }
                        }
                    }
                    if (!Found)
                    {
                        //if no 0 based solution was found, then find the lowest changeover time and use that
                        double Lowest = 999999999.0;
                        int LowestIndex = -1;
                        for (int k = 0; k < jMax; k++)
                        {
                            if (!AlreadyUsed[k])
                            {
                                ChangeTime = ChangeOver[JobsToSchedule[Previous], JobsToSchedule[k]];
                                if (ChangeTime < Lowest)
                                {
                                    Lowest = ChangeTime;
                                    LowestIndex = k;
                                }
                            }
                        }
                        //assign the shortest changeover time as the next job in the string
                        Population[i, j] = LowestIndex;
                        Previous = LowestIndex;
                        AlreadyUsed[LowestIndex] = true;
                    }
                }
            }
            return iNumToCreate;
        }

        // Overloaded - Multiple Population Version
        private void Mate(int BullIndex, int BullPopulationPointer, ref int[,] Herd, double StrengthOfFather, double DeathRate,
                           int NumberOfBulls, double MutationProbability)
        {
            int Crosses = Herd.GetUpperBound(1) + 1;
            Random Gene = new Random();
            int PopulationSize = Population.GetUpperBound(0) + 1;
            int GeneNum = Population.GetUpperBound(1) + 1;
            int[] Crossover = new int[GeneNum];
            int[] OffspringIndex = new int[Crosses];
            double[] OffspringFitness = new double[Crosses];
            double[] BestOffspring = new double[Crosses];
            bool[] MotherGenes = new bool[GeneNum];

            for (int i = 0; i < Crosses; i++)
            {
                // Set all mother genes to needed
                for (int j = 0; j < GeneNum; j++)
                {
                    MotherGenes[j] = true;
                }
                // create crossover string
                for (int j = 0; j < GeneNum; j++)
                {
                    if (Gene.NextDouble() < StrengthOfFather)
                    {
                        Crossover[j] = 1;
                        // eliminate the mother genes that are not needed
                        for (int k = 0; k < GeneNum; k++)
                        {
                            // If the father gene is used turn off the mother gene
                            if (Population[Herd[BullIndex, i], k] == Population[BullPopulationPointer, j])
                            {
                                MotherGenes[k] = false;
                            }
                        }
                    }
                    else
                    {
                        Crossover[j] = 0;
                    }
                }
                int NextMotherGene = 0;

                //Create the Offspring
                for (int j = 0; j < GeneNum; j++)
                {
                    if (Crossover[j] == 1)
                    {
                        Offspring[i, j] = Population[BullPopulationPointer, j]; //copy the father gene to the offspring if there is a 1 in the crossover string
                    }
                    else
                    {
                        //Find the next mother gene to use
                        while (NextMotherGene < GeneNum)
                        {
                            if (MotherGenes[NextMotherGene])
                            {
                                Offspring[i, j] = Population[Herd[BullIndex, i], NextMotherGene];
                                NextMotherGene++;
                                break;
                            }
                            else
                            {
                                NextMotherGene++;
                            }
                        }
                    }
                }
                //Mutate the offspring
                Mutate(i, MutationProbability, ref Offspring);
                OffspringFitness[i] = CalcFitness(ref Offspring, i);
                OffspringIndex[i] = i;
            }
            //Time to die
            //Calculate the number of cows to die
            int DeathToll = (int)((double)PopulationSize * DeathRate / 100.0); //Gross Death Toll
            // when working with more than one bull we need to reset the deathtoll for the number per herd
            //since death toll will be used as an array index, reduce it by one
            DeathToll = (int)((double)DeathToll / (double)NumberOfBulls) - 1;
            //Pick the weakest herd members to die
            double[] HerdFitness = new double[PopulationSize];
            int[] HerdIndex = new int[PopulationSize];
            for (int i = 0; i < PopulationSize; i++)
            {
                HerdFitness[i] = CalcFitness(ref Population, i);
                HerdIndex[i] = i;
            }
            //Sort the array to set up survival of the fittest
            Array.Sort(OffspringFitness, OffspringIndex);
            //myReverserClass rc = new myReverserClass();
            ReverseComparer rc = new ReverseComparer();
            Array.Sort(HerdFitness, HerdIndex, rc); //Sorts the HerdIndex Array from worst to best according to the herdindex
            // kill the weak and insert the fittest offspring
            for (int i = 0; i < DeathToll; i++)
            {
                int idxHerd = HerdIndex[i];
                int idxOffSpring = OffspringIndex[i];
                for (int j = 0; j < GeneNum; j++)
                {
                    //replace the dead members with the best new offspring
                    Population[idxHerd, j] = Offspring[idxOffSpring, j];
                }
                FitnessArray[idxHerd] = OffspringFitness[i];
            }
        }

        // Overloaded - Single Population Version
        private void Mate(int BullPopulationPointer, double StrengthOfFather, double DeathRate, double MutationProbability)
        {
            //int Crosses = Population.GetUpperBound(1) +1;// ****************************************************
            Random Gene = new Random();
            int PopulationSize = Population.GetUpperBound(0) + 1;
            int GeneNum = Population.GetUpperBound(1) + 1;
            int[] Crossover = new int[GeneNum];
            int[] OffspringIndex = new int[PopulationSize];
            double[] OffspringFitness = new double[PopulationSize];
            double[] BestOffspring = new double[PopulationSize];
            bool[] MotherGenes = new bool[GeneNum];

            for (int i = 0; i < PopulationSize; i++)
            {
                // Set all mother genes to needed
                for (int j = 0; j < GeneNum; j++)
                {
                    MotherGenes[j] = true;
                }
                // create crossover string
                for (int j = 0; j < GeneNum; j++)
                {
                    if (Gene.NextDouble() < StrengthOfFather)
                    {
                        Crossover[j] = 1;
                        // eliminate the mother genes that are not needed
                        for (int k = 0; k < GeneNum; k++)
                        {
                            // If the father gene is used turn off the mother gene
                            if (Population[i, k] == Population[BullPopulationPointer, j])
                            {
                                MotherGenes[k] = false;
                                break;
                            }
                        }
                    }
                    else
                    {
                        Crossover[j] = 0;
                    }
                }
                int NextMotherGene = 0;

                //Create the Offspring
                for (int j = 0; j < GeneNum; j++)
                {
                    if (Crossover[j] == 1)
                    {
                        Offspring[i, j] = Population[BullPopulationPointer, j]; //copy the father gene to the offspring if there is a 1 in the crossover string
                    }
                    else
                    {
                        //Find the next mother gene to use
                        while (NextMotherGene < GeneNum)
                        {
                            if (MotherGenes[NextMotherGene])
                            {
                                Offspring[i, j] = Population[i, NextMotherGene];
                                NextMotherGene++;
                                break;
                            }
                            else
                            {
                                NextMotherGene++;
                            }
                        }
                    }
                }
                //Mutate the offspring
                Mutate(i, MutationProbability, ref Offspring);
                OffspringFitness[i] = CalcFitness(ref Offspring, i);
                OffspringIndex[i] = i;
            }
            //Time to die
            //Calculate the number of cows to die
            int DeathToll = (int)((double)PopulationSize * DeathRate / 100.0); //Gross Death Toll

            //Pick the weakest herd members to die
            double[] HerdFitness = new double[PopulationSize];
            int[] HerdIndex = new int[PopulationSize];
            for (int i = 0; i < PopulationSize; i++)
            {
                HerdFitness[i] = FitnessArray[i];
                HerdIndex[i] = i;
            }
            //Sort the array to set up survival of the fittest
            Array.Sort(OffspringFitness, OffspringIndex);
            //myReverserClass rc = new myReverserClass();
            ReverseComparer rc = new ReverseComparer();
            Array.Sort(HerdFitness, HerdIndex, rc); //Sorts the HerdIndex Array from worst to best according to the herdindex

            // kill the weak and insert the fittest offspring
            for (int i = 0; i < DeathToll; i++)
            {
                int idxHerd = HerdIndex[i];
                int idxOffSpring = OffspringIndex[i];

                for (int j = 0; j < GeneNum; j++)
                {
                    //replace the dead members with the best new offspring
                    Population[idxHerd, j] = Offspring[idxOffSpring, j];
                }
                FitnessArray[idxHerd] = OffspringFitness[i];
            }
        }

        private void CreateScheduleDataTable(int[] genes)
        {
            DataTable dt = new DataTable();
            DataRow dr;

            //create a new data column, set the type and name, and add it to the table
            DataColumn dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Sequence Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Job Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Product Index";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Product Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Product Name";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Early Start";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Double");
            dc.ColumnName = "Setup Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Start Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Double");
            dc.ColumnName = "Run Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "End Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Time Due";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Double");
            dc.ColumnName = "Order Quantity";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Resource Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Resource Name";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Production Order";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Allergens";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Allergen Alert";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Resource Late";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Service Late";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Early Violation";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Resource Feasibility";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "BOM Violation";
            dc.ReadOnly = false;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            DateTime d = DateTime.Today;

            //**************************************************************

            int jMax = ScheduleResult.GetUpperBound(1) + 1;

            int BestIndex = FindBestIndex();

            for (int i = 0; i < jMax; i++)
            {
                int Job;
                int Product;
                //Job = Population[BestIndex, i];
                Job = genes[i];
                Product = JobsToSchedule[Job];
                ScheduleResult[0, i] = Job;
                ScheduleResult[1, i] = Product;
                if (Product == -1)
                {
                    ScheduleResult[2, i] = "Slack";
                    ScheduleResult[4, i] = UNCONSTRAINED_TIME;
                }
                else
                {
                    ScheduleResult[2, i] = ProductName[Product];
                    ScheduleResult[4, i] = Priority[Job];
                }
                ScheduleResult[5, i] = (int)(Math.Truncate((double)i / (double)NumberOfRealJobs)) + 1;
            }
            //put the time and setuptime into the schedule
            CalcTime(ref ScheduleResult, 3, 6, BestIndex);

            //Update the number of late jobs
            NumberOfServiceLateJobs = 0;
            NumberOfResourceLateJobs = 0;
            NumberOfResourceFeasibilityViolations = 0;
            NumberOfEarlyStartViolations = 0;
            NumberOfBOMViolations = 0; // Added 3/24/13

            for (int i = 0; i < jMax; i++)
            {
                dr = dt.NewRow();
                int Product = Convert.ToInt32(ScheduleResult[1, i]);
                int ResourceNum = (int)ScheduleResult[5, i] - 1;
                //Todo Could add a filter to skip delay jobs here (delay jobs are input with product code 9999 currently)
                if (Product != -1 & Product != 9999) //Skip slack jobs
                {
                    int LastRow = dt.Rows.Count - 1;
                    dr["Sequence Number"] = LastRow + 2;
                    int CurrentJob = (int)ScheduleResult[0, i];
                    dr["Job Number"] = CurrentJob;
                    dr["Product Index"] = Product;
                    // todo: replace 3333 with actual product number
                    dr["Product Number"] = 3333; //masterData.Tables["Products"].Rows[Product]["Product Number"];
                    dr["Product Name"] = ScheduleResult[2, i];

                    dr["End Time"] = Conversions.ConvertDate((double)ScheduleResult[3, i]);
                    // In generating the delay jobs on the fly there is a problem on this line with ScheduleResult[0,i] being out of range of
                    // masterData.Tables["Orders"].Rows
                    // todo: replace 6666 with actual production order number
                    dr["Production Order"] = 6666; //masterData.Tables["Orders"].Rows[(int)ScheduleResult[0, i]]["Production Order"];
                    dr["Setup Time"] = (double)(ScheduleResult[6, i]) * 60.0;//Convert Decimal Hour Setup Time to Minutes
                    dr["Run Time"] = JobRunTime[CurrentJob] * 60; //Convert Decimal Hour Run Times to Minutes
                    dr["Order Quantity"] = OrderQty[CurrentJob];

                    DateTime st = Conversions.ConvertDate((double)ScheduleResult[3, i]);
                    TimeSpan rm = new TimeSpan(0, (int)(JobRunTime[CurrentJob] * 60), 0);
                    st -= rm;
                    dr["Start Time"] = st;

                    dr["Early Start"] = Conversions.ConvertDate(EarlyStart[CurrentJob]);
                    if (st < Conversions.ConvertDate(EarlyStart[CurrentJob]) & EarlyStart[CurrentJob] != 0)
                    {
                        NumberOfEarlyStartViolations++;
                        dr["Early Violation"] = true;
                    }
                    else
                    {
                        dr["Early Violation"] = false;
                    }


                    if ((double)ScheduleResult[3, i] > (double)ScheduleResult[4, i])
                    {
                        NumberOfServiceLateJobs++;
                        dr["Service Late"] = true;
                    }
                    else
                    {
                        dr["Service Late"] = false;
                    }
                    if ((double)ScheduleResult[3, i] > ProdEndTime[ResourceNum])
                    {
                        NumberOfResourceLateJobs++;
                        dr["Resource Late"] = true;
                    }
                    else
                    {
                        dr["Resource Late"] = false;
                    }

                    // calculate infeasible resources
                    int prod = (int)ScheduleResult[1, i]; //find the product
                    int rn = (int)ScheduleResult[5, i] - 1;  //find the resource (base zero)
                    double rp = ResourcePreference[prod, rn];
                    if (rp == ResourceNotFeasible)
                    {
                        NumberOfResourceFeasibilityViolations++;
                        dr["Resource Feasibility"] = true;
                    }
                    else
                    {
                        dr["Resource Feasibility"] = false;
                    }

                    //Initialize BOM Violation to false as a defualt
                    dr["BOM Violation"] = false;

                    dr["Allergens"] = AllergensInProduct[Product];
                    dr["Resource Number"] = ScheduleResult[5, i];
                    dr["Resource Name"] = ResourceName[(int)ScheduleResult[5, i] - 1];
                    // set the allergen alerts
                    dr["Allergen Alert"] = Allergens.None;


                    if (LastRow == -1 & ConstrainedStart[ResourceNum])
                    {
                        dr["Allergen Alert"] = AllergenAlert(StartProduct[ResourceNum], Product);
                    }
                    if (i > 0 & LastRow > -1)
                    {
                        int pResc = (int)dt.Rows[LastRow]["Resource Number"] - 1;
                        if (ResourceNum == pResc)
                        {
                            dr["Allergen Alert"] = AllergenAlert((int)dt.Rows[LastRow]["Product Index"], Product);
                        }
                        else
                        {
                            if (ConstrainedStart[ResourceNum])
                            {
                                dr["Allergen Alert"] = AllergenAlert(StartProduct[ResourceNum], Product);
                            }
                            else
                            {
                                dr["Allergen Alert"] = Allergens.None;
                            }
                        }
                    }

                    //convert the decimal due date to a date or a blank if unconstrained
                    double decDate = (double)ScheduleResult[4, i];
                    //double decDate = Priority[Job];
                    if (decDate == UNCONSTRAINED_TIME)
                    {
                        dr["Time Due"] = DBNull.Value;
                    }
                    else
                    {
                        dr["Time Due"] = Conversions.ConvertDate(decDate);
                    }

                    //convert unconstrained early start time to a blank
                    DateTime es = (DateTime)dr["Early Start"];
                    if (es == DateTime.Today)
                    {
                        dr["Early Start"] = DBNull.Value;
                    }

                    //ToDo 3/26 it looks like I messed up the logic near here
                    dt.Rows.Add(dr);


                }
            }
            // 3/24/13 changes
            // Display BOM Violations - Need to go back through the data set to find all potential BOM violaionns
            NumberOfBOMViolations = 0;

            //// List of production orders to support calculation of BOM Item requirements
            //List<ProdSchedule> pSched = new List<ProdSchedule>();

            //******************************************************************************************
            //Get ready to check for BOM violations
            if (BOMItems.Count > 0) //This is purely a speed enhancement to skip this section if there are no BOM items.
            {
                List<ProdSchedule> pSched = new List<ProdSchedule>();
                int rMax = dt.Rows.Count - 1;
                for (int i = 0; i < rMax; i++)
                {
                    dr = dt.Rows[i];
                    double EndTime = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr["End Time"]);
                    double StartTime = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr["Start Time"]);
                    double OrderQuantity = (double)dr["Order Quantity"];
                    int ProductIndex = (int)dr["Product Index"];
                    int JobNum = (int)dr["Job Number"];
                    //Build the output schedule for BOM Items
                    //First create a new production schedule item
                    ProdSchedule p = new ProdSchedule(ProductIndex, StartTime, EndTime, OrderQuantity, JobNum);
                    //Second, add the new schedule item to the list
                    if ((string)dr["Product Number"] != "9999") pSched.Add(p); //don't add slack jobs
                }


                List<ProdSchedule> ComponentSchedule = new List<ProdSchedule>();
                foreach (ProdSchedule ps in pSched)
                {
                    // Find out if the item has components
                    int bIdx = BOMItemIndex[ps.Product];
                    if (bIdx == -1) continue;
                    int cIdx = -1;
                    BOMItem bi = BOMItems[bIdx];
                    foreach (int component in bi.Components)
                    {
                        cIdx++;
                        //add the demand of the component quantity to the schedule
                        double ComponentDemand = -(ps.OrderQty * bi.Percent[cIdx]);

                        //Note: StartTime is used twice in the line below. This is not a mistake.
                        //Component demand is not a real scheduled job.
                        //This simplification makes sure the demand occurs at the start of the parent job.
                        //Adding .0001 keeps the posting sequence = (debit inventory first at any given time then credit)
                        ProdSchedule cd = new ProdSchedule(component, ps.StartTime, ps.StartTime + 0.0001, ComponentDemand, ps.JobNum);
                        ComponentSchedule.Add(cd);
                    }

                }
                pSched.AddRange(ComponentSchedule);
                pSched.Sort();

                int pProd = -99; // set up a variable to hold the previous product
                double pQty = 0; //set up a variable to hold the previous quantity

                //Calculate the available quantities
                foreach (ProdSchedule ps in pSched)
                {
                    // Calculate the penalty
                    if (pProd == ps.Product)
                    {
                        pQty += ps.OrderQty;
                        ps.AvailableQuantity = pQty;
                    }
                    else
                    {
                        pQty = ps.OrderQty;
                        pProd = ps.Product;
                        ps.AvailableQuantity = pQty;
                    }
                    if (ps.AvailableQuantity < 0.0)
                    {
                        //BOMPenalties += BOMPenaltyCost;
                        //ScheduleViolationBOM = true;
                        NumberOfBOMViolations += 1;

                        // Update the output BOM Violations
                        int rwMax = dt.Rows.Count - 1;
                        for (int i = 0; i < rwMax; i++)
                        {
                            dr = dt.Rows[i];
                            int JobNum = (int)dr["Job Number"];
                            if (JobNum == ps.JobNum & ps.Product != -1)
                            {
                                dr["BOM Violation"] = true;
                                break;
                            }
                        }


                    }
                }
            }


            // Eliminate the delay jobs from the dataset
            int r = dt.Rows.Count - 1;
            for (int i = r; i >= 0; i--)
            {
                dr = dt.Rows[i];
                if ((int)dr["Product Index"] == DelayIndex & DelayIndex >= 0)
                {
                    dt.Rows[i].Delete();
                }
            }



            ScheduleDataSet = new DataSet();
            //Add the new DataTable to the dataset
            ScheduleDataSet.Tables.Add(dt);
        }
        private void CreateScheduleDataTable(int[] genes, double[] delayTimes)
        {
            DataTable dt = new DataTable();
            DataRow dr;

            //create a new data column, set the type and name, and add it to the table
            DataColumn dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Sequence Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Job Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Product Index";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Product Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Product Name";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Early Start";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Double");
            dc.ColumnName = "Setup Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Start Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Double");
            dc.ColumnName = "Run Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "End Time";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.DateTime");
            dc.ColumnName = "Time Due";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Double");
            dc.ColumnName = "Order Quantity";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = Type.GetType("System.Int32");
            dc.ColumnName = "Resource Number";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Resource Name";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Production Order";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Allergens";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.String");
            dc.ColumnName = "Allergen Alert";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Resource Late";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Service Late";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Early Violation";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "Resource Feasibility";
            dc.ReadOnly = true;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            dc = new DataColumn();
            dc.DataType = System.Type.GetType("System.Boolean");
            dc.ColumnName = "BOM Violation";
            dc.ReadOnly = false;
            dc.AutoIncrement = false;
            dt.Columns.Add(dc);

            DateTime d = DateTime.Today;

            //**************************************************************

            int jMax = ScheduleResult.GetUpperBound(1) + 1;

            int BestIndex = FindBestIndex();

            for (int i = 0; i < jMax; i++)
            {
                int Job;
                int Product;
                //Job = Population[BestIndex, i];
                Job = genes[i];
                Product = JobsToSchedule[Job];
                ScheduleResult[0, i] = Job;
                ScheduleResult[1, i] = Product;
                if (Product == -1)
                {
                    ScheduleResult[2, i] = "Slack";
                    ScheduleResult[4, i] = UNCONSTRAINED_TIME;
                }
                else
                {
                    ScheduleResult[2, i] = ProductName[Product];
                    ScheduleResult[4, i] = Priority[Job];
                }
                ScheduleResult[5, i] = (int)(Math.Truncate((double)i / (double)NumberOfRealJobs)) + 1;
            }
            //put the time and setuptime into the schedule
            CalcTime(ref ScheduleResult, 3, 6, genes, delayTimes);

            //Update the number of late jobs
            NumberOfServiceLateJobs = 0;
            NumberOfResourceLateJobs = 0;
            NumberOfResourceFeasibilityViolations = 0;
            NumberOfEarlyStartViolations = 0;
            NumberOfBOMViolations = 0; // Added 3/24/13

            for (int i = 0; i < jMax; i++)
            {
                dr = dt.NewRow();
                int Product = Convert.ToInt32(ScheduleResult[1, i]);
                int ResourceNum = (int)ScheduleResult[5, i] - 1;
                //Todo Could add a filter to skip delay jobs here (delay jobs are input with product code 9999 currently)
                if (Product != -1 & Product != 9999) //Skip slack jobs
                {
                    int LastRow = dt.Rows.Count - 1;
                    dr["Sequence Number"] = LastRow + 2;
                    int CurrentJob = (int)ScheduleResult[0, i];
                    dr["Job Number"] = CurrentJob;
                    dr["Product Index"] = Product;
                    // todo: replace 3333 with actual product number
                    dr["Product Number"] = 3333; //masterData.Tables["Products"].Rows[Product]["Product Number"];
                    dr["Product Name"] = ScheduleResult[2, i];

                    dr["End Time"] = Conversions.ConvertDate((double)ScheduleResult[3, i]);
                    // In generating the delay jobs on the fly there is a problem on this line with ScheduleResult[0,i] being out of range of
                    // masterData.Tables["Orders"].Rows
                    // todo: replace 6666 with actual production order number
                    dr["Production Order"] = 6666; //masterData.Tables["Orders"].Rows[(int)ScheduleResult[0, i]]["Production Order"];
                    dr["Setup Time"] = (double)(ScheduleResult[6, i]) * 60.0;//Convert Decimal Hour Setup Time to Minutes
                    dr["Run Time"] = JobRunTime[CurrentJob] * 60; //Convert Decimal Hour Run Times to Minutes
                    dr["Order Quantity"] = OrderQty[CurrentJob];

                    DateTime st = Conversions.ConvertDate((double)ScheduleResult[3, i]);
                    TimeSpan rm = new TimeSpan(0, (int)(JobRunTime[CurrentJob] * 60), 0);
                    st -= rm;
                    dr["Start Time"] = st;

                    dr["Early Start"] = Conversions.ConvertDate(EarlyStart[CurrentJob]);
                    if (st < Conversions.ConvertDate(EarlyStart[CurrentJob]) & EarlyStart[CurrentJob] != 0)
                    {
                        NumberOfEarlyStartViolations++;
                        dr["Early Violation"] = true;
                    }
                    else
                    {
                        dr["Early Violation"] = false;
                    }


                    if ((double)ScheduleResult[3, i] > (double)ScheduleResult[4, i])
                    {
                        NumberOfServiceLateJobs++;
                        dr["Service Late"] = true;
                    }
                    else
                    {
                        dr["Service Late"] = false;
                    }
                    if ((double)ScheduleResult[3, i] > ProdEndTime[ResourceNum])
                    {
                        NumberOfResourceLateJobs++;
                        dr["Resource Late"] = true;
                    }
                    else
                    {
                        dr["Resource Late"] = false;
                    }

                    // calculate infeasible resources
                    int prod = (int)ScheduleResult[1, i]; //find the product
                    int rn = (int)ScheduleResult[5, i] - 1;  //find the resource (base zero)
                    double rp = ResourcePreference[prod, rn];
                    if (rp == ResourceNotFeasible)
                    {
                        NumberOfResourceFeasibilityViolations++;
                        dr["Resource Feasibility"] = true;
                    }
                    else
                    {
                        dr["Resource Feasibility"] = false;
                    }

                    //Initialize BOM Violation to false as a defualt
                    dr["BOM Violation"] = false;

                    dr["Allergens"] = AllergensInProduct[Product];
                    dr["Resource Number"] = ScheduleResult[5, i];
                    dr["Resource Name"] = ResourceName[(int)ScheduleResult[5, i] - 1];
                    // set the allergen alerts
                    dr["Allergen Alert"] = Allergens.None;


                    if (LastRow == -1 & ConstrainedStart[ResourceNum])
                    {
                        dr["Allergen Alert"] = AllergenAlert(StartProduct[ResourceNum], Product);
                    }
                    if (i > 0 & LastRow > -1)
                    {
                        int pResc = (int)dt.Rows[LastRow]["Resource Number"] - 1;
                        if (ResourceNum == pResc)
                        {
                            dr["Allergen Alert"] = AllergenAlert((int)dt.Rows[LastRow]["Product Index"], Product);
                        }
                        else
                        {
                            if (ConstrainedStart[ResourceNum])
                            {
                                dr["Allergen Alert"] = AllergenAlert(StartProduct[ResourceNum], Product);
                            }
                            else
                            {
                                dr["Allergen Alert"] = Allergens.None;
                            }
                        }
                    }

                    //convert the decimal due date to a date or a blank if unconstrained
                    double decDate = (double)ScheduleResult[4, i];
                    //double decDate = Priority[Job];
                    if (decDate == UNCONSTRAINED_TIME)
                    {
                        dr["Time Due"] = DBNull.Value;
                    }
                    else
                    {
                        dr["Time Due"] = Conversions.ConvertDate(decDate);
                    }

                    //convert unconstrained early start time to a blank
                    DateTime es = (DateTime)dr["Early Start"];
                    if (es == DateTime.Today)
                    {
                        dr["Early Start"] = DBNull.Value;
                    }

                    //ToDo 3/26 it looks like I messed up the logic near here
                    dt.Rows.Add(dr);


                }
            }
            // 3/24/13 changes
            // Display BOM Violations - Need to go back through the data set to find all potential BOM violaionns
            NumberOfBOMViolations = 0;

            //// List of production orders to support calculation of BOM Item requirements
            //List<ProdSchedule> pSched = new List<ProdSchedule>();

            //******************************************************************************************
            //Get ready to check for BOM violations
            if (BOMItems.Count > 0) //This is purely a speed enhancement to skip this section if there are no BOM items.
            {
                List<ProdSchedule> pSched = new List<ProdSchedule>();
                int rMax = dt.Rows.Count - 1;
                for (int i = 0; i < rMax; i++)
                {
                    dr = dt.Rows[i];
                    double EndTime = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr["End Time"]);
                    double StartTime = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr["Start Time"]);
                    double OrderQuantity = (double)dr["Order Quantity"];
                    int ProductIndex = (int)dr["Product Index"];
                    int JobNum = (int)dr["Job Number"];
                    //Build the output schedule for BOM Items
                    //First create a new production schedule item
                    ProdSchedule p = new ProdSchedule(ProductIndex, StartTime, EndTime, OrderQuantity, JobNum);
                    //Second, add the new schedule item to the list
                    if ((string)dr["Product Number"] != "9999") pSched.Add(p); //don't add slack jobs
                }


                List<ProdSchedule> ComponentSchedule = new List<ProdSchedule>();
                foreach (ProdSchedule ps in pSched)
                {
                    // Find out if the item has components
                    int bIdx = BOMItemIndex[ps.Product];
                    if (bIdx == -1) continue;
                    int cIdx = -1;
                    BOMItem bi = BOMItems[bIdx];
                    foreach (int component in bi.Components)
                    {
                        cIdx++;
                        //add the demand of the component quantity to the schedule
                        double ComponentDemand = -(ps.OrderQty * bi.Percent[cIdx]);

                        //Note: StartTime is used twice in the line below. This is not a mistake.
                        //Component demand is not a real scheduled job.
                        //This simplification makes sure the demand occurs at the start of the parent job.
                        //Adding .0001 keeps the posting sequence = (debit inventory first at any given time then credit)
                        ProdSchedule cd = new ProdSchedule(component, ps.StartTime, ps.StartTime + 0.0001, ComponentDemand, ps.JobNum);
                        ComponentSchedule.Add(cd);
                    }

                }
                pSched.AddRange(ComponentSchedule);
                pSched.Sort();

                int pProd = -99; // set up a variable to hold the previous product
                double pQty = 0; //set up a variable to hold the previous quantity

                //Calculate the available quantities
                foreach (ProdSchedule ps in pSched)
                {
                    // Calculate the penalty
                    if (pProd == ps.Product)
                    {
                        pQty += ps.OrderQty;
                        ps.AvailableQuantity = pQty;
                    }
                    else
                    {
                        pQty = ps.OrderQty;
                        pProd = ps.Product;
                        ps.AvailableQuantity = pQty;
                    }
                    if (ps.AvailableQuantity < 0.0)
                    {
                        //BOMPenalties += BOMPenaltyCost;
                        //ScheduleViolationBOM = true;
                        NumberOfBOMViolations += 1;

                        // Update the output BOM Violations
                        int rwMax = dt.Rows.Count - 1;
                        for (int i = 0; i < rwMax; i++)
                        {
                            dr = dt.Rows[i];
                            int JobNum = (int)dr["Job Number"];
                            if (JobNum == ps.JobNum & ps.Product != -1)
                            {
                                dr["BOM Violation"] = true;
                                break;
                            }
                        }
                    }
                }
            }

            // Eliminate the delay jobs from the dataset
            int r = dt.Rows.Count - 1;
            for (int i = r; i >= 0; i--)
            {
                dr = dt.Rows[i];
                if ((int)dr["Product Index"] == DelayIndex & DelayIndex >= 0)
                {
                    dt.Rows[i].Delete();
                }
            }

            ScheduleDataSet = new DataSet();
            //Add the new DataTable to the dataset
            ScheduleDataSet.Tables.Add(dt);
        }

        // This is the main method invoked to begin the scheduling process
        public double Schedule(double StrengthOfFather, double MutationProbability, int NumberOfGenerations,
                                double DeathRate, int NumNonRandom, int PopulationSize)
        {
            // The new function only exists to support "demo" code.
            DateTime now = new DateTime();
            now = DateTime.Today;
            if (now > DateTime.Parse("7/01/2013"))
            {
                throw new ApplicationException("***** Time limit for this demo version is exceeded.******\n\r Please contact Junction Solutions to obtain an updated and licensed version.\n\r");
            }

            int NumJobs = JobsToSchedule.GetUpperBound(0) + 1;
            Offspring = new int[PopulationSize, NumJobs];
            Population = new int[PopulationSize, NumJobs];
            ScheduleResult = new object[7, NumJobs];
            FitnessArray = new double[PopulationSize];
            //bool Stopped = false; //Allow for interruption of a scheduling run
            IsFeasible = false;



            //    'Randomly create a population to establish a starting point
            CreatePopulation(NumNonRandom);


            //    display the status form
            StatusForm frmStatus = new StatusForm();
            if (ShowStatusWhileRunning)
            {
                frmStatus.Visible = true;
                frmStatus.lblGeneration.Text = "Initialized";
                frmStatus.lblFeasible.Text = "No Feasible Solution Found";
            }
            double eliteFitness = 0;
            // BSM:
            // GeneticOptimizer.GA is just a refactored version of the original
            // GeneticOptimizer.CGA is modified to remove delayjobs
            int popsize = 50;
            if (runRefactored)
            {
                GA = new GeneticOptimizer.GA(1, NumJobs, popsize, popsize, 0.05);
                GA.FitnessFunction = this.CalcFitness;
                GA.EvaluatePopulation();
                double avgf = 0;
                for (int i = 0; i < 1000; i++)
                {
                    CGA.GenerateOffspring();
                    CGA.SurvivalSelection();
                    avgf = CGA.AverageFitness();
                    if (i % 100 == 0)
                    {
                        frmStatus.lblCurrentValue.Text = avgf.ToString();
                    }
                }
            }
            else if (runConstrained)
            {
                CGA = new ConstrainedGeneticOptimizer.ConstrainedGA(1, NumJobs, popsize, popsize, 0.05);
                CGA.FitnessFunction = this.CCalcFitness;
                CGA.EvaluatePopulation();
                double avgf = 0;
                for (int i = 0; i < 1000; i++)
                {
                    CGA.GenerateOffspring();
                    CGA.SurvivalSelection();
                    avgf = CGA.AverageFitness();
                    if (ShowStatusWhileRunning & (i % 100 == 0))
                    {
                        //frmStatus.lblCurrentValue.Text = avgf.ToString();

                        //Update the status form

                        frmStatus.lblGeneration.Text = "Generation " + i.ToString();
                        //BestIndex = FindBestIndex();
                        //Best = FitnessArray[BestIndex];
                        //frmStatus.lblCurrentValue.Text = Best.ToString();
                        eliteFitness = avgf;
                        frmStatus.lblCurrentValue.Text = avgf.ToString();
                        //ToString();
                        frmStatus.lblCurrentValue.Text = String.Format("Fitness ={0: #,###.00}", eliteFitness);

                        if (IsFeasible)
                        {
                            frmStatus.lblFeasible.Text = "Feasible Solution Found";
                        }

                        if (frmStatus.cbStopped.Checked)
                        {
                            break;
                        }
                        System.Windows.Forms.Application.DoEvents();
                    }
                }

                // Close the status form
                frmStatus.Close();
                frmStatus = null;
                //BestIndex = FindBestIndex();
                //Best = FitnessArray[BestIndex];
                // Create a data table with the schedule
                int[] best = new int[NumJobs];
                for (int i = 0; i < NumJobs; i++)
                {
                    best[i] = CGA.population[0].Genes[i];//Population[BestIndex, i];
                }
                CreateScheduleDataTable(best, CGA.population[0].Times);


            }
            else
            {
                //    Begin Evolution
                //    Use supremacy mating
                //       Have strongest bulls mate with a selected herd of the others
                //       Replace any solution that is not as strong as the current worst offspring
                int BestIndex;
                double Best;
                for (int i = 1; i < NumberOfGenerations; i++)
                {
                    Mate(FindBestIndex(), StrengthOfFather, DeathRate, MutationProbability);

                    //Update the status form
                    if (ShowStatusWhileRunning & (i % 100 == 0))
                    {
                        frmStatus.lblGeneration.Text = "Generation " + i.ToString();
                        BestIndex = FindBestIndex();
                        Best = FitnessArray[BestIndex];
                        //frmStatus.lblCurrentValue.Text = Best.ToString();
                        frmStatus.lblCurrentValue.Text = String.Format("Fitness ={0: #,###.00}", Best);

                        if (IsFeasible)
                        {
                            frmStatus.lblFeasible.Text = "Feasible Solution Found";
                        }

                        if (frmStatus.cbStopped.Checked)
                        {
                            break;
                        }
                        System.Windows.Forms.Application.DoEvents();
                    }
                }

                // Close the status form
                frmStatus.Close();
                frmStatus = null;
                BestIndex = FindBestIndex();
                Best = FitnessArray[BestIndex];
                // Create a data table with the schedule
                int[] best = new int[NumJobs];
                for (int i = 0; i < NumJobs; i++)
                {
                    best[i] = Population[BestIndex, i];
                }
                CreateScheduleDataTable(best);
                return Best;
            }
            return eliteFitness;
        }

        private double CalcAllergenChangeOver(int FromProduct, int ToProduct)
        {
            if (FromProduct == ToProduct)
            {
                return 0;
            }

            Allergens fJob = Allergens.None;
            Allergens tJob = Allergens.None;

            //find the allergens in the "from" job
            string fStr = AllergensInProduct[FromProduct];
            foreach (char c in fStr)
            {
                for (int i = 0; i < AllergenList.GetUpperBound(0); i++)
                {
                    if (c == AllergenList[i])
                    {
                        fJob = fJob | (Allergens)System.Math.Pow(2.0, (double)i);
                    }
                }
            }
            //find the allergens in the "to" job
            string tStr = AllergensInProduct[ToProduct];
            foreach (char c in tStr)
            {
                for (int i = 0; i < AllergenList.GetUpperBound(0); i++)
                {
                    if (c == AllergenList[i])
                    {
                        tJob = tJob | (Allergens)System.Math.Pow(2.0, (double)i);
                    }
                }
            }

            // find the allergens that were in the "from job" that are not in the "to job". 
            Allergens temp = fJob ^ tJob;
            Allergens result = temp & fJob;

            if (result == Allergens.None)
            {
                return 0; // This is a hard coded penalty to return
            }
            else
            {
                return WashTime;
            }
        }

        private Allergens AllergenAlert(int FromProduct, int ToProduct)
        {
            //char[] AllergenList = new char[] { 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I' };

            Allergens fJob = Allergens.None;
            Allergens tJob = Allergens.None;

            //find up the allergens in the "from" job
            string fStr = AllergensInProduct[FromProduct];
            foreach (char c in fStr)
            {
                for (int i = 0; i < AllergenList.GetUpperBound(0); i++)
                {
                    if (c == AllergenList[i])
                    {
                        fJob = fJob | (Allergens)System.Math.Pow(2.0, (double)i);
                    }
                }
            }
            //find up the allergens in the "to" job
            string tStr = AllergensInProduct[ToProduct];
            foreach (char c in tStr)
            {
                for (int i = 0; i < AllergenList.GetUpperBound(0); i++)
                {
                    if (c == AllergenList[i])
                    {
                        tJob = tJob | (Allergens)System.Math.Pow(2.0, (double)i);
                    }
                }
            }

            // find the allergens that were in the "from job" that are not in the "to job". 
            Allergens temp = fJob ^ tJob;
            Allergens result = temp & fJob;

            return result;
        }

        private void SetProdData(DataTable dt)
        {
            int i = 0;
            int numberOfProducts = 0;
            if (doGenerateDelay)
            {
                foreach (DataRow dr in dt.Rows)
                {
                    // Count the number of real products 
                    string ProdNum = dr["Product Number"].ToString();
                    if (ProdNum != "9999")
                    {
                        numberOfProducts++;
                    }
                }
                numberOfProducts += 1;
            }
            else
            {
                numberOfProducts = dt.Rows.Count;
            }

            //redimension the arrays to hold the product data
            ProductName = new string[numberOfProducts];
            AllergensInProduct = new string[numberOfProducts];

            BOMItemIndex = new int[numberOfProducts];
            //initialize the BOMItemIndex so that all values are -1;
            //The correct values will be set in the SetBOMData method
            for (int j = 0; j < numberOfProducts; j++)
            {
                BOMItemIndex[j] = -1;
            }

            ProductNumberHash = new System.Collections.Hashtable();
            ResourcePreference = new double[numberOfProducts, NumberOfResources];

            foreach (DataRow dr in dt.Rows)
            {
                ProductName[i] = (string)dr["Product Name"]; //Read in the product name
                string ProdNum = dr["Product Number"].ToString();
                if (doGenerateDelay & ProdNum == "9999")
                {
                    break;
                }
                //todo  change delay index
                if (ProdNum == "9999")
                {
                    DelayIndex = i;
                }
                ProductNumberHash.Add(dr["Product Number"].ToString(), i);
                if (dr.IsNull(4))
                {
                    AllergensInProduct[i] = "";
                }
                else
                {
                    AllergensInProduct[i] = (string)dr["Allergens"];
                }
                //Adding resource affinity here. 
                for (int j = 5; j < 5 + NumberOfResources; j++)
                {
                    int pref = (int)(double)dr[j]; ;
                    if (pref == 0)
                    {
                        ResourcePreference[i, j - 5] = ResourceNotFeasible;
                    }
                    else
                    {
                        ResourcePreference[i, j - 5] = (ResourcePref / pref) - (ResourcePref / 10);
                    }
                }
                i++;
            }
            // If we are generating DelayJobs on the fly, then make a Delay product as well:
            if (doGenerateDelay)
            {
                ProductName[numberOfProducts - 1] = "Delay";
                DelayIndex = i;
                ProductNumberHash.Add("9999", i);
                AllergensInProduct[i] = "";
                ResourcePreference[i, 0] = ResourceNotFeasible;
                for (int j = 1; j < NumberOfResources; j++)
                {
                    ResourcePreference[i, j] = (ResourcePref / 10) - (ResourcePref / 10);
                }
            }
        }

        private void SetBOMData(DataTable dt)
        {
            BOMItems.Clear();
            int r = 1;
            int ParentIndex;
            int rMax = dt.Rows.Count;
            foreach (DataRow dr in dt.Rows)
            {
                string Parent = (string)dr["Parent"].ToString();
                // Error catch statement added 4/23/2009
                try
                {
                    ParentIndex = (int)ProductNumberHash[Parent];
                }
                catch (Exception)
                {
                    ValidDataInput = false;
                    throw new ApplicationException("Invalid BOM Item " + Parent + " at row " + r + ". \r\n");
                }

                int iMax = dt.Columns.Count;
                List<int> myComponents = new List<int>();
                List<double> myPercent = new List<double>();
                for (int i = 1; i < iMax; i += 2)
                {
                    string Component = (string)dr[i].ToString();
                    if (Component == "") break;
                    int ComponentIndex;
                    // Error catch statement added 4/23/2009
                    try
                    {
                        ComponentIndex = (int)ProductNumberHash[Component];
                    }
                    catch (Exception)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException("Invalid Component Item " + Component + " at row " + r + ". \r\n");
                    }

                    myComponents.Add(ComponentIndex);
                    myPercent.Add((double)dr[i + 1]);
                }
                BOMItem bi = new BOMItem(ParentIndex, myComponents, myPercent);
                BOMItems.Add(bi);

                // Set the index to indicate that the item has BOM's
                BOMItemIndex[ParentIndex] = r - 1;

                r++;
            }

        }

        private void SetResourceData(DataTable dt)
        {
            NumberOfResources = dt.Rows.Count;
            // Dimension the resource related arrays
            productionEndTime = new DateTime[NumberOfResources];
            ProdEndTime = new double[NumberOfResources];
            productionStartTime = new DateTime[NumberOfResources];
            ProdStartTime = new double[NumberOfResources];
            StartProduct = new int[NumberOfResources];
            ConstrainedStart = new bool[NumberOfResources];
            RLCMax = new double[NumberOfResources];
            RLCMin = new double[NumberOfResources];
            RLCRatePerHour = new double[NumberOfResources];
            ResourceName = new string[NumberOfResources];
            MaxVolume = new double[NumberOfResources];
            MinVolume = new double[NumberOfResources];
            MaxFlowIn = new double[NumberOfResources];
            MaxFlowOut = new double[NumberOfResources];
            MaxInputs = new int[NumberOfResources];
            MaxOutputs = new int[NumberOfResources];
            ResourceType = new ResourceTypes[NumberOfResources];



            // Fill in the base data
            for (int i = 0; i < NumberOfResources; i++)
            {
                productionStartTime[i] = (DateTime)dt.Rows[i]["Start_Date_Time"];
                ProdStartTime[i] = Conversions.ConvertDateTimetoDecimalHours(productionStartTime[i]);
                productionEndTime[i] = (DateTime)dt.Rows[i]["End_Date_Time"];
                ProdEndTime[i] = Conversions.ConvertDateTimetoDecimalHours(productionEndTime[i]);
                RLCMin[i] = (double)dt.Rows[i]["LLCMin"];
                RLCMax[i] = (double)dt.Rows[i]["LLCMax"];
                RLCRatePerHour[i] = (double)dt.Rows[i]["LLCperHour"];
                ResourceName[i] = (string)dt.Rows[i]["Resource Name"];
                string rt = (string)dt.Rows[i]["Resource Type"];
                ResourceType[i] = (ResourceTypes)Enum.Parse(typeof(ResourceTypes), rt);

                if (ResourceType[i] == ResourceTypes.Tank)
                {
                    MaxVolume[i] = (double)dt.Rows[i]["Max Volume"];
                    MinVolume[i] = (double)dt.Rows[i]["Min Useable Volume"];
                    MaxFlowIn[i] = (double)dt.Rows[i]["Max Flow In"];
                    MaxFlowOut[i] = (double)dt.Rows[i]["Max Flow Out"];
                    MaxInputs[i] = (int)(double)dt.Rows[i]["Max Simultaneous Inputs"];
                    MaxOutputs[i] = (int)(double)dt.Rows[i]["Max Simultaneous Outputs"];
                }
            }
        }

        private void SetConstrainedStartData(DataTable dt)
        {
            for (int i = 0; i < NumberOfResources; i++)
            {
                if (dt.Rows[i].IsNull("Start Product"))
                {
                    StartProduct[i] = -1;
                    ConstrainedStart[i] = false;
                }
                else
                {
                    string StartProductStr = dt.Rows[i]["Start Product"].ToString();

                    StartProduct[i] = (int)ProductNumberHash[StartProductStr];
                    ConstrainedStart[i] = true;
                }

            }
        }

        private void SetChangeOverData(DataTable dt)
        {
            // This doesnt work for some reason:
            // Read up on how this "DataTable" thing works with Excel
            // int jMax = dt.Columns.Count - 1; //skip first column and then make zero based
            // int iMax = dt.Rows.Count;
            int jMax = dt.Columns.Count - 2;
            int iMax = dt.Rows.Count - 1;

            // Make sure the changeover matrix is valid
            int NumberOfProducts = ProductName.GetUpperBound(0) + 1;
            if (iMax != NumberOfProducts | jMax != NumberOfProducts)
            {
                throw new ApplicationException("Wrong number of rows or columns in the Change Over matrix.\r\n The number of rows and columns must be equal to the number of products. There were " + iMax + " rows, " + jMax + " columns, and " + NumberOfProducts + " Products found. \r\n Make sure there is no stray input, including blanks, on the changeover matrix spreadsheet.\r\n");
            }

            ChangeOver = new double[iMax, jMax];
            for (int i = 0; i < iMax; i++)
            {
                for (int j = 0; j < jMax; j++)
                {
                    try
                    {
                        ChangeOver[i, j] = (double)dt.Rows[i].ItemArray[j + 1] / 60.0;
                        ChangeOver[i, j] += CalcAllergenChangeOver(i, j);
                    }
                    catch (Exception)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException("Invalid changeover time at row " + (i + 2) + " column " + (j + 2) + ". \r\n");
                    }
                }
            }
        }

        private void SetChangeOverPenaltyData(DataTable dt)
        {
            // This doesnt work for some reason:
            // Read up on how this "DataTable" thing works with Excel
            // int jMax = dt.Columns.Count - 1; //skip first column and then make zero based
            // int iMax = dt.Rows.Count;
            int jMax = dt.Columns.Count - 2;
            int iMax = dt.Rows.Count - 1;

            // Make sure the changeover matrix is valid
            if (iMax != ProductName.GetUpperBound(0) + 1 | jMax != ProductName.GetUpperBound(0) + 1)
            {
                throw new ApplicationException("Wrong number of rows or columns in the Change Over Penalty matrix.\r\n The number of rows and columns must be equal to the number of products. There were " + iMax + " rows, " + jMax + " columns, and " + (ProductName.GetUpperBound(0) + 1) + " Products found. \r\n Make sure there is no stray input, including blanks, on the changeover penalty matrix spreadsheet.\r\n");
            }

            this.ChangeOverPenalties = new double[iMax, jMax];
            for (int i = 0; i < iMax; i++)
            {
                for (int j = 0; j < jMax; j++)
                {
                    try
                    {
                        this.ChangeOverPenalties[i, j] = (double)dt.Rows[i].ItemArray[j + 1];// / 60.0;
                        //this.ChangeOverPenalties[i, j] += CalcAllergenChangeOver(i, j);
                    }
                    catch (Exception)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException("Invalid changeover penalty at row " + (i + 2) + " column " + (j + 2) + ". \r\n");
                    }
                }
            }
        }

        private void SetOrderData(DataTable dt)
        {
            if (NumberOfResources < 1)
            {
                throw new ApplicationException("Order Data Set cannot be initialized. The Resources Data Table must be initialized first.\r\n");
            }
            // If we want to generate delay jobs on the fly instead of reading them from the input spreadsheet
            // Note: "NumberOfRealJobs" is misleading.
            // It is the number of actual orders with real products + number of delay jobs, whether they are generated or in the input spreadsheet. 
            int SlackJobs, TotalJobs;
            int numberOfDelayJobs = 0;
            NumberOfRealJobs = 0;
            if (doGenerateDelay)
            {
                foreach (DataRow dr in dt.Rows)
                {
                    // Count the number of real jobs. Generate the number of delay jobs
                    string ProdNum = dr["Product Number"].ToString();
                    if (ProdNum != "9999")
                    {
                        NumberOfRealJobs++;
                    }
                }
                numberOfDelayJobs = NumberOfRealJobs * 6;
                NumberOfRealJobs = NumberOfRealJobs + numberOfDelayJobs;
            }
            else
            {
                NumberOfRealJobs = masterData.Tables["Orders"].Rows.Count;
            }
            SlackJobs = (NumberOfRealJobs * NumberOfResources) - NumberOfRealJobs;
            TotalJobs = NumberOfRealJobs + SlackJobs;

            JobsToSchedule = new int[TotalJobs];
            Priority = new double[TotalJobs];
            EarlyStart = new double[TotalJobs];
            JobRunTime = new double[TotalJobs];
            OrderQty = new double[TotalJobs];
            MaxLateCost = new double[TotalJobs];
            MinLateCost = new double[TotalJobs];
            LateCostPerHour = new double[TotalJobs];
            MaxEarlyCost = new double[TotalJobs];
            MinEarlyCost = new double[TotalJobs];
            EarlyCostPerHour = new double[TotalJobs];

            double avgJobRunTime = 0;

            int i = 0;
            foreach (DataRow dr in dt.Rows)
            {
                try
                {
                    string ProdNum = dr["Product Number"].ToString();
                    if (doGenerateDelay & ProdNum == "9999")
                    {
                        break;
                    }
                    int ProdIndex = (int)ProductNumberHash[ProdNum];
                    OrderQty[i] = (double)dr["Quantity"];
                    JobsToSchedule[i] = ProdIndex;

                    JobRunTime[i] = (double)dr.ItemArray[3] / 60.0; //Read in the product run time and convert from minutes to decimal hours
                    avgJobRunTime += JobRunTime[i];

                    if (JobsToSchedule[i] > ProductName.GetUpperBound(0))
                    {
                        throw new ApplicationException();
                    }
                    // Load the order late cost penalties
                    MinLateCost[i] = (double)dr["Min Late Cost"];
                    MaxLateCost[i] = (double)dr["Max Late Cost"];
                    LateCostPerHour[i] = (double)dr["Late Cost Per Hour"];
                    // Load the order early cost penalties
                    MinEarlyCost[i] = (double)dr["Min Early Cost"];
                    MaxEarlyCost[i] = (double)dr["Max Early Cost"];
                    EarlyCostPerHour[i] = (double)dr["Early Cost Per Hour"];

                }
                catch (Exception)
                {
                    ValidDataInput = false;
                    throw new ApplicationException("Invalid Product Index. Error found at row " + (i + 2) + " in the Orders spreadsheet.\r\n");
                }
                //input the due time if not blank
                if (dr.IsNull(4))
                {
                    Priority[i] = UNCONSTRAINED_TIME;
                }
                else
                {
                    try
                    {
                        //Priority[i] = Conversions.ConvertMilitaryTimeStringToDecimalHours(dr.ItemArray[4].ToString());
                        Priority[i] = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr.ItemArray[4]);

                    }
                    catch (ApplicationException ex)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException(ex.Message + "Error found at row " + i + 2 + " in the Orders spreadsheet.\r\n");
                    }
                    catch (Exception ex)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException(ex.Message + "Error found at row " + i + 2 + " in the Orders spreadsheet.\r\n");
                    }
                }

                //input the early start time if not blank
                if (dr.IsNull("Early Start"))
                {
                    EarlyStart[i] = 0;
                }
                else
                {
                    try
                    {
                        EarlyStart[i] = Conversions.ConvertDateTimetoDecimalHours((DateTime)dr["Early Start"]);
                    }
                    catch (ApplicationException ex)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException(ex.Message + "Error found at row " + i + 2 + " in the Orders spreadsheet.\r\n");
                    }
                    catch (Exception ex)
                    {
                        ValidDataInput = false;
                        throw new ApplicationException(ex.Message + "Error found at row " + i + 2 + " in the Orders spreadsheet.\r\n");
                    }
                }

                i++;
            }

            avgJobRunTime = avgJobRunTime / (NumberOfRealJobs - numberOfDelayJobs);
            // Set up the generated delayjobs 
            if (doGenerateDelay)
            {
                for (int j = NumberOfRealJobs - numberOfDelayJobs; j < NumberOfRealJobs; j++)
                {
                    int ProdIndex = (int)ProductNumberHash["9999"];
                    OrderQty[j] = 1;
                    JobsToSchedule[j] = ProdIndex;

                    JobRunTime[j] = avgJobRunTime;

                    // Load the order late cost penalties
                    MinLateCost[j] = 0;
                    MaxLateCost[j] = 0;
                    LateCostPerHour[j] = 0;
                    // Load the order early cost penalties
                    MinEarlyCost[j] = 0;
                    MaxEarlyCost[j] = 0;
                    EarlyCostPerHour[j] = 0;
                }

            }
            //Set up the Slack Jobs
            if (TotalJobs > NumberOfRealJobs)
            {
                for (int j = NumberOfRealJobs; j < TotalJobs; j++)
                {
                    Priority[j] = UNCONSTRAINED_TIME;
                    JobsToSchedule[j] = -1; //Set this to a -1 to indicate that this is a slack job.
                }
            }
        }

        private double CalcFitness(int[] genes)
        {
            double Time = ProdStartTime[0];
            double NonDelayTime = Time; //Added 3/24 to elim delay time
            double JobStartTime, JobEndTime;
            double Fitness;
            double SumOfServiceEarlyPenalties = 0;
            double SumOfServiceLatePenalties = 0;
            double SumOfResourceLatePenalties = 0;
            double BOMPenalties = 0;
            int Previous = -1;
            bool ScheduleViolationBOM = false;
            bool ScheduleViolationResourceLate = false;
            bool ScheduleViolationOrderLate = false;
            bool ScheduleViolationResourceFeasiblilty = false;
            bool ScheduleViolationEarlyTime = false;
            double LateTime, EarlyTime;
            int CurrentProd;
            double TotalTimeAllResources = 0;
            int CurrentJob;
            double ResourcePrefPenalties = 0;
            double SumOfChangeOverPenalties = 0;
            double EarlyStartFactor = 0;

            // List of production orders to support calculation of BOM Item requirements
            List<ProdSchedule> pSched = new List<ProdSchedule>();


            for (int Resource = 0; Resource < NumberOfResources; Resource++)
            {
                Time = ProdStartTime[Resource];
                NonDelayTime = Time; // added to eliminate delay orders

                if (ConstrainedStart[Resource])
                {
                    Previous = StartProduct[Resource];
                }
                else
                {
                    Previous = -1;
                }
                // Calculate the time for the following jobs
                int FirstGeneInResource = NumberOfRealJobs * Resource;
                int LastGeneInResource = (NumberOfRealJobs * (Resource + 1)) - 1;
                double co, cop;
                for (int i = FirstGeneInResource; i <= LastGeneInResource; i++)
                {
                    CurrentJob = genes[i];
                    CurrentProd = JobsToSchedule[CurrentJob];
                    if (Previous != -1 & CurrentProd != -1)
                    {
                        co = ChangeOver[Previous, CurrentProd];
                        cop = ChangeOverPenalties[Previous, CurrentProd];
                    }
                    else
                    {
                        co = 0;
                        cop = 0;
                    }
                    // Change code to eliminate Delay Jobs from the fitness calculation as well as slack jobs
                    // Delay jobs are being coded manually as product 9999
                    //ToDo enhance input to give a better spread on delay jobs vs adding products and orders for delays. Get rid of the 9999 comparison.
                    //if (CurrentProd != -1)  Changed on 3/24/2012
                    if (CurrentProd != -1)
                    {

                        //This is a real job so process it
                        if (Previous == -1)
                        {
                            //First job on the resource was a slack job
                            JobStartTime = Time;
                            Time += JobRunTime[CurrentJob];
                            JobEndTime = Time;
                        }
                        else
                        {
                            //we have a real job in the previous variable
                            JobStartTime = Time;
                            Time += JobRunTime[CurrentJob] + co;
                            JobEndTime = Time;
                            // Find last non delay time on the resource

                        }
                        if (CurrentProd != DelayIndex)
                        {
                            //Used to find the last real job running on a resource
                            NonDelayTime = Time;
                            //Used to encourage jobs to start as soon as possible
                            //Todo  Turn Early start facto into a configurable factor (by resorce?)
                            EarlyStartFactor += JobStartTime;
                        }

                        Previous = JobsToSchedule[CurrentJob];

                        //Calculate Service Early Cost
                        EarlyTime = EarlyStart[CurrentJob];
                        if (JobStartTime < EarlyTime & EarlyTime != 0.0)
                        {
                            SumOfServiceEarlyPenalties += Math.Min(MaxEarlyCost[CurrentJob], MinEarlyCost[CurrentJob] + EarlyCostPerHour[CurrentJob] * (EarlyTime - (JobStartTime)));
                            ScheduleViolationEarlyTime = true;
                        }

                        //Calculate Service Late Cost
                        LateTime = Priority[CurrentJob];
                        if (Time > LateTime)
                        {
                            SumOfServiceLatePenalties += Math.Min(MaxLateCost[CurrentJob], MinLateCost[CurrentJob] + LateCostPerHour[CurrentJob] * (JobEndTime - Priority[CurrentJob]));
                            ScheduleViolationOrderLate = true;
                        }

                        //Calculate Resource Late Cost
                        if (Time > ProdEndTime[Resource])
                        {
                            SumOfResourceLatePenalties += Math.Min(RLCMax[Resource], RLCMin[Resource] + RLCRatePerHour[Resource] * (Time - ProdEndTime[Resource]));
                            ScheduleViolationResourceLate = true;
                        }

                        // Add the resource preference penalties
                        ResourcePrefPenalties += ResourcePreference[CurrentProd, Resource];
                        if (ResourcePreference[CurrentProd, Resource] == ResourceNotFeasible)
                        {
                            ScheduleViolationResourceFeasiblilty = true;
                        }

                        //Sum up the changeover penalties
                        SumOfChangeOverPenalties += cop;

                        //Build the output schedule for BOM Items
                        //First create a new production schedule item
                        ProdSchedule p = new ProdSchedule(CurrentProd, JobStartTime, JobEndTime, OrderQty[CurrentJob]);
                        //Second, add the new schedule item to the list
                        pSched.Add(p);
                    }
                }
                // Calculate the total production time required
                //TotalTimeAllResources += Time - ProdStartTime[Resource]; 
                TotalTimeAllResources += NonDelayTime - ProdStartTime[Resource];
            }

            //Get ready to check for BOM violations
            if (BOMItems.Count > 0) //This is purely a speed enhancement to skip this section if there are no BOM items.
            {
                List<ProdSchedule> ComponentSchedule = new List<ProdSchedule>();
                foreach (ProdSchedule ps in pSched)
                {
                    //Find out if the item has components
                    int bIdx = BOMItemIndex[ps.Product];
                    if (bIdx == -1) continue;
                    int cIdx = -1;
                    BOMItem bi = BOMItems[bIdx];
                    foreach (int component in bi.Components)
                    {
                        cIdx++;
                        //add the demand of the component quantity to the schedule
                        double ComponentDemand = -(ps.OrderQty * bi.Percent[cIdx]);
                        //Note: StartTime is used twice in the line below. This is not a mistake.
                        //Component demand is not a real scheduled job.
                        //This simplification makes sure the demand occurs at the start of the parent job.
                        //Adding .0001 keeps the posting sequence = (debit inventory first at any given time then credit)
                        ProdSchedule cd = new ProdSchedule(component, ps.StartTime, ps.StartTime + 0.0001, ComponentDemand);
                        ComponentSchedule.Add(cd);
                    }

                }
                pSched.AddRange(ComponentSchedule);
                pSched.Sort();
                int pProd = -99; // set up a variable to hold the previous product
                double pQty = 0; //set up a variable to hold the previous quantity

                //Calculate the available quantities
                foreach (ProdSchedule ps in pSched)
                {
                    // Calculate the penalty
                    if (pProd == ps.Product)
                    {
                        pQty += ps.OrderQty;
                        ps.AvailableQuantity = pQty;
                    }
                    else
                    {
                        pQty = ps.OrderQty;
                        pProd = ps.Product;
                        ps.AvailableQuantity = pQty;
                    }
                    if (ps.AvailableQuantity < 0.0)
                    {
                        BOMPenalties += BOMPenaltyCost;
                        ScheduleViolationBOM = true;
                    }
                }
            }

            if (!(ScheduleViolationBOM | ScheduleViolationResourceLate | ScheduleViolationOrderLate | ScheduleViolationResourceFeasiblilty | ScheduleViolationEarlyTime))
            {
                IsFeasible = true;
            }

            //Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
            //    + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties; 
            Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
             + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties + EarlyStartFactor;

            // Fitness must be increasing.
            return (-1.0 * Fitness);
        }

        private double CCalcFitness(int[] genes, double[] times)
        {
            double Time = ProdStartTime[0];
            double NonDelayTime = Time; //Added 3/24 to elim delay time
            double JobStartTime, JobEndTime;
            double Fitness;
            double SumOfServiceEarlyPenalties = 0;
            double SumOfServiceLatePenalties = 0;
            double SumOfResourceLatePenalties = 0;
            double BOMPenalties = 0;
            int Previous = -1;
            bool ScheduleViolationBOM = false;
            bool ScheduleViolationResourceLate = false;
            bool ScheduleViolationOrderLate = false;
            bool ScheduleViolationResourceFeasiblilty = false;
            bool ScheduleViolationEarlyTime = false;
            double LateTime, EarlyTime;
            int CurrentProd;
            double TotalTimeAllResources = 0;
            int CurrentJob;
            double ResourcePrefPenalties = 0;
            double SumOfChangeOverPenalties = 0;
            double EarlyStartFactor = 0;

            // List of production orders to support calculation of BOM Item requirements
            List<ProdSchedule> pSched = new List<ProdSchedule>();


            for (int Resource = 0; Resource < NumberOfResources; Resource++)
            {
                Time = ProdStartTime[Resource];
                NonDelayTime = Time; // added to eliminate delay orders

                if (ConstrainedStart[Resource])
                {
                    Previous = StartProduct[Resource];
                }
                else
                {
                    Previous = -1;
                }
                // Calculate the time for the following jobs
                int FirstGeneInResource = NumberOfRealJobs * Resource;
                int LastGeneInResource = (NumberOfRealJobs * (Resource + 1)) - 1;
                double co, cop;
                for (int i = FirstGeneInResource; i <= LastGeneInResource; i++)
                {
                    CurrentJob = genes[i];
                    CurrentProd = JobsToSchedule[CurrentJob];
                    if (Previous != -1 & CurrentProd != -1)
                    {
                        co = ChangeOver[Previous, CurrentProd];
                        cop = ChangeOverPenalties[Previous, CurrentProd];
                    }
                    else
                    {
                        co = 0;
                        cop = 0;
                    }
                    // Change code to eliminate Delay Jobs from the fitness calculation as well as slack jobs
                    // Delay jobs are being coded manually as product 9999
                    //ToDo enhance input to give a better spread on delay jobs vs adding products and orders for delays. Get rid of the 9999 comparison.
                    //if (CurrentProd != -1)  Changed on 3/24/2012
                    if (CurrentProd != -1)
                    {

                        JobStartTime = Time;
                        // TODO: Verify that this logic is redundant and remove it.
                        // if currentProd != -1 && Previous != -1, then Time += JobRuntime[CurrentJob] + 0;
                        if (Previous == -1)
                        {
                            //First job on the resource was a slack job
                            Time += JobRunTime[CurrentJob];
                        }
                        else
                        {
                            //we have a real job in the previous variable
                            Time += JobRunTime[CurrentJob] + co;
                        }
                        JobEndTime = Time;

                        // There are no longer DelayJobs
                        if (CurrentProd != DelayIndex)
                        {
                            //Used to find the last real job running on a resource
                            NonDelayTime = Time;
                            //Used to encourage jobs to start as soon as possible
                            //Todo  Turn Early start facto into a configurable factor (by resorce?)
                            EarlyStartFactor += JobStartTime;
                        }

                        Previous = JobsToSchedule[CurrentJob];

                        //Calculate Service Early Cost
                        EarlyTime = EarlyStart[CurrentJob];
                        if (JobStartTime < EarlyTime & EarlyTime != 0.0)
                        {
                            SumOfServiceEarlyPenalties += Math.Min(MaxEarlyCost[CurrentJob], MinEarlyCost[CurrentJob] + EarlyCostPerHour[CurrentJob] * (EarlyTime - (JobStartTime)));
                            ScheduleViolationEarlyTime = true;
                        }

                        //Calculate Service Late Cost
                        LateTime = Priority[CurrentJob];
                        if (Time > LateTime)
                        {
                            SumOfServiceLatePenalties += Math.Min(MaxLateCost[CurrentJob], MinLateCost[CurrentJob] + LateCostPerHour[CurrentJob] * (JobEndTime - Priority[CurrentJob]));
                            ScheduleViolationOrderLate = true;
                        }

                        //Calculate Resource Late Cost
                        if (Time > ProdEndTime[Resource])
                        {
                            SumOfResourceLatePenalties += Math.Min(RLCMax[Resource], RLCMin[Resource] + RLCRatePerHour[Resource] * (Time - ProdEndTime[Resource]));
                            ScheduleViolationResourceLate = true;
                        }

                        // Add the resource preference penalties
                        ResourcePrefPenalties += ResourcePreference[CurrentProd, Resource];
                        if (ResourcePreference[CurrentProd, Resource] == ResourceNotFeasible)
                        {
                            ScheduleViolationResourceFeasiblilty = true;
                        }

                        //Sum up the changeover penalties
                        SumOfChangeOverPenalties += cop;

                        //Build the output schedule for BOM Items
                        //First create a new production schedule item
                        ProdSchedule p = new ProdSchedule(CurrentProd, JobStartTime, JobEndTime, OrderQty[CurrentJob]);
                        //Second, add the new schedule item to the list
                        pSched.Add(p);
                    }
                }
                // Calculate the total production time required
                //TotalTimeAllResources += Time - ProdStartTime[Resource]; 
                TotalTimeAllResources += NonDelayTime - ProdStartTime[Resource];
            }

            //Get ready to check for BOM violations
            if (BOMItems.Count > 0) //This is purely a speed enhancement to skip this section if there are no BOM items.
            {
                List<ProdSchedule> ComponentSchedule = new List<ProdSchedule>();
                foreach (ProdSchedule ps in pSched)
                {
                    //Find out if the item has components
                    int bIdx = BOMItemIndex[ps.Product];
                    if (bIdx == -1) continue;
                    int cIdx = -1;
                    BOMItem bi = BOMItems[bIdx];
                    foreach (int component in bi.Components)
                    {
                        cIdx++;
                        //add the demand of the component quantity to the schedule
                        double ComponentDemand = -(ps.OrderQty * bi.Percent[cIdx]);
                        //Note: StartTime is used twice in the line below. This is not a mistake.
                        //Component demand is not a real scheduled job.
                        //This simplification makes sure the demand occurs at the start of the parent job.
                        //Adding .0001 keeps the posting sequence = (debit inventory first at any given time then credit)
                        ProdSchedule cd = new ProdSchedule(component, ps.StartTime, ps.StartTime + 0.0001, ComponentDemand);
                        ComponentSchedule.Add(cd);
                    }

                }
                pSched.AddRange(ComponentSchedule);
                pSched.Sort();
                int pProd = -99; // set up a variable to hold the previous product
                double pQty = 0; //set up a variable to hold the previous quantity

                //Calculate the available quantities
                foreach (ProdSchedule ps in pSched)
                {
                    // Calculate the penalty
                    if (pProd == ps.Product)
                    {
                        pQty += ps.OrderQty;
                        ps.AvailableQuantity = pQty;
                    }
                    else
                    {
                        pQty = ps.OrderQty;
                        pProd = ps.Product;
                        ps.AvailableQuantity = pQty;
                    }
                    if (ps.AvailableQuantity < 0.0)
                    {
                        BOMPenalties += BOMPenaltyCost;
                        ScheduleViolationBOM = true;
                    }
                }
            }

            if (!(ScheduleViolationBOM | ScheduleViolationResourceLate | ScheduleViolationOrderLate | ScheduleViolationResourceFeasiblilty | ScheduleViolationEarlyTime))
            {
                IsFeasible = true;
            }

            //Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
            //    + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties; 
            Fitness = TotalTimeAllResources + SumOfResourceLatePenalties + SumOfServiceLatePenalties + BOMPenalties + ResourcePrefPenalties
             + SumOfChangeOverPenalties + SumOfServiceEarlyPenalties + EarlyStartFactor;

            // Fitness must be increasing.
            return (-1.0 * Fitness);
        }
    }



    // This is the fastest reverse comparer for type specific sorting
    internal class ReverseComparer : IComparer<double>
    {
        public int Compare(double x, double y)
        {
            // Compare y and x in reverse order.
            return y.CompareTo(x);
        }
    }

    // Create a class for production sequencing to support BOM Items
    public class ProdSchedule : IComparable<ProdSchedule>
    {
        // Define a 4 argument constructor for use during the fitness function calculations
        public ProdSchedule(int product, double startTime, double endTime, double orderQty)
        {
            this.Product = product;
            this.StartTime = startTime;
            this.EndTime = endTime;
            this.OrderQty = orderQty;
            this.AvailableQuantity = 0;
        }
        // Define a 5 argument constructor for use during the results display functions
        public ProdSchedule(int product, double startTime, double endTime, double orderQty, int jobNum)
        {
            this.Product = product;
            this.StartTime = startTime;
            this.EndTime = endTime;
            this.OrderQty = orderQty;
            this.JobNum = jobNum;
            this.AvailableQuantity = 0;
        }

        public int Product { get; set; }
        public double StartTime { get; set; }
        public double EndTime { get; set; }
        public double OrderQty { get; set; }
        public double AvailableQuantity { get; set; }
        public int JobNum { get; set; }

        //Implements IComparer to sort by product and time
        public int CompareTo(ProdSchedule other)
        {
            int compare = this.Product.CompareTo(other.Product);
            if (compare == 0)
            {
                //Todo: validate start time vs end time impact on this logic.
                // May need to add a use time to the logic that is start for consumption orders or end for production orders
                // May also be start for tank production orders
                // This could be a separate field or calculated in the compare logic of the ProductionSchedule class
                compare = this.EndTime.CompareTo(other.EndTime);
            }
            return compare;
        }
    }

    // Create a class to support BOM items
    public class BOMItem
    {
        public BOMItem(int product, List<int> components, List<double> percent)
        {
            this.Product = product;
            this.Components = components;
            this.Percent = percent;
        }
        public int Product { get; set; }
        public List<int> Components { get; set; }
        public List<double> Percent { get; set; }
    }


}
namespace ConstrainedGeneticOptimizer
{
    // Job Scheduling Problem description:
    //
    // ** Assumptions about Jobs:
    // * Precedence and overlap
    // Jobs have precedence relationships. This means one job cannot be started until another job is complete.
    // However, overlap is possible: a job may be started when its predecessor is only partially complete
    // * Temporal restrictions
    // Jobs may be constrained such that they can only be done at a certain time.
    //
    // ** Assumptions about Resources:
    // * Temporal restrictions
    // Resources may be constrained that limit their use to a certain time or time period
    // * Job-Resource dependencies
    // Resoruces may be constrained depending on the type of work they are assigned to
    // 
    // ** Assumptions about Objectives:
    // * Minimal makespan
    // Reduce the time it takes to complete the jobs without violating constraints
    // * Minimize cost
    // There are other penalties... todo: define penalties and costs.

    /// <summary>
    /// Second GA attempt. Does not allow precedence contraint violations.
    /// Didn't just replace the last one because I want to have them both available for comparison.
    /// </summary>
    public class ConstrainedGA
    {
        public Func<int[], double[], double> FitnessFunction { get; set; }
        public ConstrainedCreature[] population;
        private ConstrainedCreature[] offspring;
        private Random _rand;
        // GA parameters:
        private int _seed;
        private int _length;
        private int _popsize;
        private int _offsize;
        private double _mutationRate;
        public ConstrainedGA(int seed, int length, int popsize, int offsize, double mutationRate)
        {
            _seed = seed;
            _rand = new Random(seed);
            _length = length;
            _popsize = popsize;
            _offsize = offsize;
            _mutationRate = mutationRate;
            population = new ConstrainedCreature[_popsize];
            offspring = new ConstrainedCreature[_offsize];
            for (int i = 0; i < popsize; i++)
            {
                population[i] = new ConstrainedCreature(length);
                // population[i].fitness = FitnessFunction(population[i].Genes);
            }
            for (int i = 0; i < offsize; i++)
            {
                offspring[i] = new ConstrainedCreature(length);
            }

        }
        public double AverageFitness()
        {
            double avg = 0;
            for (int i = 0; i < _popsize; i++)
            {
                avg += population[i].fitness;
            }
            avg = avg / _popsize;
            return avg;
        }

        public void EvaluatePopulation()
        {
            for (int i = 0; i < _popsize; i++)
            {
                population[i].fitness = FitnessFunction(population[i].Genes, population[i].Times);
            }

        }
        public void GenerateOffspring()
        {
            for (int i = 0; i < _offsize; i += 2)
            {
                // Select two parents
                int p1 = SelectParent();
                int p2 = SelectParent();

                // Crossover to create two offspring
                Crossover(p1, p2, i, i + 1);

                // Mutation chance
                Mutate(i);
                if (!offspring[i].IsValid())
                {
                    MessageBox.Show("Invalid mutation");
                    //Array.Sort(offspring[i].Genes);
                    //throw new ApplicationException("Invalid offspring");
                }

                Mutate(i + 1);
                if (!offspring[i + 1].IsValid())
                {
                    //Array.Sort(offspring[i + 1].Genes);
                    MessageBox.Show("Invalid mutation");
                    // throw new ApplicationException("Invalid offspring");
                }
                offspring[i].fitness = FitnessFunction(offspring[i].Genes, offspring[i].Times);
                offspring[i + 1].fitness = FitnessFunction(offspring[i + 1].Genes, offspring[i].Times);

            }
        }
        private int SelectParent()
        {
            // Binary tourny for no reason
            int p1 = _rand.Next(_popsize);
            int p2 = _rand.Next(_popsize);
            int p = 0;
            if (population[p1].fitness > population[p2].fitness)
            {
                p = p1;
            }
            else
            {
                p = p2;
            }
            return p;
        }
        public void SurvivalSelection()
        {
            List<ConstrainedCreature> combo = new List<ConstrainedCreature>();
            combo.AddRange(population);
            combo.AddRange(offspring);
            combo.Sort(new NewComp());
            for (int i = 0; i < _popsize; i++)
            {
                population[i].fitness = combo[i].fitness;
                for (int j = 0; j < _length; j++)
                {
                    population[i].Genes[j] = combo[i].Genes[j];
                }
            }
            // This doesnt work due to shallow copy nonsense:
            // Creature[] combo = new Creature[_popsize + _offsize];
            // population.CopyTo(combo, 0);
            // offspring.CopyTo(combo, _popsize);
            // Array.Sort(combo, new NewComp());
            // Array.Copy(combo, population, _popsize);
        }
        public void DTCrossover(int p1, int p2, int o1, int o2)
        {
            int cutpoint = _rand.Next(_length);
            for (int i = 0; i < cutpoint; i++)
            {
                offspring[o1].Times[i] = population[p1].Times[i];
                offspring[o2].Times[i] = population[p2].Times[i];
            }
            for (int i = cutpoint; i < _length; i++)
            {
                offspring[o1].Times[i] = population[p2].Times[i];
                offspring[o2].Times[i] = population[p1].Times[i];
            }
        }
        public void Crossover(int p1, int p2, int o1, int o2)
        {
            int cutpoint = _rand.Next(_length);
            //population[p1].Genes.CopyTo(offspring[o1].Genes, 0);
            //population[p2].Genes.CopyTo(offspring[o2].Genes, 0);

            for (int i = 0; i < _length; i++)
            {
                offspring[o1].Genes[i] = population[p1].Genes[i];
            }
            for (int i = 0; i < _length; i++)
            {
                offspring[o2].Genes[i] = population[p2].Genes[i];
            }
            for (int i = 0; i < _length; i++)
            {
                if (population[p1].Genes[i] != offspring[o1].Genes[i])
                {
                    MessageBox.Show("Offspring 1 did not copy correctly");
                    break;
                }
            }

            if (!offspring[o1].IsValid())
            {
                MessageBox.Show("Invalid creature before crossover");
            }
            if (!offspring[o2].IsValid())
            {
                MessageBox.Show("Invalid creature before crossover");
            }
            List<int> remainder = new List<int>(population[p2].Genes);
            //remainder = population[p2].Genes;
            for (int i = 0; i < cutpoint; i++)
            {
                remainder.Remove(population[p1].Genes[i]);
            }
            for (int i = cutpoint; i < _length; i++)
            {
                offspring[o1].Genes[i] = remainder[i - cutpoint];
            }

            if (!offspring[o1].IsValid())
            {
                MessageBox.Show("Invalid offspring1 after crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            // Repeat for offspring 2
            remainder = new List<int>(population[p1].Genes);
            for (int i = cutpoint; i < _length; i++)
            {
                remainder.Remove(population[p2].Genes[i]);
            }

            for (int i = 0; i < cutpoint; i++)
            {
                offspring[o2].Genes[i] = remainder[i];
            }
            if (!offspring[o2].IsValid())
            {
                MessageBox.Show("Invalid offspring2 after crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            DTCrossover(p1, p2, o1, o2);

        }
        public void Mutate(int o)
        {
            for (int i = 0; i < _length; i++)
            {
                if (_rand.NextDouble() < _mutationRate)
                {
                    int r = _rand.Next(_length);
                    int temp = offspring[o].Genes[i];
                    offspring[o].Genes[i] = offspring[o].Genes[r];
                    offspring[o].Genes[r] = temp;
                    // Mutate the delay time
                    r = _rand.Next(_length);
                    offspring[o].Times[r] = TestSimpleRNG.SimpleRNG.GetExponential(1);
                }
            }
        }
        public class ConstrainedCreature
        {
            static Random _rand = new Random();

            public int[] Genes;
            public double[] Times;
            public double fitness;
            public ConstrainedCreature(int length)
            {
                Genes = new int[length];
                List<int> randarray = new List<int>();
                for (int i = 0; i < length; i++)
                {
                    randarray.Add(i);
                }
                for (int i = 0; i < length; i++)
                {
                    int r = _rand.Next(0, length - i);
                    Genes[i] = randarray[r];
                    randarray.RemoveAt(r);
                }
                fitness = -1;
                Times = new double[length];
                for (int i = 0; i < length; i++)
                {
                    Times[i] = TestSimpleRNG.SimpleRNG.GetExponential(1);
                }
            }

            public bool IsValid()
            {
                List<int> vals = new List<int>();
                bool r = true;
                foreach (int i in Genes)
                {
                    if (vals.Contains(i))
                    {
                        r = false;
                        break;
                    }
                    vals.Add(i);
                }
                return r;
            }

        }

        public sealed class NewComp : IComparer<ConstrainedCreature>
        {
            public int Compare(ConstrainedCreature x, ConstrainedCreature y)
            {
                return (y.fitness.CompareTo(x.fitness));
            }
        }

    }
}

namespace GeneticOptimizer
{

    /// <summary>
    /// My first GA attempt. Roughly replicates the original nestle demo functionality.
    /// </summary>
    public class GA
    {
        public Func<int[], double> FitnessFunction { get; set; }
        public Creature[] population;
        private Creature[] offspring;
        private Random _rand;
        // GA parameters:
        private int _seed;
        private int _length;
        private int _popsize;
        private int _offsize;
        private double _mutationRate;
        public GA(int seed, int length, int popsize, int offsize, double mutationRate)
        {
            _seed = seed;
            _rand = new Random(seed);
            _length = length;
            _popsize = popsize;
            _offsize = offsize;
            _mutationRate = mutationRate;
            population = new Creature[_popsize];
            offspring = new Creature[_offsize];
            for (int i = 0; i < popsize; i++)
            {
                population[i] = new Creature(length);
                // population[i].fitness = FitnessFunction(population[i].Genes);
            }
            for (int i = 0; i < offsize; i++)
            {
                offspring[i] = new Creature(length);
            }

        }
        public double AverageFitness()
        {
            double avg = 0;
            for (int i = 0; i < _popsize; i++)
            {
                avg += population[i].fitness;
            }
            avg = avg / _popsize;
            return avg;
        }

        public void EvaluatePopulation()
        {
            for (int i = 0; i < _popsize; i++)
            {
                population[i].fitness = FitnessFunction(population[i].Genes);
            }

        }
        public void GenerateOffspring()
        {
            for (int i = 0; i < _offsize; i += 2)
            {
                // Select two parents
                int p1 = SelectParent(); // _rand.Next(_popsize);
                int p2 = SelectParent(); // _rand.Next(_popsize);

                // Crossover to create two offspring
                Crossover(p1, p2, i, i + 1);

                // Mutation chance
                Mutate(i);
                if (!offspring[i].IsValid())
                {
                    MessageBox.Show("Invalid mutation");
                    //Array.Sort(offspring[i].Genes);
                    //throw new ApplicationException("Invalid offspring");
                }

                Mutate(i + 1);
                if (!offspring[i + 1].IsValid())
                {
                    //Array.Sort(offspring[i + 1].Genes);
                    MessageBox.Show("Invalid mutation");
                    // throw new ApplicationException("Invalid offspring");
                }
                offspring[i].fitness = FitnessFunction(offspring[i].Genes);
                offspring[i + 1].fitness = FitnessFunction(offspring[i + 1].Genes);

            }
        }
        private int SelectParent()
        {
            // Binary tourny for no reason
            int p1 = _rand.Next(_popsize);
            int p2 = _rand.Next(_popsize);
            int p = 0;
            if (population[p1].fitness > population[p2].fitness)
            {
                p = p1;
            }
            else
            {
                p = p2;
            }
            return p;
        }
        public void SurvivalSelection()
        {
            List<Creature> combo = new List<Creature>();
            combo.AddRange(population);
            combo.AddRange(offspring);
            combo.Sort(new NewComp());
            for (int i = 0; i < _popsize; i++)
            {
                population[i].fitness = combo[i].fitness;
                for (int j = 0; j < _length; j++)
                {
                    population[i].Genes[j] = combo[i].Genes[j];
                }
            }
            // This doesnt work due to shallow copy nonsense:
            // Creature[] combo = new Creature[_popsize + _offsize];
            // population.CopyTo(combo, 0);
            // offspring.CopyTo(combo, _popsize);
            // Array.Sort(combo, new NewComp());
            // Array.Copy(combo, population, _popsize);
        }
        public void Crossover(int p1, int p2, int o1, int o2)
        {
            int cutpoint = _rand.Next(_length);
            //population[p1].Genes.CopyTo(offspring[o1].Genes, 0);
            //population[p2].Genes.CopyTo(offspring[o2].Genes, 0);

            for (int i = 0; i < _length; i++)
            {
                offspring[o1].Genes[i] = population[p1].Genes[i];
            }
            for (int i = 0; i < _length; i++)
            {
                offspring[o2].Genes[i] = population[p2].Genes[i];
            }
            for (int i = 0; i < _length; i++)
            {
                if (population[p1].Genes[i] != offspring[o1].Genes[i])
                {
                    MessageBox.Show("Offspring 1 did not copy correctly");
                    break;
                }
            }

            if (!offspring[o1].IsValid())
            {

                MessageBox.Show("Invalid creature before crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            if (!offspring[o2].IsValid())
            {
                MessageBox.Show("Invalid creature before crossover");
                //Array.Sort(offspring[o2].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            List<int> remainder = new List<int>(population[p2].Genes);
            //remainder = population[p2].Genes;
            for (int i = 0; i < cutpoint; i++)
            {
                remainder.Remove(population[p1].Genes[i]);
            }
            for (int i = cutpoint; i < _length; i++)
            {
                offspring[o1].Genes[i] = remainder[i - cutpoint];
            }

            if (!offspring[o1].IsValid())
            {
                MessageBox.Show("Invalid offspring1 after crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            // Repeat for offspring 2
            remainder = new List<int>(population[p1].Genes);
            for (int i = cutpoint; i < _length; i++)
            {
                remainder.Remove(population[p2].Genes[i]);
            }

            for (int i = 0; i < cutpoint; i++)
            {
                offspring[o2].Genes[i] = remainder[i];
            }
            if (!offspring[o2].IsValid())
            {
                MessageBox.Show("Invalid offspring2 after crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
        }
        public void Mutate(int o)
        {
            for (int i = 0; i < _length; i++)
            {
                if (_rand.NextDouble() < _mutationRate)
                {
                    int r = _rand.Next(_length);
                    int temp = offspring[o].Genes[i];
                    offspring[o].Genes[i] = offspring[o].Genes[r];
                    offspring[o].Genes[r] = temp;
                }
            }
        }
        public class Creature
        {
            static Random _rand = new Random();

            public int[] Genes;
            public double fitness;
            public Creature(int length)
            {
                Genes = new int[length];
                List<int> randarray = new List<int>();
                for (int i = 0; i < length; i++)
                {
                    randarray.Add(i);
                }
                for (int i = 0; i < length; i++)
                {
                    int r = _rand.Next(0, length - i);
                    Genes[i] = randarray[r];
                    randarray.RemoveAt(r);
                }
                fitness = -1;
            }
            public Creature(Creature c)
            {
                // This doesn't work. Creates shallow copy.
                //c.Genes.CopyTo(Genes, 0);
                fitness = c.fitness;
            }
            public bool IsValid()
            {
                List<int> vals = new List<int>();
                bool r = true;
                foreach (int i in Genes)
                {
                    if (vals.Contains(i))
                    {
                        r = false;
                        break;
                    }
                    vals.Add(i);
                }
                return r;
            }

        }
        public sealed class NewComp : IComparer<Creature>
        {
            public int Compare(Creature x, Creature y)
            {
                return (y.fitness.CompareTo(x.fitness));
            }
        }

    }
}
