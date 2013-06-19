// File: GeneticOptimizer.cs
// Date: 2013 6 17
// Author: Brien Smith-Martinez
// Summary:
// Contains an implementation of the Junction Solutions GeneticOptimizer,
// a genetic algorithm for finding production schedules.sing System;

using System;
using System.Collections.Generic;
using System.Diagnostics;

using TestSimpleRNG;


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

namespace Junction
{

    /// <summary>
    /// Second GA attempt. Includes the following improvements:
    /// - Uses Delay Times instead of delay jobs.
    /// Didn't just replace the last one because I want to have them both available for comparison.
    /// </summary>
    public class GeneticOptimizer
    {
        public Func<int[], double[], double> FitnessFunction { get; set; }
        public ConstrainedCreature[] population;
        private ConstrainedCreature[] offspring;
        static private Random _rand;
        static private SimpleRNG _srng;
        // Generic GA parameters:
        private int _seed;
        private int _length;
        private int _popsize;
        private int _offsize;
        private double _mutationRate;
        private double _deathRate;
        // Genetic Operator Flags:
        public enum RealCrossoverOp { Uniform, MeanWithNoise }
        public enum SurvivalSelectionOp { Elitist, Generational, Struggle }
        public RealCrossoverOp realCrossover { get; set; }
        public SurvivalSelectionOp survivalSelection { get; set; }
        // Problem specific parameters:
        private double _delayMean;
        double _delayRate;
        //double _delayVar;
        public GeneticOptimizer(int seed, int length, int tl, int popsize, int offsize, double mutationRate, double deathRate, double delayRate, double delayMean)
        {
            _seed = seed;
            _rand = new Random(_seed);
            _srng = new SimpleRNG((uint)_seed);
            _length = length;
            _popsize = popsize;
            _offsize = offsize;
            _mutationRate = mutationRate;
            _deathRate = deathRate;
            _delayRate = delayRate;
            _delayMean = delayMean;
            population = new ConstrainedCreature[_popsize];
            offspring = new ConstrainedCreature[_offsize];
            for (int i = 0; i < popsize; i++)
            {
                population[i] = new ConstrainedCreature(length, tl, _delayRate, _delayMean);
            }
            for (int i = 0; i < offsize; i++)
            {
                offspring[i] = new ConstrainedCreature(length, tl, _delayRate, _delayMean);
            }
            // Default operator options:
            realCrossover = RealCrossoverOp.Uniform;
            survivalSelection = SurvivalSelectionOp.Elitist;

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
        public void GenRand()
        {
            population[0].GenRand(); //TestSimpleRNG.SimpleRNG.GetExponential();
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
                    Debug.Write("Invalid Mutation");
                }

                Mutate(i + 1);
                if (!offspring[i + 1].IsValid())
                {
                    Debug.Write("Invalid Mutation");
                }
                offspring[i].fitness = FitnessFunction(offspring[i].Genes, offspring[i].Times);
                offspring[i + 1].fitness = FitnessFunction(offspring[i + 1].Genes, offspring[i + 1].Times);

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
            switch (survivalSelection)
            {
                case SurvivalSelectionOp.Elitist:
                    // Elitist survival selection:
                    List<ConstrainedCreature> combo = new List<ConstrainedCreature>();
                    combo.AddRange(population);
                    combo.AddRange(offspring);
                    combo.Sort(new NewComp());
                    for (int i = 0; i < _popsize; i++)
                    {
                        population[i].Copy(combo[i]);
                    }
                    break;
                case SurvivalSelectionOp.Generational:
                    // Generational survival selection:
                    for (int i = 0; i < _popsize; i++)
                    {
                        population[i].Copy(offspring[i]);
                    }
                    Array.Sort(population, new NewComp());
                    break;
                case SurvivalSelectionOp.Struggle:
                    // Struggle survival selection:
                    // Replace Most-Similar if new is better
                    int replaced = 0;
                    for (int i = 0; i < _popsize; i++)
                    {
                        double d = 999999;
                        int replacementIndex = -1;
                        for (int j = 0; j < _popsize; j++)
                        {
                            // Find most similar
                            double newd = 0;
                            if (offspring[i].fitness > population[j].fitness)
                            {
                                newd = offspring[i].Distance(population[j]);
                                if (newd < d)
                                {
                                    d = newd;
                                    replacementIndex = j;
                                }
                            }
                        }
                        if (replacementIndex > -1)
                        {
                            population[replacementIndex].Copy(offspring[i]);
                            replaced++;
                        }
                    }
                    Debug.Write(Environment.NewLine + "Replaced: " + replaced);
                    Array.Sort(population, new NewComp());
                    break;
            }
            /*
            // Percent replacement:
            Array.Sort(population, new NewComp());
            Array.Sort(offspring, new NewComp());
            int cutpoint = (int)(_popsize * _deathRate);
            for (int i = cutpoint; i < _popsize; i++)
            {
                population[i].Copy(offspring[i - cutpoint]);
            }
            */

            // This doesnt work due to shallow copy nonsense:
            // Creature[] combo = new Creature[_popsize + _offsize];
            // population.CopyTo(combo, 0);
            // offspring.CopyTo(combo, _popsize);
            // Array.Sort(combo, new NewComp());
            // Array.Copy(combo, population, _popsize);
        }

        public void DTCrossover(int p1, int p2, int o1, int o2)
        {
            // Mean-with-noise Crossover:
            for (int i = 0; i < _length; i++)
            {
                double mean = population[p1].Times[i] + population[p2].Times[i];
                mean = mean / 2.0;
                offspring[o1].Times[i] = SimpleRNG.GetNormal(mean, 0.5);
                offspring[o2].Times[i] = SimpleRNG.GetNormal(mean, 0.5);
                if (offspring[o1].Times[i] < 0.0)
                {
                    offspring[o1].Times[i] = 0.0;
                }
                if (offspring[o2].Times[i] < 0.0)
                {
                    offspring[o2].Times[i] = 0.0;
                }
            }
            /*
            // Uniform Crossover:
            int cutpoint = _rand.Next(_length + 1);
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
            */
        }

        public void Crossover(int p1, int p2, int o1, int o2)
        {
            int cutpoint = _rand.Next(_length);
            //population[p1].Genes.CopyTo(offspring[o1].Genes, 0);
            //population[p2].Genes.CopyTo(offspring[o2].Genes, 0);

            //Debug.Write(Environment.NewLine + "Distance between " + p1 + " - " + p2 + ": " + population[p1].Distance(population[p2]));

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
                    Debug.Write("Offspring 1 did not copy correctly");
                    break;
                }
            }

            if (!offspring[o1].IsValid())
            {
                Debug.Write("Invalid creature before crossover");
            }
            if (!offspring[o2].IsValid())
            {
                Debug.Write("Invalid creature before crossover");
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
                Debug.Write("Invalid offspring1 after crossover");
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
                Debug.Write("Invalid offspring2 after crossover");
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
                    r = _rand.Next(offspring[o].timesLength);
                    double mutatedDelay = SimpleRNG.GetNormal(offspring[o].Times[r], 1.0);
                    //offspring[o].Times[r] = _rand.NextDouble() * _delayMean; //TestSimpleRNG.SimpleRNG.GetExponential(_delayMean);
                    if (mutatedDelay < 0.0)
                    {
                        mutatedDelay = 0.0;
                    }
                }
            }
        }

        public class ConstrainedCreature
        {
            public int[] Genes;
            public double[] Times;
            public double fitness;
            public int timesLength;

            public ConstrainedCreature(int length, int tl, double delayRate, double delayMean)
            {
                Genes = new int[length];
                timesLength = tl;
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
                    if (_rand.NextDouble() < delayRate)
                    {
                        Times[i] = SimpleRNG.GetExponential(delayMean);
                    }
                    else
                    {
                        Times[i] = 0.0;
                    }
                }
            }

            public void Copy(ConstrainedCreature c)
            {
                fitness = c.fitness;
                for (int i = 0; i < Genes.Length; i++)
                {
                    Genes[i] = c.Genes[i];
                    Times[i] = c.Times[i];
                }
            }

            public double Distance(ConstrainedCreature c)
            {
                double d = 0;
                for (int i = 0; i < timesLength; i++)
                {
                    d += Math.Pow(Times[i] - c.Times[i], 2.0);
                }
                return Math.Sqrt(d);
            }

            public void GenRand()
            {
                Debug.Write(Environment.NewLine + _rand.Next(Genes.Length));
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


    /// <summary>
    /// My first GA attempt. Roughly replicates the original nestle demo functionality.
    /// </summary>
    public class SimpleGA
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
        public SimpleGA(int seed, int length, int popsize, int offsize, double mutationRate)
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
                    Debug.Write("Invalid mutation");
                }

                Mutate(i + 1);
                if (!offspring[i + 1].IsValid())
                {
                    Debug.Write("Invalid mutation");
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
                    Debug.Write("Offspring 1 did not copy correctly");
                    break;
                }
            }

            if (!offspring[o1].IsValid())
            {

                Debug.Write("Invalid creature before crossover");
                //Array.Sort(offspring[o1].Genes);
                //throw new ApplicationException("Invalid offspring");
            }
            if (!offspring[o2].IsValid())
            {
                Debug.Write("Invalid creature before crossover");
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
                Debug.Write("Invalid offspring1 after crossover");
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
                Debug.Write("Invalid offspring2 after crossover");
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
                // do this instead:
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
