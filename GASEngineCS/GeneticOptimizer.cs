﻿// File: GeneticOptimizer.cs
// Date: 2013 6 17
// Author: Brien Smith-Martinez
// Summary:
// Contains an implementation of the Junction Solutions GeneticOptimizer,
// a genetic algorithm for finding production schedules.

using System;
using System.Collections.Generic;
using System.Threading;
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
    /// Third GA attempt. Includes the following improvements:
    /// - Include Usage Modes (only used to represent resource usage atm)
    /// - Better OOP
    /// Didn't just replace the last one because I want to have them both available for comparison.
    /// </summary>
    namespace GeneticOptimizer
    {
        // Genetic Operator Flags:
        public enum RealCrossoverOp { Uniform, MeanWithNoise }
        public enum SurvivalSelectionOp { ReplaceWorst, Elitist, Generational, Struggle }
        public enum ParentSelectionOp { Tournament, FitnessProportional }

        public class GA
        {
            public Func<int[], double[], int[], double> FitnessFunction { get; set; }
            public ScheduleGenome[] population;
            private ScheduleGenome[] offspring;
            public ScheduleGenome elite;
            static private Random _rand;
            static private SimpleRNG _srng;
            // Generic GA parameters:
            private int _seed;
            private int _length;
            private int _tl;
            private int _mModes;
            private int _popsize;
            private int _offsize;
            private double _mutationRate;
            private double _deathRate;
            // Genetic Operator Flags:
            public ParentSelectionOp parentSelection { get; set; }
            public RealCrossoverOp realCrossover { get; set; }
            public SurvivalSelectionOp survivalSelection { get; set; }
            // Problem specific parameters:
            private double _delayMean;
            double _delayRate;
            //double _delayVar;
            public GA(int seed, int length, int tl, int modes, int popsize, int offsize, double mutationRate, double deathRate, double delayRate, double delayMean)
            {
                _seed = seed;
                _rand = new Random(_seed);
                _srng = new SimpleRNG((uint)_seed);
                _length = length;
                _tl = tl;
                _mModes = modes;
                _popsize = popsize;
                _offsize = offsize;
                _mutationRate = mutationRate;
                _deathRate = deathRate;
                _delayRate = delayRate;
                _delayMean = delayMean;
                population = new ScheduleGenome[_popsize];
                offspring = new ScheduleGenome[_offsize];
                // Default operator options:
                realCrossover = RealCrossoverOp.MeanWithNoise;
                survivalSelection = SurvivalSelectionOp.Elitist;
                parentSelection = ParentSelectionOp.Tournament;

                elite = new ScheduleGenome(_length, tl, modes, mutationRate, delayRate, delayMean);
                for (int i = 0; i < popsize; i++)
                {
                    population[i] = new ScheduleGenome(length, tl, modes, mutationRate, _delayRate, _delayMean);
                    population[i].realCrossover = realCrossover;
                    //population[i].maxModes = length / tl - 1;
                }
                for (int i = 0; i < offsize; i++)
                {
                    offspring[i] = new ScheduleGenome(length, tl, modes, mutationRate, _delayRate, _delayMean);
                    offspring[i].realCrossover = realCrossover;
                    //offspring[i].maxModes = length / tl - 1;
                }

            }
            public void SeedPopulation(int[] genes, double[] times)
            {
                population[0] = new ScheduleGenome(_length, _tl, _mModes, _mutationRate, genes, times);
                /*
                for (int i = 1; i < _popsize; i++)
                {
                    population[i] = new ConstrainedCreature(_length, _length, genes, times);
                    Mutate(i);
                }
                 */
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

            // Copies best individual in population to elite.
            // Assumes population has been evaluated. Use with caution.
            public void FindElite()
            {
                elite.fitness = FitnessFunction(elite.Genes, elite.Times, elite.Modes);
                for (int i = 0; i < _popsize; i++)
                {
                    if (population[i].fitness > elite.fitness)
                    {
                        elite.Copy(population[i]);
                    }
                }
            }

            public void EvaluatePopulation()
            {
                elite.fitness = FitnessFunction(elite.Genes, elite.Times, elite.Modes);
                for (int i = 0; i < _popsize; i++)
                {
                    population[i].fitness = FitnessFunction(population[i].Genes, population[i].Times, elite.Modes);
                    if (population[i].fitness > elite.fitness)
                    {
                        elite.Copy(population[i]);
                    }
                }

            }

            public void GenerateOffspring()
            {
                if (survivalSelection == SurvivalSelectionOp.ReplaceWorst)
                {
                    _offsize = (int)(_popsize * _deathRate);
                }
                for (int i = 0; i < _offsize; i += 2)
                {
                    // Select two parents
                    int p1 = SelectParent();
                    int p2 = SelectParent();

                    // Crossover to create two offspring
                    //Crossover(p1, p2, i, i + 1);
                    population[p1].Crossover(ref population[p2], ref offspring[i]);
                    population[p2].Crossover(ref population[p1], ref offspring[i + 1]);

                    // Mutation chance
                    // Mutate(i);
                    offspring[i].Mutate();
                    Debug.Assert(offspring[i].IsValid(), "Invalid mutation");
                    //Mutate(i + 1);
                    offspring[i + 1].Mutate();
                    Debug.Assert(offspring[i + 1].IsValid(), "Invalid mutation");

                    //offspring[i].fitness = FitnessFunction(offspring[i].Genes, offspring[i].Times);
                    //offspring[i + 1].fitness = FitnessFunction(offspring[i + 1].Genes, offspring[i + 1].Times);
                }
                int threadcount = 20;
                int ck = 0;
                while (ck < _offsize)
                {
                    ManualResetEvent[] doneEvents = new ManualResetEvent[threadcount];
                    for (int k = 0; k < threadcount; k++)
                    {
                        if (ck < _offsize)
                        {
                            doneEvents[k] = new ManualResetEvent(false);
                            FitnessEvaluationThread f = new FitnessEvaluationThread(ck, this, doneEvents[k]);
                            ThreadPool.QueueUserWorkItem(f.Evaluate);
                            ck++;
                        }
                    }
                    //WaitHandle.WaitAll(doneEvents);
                    for (int i = 0; i < threadcount; i++)
                    {
                        if (doneEvents[i] != null)
                        {
                            doneEvents[i].WaitOne();
                        }
                    }
                }

            }
            public class FitnessEvaluationThread
            {
                public Func<int[], double[], double> FitnessFunction { get; set; }
                GA _reftoGO;
                public double Fitness { get { return _fitness; } }
                private double _fitness;
                private int _i;
                private ManualResetEvent _doneEvent;
                public FitnessEvaluationThread(int i, GA reftoGO, ManualResetEvent doneEvent)
                {
                    _reftoGO = reftoGO;
                    _i = i;
                    _doneEvent = doneEvent;
                }
                public void Evaluate(Object threadContext)
                {
                    _reftoGO.offspring[_i].fitness = _reftoGO.FitnessFunction(_reftoGO.offspring[_i].Genes, _reftoGO.offspring[_i].Times, _reftoGO.offspring[_i].Modes);
                    _doneEvent.Set();
                }

            }
            private int SelectParent()
            {
                int p = 0;
                switch (parentSelection)
                {
                    case ParentSelectionOp.FitnessProportional:
                        double totalFitness = 0;
                        for (int i = 0; i < _popsize; i++)
                        {
                            totalFitness += population[i].fitness;
                        }
                        double r = _rand.NextDouble() * totalFitness;
                        double runningTotal = population[p].fitness;
                        while (runningTotal > r)
                        {
                            p++;
                            runningTotal += population[p].fitness;
                        }
                        break;
                    case ParentSelectionOp.Tournament:
                        int k = _popsize / 10;
                        p = _rand.Next(_popsize);
                        double bestfitness = population[p].fitness;
                        for (int i = 0; i < k; i++)
                        {
                            int px = _rand.Next(_popsize);
                            if (population[px].fitness > bestfitness)
                            {
                                bestfitness = population[px].fitness;
                                p = px;
                            }
                        }
                        break;
                }

                return p;
            }

            public void SurvivalSelection()
            {
                switch (survivalSelection)
                {
                    case SurvivalSelectionOp.ReplaceWorst:
                        // Replace worst _deathRate * populationSize with offspring.
                        Array.Sort(population, new NewComp());
                        int cutpoint = (int)(_popsize * (1.0 - _deathRate));
                        for (int i = cutpoint; i < _popsize; i++)
                        {
                            population[i].Copy(offspring[i - cutpoint]);
                        }
                        break;
                    case SurvivalSelectionOp.Elitist:
                        // Elitist survival selection:
                        List<ScheduleGenome> combo = new List<ScheduleGenome>();
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
                        //Array.Sort(population, new NewComp());
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

            }

            public void DTCrossover(int p1, int p2, int o1, int o2)
            {
                switch (realCrossover)
                {
                    case RealCrossoverOp.MeanWithNoise:
                        // Mean-with-noise Crossover:
                        for (int i = 0; i < population[p1]._timesLength; i++)
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
                        break;
                    case RealCrossoverOp.Uniform:
                        // Uniform Crossover:
                        int cutpoint = _rand.Next(population[p1]._timesLength + 1);
                        for (int i = 0; i < cutpoint; i++)
                        {
                            offspring[o1].Times[i] = population[p1].Times[i];
                            offspring[o2].Times[i] = population[p2].Times[i];
                        }
                        for (int i = cutpoint; i < population[p1]._timesLength; i++)
                        {
                            offspring[o1].Times[i] = population[p2].Times[i];
                            offspring[o2].Times[i] = population[p1].Times[i];
                        }
                        break;
                }
            }

            public void Crossover(int p1, int p2, int o1, int o2)
            {
                int cutpoint = _rand.Next(_length);

                //Debug.Write(Environment.NewLine + "Distance between " + p1 + " - " + p2 + ": " + population[p1].Distance(population[p2]));

                for (int i = 0; i < _length; i++)
                {
                    offspring[o1].Genes[i] = population[p1].Genes[i];
                }
                for (int i = 0; i < _length; i++)
                {
                    offspring[o2].Genes[i] = population[p2].Genes[i];
                }

                Debug.Assert(offspring[o1].IsValid(), "Invalid creature before crossover");
                Debug.Assert(offspring[o2].IsValid(), "Invalid creature before crossover");

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

                Debug.Assert(offspring[o1].IsValid(), "Invalid creature after crossover");

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
                Debug.Assert(offspring[o2].IsValid(), "Invalid creature after crossover");

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
                        r = _rand.Next(offspring[o]._timesLength);
                        double mutatedDelay = 0;
                        //mutatedDelay = SimpleRNG.GetExponential(_delayMean);
                        mutatedDelay = SimpleRNG.GetNormal(offspring[o].Times[r], 1.0);
                        //mutatedDelay = _rand.NextDouble() * _delayMean;
                        if (mutatedDelay < 0.0)
                        {
                            mutatedDelay = 0.0;
                        }
                        offspring[o].Times[r] = mutatedDelay;
                    }
                }
            }

            public class ScheduleGenome
            {
                public int[] Genes;
                public double[] Times;
                public int[] Modes;
                public int maxModes;
                private double _mutationRate;
                public double fitness;
                public int _timesLength;
                public int _length;
                public RealCrossoverOp realCrossover;


                public ScheduleGenome(int length, int tl, int mModes, double mut, int[] geneSeeds, double[] timeSeeds)
                {
                    _length = length;
                    Genes = new int[length];
                    Times = new double[tl];
                    Modes = new int[tl];
                    maxModes = mModes;
                    _timesLength = tl;
                    _mutationRate = mut;
                    for (int i = 0; i < length; i++)
                    {
                        Genes[i] = geneSeeds[i];
                    }
                    for (int i = 0; i < tl; i++)
                    {
                        Times[i] = timeSeeds[i];
                    }
                    fitness = -1;
                }

                public ScheduleGenome(int length, int tl, int mModes, double mut, double delayRate, double delayMean)
                {
                    Genes = new int[length];
                    Times = new double[tl];
                    Modes = new int[tl];
                    maxModes = mModes;
                    _length = length;
                    _timesLength = tl;
                    _mutationRate = mut;
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
                    for (int i = 0; i < tl; i++)
                    {
                        if (_rand.NextDouble() < delayRate)
                        {
                            Times[i] = SimpleRNG.GetExponential(delayMean);
                        }
                        else
                        {
                            Times[i] = 0.0;
                        }
                        Modes[i] = _rand.Next(maxModes);
                    }
                }

                public void Copy(ScheduleGenome c)
                {
                    fitness = c.fitness;
                    for (int i = 0; i < Genes.Length; i++)
                    {
                        Genes[i] = c.Genes[i];
                        if (i < _timesLength)
                        {
                            Times[i] = c.Times[i];
                            Modes[i] = c.Modes[i];
                        }
                    }
                }

                public double Distance(ScheduleGenome c)
                {
                    double d = 0;
                    for (int i = 0; i < _timesLength; i++)
                    {
                        d += Math.Pow(Times[i] - c.Times[i], 2.0);
                    }
                    return Math.Sqrt(d);
                }

                public void GenRand()
                {
                    Debug.Write(Environment.NewLine + _rand.Next(Genes.Length));
                }
                public void DTCrossover(ref ScheduleGenome p2, ref ScheduleGenome o1) //out ScheduleGenome o2)
                {
                    switch (realCrossover)
                    {
                        case RealCrossoverOp.MeanWithNoise:
                            // Mean-with-noise Crossover:
                            for (int i = 0; i < _timesLength; i++)
                            {
                                double mean = Times[i] + p2.Times[i];
                                mean = mean / 2.0;
                                o1.Times[i] = SimpleRNG.GetNormal(mean, 0.5);
                                if (o1.Times[i] < 0.0)
                                {
                                    o1.Times[i] = 0.0;
                                }
                            }
                            break;
                        case RealCrossoverOp.Uniform:
                            // Uniform Crossover:
                            int cutpoint = _rand.Next(_timesLength + 1);
                            for (int i = 0; i < cutpoint; i++)
                            {
                                o1.Times[i] = Times[i];
                            }
                            for (int i = cutpoint; i < _timesLength; i++)
                            {
                                o1.Times[i] = p2.Times[i];
                            }
                            break;
                    }
                }

                public void Crossover(ref ScheduleGenome p2, ref ScheduleGenome o1)
                {
                    int cutpoint = _rand.Next(_length);

                    //Debug.Write(Environment.NewLine + "Distance between " + p1 + " - " + p2 + ": " + population[p1].Distance(population[p2]));

                    for (int i = 0; i < _length; i++)
                    {
                        o1.Genes[i] = Genes[i];
                    }

                    Debug.Assert(o1.IsValid(), "Invalid creature before crossover");

                    List<int> remainder = new List<int>(p2.Genes);
                    for (int i = 0; i < cutpoint; i++)
                    {
                        remainder.Remove(Genes[i]);
                    }
                    for (int i = cutpoint; i < _length; i++)
                    {
                        o1.Genes[i] = remainder[i - cutpoint];
                    }

                    Debug.Assert(o1.IsValid(), "Invalid creature after crossover");

                    DTCrossover(ref p2, ref o1);
                    CombinationCrossover(ref p2, ref o1);
                }
                public void CombinationCrossover(ref ScheduleGenome p2, ref ScheduleGenome o1)
                {
                    int cutpoint = _rand.Next(_timesLength);

                    for (int i = 0; i < cutpoint; i++)
                    {
                        o1.Modes[i] = p2.Modes[i];
                    }
                    for (int i = cutpoint; i < _timesLength; i++)
                    {
                        o1.Modes[i] = Modes[i];
                    }
                }
                public void Mutate()
                {
                    for (int i = 0; i < _length; i++)
                    {
                        if (_rand.NextDouble() < _mutationRate)
                        {
                            int r = _rand.Next(_length);
                            int temp = Genes[i];
                            Genes[i] = Genes[r];
                            Genes[r] = temp;
                            // Mutate the delay time
                            r = _rand.Next(_timesLength);
                            double mutatedDelay = 0;
                            //mutatedDelay = SimpleRNG.GetExponential(_delayMean);
                            mutatedDelay = SimpleRNG.GetNormal(Times[r], 1.0);
                            //mutatedDelay = _rand.NextDouble() * _delayMean;
                            if (mutatedDelay < 0.0)
                            {
                                mutatedDelay = 0.0;
                            }
                            Times[r] = mutatedDelay;
                        }
                    }
                    //Mutate the Mode vector:
                    for (int i = 0; i < _timesLength; i++)
                    {
                        if (_rand.NextDouble() < _mutationRate)
                        {
                            Modes[i] = _rand.Next(maxModes);
                        }
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

            public sealed class NewComp : IComparer<ScheduleGenome>
            {
                public int Compare(ScheduleGenome x, ScheduleGenome y)
                {
                    return (y.fitness.CompareTo(x.fitness));
                }
            }

        }


        /// <summary>
        /// Second GA attempt. Includes the following improvements:
        /// - Uses Delay Times instead of delay jobs.
        /// - Allow more than one kind of survival selection
        /// Didn't just replace the last one because I want to have them both available for comparison.
        /// </summary>
        public class GeneticOptimizer
        {
            public Func<int[], double[], double> FitnessFunction { get; set; }
            public ConstrainedCreature[] population;
            private ConstrainedCreature[] offspring;
            public ConstrainedCreature elite;
            static private Random _rand;
            static private SimpleRNG _srng;
            // Generic GA parameters:
            private int _seed;
            private int _length;
            private int _tl;
            private int _popsize;
            private int _offsize;
            private double _mutationRate;
            private double _deathRate;
            // Genetic Operator Flags:
            public enum RealCrossoverOp { Uniform, MeanWithNoise }
            public enum SurvivalSelectionOp { ReplaceWorst, Elitist, Generational, Struggle }
            public enum ParentSelectionOp { Tournament, FitnessProportional }
            public ParentSelectionOp parentSelection { get; set; }
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
                _tl = tl;
                _popsize = popsize;
                _offsize = offsize;
                _mutationRate = mutationRate;
                _deathRate = deathRate;
                _delayRate = delayRate;
                _delayMean = delayMean;
                population = new ConstrainedCreature[_popsize];
                offspring = new ConstrainedCreature[_offsize];
                elite = new ConstrainedCreature(_length, tl, delayRate, delayMean);
                for (int i = 0; i < popsize; i++)
                {
                    population[i] = new ConstrainedCreature(length, tl, _delayRate, _delayMean);
                }
                for (int i = 0; i < offsize; i++)
                {
                    offspring[i] = new ConstrainedCreature(length, tl, _delayRate, _delayMean);
                }
                // Default operator options:
                realCrossover = RealCrossoverOp.MeanWithNoise;
                survivalSelection = SurvivalSelectionOp.Elitist;
                parentSelection = ParentSelectionOp.Tournament;

            }
            public void SeedPopulation(int[] genes, double[] times)
            {
                population[0] = new ConstrainedCreature(_length, _tl, genes, times);
                /*
                for (int i = 1; i < _popsize; i++)
                {
                    population[i] = new ConstrainedCreature(_length, _length, genes, times);
                    Mutate(i);
                }
                 */
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

            // Copies best individual in population to elite.
            // Assumes population has been evaluated. Use with caution.
            public void FindElite()
            {
                elite.fitness = FitnessFunction(elite.Genes, elite.Times);
                for (int i = 0; i < _popsize; i++)
                {
                    if (population[i].fitness > elite.fitness)
                    {
                        elite.Copy(population[i]);
                    }
                }
            }

            public void EvaluatePopulation()
            {
                elite.fitness = FitnessFunction(elite.Genes, elite.Times);
                for (int i = 0; i < _popsize; i++)
                {
                    population[i].fitness = FitnessFunction(population[i].Genes, population[i].Times);
                    if (population[i].fitness > elite.fitness)
                    {
                        elite.Copy(population[i]);
                    }
                }

            }

            public void GenerateOffspring()
            {
                if (survivalSelection == SurvivalSelectionOp.ReplaceWorst)
                {
                    _offsize = (int)(_popsize * _deathRate);
                }
                for (int i = 0; i < _offsize; i += 2)
                {
                    // Select two parents
                    int p1 = SelectParent();
                    int p2 = SelectParent();

                    // Crossover to create two offspring
                    Crossover(p1, p2, i, i + 1);

                    // Mutation chance
                    Mutate(i);
                    Debug.Assert(offspring[i].IsValid(), "Invalid mutation");
                    Mutate(i + 1);
                    Debug.Assert(offspring[i + 1].IsValid(), "Invalid mutation");

                    //offspring[i].fitness = FitnessFunction(offspring[i].Genes, offspring[i].Times);
                    //offspring[i + 1].fitness = FitnessFunction(offspring[i + 1].Genes, offspring[i + 1].Times);
                }
                int threadcount = 20;
                int ck = 0;
                while (ck < _offsize)
                {
                    ManualResetEvent[] doneEvents = new ManualResetEvent[threadcount];
                    for (int k = 0; k < threadcount; k++)
                    {
                        if (ck < _offsize)
                        {
                            doneEvents[k] = new ManualResetEvent(false);
                            FitnessEvaluationThread f = new FitnessEvaluationThread(ck, this, doneEvents[k]);
                            ThreadPool.QueueUserWorkItem(f.Evaluate);
                            ck++;
                        }
                    }
                    //WaitHandle.WaitAll(doneEvents);
                    for (int i = 0; i < threadcount; i++)
                    {
                        if (doneEvents[i] != null)
                        {
                            doneEvents[i].WaitOne();
                        }
                    }
                }

            }
            public class FitnessEvaluationThread
            {
                public Func<int[], double[], double> FitnessFunction { get; set; }
                GeneticOptimizer _reftoGO;
                public double Fitness { get { return _fitness; } }
                private double _fitness;
                private int _i;
                private ManualResetEvent _doneEvent;
                public FitnessEvaluationThread(int i, GeneticOptimizer reftoGO, ManualResetEvent doneEvent)
                {
                    _reftoGO = reftoGO;
                    _i = i;
                    _doneEvent = doneEvent;
                }
                public void Evaluate(Object threadContext)
                {
                    _reftoGO.offspring[_i].fitness = _reftoGO.FitnessFunction(_reftoGO.offspring[_i].Genes, _reftoGO.offspring[_i].Times);
                    _doneEvent.Set();
                }

            }
            private int SelectParent()
            {
                int p = 0;
                switch (parentSelection)
                {
                    case ParentSelectionOp.FitnessProportional:
                        double totalFitness = 0;
                        for (int i = 0; i < _popsize; i++)
                        {
                            totalFitness += population[i].fitness;
                        }
                        double r = _rand.NextDouble() * totalFitness;
                        double runningTotal = population[p].fitness;
                        while (runningTotal > r)
                        {
                            p++;
                            runningTotal += population[p].fitness;
                        }
                        break;
                    case ParentSelectionOp.Tournament:
                        int k = _popsize / 10;
                        p = _rand.Next(_popsize);
                        double bestfitness = population[p].fitness;
                        for (int i = 0; i < k; i++)
                        {
                            int px = _rand.Next(_popsize);
                            if (population[px].fitness > bestfitness)
                            {
                                bestfitness = population[px].fitness;
                                p = px;
                            }
                        }
                        break;
                }

                return p;
            }

            public void SurvivalSelection()
            {
                switch (survivalSelection)
                {
                    case SurvivalSelectionOp.ReplaceWorst:
                        // Replace worst _deathRate * populationSize with offspring.
                        Array.Sort(population, new NewComp());
                        int cutpoint = (int)(_popsize * (1.0 - _deathRate));
                        for (int i = cutpoint; i < _popsize; i++)
                        {
                            population[i].Copy(offspring[i - cutpoint]);
                        }
                        break;
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
                        //Array.Sort(population, new NewComp());
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

            }

            public void DTCrossover(int p1, int p2, int o1, int o2)
            {
                switch (realCrossover)
                {
                    case RealCrossoverOp.MeanWithNoise:
                        // Mean-with-noise Crossover:
                        for (int i = 0; i < population[p1].timesLength; i++)
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
                        break;
                    case RealCrossoverOp.Uniform:
                        // Uniform Crossover:
                        int cutpoint = _rand.Next(population[p1].timesLength + 1);
                        for (int i = 0; i < cutpoint; i++)
                        {
                            offspring[o1].Times[i] = population[p1].Times[i];
                            offspring[o2].Times[i] = population[p2].Times[i];
                        }
                        for (int i = cutpoint; i < population[p1].timesLength; i++)
                        {
                            offspring[o1].Times[i] = population[p2].Times[i];
                            offspring[o2].Times[i] = population[p1].Times[i];
                        }
                        break;
                }
            }

            public void Crossover(int p1, int p2, int o1, int o2)
            {
                int cutpoint = _rand.Next(_length);

                //Debug.Write(Environment.NewLine + "Distance between " + p1 + " - " + p2 + ": " + population[p1].Distance(population[p2]));

                for (int i = 0; i < _length; i++)
                {
                    offspring[o1].Genes[i] = population[p1].Genes[i];
                }
                for (int i = 0; i < _length; i++)
                {
                    offspring[o2].Genes[i] = population[p2].Genes[i];
                }

                Debug.Assert(offspring[o1].IsValid(), "Invalid creature before crossover");
                Debug.Assert(offspring[o2].IsValid(), "Invalid creature before crossover");

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

                Debug.Assert(offspring[o1].IsValid(), "Invalid creature after crossover");

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
                Debug.Assert(offspring[o2].IsValid(), "Invalid creature after crossover");

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
                        double mutatedDelay = 0;
                        //mutatedDelay = SimpleRNG.GetExponential(_delayMean);
                        mutatedDelay = SimpleRNG.GetNormal(offspring[o].Times[r], 1.0);
                        //mutatedDelay = _rand.NextDouble() * _delayMean;
                        if (mutatedDelay < 0.0)
                        {
                            mutatedDelay = 0.0;
                        }
                        offspring[o].Times[r] = mutatedDelay;
                    }
                }
            }

            public class ConstrainedCreature
            {
                public int[] Genes;
                public double[] Times;
                public double fitness;
                public int timesLength;

                public ConstrainedCreature(int length, int tl, int[] geneSeeds, double[] timeSeeds)
                {
                    Genes = new int[length];
                    Times = new double[tl];
                    timesLength = tl;
                    for (int i = 0; i < length; i++)
                    {
                        Genes[i] = geneSeeds[i];
                    }
                    for (int i = 0; i < tl; i++)
                    {
                        Times[i] = timeSeeds[i];
                    }
                    fitness = -1;
                }

                public ConstrainedCreature(int length, int tl, double delayRate, double delayMean)
                {
                    Genes = new int[length];
                    Times = new double[tl];
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
                    for (int i = 0; i < tl; i++)
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
                        if (i < timesLength)
                        {
                            Times[i] = c.Times[i];
                        }
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
}
