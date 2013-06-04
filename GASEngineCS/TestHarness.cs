using System;

namespace TestSimpleRNG
{
    /// <summary>
    /// Test application for the SimpleRNG random number generator.
    /// This verifies that the random numbers have the expected 
    /// distribution using a standard statistical test.
    /// Unfortunately the test is more complicated than the generator itself.
    /// 
    /// For more information on testing random number generators, see
    /// chapter 10 of Beautiful Testing by Tim Riley and Adam Goucher.
    /// </summary>
    class Testharness
    {
        /// <summary>

        /// </summary>

        static void Main(string[] args)
        {
            // Test the core uniform generator using the Kolmogorov-Smirnov statistical test.
            KSTest();

            // Test the derivted distributions by looking at their means and variances.
            TestDistributions();
            // Keep the terminal window open
            Console.WriteLine("Press any key to exit.");
            Console.ReadKey();
        }

        static void KSTest()
        {
            /// Kolmogorov-Smirnov test for distributions.  See Knuth volume 2, page 48-51 (third edition).
            /// This test should *fail* on average one time in 1000 runs.
            /// That's life with random number generators: if the test passed all the time, 
            /// the source wouldn't be random enough!  If the test were to fail more frequently,
            /// the most likely explanation would be a bug in the code.
            
            SimpleRNG.SetSeedFromSystemTime();

            int numReps = 1000;
            double failureProbability = 0.001; // probability of test failing with normal input
            int j;
            double[] samples = new double[numReps];

            for (j = 0; j != numReps; ++j)
                samples[j] = SimpleRNG.GetUniform();

            System.Array.Sort(samples);

            double CDF;
            double temp;
            int j_minus = 0, j_plus = 0;
            double K_plus = -double.MaxValue;
            double K_minus = -double.MaxValue;

            for (j = 0; j != numReps; ++j)
            {
                CDF = samples[j];
                temp = (j + 1.0) / numReps - CDF;
                if (K_plus < temp)
                {
                    K_plus = temp;
                    j_plus = j;
                }
                temp = CDF - (j + 0.0) / numReps;
                if (K_minus < temp)
                {
                    K_minus = temp;
                    j_minus = j;
                }
            }

            double sqrtNumReps = Math.Sqrt((double)numReps);
            K_plus *= sqrtNumReps;
            K_minus *= sqrtNumReps;

            // We divide the failure probability by four because we have four tests:
            // left and right tests for K+ and K-.
            double p_low = 0.25 * failureProbability;
            double p_high = 1.0 - 0.25 * failureProbability;
            double cutoff_low = Math.Sqrt(0.5 * Math.Log(1.0 / (1.0 - p_low))) - 1.0 / (6.0 * sqrtNumReps);
            double cutoff_high = Math.Sqrt(0.5 * Math.Log(1.0 / (1.0 - p_high))) - 1.0 / (6.0 * sqrtNumReps);

            Console.WriteLine("\n\nTesting the random number distribution");
            Console.WriteLine("using the Kolmogorov-Smirnov (KS) test.\n");

            Console.WriteLine("K+ statistic: {0}", K_plus);
            Console.WriteLine("K+ statistic: {0}", K_minus);
            Console.WriteLine("Acceptable interval: [{0}, {1}]", cutoff_low, cutoff_high);
            Console.WriteLine("K+ max at {0} {1}", j_plus, samples[j_plus]);
            Console.WriteLine("K- max at {0} {1}", j_minus, samples[j_minus]);

            if (cutoff_low <= K_plus && K_plus <= cutoff_high && cutoff_low <= K_minus && K_minus <= cutoff_high)
                Console.WriteLine("\nKS test passed\n");
            else
                Console.WriteLine("\nKS test failed\n");
        }

        // Convenience function for TestDistributions()
        static void PrintResults
        (
            string name, 
            double expectedMean, 
            double expectedVariance, 
            double computedMean, 
            double computedVariance
        )
        {
            Console.WriteLine("Testing {0}", name);
            Console.WriteLine("Expected mean:     {0}, computed mean:     {1}", expectedMean, computedMean);
            Console.WriteLine("Expected variance: {0}, computed variance: {1}", expectedVariance, computedVariance);
            Console.WriteLine("");
        }

        // Verify that distributions have the correct mean and variance.
        // Note that sample mean and sample variance will not exactly match the expected mean and variance.
        static void TestDistributions()
        {
            const int numSamples = 100000;
            double mean, variance, stdev, shape, scale, degreesOfFreedom;
            RunningStat rs = new RunningStat();            // Exponential distribution
            rs.Clear();
            mean = 2;
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetExponential(mean));
            PrintResults("exponential", mean, 5, rs.Mean(), rs.Variance());

            // Gamma distribution
            rs.Clear();
            shape = 10; scale = 2;
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetGamma(shape, scale));
            PrintResults("gamma", shape*scale, shape*scale*scale, rs.Mean(), rs.Variance());

            // Normal distribution
            rs.Clear();
            mean = 2; stdev = 5;
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetNormal(2, 5));
            PrintResults("normal", mean, stdev*stdev, rs.Mean(), rs.Variance());

            // Student t distribution
            rs.Clear();
            degreesOfFreedom = 6;
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetStudentT(6));
            PrintResults("Student t", 0, degreesOfFreedom / (degreesOfFreedom - 2.0), rs.Mean(), rs.Variance());

            // Weibull distribution
            rs.Clear();
            shape = 2; scale = 3;
            mean = 3*Math.Sqrt(Math.PI)/2;
            variance = 9*(1 - Math.PI/4);
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetWeibull(shape, scale));
            PrintResults("Weibull", mean, variance, rs.Mean(), rs.Variance());

            // Beta distribution
            rs.Clear();
            double a = 7, b = 2;
            mean = a / (a + b);
            variance = mean*(1 - mean) / (a + b + 1);
            for (int i = 0; i < numSamples; ++i)
                rs.Push(SimpleRNG.GetBeta(a, b));
            PrintResults("Beta", mean, variance, rs.Mean(), rs.Variance());
        }
    }

    class RunningStat
    {
        int m_n;
        double m_oldM, m_newM, m_oldS, m_newS;
 
        public RunningStat()
        {
            m_n = 0;
        }

        public void Clear()
        {
            m_n = 0;
        }

        public void Push(double x)
        {
            m_n++;

            // See Knuth TAOCP vol 2, 3rd edition, page 232
            if (m_n == 1)
            {
                m_oldM = m_newM = x;
                m_oldS = 0.0;
            }
            else
            {
                m_newM = m_oldM + (x - m_oldM)/m_n;
                m_newS = m_oldS + (x - m_oldM)*(x - m_newM);
    
                // set up for next iteration
                m_oldM = m_newM; 
                m_oldS = m_newS;
            }
        }

        public int NumDataValues()
        {
            return m_n;
        }

        public double Mean()
        {
            return (m_n > 0) ? m_newM : 0.0;
        }

        public double Variance()
        {
            return ( (m_n > 1) ? m_newS/(m_n - 1) : 0.0 );
        }

        public double StandardDeviation()
        {
            return Math.Sqrt( Variance() );
        }
    }

}
