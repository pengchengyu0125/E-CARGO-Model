import ilog.concert.IloException;
import ilog.concert.IloIntVar;
import ilog.concert.IloLinearNumExpr;
import ilog.cplex.IloCplex;
import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartUtilities;
import org.jfree.chart.JFreeChart;
import org.jfree.chart.plot.PlotOrientation;
import org.jfree.data.xy.XYSeries;
import org.jfree.data.xy.XYSeriesCollection;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.text.DecimalFormat;
import java.util.*;


class GRACAR_ILOG {

    private int m;    //number of servers
    private int n;    //number of fields
    private int m1;    //number of servers
    private int n1;    //number of fields
    private int m2;
    private int n2;

    private double[] Q;
    private double[] Q1;    //non sensitive Qualification matrix
    private double[] Q2;    //sensitive Qualification matrix
    private int[] AC1;        //Conflict matrix
    private int[] AC;        //Conflict matrix
    private int[] L;
    private int[] L1;    //Requirement array
    private int[] LA;
    private int[] LA1;    //Requirement array
    private int[] DQ1;    //Requirement array
    private int[] SC1;    //Requirement array
    private double[] P1;    //Requirement array
    private int[] DQ;    //Requirement array
    private int[] SC;    //Requirement array
    private double[] P;    //Requirement array
    private int[][] A1;  //Assignment array
    private double[] B1;
    private double[] B;
    private double[] B2;
    private int[] AC2;        //Conflict matrix
    private int[] L2;    //Requirement array
    private int[] LA2;    //Requirement array
    private int[] DQ2;    //Requirement array
    private int[] SC2;    //Requirement array
    private double[] P2;    //Requirement array
    private int[][] A2;  //Assignment array
    private double[] TV;
    private double[] DS;
    private int[][] A;
//    private List<List<Integer>> conflitLists;

    DecimalFormat df = new DecimalFormat("0.00");

    double optimized_result = 0;
    boolean bILOG_result;

    public GRACAR_ILOG(int nagent, int nrole, double[][] QM, int[][] AC, int[] LIN, int[] LAIN, int[] DQ, int[] SC, double[] B, double[] P, int m1, int n1, double[] TV, double[] DS) {
        m = nagent;
        n = nrole;
        this.m1 = m1;
        this.n1 = n1;
        m2 = m - m1;
        n2 = n - n1;
//        this.conflitLists = conflitLists;

        Q1 = new double[m1 * n1];
        for (int num = 0, i = 0; i < m1; ++i) {
            for (int j = 0; j < n1; ++j) {
                Q1[num] = QM[i][j];
                ++num;
            }
        }

        Q2 = new double[m2 * n2];
        for (int num = 0, i = m1; i < m; ++i) {
            for (int j = n1; j < n; ++j) {
                Q2[num] = QM[i][j];
                ++num;
            }
        }

        AC1 = new int[m1 * m1];
        AC2 = new int[m2 * m2];
        for (int i = 0, r = 0; r < m1; ++r) {
            for (int c = 0; c < m1; ++c) {
                AC1[i] = AC[r][c];
                ++i;
            }
        }
        for (int i = 0, r = m1; r < m; ++r) {
            for (int c = m1; c < m; ++c) {
                AC2[i] = AC[r][c];
                ++i;
            }
        }

        L1 = new int[n1];
        P1 = new double[m1];
        P2 = new double[m2];
        for (int c = 0; c < m1; ++c) {
            P1[c] = P[c];
        }
        for (int a = 0, i = m1; i < m; ++i) {
            P2[a] = P[i];
            ++a;
        }
        B1 = new double[n1];
        B2 = new double[n2];
        for (int i = 0; i < n1; ++i) {
            B1[i] = B[i];
        }
        for (int i = 0; i < n2; ++i) {
            B2[i] = B[n1 + i];
        }

        LA1 = new int[m1];
        for (int r = 0; r < m1; ++r) {
            LA1[r] = LAIN[r];
        }
        LA2 = new int[m2];
        for (int i = 0; i < m2; ++i) {
            LA2[i] = 1;
        }
        DQ1 = new int[n1];
        for (int c = 0; c < n1; ++c) {
            L1[c] = LIN[c];
            DQ1[c] = DQ[c];
        }
        DQ2 = new int[n2];
        L2 = new int[n2];
        for (int c = 0; c < n2; ++c) {
            L2[c] = LIN[c + n1];
            DQ2[c] = DQ[c + n1];
        }
        SC1 = new int[m1];
        SC2 = new int[m2];
        for (int r = 0; r < m1; ++r)
            SC1[r] = SC[r];
        for (int r = 0; r < m2; ++r)
            SC2[r] = SC[r + m1];
        A1 = new int[m1][n1];
        for (int r = 0; r < m1; ++r) {
            for (int c = 0; c < n1; ++c)
                A1[r][c] = 0;
        }
        A2 = new int[m2][n2];
        for (int i = 0; i < m2; i++) {
            for (int j = 0; j < n2; j++) {
                A2[i][j] = 0;
            }
        }
        A = new int[m][n];
        this.TV = new double[m * n];
        LA = new int[m];
        this.DQ = new int[n];
        this.SC = new int[m];
        this.P = new double[m];
        this.B = new double[n];
        L = new int[n];
        for (int i = 0; i < n; i++) {
            this.DQ[i] = DQ[i];
            this.B[i] = B[i];
            L[i] = LIN[i];
        }
        Q = new double[m * n];
        for (int num = 0, i = 0; i < m; ++i) {
            LA[i] = LAIN[i];
            this.SC[i] = SC[i];
            this.P[i] = P[i];
            for (int j = 0; j < n; ++j) {
                this.TV[num] = TV[i];
                Q[num] = QM[i][j];
                ++num;
            }
        }
        this.AC = new int[m * m];
        for (int num = 0, i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                this.AC[num] = AC[i][j];
                ++num;
            }
        }
        this.DS = DS;
    }

    //our method
    public double revisedSolution(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists, HashMap<Integer, List<Integer>> records) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.
            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, 1);
            }

            //already stored constraint
            if (records.size() != 0) {
                for (Map.Entry<Integer, List<Integer>> entry : records.entrySet()) {
                    for (int i = 0; i < entry.getValue().size(); i++) {
                        IloLinearNumExpr constraint = cplex.linearNumExpr();
                        constraint.addTerm(1, x[entry.getValue().get(i) * n + entry.getKey()]);
                        cplex.addEq(constraint, 0);
                        for (int a = 0; a < conflitLists.size(); a++) {
                            List<Integer> servers1 = serverProviders.get(conflitLists.get(a).get(0));
                            List<Integer> servers2 = serverProviders.get(conflitLists.get(a).get(1));
                            if (servers1.contains(entry.getValue().get(i))) {
                                for (int j = 0; j < servers2.size(); j++) {
                                    IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                                    for (int k = 0; k < n; k++) {
                                        conflict1.addTerm(1, x[servers2.get(j) * n + k]);
                                    }
                                    cplex.addEq(conflict1, 0);
                                }
                            }
                            else if (servers2.contains(entry.getValue().get(i))) {
                                for (int j = 0; j < servers1.size(); j++) {
                                    IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                                    for (int k = 0; k < n; k++) {
                                        conflict2.addTerm(1, x[servers1.get(j) * n + k]);
                                    }
                                    cplex.addEq(conflict2, 0);
                                }
                            }
                        }
                    }
                }
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }


            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            //Constrain type 3: The agent conflict constrains.
            for (int i = 0; i < conflitLists.size(); i++) {
                //
                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));
                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                for (int j = 0; j < servers1.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict1.addTerm(1, x[servers1.get(j) * n + k]);
                    }
                }
                for (int j = 0; j < servers2.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict2.addTerm(1, x[servers2.get(j) * n + k]);
                    }
                }
                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
            }

            //Solve LP
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                double[] val = cplex.getValues(x);
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
                    TR[j / n][j % n] = A[j / n][j % n];
                    if (TR[j / n][j % n] == 1) {
                        List<Integer> list = new ArrayList<>();
                        if (records.containsKey(j % n)) {
                            list = records.get(j % n);
                        }
                        list.add(j / n);
                        records.put(j % n, list);
                    }
                }
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    public double solution(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

//            Random generator = new Random();
//            int[][] RC = new int[n][n];
//            for (int i = (n - 1); i >= 0; i--) //Init
//            {
//                for (int j = 0; j <= i; j++) {
//                    int signal;
//                    if (i == j) signal = 0;
////				 else if (generator.nextDouble() <= probability) signal = 1;
//                    else if (generator.nextDouble() < 0.1) signal = 1;
//                    else signal = 0;
//                    RC[i][j] = signal;
//                    RC[j][i] = RC[i][j];
//                }
//            }
//            int[] RC1 = new int[n * n];
//            for (int i = 0, r = 0; r < n; r++)
//                for (int c = 0; c < n; c++) {
//                    RC1[i] = RC[r][c];
//                    i++;
//                }

            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }


            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            //Constrain type 3: The agent conflict constrains.
            //Constraints on the partnership between service providers
            //conflitLists: List of Recorded Partnerships
            for (int i = 0; i < conflitLists.size(); i++) {
                //One group of all servers belonging to this SP
                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
                //The other group of all servers belonging to another SP
                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));

                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                for (int j = 0; j < servers1.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict1.addTerm(1, x[servers1.get(j) * n + k]);
                    }
                }
                for (int j = 0; j < servers2.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict2.addTerm(1, x[servers2.get(j) * n + k]);
                    }
                }
                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
            }
            //Constraints for all servers belonging to the same SP
            //serverProviders: List of all servers with SP status
            for (int i = 0; i < serverProviders.size(); i++) {
                //All servers of this SP
                List<Integer> servers = serverProviders.get(i);
                //Add a constraint to each server that when it is assigned a field, other servers in the same group cannot be assigned
                for (int j = 0; j < servers.size(); j++) {
                    IloLinearNumExpr server1 = cplex.linearNumExpr();
                    int server = servers.get(j);
                    for (int k = 0; k < n; k++) {
                        server1.addTerm(1, x[server * n + k]);
                    }
                    IloLinearNumExpr others = cplex.linearNumExpr();
                    for (int k = 0; k < servers.size(); k++) {
                        if (servers.get(k) != server) {
                            for (int l = 0; l < n; l++) {
                                others.addTerm(1, x[servers.get(k) * n + l]);
                            }
                        }
                    }
                    cplex.add(cplex.ifThen(cplex.ge(server1, 1), cplex.eq(others, 0)));
                }
            }

            //Constrain type 4: The role conflict constrains.
//            for (int r = 0; r < m; r++) // Scan the T matrix by column
//            {
//                if (1 < LA[r]) {
//                    //Find out all the index of x on that column
//                    int index[] = new int[n]; //number of role
//                    int indexcounter = 0;
//                    for (int i = 0; i < m * n; i++) {
//                        if (i % m == r) {
//                            index[indexcounter] = i;
//                            indexcounter++;
//                        }
//                    }
//                    //Add conflicts constrains on that role.
//                    for (int i = 0; i < n * n; i++) //i size of the conflict chart
//                    {
//                        int row = i / n;
//                        int col = i % n;
//                        if (1 == RC1[i]) {
//                            IloLinearNumExpr conflict = cplex.linearNumExpr();
//                            conflict.addTerm(1, x[index[col]]);
//                            conflict.addTerm(1, x[index[row]]);
//                            cplex.addLe(conflict, 1);
//                        }
//                    }
//                }
//            }

            //Solve LP
            //long t1 = System.nanoTime();
//            cplex.exportModel("lpex1.lp");
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                //cplex.output().println("Solution status = " + cplex.getStatus());
                //cplex.output().println("Solution value = " + cplex.getObjValue());

                double[] val = cplex.getValues(x);
//                int ncols = cplex.getNcols();
                //cplex.output().println("Num COL: " + ncols);

//				cplex.output().println("Result Table: " );
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
//					System.out.print(A[j/n][j%n] + " ");
                    TR[j / n][j % n] = A[j / n][j % n];
                    //System.out.print(val1[j]+ "	");
//					if ((j+1)%(n) == 0) {System.out.print("\n");}
                }
                //TR = A;
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    public double linear(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            //Constrain type 3: The agent conflict constrains.
            for (int i = 0; i < conflitLists.size(); i++) {
                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));
                for (int j = 0; j < servers1.size(); j++) {
                    for (int j2 = 0; j2 < servers2.size(); j2++) {
                        for (int k = 0; k < n; k++) {
                            for (int l = 0; l < n; l++) {
                                if (k != l) {
                                    IloLinearNumExpr conflict = cplex.linearNumExpr();
                                    conflict.addTerm(1, x[servers1.get(j) * n + k]);
                                    conflict.addTerm(1, x[servers2.get(j2) * n + l]);
                                    cplex.addLe(conflict, 1);
                                }
                            }
                        }
                    }
                }
            }


            //Solve LP
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();

                double[] val = cplex.getValues(x);
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
                    TR[j / n][j % n] = A[j / n][j % n];
                }
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    //optimal without conflict
    public double resolve(int[][] TR) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                double[] val = cplex.getValues(x);
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
                    TR[j / n][j % n] = A[j / n][j % n];
                }
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    //method3
    public double resolve1(int[][] TR, List<Integer> reDistribute, List<Integer> fields, List<List<Integer>> conflictServers) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object
            int m = reDistribute.size();
            int n = fields.size();

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            int num1 = 0;
            int num2 = 0;

            num1 = 0;
            num2 = 0;
            while (num2 < n) {
                if (fields.get(num2) < n1) {
                    ++num2;
                } else {
                    IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                    while (reDistribute.get(num1) < m1) {
                        sensitivityConstrain2.addTerm(1, x[num1 * n + num2]);
                        ++num1;
                    }
                    num1 = 0;
                    cplex.addEq(sensitivityConstrain2, 0);
                    ++num2;
                }
            }

            num1 = 0;
            num2 = 0;
            while (num2 < n) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                while (num1 < m) {
                    exprReqConstrain.addTerm(1, x[num1 * n + num2]);
                    budgetConstrain.addTerm(P[reDistribute.get(num1)], x[num1 * n + num2]);
                    ++num1;
                }
                num1 = 0;
                cplex.addEq(exprReqConstrain, L[fields.get(num2)]);
                cplex.addLe(budgetConstrain, B[fields.get(num2)]);
                ++num2;
            }

            num1 = 0;
            num2 = 0;
            while (num1 < m) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                while (num2 < n) {
                    AgentAbilityConstraint.addTerm(1, x[num1 * n + num2]);
                    storeConstrain.addTerm(DQ[fields.get(num2)], x[num1 * n + num2]);
                    ++num2;
                }
                num2 = 0;
                cplex.addLe(AgentAbilityConstraint, LA[reDistribute.get(num1)]);
                cplex.addLe(storeConstrain, SC[reDistribute.get(num1)]);
                ++num1;
            }

            num1 = 0;
            num2 = 0;
            //Constrain type 3: The agent conflict constrains.
            for (int i = 0; i < conflictServers.size(); i++) //i size of the conflict chart
            {
                if (reDistribute.indexOf(conflictServers.get(i).get(0)) != -1 && reDistribute.indexOf(conflictServers.get(i).get(1)) != -1) {
                    IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                    IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                    while (num2 < n) {
                        conflict1.addTerm(1, x[reDistribute.indexOf(conflictServers.get(i).get(0)) * n + num2]);
                        conflict2.addTerm(1, x[reDistribute.indexOf(conflictServers.get(i).get(1)) * n + num2]);
                        ++num2;
                    }
                    num2 = 0;
                    cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
                }
            }


            //Solve LP
            //long t1 = System.nanoTime();
//            cplex.exportModel("lpex1.lp");
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                //cplex.output().println("Solution status = " + cplex.getStatus());
                //cplex.output().println("Solution value = " + cplex.getObjValue());

                double[] val = cplex.getValues(x);
                int ncols = cplex.getNcols();
                //cplex.output().println("Num COL: " + ncols);

//				cplex.output().println("Result Table: " );
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
//					System.out.print(A[j/n][j%n] + " ");
                    TR[reDistribute.get(j / n)][fields.get(j % n)] = A[j / n][j % n];
                    //System.out.print(val1[j]+ "	");
//					if ((j+1)%(n) == 0) {System.out.print("\n");}
                }
                //TR = A;
                cplex.end();

            } else {
                System.out.println("无解");
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    public double getOptimizedResult() {
        return optimized_result;
    }

    public double resolve2(double[][] qual, int[][] TR) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            double[] q = new double[m * n];
            for (int num = 0, i = 0; i < m; ++i) {
                for (int j = 0; j < n; ++j) {
                    q[num] = qual[i][j];
                    ++num;
                }
            }
            cplex.addMaximize(cplex.scalProd(x, q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = 0; j < n1; j++) {
                IloLinearNumExpr sensitivityConstrain1 = cplex.linearNumExpr();
                for (int i = m1; i < m; i++) {
                    sensitivityConstrain1.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain1, 0);
            }
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }
            //Solve LP
            //long t1 = System.nanoTime();
//            cplex.exportModel("lpex1.lp");
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                //cplex.output().println("Solution status = " + cplex.getStatus());
                //cplex.output().println("Solution value = " + cplex.getObjValue());

                double[] val = cplex.getValues(x);
//                int ncols = cplex.getNcols();
                //cplex.output().println("Num COL: " + ncols);

//				cplex.output().println("Result Table: " );
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
//					System.out.print(A[j/n][j%n] + " ");
                    TR[j / n][j % n] = A[j / n][j % n];
                    //System.out.print(val1[j]+ "	");
//					if ((j+1)%(n) == 0) {System.out.print("\n");}
                }
                //TR = A;
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    public double compare(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object
            cplex.setOut(null);

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);

            double[] max = new double[m * n];
            for (int num = 0, i = 0; i < m; i++) {
                for (int j = 0; j < n; j++) {
                    max[num] = TV[m] - DS[j];
                    if (max[num] < 0) {
                        max[num] = 0;
                    }
                    ++num;
                }
            }

            cplex.addMaximize(cplex.scalProd(x, max));

            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            for (int i = 0; i < conflitLists.size(); i++) {
                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));
                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                for (int j = 0; j < servers1.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict1.addTerm(1, x[servers1.get(j) * n + k]);
                    }
                }
                for (int j = 0; j < servers2.size(); j++) {
                    for (int k = 0; k < n; k++) {
                        conflict2.addTerm(1, x[servers2.get(j) * n + k]);
                    }
                }
                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
            }

            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();

                double[] val = cplex.getValues(x);
//                int ncols = cplex.getNcols();

                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
                    TR[j / n][j % n] = A[j / n][j % n];
                }
                cplex.end();
            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }
        return optimized_result;
    }

    public double base(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.

            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            //Constrain type 3: The agent conflict constrains.
//            for (int i = 0; i < conflitLists.size(); i++) {
//                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
//                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));
//                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
//                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
//                for (int j = 0; j < servers1.size(); j++) {
//                    for (int k = 0; k < n; k++) {
//                        conflict1.addTerm(1, x[servers1.get(j) * n + k]);
//                    }
//                }
//                for (int j = 0; j < servers2.size(); j++) {
//                    for (int k = 0; k < n; k++) {
//                        conflict2.addTerm(1, x[servers2.get(j) * n + k]);
//                    }
//                }
//                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
//            }

            //Solve LP
            //long t1 = System.nanoTime();
//            cplex.exportModel("lpex1.lp");
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                //cplex.output().println("Solution status = " + cplex.getStatus());
                //cplex.output().println("Solution value = " + cplex.getObjValue());

                double[] val = cplex.getValues(x);
//                int ncols = cplex.getNcols();
                //cplex.output().println("Num COL: " + ncols);

//				cplex.output().println("Result Table: " );
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
//					System.out.print(A[j/n][j%n] + " ");
                    TR[j / n][j % n] = A[j / n][j % n];
                    //System.out.print(val1[j]+ "	");
//					if ((j+1)%(n) == 0) {System.out.print("\n");}
                }
                //TR = A;
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
//            cplex.solve();
//            IloNumVar[] startVar = new IloNumVar[m * n];
//            double[] startVal = new double[m * n];
//            startVar = x;
//            startVal = Q;
//            for (int i = 0; i < conflitLists.size(); i++) //i size of the conflict chart
//            {
//                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
//                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
//                for (int j = 0; j < n; j++) {
//                    conflict1.addTerm(1, x[conflitLists.get(i).get(0) * n + j]);
//                }
//
//                for (int j = 0; j < n; j++) {
//                    conflict2.addTerm(1, x[conflitLists.get(i).get(1) * n + j]);
//                }
//                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
//            }
//            cplex.addMIPStart(startVar, startVal);
//            if (cplex.solve()) {
//                bILOG_result = true;
//                optimized_result = cplex.getObjValue();
//                //cplex.output().println("Solution status = " + cplex.getStatus());
//                //cplex.output().println("Solution value = " + cplex.getObjValue());
//
//                double[] val = cplex.getValues(x);
////                int ncols = cplex.getNcols();
//                //cplex.output().println("Num COL: " + ncols);
//
////				cplex.output().println("Result Table: " );
//                for (int j = 0; j < val.length; j++) {
//                    A[j / n][j % n] = (int) (val[j] + 0.000001);
////					System.out.print(A[j/n][j%n] + " ");
//                    TR[j / n][j % n] = A[j / n][j % n];
//                    //System.out.print(val1[j]+ "	");
////					if ((j+1)%(n) == 0) {System.out.print("\n");}
//                }
//                //TR = A;
//                cplex.end();
//
//            } else {
//                cplex.end();
//                bILOG_result = true;
//            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    //condensed
    public double condensed(int m, int m1, double[] Q, int[] LA, int[] SC, double[] P, int[][] TR) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n, 0, 1);    //initialize the variables array under cplex.

            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = 0; j < n1; j++) {
                IloLinearNumExpr sensitivityConstrain1 = cplex.linearNumExpr();
                for (int i = m1; i < m; i++) {
                    sensitivityConstrain1.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain1, 0);
            }
            for (int j = n1; j < n; j++) {
                IloLinearNumExpr sensitivityConstrain2 = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstrain2.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(sensitivityConstrain2, 0);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n + j]);
                }
                cplex.addEq(exprReqConstrain, L[j]);
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n; ++j) {
                    storeConstrain.addTerm(DQ[j], x[i * n + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

            for (int j = 0; j < n; j++) {
                IloLinearNumExpr budgetConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstrain.addTerm(P[i], x[i * n + j]);
                }
                cplex.addLe(budgetConstrain, B[j]);
            }

            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();

                double[] val = cplex.getValues(x);
                for (int j = 0; j < val.length; j++) {
                    A[j / n][j % n] = (int) (val[j] + 0.000001);
                    TR[j / n][j % n] = A[j / n][j % n];
                }
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }

    public double solutionImproved(int[][] TR, List<List<Integer>> serverProviders, List<List<Integer>> conflitLists) {
        try {
            //Creat cplex obj
            IloCplex cplex = new IloCplex();    //initialize the cplex object

            IloIntVar[] x = cplex.intVarArray(m * n * 2, 0, 1);    //initialize the variables array under cplex.
            double[] Q = new double[m * n * 2];
            for (int i = 0; i < m * n * 2; i++) {
                Q[i] = this.Q[i / 2];
            }
            cplex.addMaximize(cplex.scalProd(x, Q));    //add the optimize objective to cplex.
            cplex.setOut(null);

            //Constrain type 1: Add role requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int j = n1 * 2; j < n * 2; j += 2) {
                IloLinearNumExpr sensitivityConstraint = cplex.linearNumExpr();
                for (int i = 0; i < m1; i++) {
                    sensitivityConstraint.addTerm(1, x[i * n * 2 + j]);
                    sensitivityConstraint.addTerm(1, x[i * n * 2 + j + 1]);
                }
                cplex.addEq(sensitivityConstraint, 0);
            }

            for (int j = 0; j < n * 2; j++) {
                IloLinearNumExpr exprReqConstrain = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    exprReqConstrain.addTerm(1, x[i * n * 2 + j]);
                }
                cplex.addEq(exprReqConstrain, 1);
            }

            for (int i = 0; i < m; i++) {
                for (int j = 0; j < n * 2; j += 2) {
                    IloLinearNumExpr repConstraint = cplex.linearNumExpr();
                    repConstraint.addTerm(1, x[i * n * 2 + j]);
                    repConstraint.addTerm(1, x[i * n * 2 + j + 1]);
                    cplex.addLe(repConstraint, 1);
                }
            }

            //Constrain type 2: Add agent ability requirement constrains,
            //the number of people assigned on each role should meet the requirement on that role.
            //Hence, n constrains will be added.
            for (int i = 0; i < m; i++) {
                IloLinearNumExpr AgentAbilityConstraint = cplex.linearNumExpr();
                for (int j = 0; j < n * 2; j++) {
                    AgentAbilityConstraint.addTerm(1, x[i * n * 2 + j]);
                }
                cplex.addLe(AgentAbilityConstraint, LA[i]);
            }
            //budget
            for (int j = 0; j < n * 2; j += 2) {
                IloLinearNumExpr budgetConstraint = cplex.linearNumExpr();
                for (int i = 0; i < m; i++) {
                    budgetConstraint.addTerm(P[i], x[i * n * 2 + j]);
                    budgetConstraint.addTerm(P[i], x[i * n * 2 + j + 1]);
                }
                cplex.addLe(budgetConstraint, B[j / 2]);
            }

            for (int i = 0; i < m; ++i) {
                IloLinearNumExpr storeConstrain = cplex.linearNumExpr();
                for (int j = 0; j < n * 2; ++j) {
                    storeConstrain.addTerm(DQ[j / 2], x[i * n * 2 + j]);
                }
                cplex.addLe(storeConstrain, SC[i]);
            }

//            Constrain type 3: The agent conflict constrains.
            for (int i = 0; i < conflitLists.size(); i++) {
                //
                List<Integer> servers1 = serverProviders.get(conflitLists.get(i).get(0));
                List<Integer> servers2 = serverProviders.get(conflitLists.get(i).get(1));
                IloLinearNumExpr conflict1 = cplex.linearNumExpr();
                IloLinearNumExpr conflict2 = cplex.linearNumExpr();
                for (int j = 0; j < servers1.size(); j++) {
                    for (int k = 0; k < n * 2; k++) {
                        conflict1.addTerm(1, x[servers1.get(j) * n * 2 + k]);
                    }
                }
                for (int j = 0; j < servers2.size(); j++) {
                    for (int k = 0; k < n * 2; k++) {
                        conflict2.addTerm(1, x[servers2.get(j) * n * 2 + k]);
                    }
                }
                cplex.add(cplex.ifThen(cplex.ge(conflict1, 1), cplex.eq(conflict2, 0)));
            }

            //Solve LP
            //long t1 = System.nanoTime();
//            cplex.exportModel("lpex1.lp");
            if (cplex.solve()) {
                bILOG_result = true;
                optimized_result = cplex.getObjValue();
                //cplex.output().println("Solution status = " + cplex.getStatus());
                //cplex.output().println("Solution value = " + cplex.getObjValue());

                double[] val = cplex.getValues(x);
//                int ncols = cplex.getNcols();
                //cplex.output().println("Num COL: " + ncols);

//				cplex.output().println("Result Table: " );
                for (int j = 0; j < val.length; j += 2) {
                    int a = (int) (val[j] + 0.000001);
                    int b = (int) (val[j + 1] + 0.000001);
                    if (a == 1 || b == 1) {
                        TR[j / (n * 2) ][(j / 2) % n] = 1;
                    }
                }
                //TR = A;
                cplex.end();

            } else {
                cplex.end();
                bILOG_result = true;
            }
        } catch (IloException e) {
            System.err.println("Concert exception" + e + " caught");
        }


        return (optimized_result);
    }
}

public class GMRACABC {
    private static double nextNextGaussian;
    private static boolean haveNextNextGaussian = false;

    public static void printDMatrix(double[][] x, int m, int n) {
        DecimalFormat tw = new DecimalFormat("0.00");
        System.out.print("{");
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                System.out.print(tw.format(x[i][j]));
                System.out.print(",");
            }
        }
        System.out.print("}");
        System.out.println();
    }

    public static void printIMatrix(int[][] x, int m, int n) {
        DecimalFormat tw = new DecimalFormat("0");
        System.out.print("{");
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                System.out.print(tw.format(x[i][j]));
                System.out.print(",");
            }
            System.out.println();
        }
        System.out.print("}");
        System.out.println();
    }

    public static void printIVector(int[] x) {
        DecimalFormat tw = new DecimalFormat("0");
        for (int i = 0; i < x.length; i++) {
            System.out.print(tw.format(x[i]));
            System.out.print(",");
        }
        System.out.println();
    }

    public static void printDVector(double[] x) {
        DecimalFormat tw = new DecimalFormat("0.00");
        for (int i = 0; i < x.length; i++) {
            System.out.print(tw.format(x[i]));
            System.out.print(",");
        }
        System.out.println();
    }

    public static int sigmaL(int[] L) {
        int total = 0;
        for (int j = 0; j < L.length; j++)
            total += L[j];
        return total;
    }

    public static void main(String[] args) {
        Random generator = new Random();
        int m = 300, n = 100;
        double ta = 0;
        double ca = 0;
        double ta1 = 0;
        double ca1 = 0;
        XYSeries firefox = new XYSeries("Improved Method");
        XYSeries chrome = new XYSeries("Trust-based Method");
        XYSeries ie = new XYSeries("Baseline Method");
        XYSeries r3 = new XYSeries("Method");
        XYSeries firefox1 = new XYSeries("Improved Method");
        XYSeries chrome1 = new XYSeries("Trust-based Method");
        XYSeries ie1 = new XYSeries("Baseline Method");
        int conflict1 = 0;
        int conflict2 = 0;
        int conflict3 = 0;
        int infeasible = 0;
        int excute = 100;
        int infeasibleM1 = 0;
        int infeasibleM2 = 0;
        int infeasibleM3 = 0;
        double[] time = new double[excute];
        double[] time2 = new double[excute];
        double[] time3 = new double[excute];
        double[] time4 = new double[excute];
        double[] TCL = new double[excute];
        double[] PCL = new double[excute];
        double diff = 0;
        double dif = 0;
        //data sensitivity
        for (int times = 0; times < excute; times++) {
            double[] DS = new double[n];
            //server trust value
            double[] TV = new double[m];
            //trust confidence value
            double[][] TC = new double[m][n];
            //server performance
            double[][] SP = new double[m][3];
            //performance requirement
            double[][] PR = new double[n][3];
            //performance confidence
            double[][] PC = new double[m][n];
            //qualification value
            double[][] Q = new double[m][n];
            //coefficient
            double a = 0.7;
            //number of cloud servers
            int m1 = m / 10, n1 = 0;
            //role vector
            int[] L = new int[n];
            //data field quantity
            int[] DQ = new int[n];
            int[] LA = new int[m];
            //server capacity
            int[] SC = new int[m];
            //price
            double[] P = new double[m];
            //Budget
            double[] B = new double[n];
            //conflict
            int[][] AC = new int[m][m];
            double probability = 0.1;
            //generate data sensitivity randomly
            for (int i = 0; i < n; ++i) {
                DS[i] = generator.nextDouble() * 0.9;
                if (DS[i] < 0.5) {
                    ++n1;
                }
            }
            Arrays.sort(DS);

            for (int i = 0; i < n; ++i) {
                //generate performance requirement
                PR[i][0] = generator.nextInt(5) * 0.1 + 0.1;
                PR[i][1] = generator.nextInt(6) * (1.0 / 12.0) + (1.0 / 12.0);
                PR[i][2] = generator.nextInt(10) * 0.05 + 0.05;
                //set L
                L[i] = 1;
                //set data quantity
                DQ[i] = generator.nextInt(10) + 1;
                //set budget
//                B[i] = generator.nextInt(4) * 100 + 300;
                B[i] = DS[i] * 1000 + 300;
            }

            for (int i = 0; i < m; ++i) {
                //generate trust value randomly
                TV[i] = generator.nextGaussian() * Math.sqrt(0.1) + 0.9;
                if (TV[i] < 0) {
                    TV[i] = 0;
                } else if (TV[i] > 1) {
                    TV[i] = 1;
                }
                //generate server performance
                SP[i][0] = generator.nextInt(8) * 0.1 + 0.3;
                SP[i][1] = generator.nextInt(8) * (1.0 / 12.0) + 5 * (1.0 / 12.0);
                SP[i][2] = generator.nextInt(17) * 0.05 + 0.20;
                //generate server capacity
                SC[i] = (int) (Math.pow(2, generator.nextInt(11)) * 32);
                //set LA
                if (i < m1) {
                    LA[i] = 10;
                } else {
                    LA[i] = 1;
                }
                //calculate price
//            P[i] = ((double) (generator.nextInt(4) + 2) / 100) * Math.pow(2, SP[i][1] / (1.0 / 12.0)) * 730 + 1.5 * (SC[i] / 32) + (SP[i][2] - 0.05) * 0.05;
                P[i] = TV[i] * 150 + 1.5 * (SC[i] / 32) + SP[i][1] * 150 + (SP[i][2] - 0.05) * 0.05;
            }


            for (int i = 0; i < m; ++i) {
                for (int j = 0; j < n; ++j) {
                    //get trust coincidence value
                    TC[i][j] = 1 - (TV[i] - DS[j]);
                    if (TC[i][j] > 1) {
                        TC[i][j] = 0;
                    }
                    //get performance coincidence
                    if (SP[i][0] - PR[j][0] < 0 || SP[i][1] - PR[j][1] < 0 || SP[i][2] - PR[j][2] < 0) {
                        PC[i][j] = 0;
                    } else {
                        PC[i][j] = 1 - ((SP[i][0] - PR[j][0]) + (SP[i][1] - PR[j][1]) + (SP[i][2] - PR[j][2])) / 3;
                    }
                    if (TC[i][j] <= 0 || PC[i][j] <= 0) {
                        Q[i][j] = 0;
                    } else {
                        Q[i][j] = a * TC[i][j] + (1 - a) * PC[i][j];
                    }
                }
            }
//         Random AC
            List<Integer> serverList = new ArrayList<>();
            for (int i = 0; i < m; i++) {
                serverList.add(i);
            }
            Collections.shuffle(serverList);
            List<List<Integer>> serverProviders = new ArrayList<>();
            int sizeOfSP = 100;
            int numbers = m / sizeOfSP;
            for (int i = 0; i < sizeOfSP; ++i) {
                List<Integer> list = new ArrayList<>();
                for (int j = 0; j < numbers; j++) {
                    list.add(serverList.get(i * numbers + j));
                }
                serverProviders.add(list);
            }
//            int generate1 = 0;
//            int generate2 = 0;
//            while (generate1 == generate2) {
//                generate1 = generator.nextInt(10);
//                generate2 = generator.nextInt(10);
//            }
//            int generate3 = 0;
//            int generate4 = 0;
//            while (generate3 == generate4) {
//                generate3 = generator.nextInt(10);
//                generate4 = generator.nextInt(10);
//            }
//            int generate5 = 0;
//            int generate6 = 0;
//            while (generate5 == generate6) {
//                generate5 = generator.nextInt(10);
//                generate6 = generator.nextInt(10);
//            }
//            int generate7 = 0;
//            int generate8 = 0;
//            while (generate7 == generate8) {
//                generate7 = generator.nextInt(10);
//                generate8 = generator.nextInt(10);
//            }
            List<List<Integer>> conflitLists = new ArrayList<>();
            conflitLists.add(Arrays.asList(1, 2));
            conflitLists.add(Arrays.asList(1, 3));
            conflitLists.add(Arrays.asList(2, 3));
            conflitLists.add(Arrays.asList(4, 5));
            conflitLists.add(Arrays.asList(6, 7));
            conflitLists.add(Arrays.asList(8, 9));
//            List<List<Integer>> conList = new ArrayList<>();
//            for (int i = 0; i < conflitLists.size(); i++) {
//                List<Integer> lista = serverProviders.get(conflitLists.get(i).get(0));
//                List<Integer> listb = serverProviders.get(conflitLists.get(i).get(1));
//                for (int j = 0; j < lista.size(); j++) {
//                    for (int k = 0; k < listb.size(); k++) {
//                        conList.add(new ArrayList<>(Arrays.asList(lista.get(j), listb.get(k))));
//                    }
//                }
//            }
            List<List<Integer>> conflictServers = new ArrayList<>();
            for (int i = 0; i < conflitLists.size(); i++) {
                int x = conflitLists.get(i).get(0);
                int y = conflitLists.get(i).get(1);
                for (int j = 0; j < serverProviders.get(x).size(); j++) {
                    int server = serverProviders.get(x).get(j);
                    for (int k = 0; k < serverProviders.get(y).size(); k++) {
                        conflictServers.add(new ArrayList<>(Arrays.asList(server, serverProviders.get(y).get(k))));
                    }
                }
            }
            for (int i = 0; i < conflictServers.size(); i++) {
                for (int j = 0; j < conflictServers.get(i).size(); j++) {
                    int x = conflictServers.get(i).get(0);
                    int y = conflictServers.get(i).get(1);
                    AC[x][y] = 1;
                    AC[y][x] = 1;
                }
            }
            for (int i = 0; i < serverProviders.size(); i++) {
                for (int j = 0; j < serverProviders.get(i).size(); j++) {
                    int x = serverProviders.get(i).get(j);
                    for (int k = j + 1; k < serverProviders.get(i).size(); k++) {
                        int y = serverProviders.get(i).get(k);
                        AC[x][y] = 1;
                        AC[y][x] = 1;
                    }
                }
            }
//            System.out.println(n1);
//            printDMatrix(Q, m, n);
//            printIVector(DQ);
//            printIVector(SC);
//            printDVector(B);
//            printDVector(P);
//            printIMatrix(AC, m, m);
            //TEST parameters:
            int[][] T = new int[m][n];
            //Init ILOG and resolve
            GRACAR_ILOG ILOG = new GRACAR_ILOG(m, n, Q, AC, L, LA, DQ, SC, B, P, m1, n1, TV, DS);

            System.out.println("zhixing" + times);
            //improved method backup
            long runTime = System.nanoTime();
//            double result = ILOG.solutionImproved(T, serverProviders, conflitLists);
            //our method
            int[][] finalT = new int[m][n];
//            HashMap<Integer, List<Integer>> records = new HashMap<>();
//            for (int i = 0; i < L[0]; i++) {
//                ILOG.revisedSolution(T, serverProviders, conflitLists, records);
//                for (int j = 0; j < m; j++) {
//                    for (int k = 0; k < n; k++) {
//                        if (T[j][k] == 1) {
//                            finalT[j][k] = 1;
//                            T[j][k] = 0;
//                        }
//                    }
//                }
//            }
            double result = ILOG.solution(T, serverProviders, conflitLists);
            //判断冲突
//            List<Integer> assign = new ArrayList<>();
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T[i][j] == 1) {
//                        assign.add(i);
//                        break;
//                    }
//                }
//            }
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < m; j++) {
//                    if (AC[i][j] == 1 && assign.contains(i) && assign.contains(j)) {
//                        System.out.println("有冲突");
//                    }
//                }
//            }


//            double result = ILOG.base(T, serverProviders, conflitLists);
            long finishTime = System.nanoTime();
            time[times] = (double) (finishTime - runTime) / 1000000;
            System.out.println(result);
            System.out.println(time[times] + "s");
//            System.out.println();
//            for (int j = 0; j < m; j++) {
//                for (int k = 0; k < n; k++) {
//                    if (finalT[j][k] == 1) {
//                        result += Q[j][k];
//                    }
//                }
//            }
//            System.out.println(result);
//            printIMatrix(T, m, n);
//            runTime = System.nanoTime();
            int[][] T1 = new int[m][n];
//////            double result1 = ILOG.compare(T1, serverProviders, conflitLists);
//            double result1 = 0;
            double result1 = ILOG.linear(T1, serverProviders, conflitLists);
//            finishTime = System.nanoTime();
//            time2[times] = (double) (finishTime - runTime) / 1000000;
            System.out.println(result1);
//            System.out.println(time2[times] + "s");
//            printIMatrix(T, m, n);
//            printIMatrix(T1, m, n);
//            runTime = System.nanoTime();
//            int[][] T2 = new int[m][n];
//            double result2 = ILOG.base(T2, serverProviders, conflitLists);
//            finishTime = System.nanoTime();
//            time3[times] = (double) (finishTime - runTime) / 1000000;
//            for (int j = 0; j < m; j++) {
//                for (int k = 0; k < n; k++) {
//                    if (T2[j][k] == 1) {
//                        result2 += Q[j][k];
//                    }
//                }
//            }
            //condensed conflict servers
//            Set<Integer> con = new HashSet<>();
//            for (int i = 0; i < conflictServers.size(); i++) {
//                for (int j = 0; j < conflictServers.get(i).size(); j++) {
//                    con.add(conflictServers.get(i).get(0));
//                    con.add(conflictServers.get(i).get(1));
//                }
//            }
//            double maxQ = 0;
//            int maxIndex = 0;
//            for(Integer value: con){
//                double sum = 0;
//                if (value < m1) {
//                    for (int j = 0; j < n1; j++) {
//                        sum += Q[value][j];
//                    }
//                    sum = sum / n1;
//                }
//                else {
//                    for (int j = n1; j < n; j++) {
//                        sum += Q[value][j];
//                    }
//                    sum = sum / (n - n1);
//                }
//                if (sum > maxQ) {
//                    maxQ = sum;
//                    maxIndex = value;
//                }
//            }
//            con.remove(maxIndex);
//            int newm = m - con.size();
//            int newm1 = 0;
//            for (int i = 0; i < m; i++) {
//                if (!con.contains(i) && TV[i] < 0.5) {
//                    ++newm1;
//                }
//            }
//            double[][] newQ = new double[newm][n];
//            int[] newLa = new int[newm];
//            int[] newSc = new int[newm];
//            double[] newP = new double[newm];
//            int num = 0;
//            for (int i = 0; i < m; i++) {
//                if (!con.contains(i)) {
//                    newLa[num] = LA[i];
//                    newSc[num] = SC[i];
//                    newP[num] = P[i];
//                    for (int j = 0; j < n; j++) {
//                        newQ[num][j] = Q[i][j];
//                    }
//                    ++num;
//                }
//            }
//            double sum = 0;
//            double[] QQ = new double[newm * n];
//            for (int i = 0; i < newm * n; i++) {
//                QQ[i] = newQ[i / n][i % n];
//            }
//            runTime = System.nanoTime();
//            double res = ILOG.condensed(newm, newm1, QQ, newLa, newSc, newP, T);
//            finishTime = System.nanoTime();
//            System.out.println(res);
//            sum = res;
//            time2[times] = (double) (finishTime - runTime) / 1000000;
            //Genetic algorithm
//            GA ga = new GA(100, m, 500, 0.7f, 0.7f, n, m1, n1, Q, DQ, SC, B, P, serverProviders, conflitLists, T, result, L, LA);
//            runTime = System.nanoTime();
//            ga.init();
//            ga.solve();
//            finishTime = System.nanoTime();
//            System.out.println((double) (finishTime - runTime) / 1000000);
            //greedy
//            int[] ma = new int[m];
//            int[] msc = new int[m];
//            boolean flag = true;
//            Set<Integer> set = new HashSet<>();
//            for (int j = 0; j < n1; j++) {
//                double max = 0;
//                int index = -1;
//                for (int i = 0; i < m1; i++) {
//                    if ((SC[i] - msc[i]) >= DQ[j] && P[i] <= B[j] && ma[i] < LA[i] && (!set.contains(i)) && Q[i][j] > max) {
//                        max = Q[i][j];
//                        index = i;
//                        for (int k = 0; k < m; k++) {
//                            if (AC[i][k] == 1) {
//                                set.add(k);
//                            }
//                        }
//                    }
//                }
//                if (max == 0) {
//                    flag = false;
//                    ++infeasibleM1;
//                    sum = 0;
//                    System.out.println("无解");
//                    break;
//                }
//                sum += max;
//                ++ma[index];
//                msc[index] += DQ[j];
//            }
//            if (flag) {
//                for (int j = n1; j < n; j++) {
//                    double max = 0;
//                    int index = -1;
//                    for (int i = m1; i < m; i++) {
//                        if ((SC[i] - msc[i]) >= DQ[j] && P[i] <= B[j] && ma[i] < LA[i] && (!set.contains(i)) && Q[i][j] > max) {
//                            max = Q[i][j];
//                            index = i;
//                            for (int k = 0; k < m; k++) {
//                                if (AC[i][k] == 1) {
//                                    set.add(k);
//                                }
//                            }
//                        }
//                    }
//                    if (max == 0) {
//                        System.out.println("无解");
//                        break;
//                    }
//                    sum += max;
//                    ++ma[index];
//                    msc[index] += DQ[j];
//                }
//            }
//            System.out.println(sum);
            //new greedy
//            List<Integer> list = new ArrayList<>();
//            runTime = System.nanoTime();
//            for (int k = 0; k < n1; k++) {
//                double max = 0;
//                int index = -1;
//                int index1 = -1;
//                for (int j = 0; j < n1; j++) {
//                    if (!list.contains(j)) {
//                        for (int i = 0; i < m1; i++) {
//                            if ((SC[i] - msc[i]) >= DQ[j] && P[i] <= B[j] && ma[i] < LA[i] && (!set.contains(i)) && Q[i][j] > max) {
//                                max = Q[i][j];
//                                index = i;
//                                index1 = j;
//                            }
//                        }
//                    }
//                }
//                if (max == 0) {
//                    flag = false;
//                    ++infeasibleM1;
//                    sum = 0;
//                    System.out.println("无解");
//                    break;
//                }
//                sum += max;
//                ++ma[index];
//                msc[index] += DQ[index1];
//                list.add(index1);
//                for (int l = 0; l < m; l++) {
//                    if (AC[index][l] == 1) {
//                        set.add(l);
//                    }
//                }
//            }
//            if (flag) {
//                for (int k = n1; k < n; k++) {
//                    double max = 0;
//                    int index = -1;
//                    int index1 = -1;
//                    for (int j = n1; j < n; j++) {
//                        if (!list.contains(j)) {
//                            for (int i = m1; i < m; i++) {
//                                if ((SC[i] - msc[i]) >= DQ[j] && P[i] <= B[j] && ma[i] < LA[i] && (!set.contains(i)) && Q[i][j] > max) {
//                                    max = Q[i][j];
//                                    index = i;
//                                    index1 = j;
//                                }
//                            }
//                        }
//                    }
//                    if (max == 0) {
//                        ++infeasibleM1;
//                        sum = 0;
//                        System.out.println("无解");
//                        break;
//                    }
//                    sum += max;
//                    ++ma[index];
//                    msc[index] += DQ[index1];
//                    list.add(index1);
//                    for (int l = 0; l < m; l++) {
//                        if (AC[index][l] == 1) {
//                            set.add(l);
//                        }
//                    }
//                }
//            }
//            finishTime = System.nanoTime();
//            time2[times] = (double) (finishTime - runTime) / 1000000;
//            System.out.println(sum);
            //method2
//            int[][] T1 = new int[m][n];
//            int[][] T2 = new int[m][n];
//            runTime = System.nanoTime();
//            ILOG.resolve(T1);
//            List<Integer> server1 = new ArrayList<>();
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T1[i][j] == 1) {
//                        server1.add(i);
//                        break;
//                    }
//                }
//            }
//            boolean flag = false;
//            for (int i = 0; i < conList.size(); i++) {
//                int x = conList.get(i).get(0);
//                int y = conList.get(i).get(1);
//                if (server1.contains(x) && server1.contains(y)) {
//                    flag = true;
//                    break;
//                }
//            }
//            if (flag) {
//                ILOG.solution(T2, serverProviders, conflitLists);
//            }
//            finishTime = System.nanoTime();
//            time2[times] = (double) (finishTime - runTime) / 1000000;
//            //method3
//            conList.clear();
//            for (int i = 0; i < m; i++) {
//                for (int j = i + 1; j < m; j++) {
//                    if (AC[i][j] == 1) {
//                        List<Integer> temp = new ArrayList<>();
//                        temp.add(i);
//                        temp.add(j);
//                        conList.add(temp);
//                    }
//                }
//            }
//            int[][] T3 = new int[m][n];
//            runTime = System.nanoTime();
//            double result3 = 0;
//            ILOG.resolve(T3);
//            List<Integer> reDistribute = new ArrayList<>();
//            List<Integer> server1 = new ArrayList<>();
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T3[i][j] == 1) {
//                        server1.add(i);
//                        break;
//                    }
//                }
//            }
//            boolean flag = false;
//            for (int i = 0; i < conList.size(); i++) {
//                int x = conList.get(i).get(0);
//                int y = conList.get(i).get(1);
//                if (server1.contains(x) && server1.contains(y)) {
//                    flag = true;
//                    if (!reDistribute.contains(x)) {
//                        reDistribute.add(x);
//                    }
//                    if (!reDistribute.contains(y)) {
//                        reDistribute.add(y);
//                    }
//                }
//            }
//            if (flag) {
//                Collections.sort(reDistribute);
//                List<Integer> fields = new ArrayList<>();
//                for (int i = 0; i < reDistribute.size(); i++) {
//                    int s = reDistribute.get(i);
//                    for (int j = 0; j < n; j++) {
//                        if (T3[s][j] == 1 && !fields.contains(j)) {
//                            fields.add(j);
//                        }
//                    }
//                }
//                Collections.sort(fields);
//                for (int i = 0; i < reDistribute.size(); i++) {
//                    for (int j = 0; j < fields.size(); j++) {
//                        T3[reDistribute.get(i)][fields.get(j)] = 0;
//                    }
//                }
//                ILOG.resolve1(T3, reDistribute, fields, conList);
//            }
//            finishTime = System.nanoTime();
//            time3[times] = (double) (finishTime - runTime) / 1000000;
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T3[i][j] == 1) {
//                        result3 += Q[i][j];
//                    }
//                }
//            }
//            System.out.println(result3);
//            //method4
//            List<List<Integer>> combo = new ArrayList<>();
//            List<Integer> set = new ArrayList<>();
//            int[][] T4 = new int[m][n];
//            HashMap<Integer, List<Integer>> hashMap = new HashMap<>();
//            for (int i = 0; i < conflitLists.size(); i++) {
//                int x = conflitLists.get(i).get(0);
//                int y = conflitLists.get(i).get(1);
//                List<Integer> list = new ArrayList<>();
//                if (!hashMap.containsKey(x)) {
//                    list.add(x);
//                    list.add(y);
//                    for (int j = i + 1; j < conflitLists.size(); j++) {
//                        if (conflitLists.get(j).get(0) == x) {
//                            list.add(conflitLists.get(j).get(1));
//                        } else if (conflitLists.get(j).get(1) == x) {
//                            list.add(conflitLists.get(j).get(0));
//                        }
//                    }
//                    hashMap.put(x, list);
//                }
//                list = new ArrayList<>();
//                if (!hashMap.containsKey(y)) {
//                    list.add(y);
//                    list.add(x);
//                    for (int j = i + 1; j < conflitLists.size(); j++) {
//                        if (conflitLists.get(j).get(0) == y) {
//                            list.add(conflitLists.get(j).get(1));
//                        } else if (conflitLists.get(j).get(1) == y) {
//                            list.add(conflitLists.get(j).get(0));
//                        }
//                    }
//                    hashMap.put(y, list);
//                }
//            }
//            runTime = System.nanoTime();
////            root1 = createTree()
//            int level = 0;
//            List<List<Integer>> record = new ArrayList<>();
//            search(level, conflitLists, set, combo, record, hashMap);
//            List<List<Integer>> newCombo = new ArrayList<>();
//            for (int i = 0; i < combo.size(); i++) {
//                boolean isContains = newCombo.contains(combo.get(i));
//                if (!isContains) {
//                    newCombo.add(combo.get(i));
//                }
//            }
//            combo.clear();
//            combo.addAll(newCombo);
////            for (int i = 0; i < combo.size(); i++) {
////                List<Integer> list = new ArrayList<>(combo.get(i));
////                HashSet<Integer> hashSet = new HashSet<>(list);
////                if (list.size() != hashSet.size()) {
////                    ArrayList<Integer> listWithoutDuplicates = new ArrayList<>(hashSet);
////                    combo.set(i, listWithoutDuplicates);
////                    list = new ArrayList<>(combo.get(i));
////                }
////                for (int j = 0; j < conflitLists.size(); j++) {
////                    if (list.contains(conflitLists.get(j).get(0)) && list.contains(conflitLists.get(j).get(1))) {
////                        int x = list.indexOf(conflitLists.get(j).get(0));
////                        int y = list.indexOf(conflitLists.get(j).get(1));
////                        list.remove(y);
////                        combo.get(i).remove(x);
////                        combo.add(list);
////                        --i;
////                        break;
////                    }
////                }
////            }
//            if (combo.size() == 0) {
//                for (int i = 0; i < conflitProviders.size(); i++) {
//                    combo.add(new ArrayList<>(Arrays.asList(conflitProviders.get(i))));
//                }
//            }
//            double[] maxRes = new double[combo.size()];
//            for (int i = 0; i < combo.size(); i++) {
//                double[][] qualification = Q;
//                for (int j = 0; j < conflitProviders.size(); j++) {
//                    int providerNum = conflitProviders.get(j);
//                    if (!combo.get(i).contains(providerNum)) {
//                        List<Integer> ser = serverProviders.get(providerNum);
//                        for (int k = 0; k < ser.size(); k++) {
//                            for (int l = 0; l < n; l++) {
//                                qualification[ser.get(k)][l] = 0;
//                            }
//                        }
//                    }
//                }
//                maxRes[i] = ILOG.resolve2(qualification, T4);
//            }
//            Arrays.sort(maxRes);
//            finishTime = System.nanoTime();
//            time4[times] = (double) (finishTime - runTime) / 1000000;
//            double result4 = maxRes[maxRes.length - 1];


//            long t11 = System.nanoTime();
//            for (int i = 0; i < combo.size(); i++) {
//                double[][] qualification = Q;
//                for (int j = 0; j < conflitProviders.size(); j++) {
//                    int providerNum = conflitProviders.get(j);
//                    if (!combo.get(i).contains(providerNum)) {
//                        List<Integer> ser = serverProviders.get(providerNum);
//                        for (int k = 0; k < ser.size(); k++) {
//                            for (int l = 0; l < n; l++) {
//                                qualification[ser.get(k)][l] = 0;
//                            }
//                        }
//                    }
//                }
//                maxRes[i] = ILOG.resolve2(qualification, T1);
//            }
//            Arrays.sort(maxRes);
//            long t12 = System.nanoTime();
//            double diff1 = (double) (t12 - t11) / 1000000;
//            double result = maxRes[maxRes.length - 1];
//            long tt1 = System.nanoTime();
//            ILOG.resolve(T);
//            boolean flag = false;
//            if (flag) {
//                ILOG.solution(T);
//            }
//            else {
//                System.out.println(times);
//            }
//            ILOG.compare(T3);
//            ILOG.solution(T);
//            ILOG.base(T4);
//        printIMatrix(T1, m1, n1);
//        printIMatrix(T2, m - m1, n - n1);
//            ILOG.resolve(T3);
//            for (int i = 0; i < m; i++) {
//                if (!server1.contains(i)) {
//                    reDistribute.add(i);
//                }
//            }
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < m; j++) {
//                    if (AC[i][j] == 1) {
//                        if (server1.contains(i) && server1.contains(j)) {
//                            if (!reDistribute.contains(i)) {
//                                reDistribute.add(i);
//                            }
//                            if (!reDistribute.contains(j)) {
//                                reDistribute.add(j);
//                            }
//                            ++conflict1;
////                            System.out.println("服务器冲突" + i + "和" + j);
////                            System.out.println(server1.toString());
//                        }
//                        AC[i][j] = 0;
//                        AC[j][i] = 0;
//                    }
//                }
//            }
//            Collections.sort(reDistribute);
//            List<Integer> fields = new ArrayList<>();
//            for (int i = 0; i < reDistribute.size(); i++) {
//                int s = reDistribute.get(i);
//                for (int j = 0; j < n; j++) {
//                    if (T[s][j] == 1 && !fields.contains(j)) {
//                        fields.add(j);
//                    }
//                }
//            }
//            Collections.sort(fields);
//            for (int i = 0; i < reDistribute.size(); i++) {
//                for (int j = 0; j < fields.size(); j++) {
//                    T[reDistribute.get(i)][fields.get(j)] = 0;
//                }
//            }
//            double resCompare1=0;
////            double resCompare1 = ILOG.resolve1(T, reDistribute, fields);
//            long tt2 = System.nanoTime();
//            dif += (double) (tt2 - tt1) / 1000000;
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T[i][j] == 1) {
//                        resCompare1 += Q[i][j];
//                    }
//                }
//            }
//            long t12 = System.nanoTime();
//            double diff1 = (double) (t12 - t11) / 1000000;
//            time[times] = diff1;
//            long time1 = System.nanoTime();
//            double resBase = ILOG.solution(T3);
//            long time2 = System.nanoTime();
//            diff += (double) (time2 - time1) / 1000000;
//            double res3 = ILOG.base(T4);
//            System.out.println(t12);
//            System.out.println(diff1);
//            for (int i = 0; i < m1; i++) {
//                for (int j = 0; j < n1; j++) {
//                    T[i][j] = T1[i][j];
//                }
//            }
//            for (int i = m1; i < m; i++) {
//                for (int j = n1; j < n; j++) {
//                    T[i][j] = T2[i - m1][j - n1];
//                }
//            }
//            printIMatrix(T, m, n);
            double cost1 = 0;
            double cost2 = 0;
            double cost3 = 0;
            for (int i = 0; i < m; i++) {
                for (int j = 0; j < n; j++) {
                    if (T[i][j] == 1) {
                        cost1 += P[i];
                        break;
                    }
                }
            }
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T1[i][j] == 1) {
//                        cost2 += P[i];
//                        break;
//                    }
//                }
//            }
//            for (int i = 0; i < m; i++) {
//                for (int j = 0; j < n; j++) {
//                    if (T2[i][j] == 1) {
//                        cost3 += P[i];
//                        break;
//                    }
//                }
//            }
//            List<Integer> server2 = new ArrayList<>();
//            List<Integer> server3 = new ArrayList<>();

//            System.out.println("result" + times + ":" + result);
//            System.out.println("cost" + times + ":" + cost1);
//            System.out.println("Compare" + times + ":" + resCompare1);
//            System.out.println("cost" + times + ":" + cost2);
//            System.out.println("result" + times + ":" + (result - resCompare1) / resCompare1);
//            System.out.println("cost" + times + ":" + (cost2 - cost1) / cost2);
            firefox.add(times + 1, result);
//            chrome.add(times + 1, result1);
//            if (sum != 0) {
//                ta += (result - sum) / result;
//            }
//            ie.add(times + 1, result2);
//            r3.add(times +1, result2);
//            firefox1.add(times + 1, cost1);
//            chrome1.add(times + 1, cost2);
//            ie1.add(times + 1, cost3);
            if (result == 0.0 || result1 == 0.0) {
            if (result == 0.0) {
                ++infeasibleM1;
            }
            if (result1 == 0.0) {
                ++infeasibleM2;
            }
//            if (result2 == 0.0) {
//                ++infeasibleM3;
//            }
//                if (resCompare1 == 0.0) {
//                    ++infeasible;
//                }
            }
            else {
                ta += (result - result1) / result1;
                ca += (cost2 - cost1) / cost1;
//                ta1 += (result - result2) / result2;
                ca1 += (cost3 - cost1) / cost1;
            }
        }
        Arrays.sort(time);
        Arrays.sort(time2);
        Arrays.sort(time3);
        Arrays.sort(time4);
        System.out.println("minimum time:" + time[0]);
        System.out.println("maxinum time:" + time[excute - 1]);
        System.out.println("minimum time2:" + time2[0]);
        System.out.println("maxinum time2:" + time2[excute - 1]);
        System.out.println("minimum time3:" + time3[0]);
        System.out.println("maxinum time3:" + time3[excute - 1]);
        System.out.println("minimum time4:" + time4[0]);
        System.out.println("maxinum time4:" + time4[excute - 1]);
        double average = 0;
        for (int i = 0; i < time.length; i++) {
            average += time[i];
        }
        System.out.println("average time:" + average / excute);
        average = 0;
        for (int i = 0; i < time2.length; i++) {
            average += time2[i];
        }
        System.out.println("average time2:" + average / excute);
        average = 0;
        for (int i = 0; i < time3.length; i++) {
            average += time3[i];
        }
        System.out.println("average time3:" + average / excute);
        average = 0;
        for (int i = 0; i < time4.length; i++) {
            average += time4[i];
        }
        System.out.println("average time4:" + average / excute);
        System.out.println("average1:" + diff / excute);
        System.out.println("ave:" + dif / excute);
        System.out.println("trust average:" + ta / (excute - infeasibleM1));
        System.out.println("cost average:" + ca / (excute - infeasibleM1));
        System.out.println("trust average1:" + ta1 / (excute - infeasible));
        System.out.println("cost average1:" + ca1 / (excute - infeasible));
        System.out.println("conflict1:" + conflict1);
//        System.out.println("conflict2:" + conflict2);
//        System.out.println("conflict3:" + conflict3);
//        System.out.println("infeasible:" + infeasible);
        System.out.println("M1 infeasible:" + infeasibleM1);
        System.out.println("M2 infeasible:" + infeasibleM2);
        System.out.println("M3 infeasible:" + infeasibleM3);
//        System.out.println("cost:"+ ca +','+ca1);
//        double PCre = 0;
//        double TCre = 0;
//        for (int i = 0; i < excute; i++) {
//            TCre += TCL[i];
//            PCre += PCL[i];
//        }
//        System.out.println("TC:"+ TCre / (excute - infeasibleM1));
//        System.out.println("PC:"+ PCre / (excute - infeasibleM1));
        XYSeriesCollection dataset = new XYSeriesCollection();
        dataset.addSeries(firefox);
        dataset.addSeries(chrome);
        dataset.addSeries(ie);
//        dataset.addSeries(r3);
//
//        XYSeriesCollection dataset1 = new XYSeriesCollection();
//        dataset1.addSeries(firefox1);
//        dataset1.addSeries(chrome1);
//        dataset1.addSeries(ie1);
//
        JFreeChart freeChart = ChartFactory.createScatterPlot(
                "Qualification value",// 图表标题
                "Number of experiments",//y轴方向数据标签
                "Qualification",//x轴方向数据标签
                dataset,//数据集，即要显示在图表上的数据
                PlotOrientation.VERTICAL,//设置方向
                true,//是否显示图例
                true,//是否显示提示
                false//是否生成URL连接
        );
//        JFreeChart freeChart1 = ChartFactory.createScatterPlot(
//                "Cost",// 图表标题
//                "Number of experiments",//y轴方向数据标签
//                "Cost",//x轴方向数据标签
//                dataset1,//数据集，即要显示在图表上的数据
//                PlotOrientation.VERTICAL,//设置方向
//                true,//是否显示图例
//                true,//是否显示提示
//                false//是否生成URL连接
//        );

        //使用输出流输出图表文件
        //输出JPG文件
        try {
            OutputStream os = null;
            os = new FileOutputStream("picture.jpg");
            ChartUtilities.writeChartAsJPEG(os, freeChart, 500, 500);
//            os = new FileOutputStream("picture1.jpg");
//            ChartUtilities.writeChartAsJPEG(os, freeChart1, 500, 500);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return;
    }
}

