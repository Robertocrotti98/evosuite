package org.evosuite.ga.metaheuristics.mosa.jbse;

import static org.evosuite.ga.metaheuristics.mosa.jbse.JBSERunnerUtil.bytecodeJump;
import static org.evosuite.ga.metaheuristics.mosa.jbse.JBSERunnerUtil.bytecodeLoadConstant;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

import org.evosuite.Properties;
import org.evosuite.classpath.ClassPathHandler;
import org.evosuite.coverage.branch.Branch;
import org.evosuite.ga.metaheuristics.mosa.structural.AidingPathConditionManager.ApcGroup;
import org.evosuite.junit.writer.TestSuiteWriter;
import org.evosuite.testcase.TestCase;
import org.evosuite.testcase.execution.ExecutionResult;
import org.evosuite.utils.LoggingUtils;

import jbse.algo.exc.CannotManageStateException;
import jbse.apps.run.DecisionProcedureGuidance;
import jbse.apps.run.DecisionProcedureGuidanceJDI;
import jbse.apps.run.GuidanceException;
import jbse.bc.exc.InvalidClassFileFactoryClassException;
import jbse.common.exc.ClasspathException;
import jbse.common.exc.InvalidInputException;
import jbse.dec.DecisionProcedureAlgorithms;
import jbse.dec.DecisionProcedureAlwSat;
import jbse.dec.DecisionProcedureClassInit;
import jbse.dec.exc.DecisionException;
import jbse.jvm.Runner;
import jbse.jvm.RunnerBuilder;
import jbse.jvm.RunnerParameters;
import jbse.jvm.EngineParameters.StateIdentificationMode;
import jbse.jvm.Runner.Actions;
import jbse.jvm.exc.CannotBacktrackException;
import jbse.jvm.exc.CannotBuildEngineException;
import jbse.jvm.exc.EngineStuckException;
import jbse.jvm.exc.FailureException;
import jbse.jvm.exc.InitializationException;
import jbse.jvm.exc.NonexistingObservedVariablesException;
import jbse.mem.Clause;
import jbse.mem.Objekt;
import jbse.mem.State;
import jbse.mem.State.Phase;
import jbse.mem.exc.ContradictionException;
import jbse.mem.exc.FrozenStateException;
import jbse.mem.exc.InvalidNumberOfOperandsException;
import jbse.mem.exc.ThreadStackEmptyException;
import jbse.rewr.CalculatorRewriting;
import jbse.rewr.RewriterExpressionOrConversionOnSimplex;
import jbse.rules.ClassInitRulesRepo;
import jbse.tree.StateTree.BranchPoint;
import jbse.val.Reference;
import jbse.val.ReferenceSymbolic;
import jbse.val.ReferenceConcrete;
import jbse.val.Value;


public class JBSERunner {
	public static void run(ApcGroup hostApcGroup, Branch branch, TestCase tc, MethodData entryMethodData, int entryMethodOccurrences, int targetBranchOccurrences, int uniqueSuffix, String evaluatorDependencySpec) {
		LoggingUtils.getEvoLogger().info("[JBSE] TRACKING BRANCH: " + branch 
				+ " - FROM METHOD " + entryMethodData + " - GUIDED FROM TEST ");
		LoggingUtils.getEvoLogger().info(tc.toString());		

		//write and compile the guiding test case for JBSE
		String testFileName = emitAndCompileGuidingTestCase(tc, branch.getActualBranchId());
		if (testFileName == null) {
			return;
		}

		LoggingUtils.getEvoLogger().info("[JBSE] ASKING RELOCATION FOR BRANCH {}, INSTR {}", branch, branch.getInstruction());
		int bytecodeOffset = JBSEBytecodeRelocationRegistry._I().getRelocatedOffset(branch.getInstruction());

		//call JBSE as external process
		/*new Thread() {
			@Override
			public void run() {*/
				try {
					
					String retValue = null;
					/*retValue = run0(branch.getClassName(), branch.getMethodName(), bytecodeOffset, targetBranchOccurrences, entryMethodData.getClassNameSlashed(),
							entryMethodData.getMethodName(), entryMethodData.getMethodDescriptor(), entryMethodOccurrences, Properties.TMP_TEST_DIR,		
							ClassPathHandler.getInstance().getTargetProjectClasspath(), testFileName, branch.getActualBranchId(), uniqueSuffix, evaluatorDependencySpec);
					*/

					//======= BEGIN: EXT PROCESS EXECUTION =====
					LoggingUtils.getEvoLogger().info("[JBSE] Launching external JVM: {}", System.getProperties().getProperty("java.home") + File.separator + "bin" + File.separator + "java");
					String[] commandLine = new String[] {
							System.getProperties().getProperty("java.home") + File.separator + "bin" + File.separator + "java", //java1.8
							
					"-classpath", extractClassPathEntry(org.evosuite.ClientProcess.class) + //evosuite-client/target/classes/
					File.pathSeparator + ClassPathHandler.getInstance().getTargetProjectClasspath() + 
					//":/Users/denaro/git/evosuite/sushi-lib/lib/javaparser-core-3.4.0.jar" + //needed for using java-parser on test cases
					File.pathSeparator + extractClassPathEntry(compiler.getClass()) + //tools.jar, needed for calling javac 
					File.pathSeparator + extractClassPathEntry(javassist.bytecode.ClassFile.class) + //javassist-3.22.0-GA.jar" + 
					//":/Users/denaro/.m2/repository/org/slf4j/slf4j-api/1.7.22/slf4j-api-1.7.22.jar" + 
					//":/Users/denaro/.m2/repository/org/ow2/asm/asm-all/5.1/asm-all-5.1.jar" + 
					File.pathSeparator + extractClassPathEntry(org.evosuite.runtime.Runtime.class) + //evosuite-runtime/target/classes
					File.pathSeparator + extractClassPathEntry(jbse.jvm.RunnerBuilder.class) + //jbse.jar
					File.pathSeparator + extractClassPathEntry(sushi.compile.path_condition_distance.DistanceBySimilarityWithPathCondition.class) + //sushi-lib
					File.pathSeparator + Properties.TMP_TEST_DIR,

					"org.evosuite.ga.metaheuristics.mosa.jbse.JBSERunner",

					//TARGET BRANCH DATA				
					branch.getClassName(), 
					branch.getMethodName(),
					"" + bytecodeOffset, 
					"" + targetBranchOccurrences, 

					// ENTRY_METHOD_DATA
					entryMethodData.getClassNameSlashed(),
					entryMethodData.getMethodName(),
					entryMethodData.getMethodDescriptor(),
					"" + entryMethodOccurrences,

					Properties.TMP_TEST_DIR, //TEST_DIR	
					ClassPathHandler.getInstance().getTargetProjectClasspath(),//Target project bin path
					testFileName, //TEST_FILE_NAME
					"" + branch.getActualBranchId(), //APC_ID 
					"" + uniqueSuffix, //APC_ID_suffix
					evaluatorDependencySpec //EVALUATOR DEPENDENCY SPEC
					};
					
					//LoggingUtils.getEvoLogger().info("[JBSE] DEBUG: command line: {}", Arrays.toString(commandLine));

					Process process = Runtime.getRuntime().exec(commandLine, null, null);

					BufferedReader br = new BufferedReader(new InputStreamReader(process.getInputStream()));
					BufferedReader brErr = new BufferedReader(new InputStreamReader(process.getErrorStream()));
					String line;
					while ((line = br.readLine()) != null) {
						LoggingUtils.getEvoLogger().info("[JBSE EXT PROCESS] " + line);
						if(line.startsWith("SUCCESS:")) {
							retValue = line.substring(8);
						}
					}
					while ((line = brErr.readLine()) != null) {
						LoggingUtils.getEvoLogger().info(line);
					}
					//======= END: EXT PROCESS EXECUTION =====
					
					
					if (retValue == null) {
						LoggingUtils.getEvoLogger().info("[JBSE] * WARNING: JBSE FAILED TO COMPUTE THE REFINED APC WITH SPEC {}: TARGET BRANCH NOT FOUND", evaluatorDependencySpec);
					} else {
						String entryClassName = branch.getClassName();
						String entryMethodName = entryMethodData.getMethodName() + entryMethodData.getMethodDescriptor();
						int apcIndex = uniqueSuffix;
						String evaluatorName = retValue;
						hostApcGroup.scheduleNewApcFromJbse(apcIndex, entryClassName, entryMethodName, evaluatorName, false, 0/*currentIteration*/);

					}

				} catch (Exception e) {
					e.printStackTrace();
					LoggingUtils.getEvoLogger().info(e.getMessage() + ": " + Arrays.toString(e.getStackTrace()));
				}
			/*}
		}.start();*///TODO: Run in separate thread
	}


	private static String extractClassPathEntry(Class<?> clazz) {
		URL url = clazz.getResource(clazz.getSimpleName() + ".class");
		if (url == null) throw new RuntimeException("cannot find class resource for class" + clazz.getSimpleName() + ".class");
		
		URI uri = null;
		try {
			uri = url.toURI();
		} catch (URISyntaxException e) {
			throw new RuntimeException(e);
		}
	    final String suffix = clazz.getCanonicalName().replace('.', '/') + ".class";
	    if (!uri.toString().endsWith(suffix)) throw new RuntimeException("class resource for class" + clazz.getSimpleName() + ".class returned weird URI: " + uri);

	    // strip the class's path from the URL string
	    String path = uri.toString().substring(0, uri.toString().length() - suffix.length() - 1);
	    if (path.startsWith("jar:")) path = path.substring(path.indexOf(':') + 1, path.length() - 1);
	    try {
	        return new URI(path).getPath().replace("/C:", "C:");
	    } catch (final URISyntaxException e) {
			throw new RuntimeException(e);
	    } 
	}

	private static JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

	private static String TEST_DIR;
	private static String TARGET_BIN_PATH;
	private static String TARGET_BRANCH_CLASS;
	private static String TARGET_BRANCH_METHOD;
	private static int TARGET_BRANCH_BYTECODE_OFFSET;
	private static int TARGET_BRANCH_OCCURRENCES;
	private static MethodData ENTRY_METHOD_DATA;
	private static int ENTRY_METHOD_OCCURRENCES;
	private static GuidingTestCaseData GUIDING_TC_DATA;
	
	//private final String z3Path = Paths.get("/Users", "denaro", "Desktop", "RTools", "Z3", "z3-4.3.2.d548c51a984e-x64-osx-10.8.5", "bin", "z3").toString(); //Do not need Z3: we do only test-guided symbolic execution;
	private final RunnerParameters commonParamsGuided;
	private final RunnerParameters commonParamsGuiding;
	private State initialState = null;
	private State  finalState = null;
    private HashMap<Long, String> stringLiterals = null;
	private HashMap<Clause, String> clauseLocations;

	public static void main(String[] args) throws DecisionException, CannotBuildEngineException, InitializationException, InvalidClassFileFactoryClassException, 
	NonexistingObservedVariablesException, ClasspathException, CannotBacktrackException, CannotManageStateException, ThreadStackEmptyException, 
	ContradictionException, EngineStuckException, FailureException, InvalidInputException {
		System.out.println("ARGS: " + Arrays.toString(args));
		run0(args[0], args[1], Integer.parseInt(args[2]), Integer.parseInt(args[3]), args[4], 
				args[5], args[6], Integer.parseInt(args[7]), args[8], 
				args[9], args[10], Integer.parseInt(args[11]), Integer.parseInt(args[12]), args[13]);
	}
	
	private static String run0 (String BRANCH_CLASS, String BRANCH_METHOD, int BRANCH_BYTECODE_OFFSET, int BRANCH_OCCURRENCES, 
			String METHOD_DATA_CLASS, String METHOD_DATA_METHOD_NAME,String  METHOD_DATA_DESCR, int METHOD_OCCURRENCES, 
			String TEST_DIRECTORY, String TARGET_DIRECTORIES_AND_JARS, String TEST_FILE, int apcId, int apcIdSuffix, String evaluatorDependencySpec) throws DecisionException, CannotBuildEngineException, 
	InitializationException, InvalidClassFileFactoryClassException, NonexistingObservedVariablesException, ClasspathException, CannotBacktrackException, 
	CannotManageStateException, ThreadStackEmptyException, ContradictionException, EngineStuckException, FailureException, InvalidInputException  {
		TARGET_BRANCH_CLASS = BRANCH_CLASS;
		TARGET_BRANCH_METHOD = BRANCH_METHOD;
		TARGET_BRANCH_BYTECODE_OFFSET = BRANCH_BYTECODE_OFFSET;
		TARGET_BRANCH_OCCURRENCES = BRANCH_OCCURRENCES;
		
		ENTRY_METHOD_DATA = new MethodData(METHOD_DATA_CLASS, METHOD_DATA_METHOD_NAME, METHOD_DATA_DESCR);
		ENTRY_METHOD_OCCURRENCES = METHOD_OCCURRENCES;
		
		TEST_DIR = TEST_DIRECTORY;
		TARGET_BIN_PATH = TARGET_DIRECTORIES_AND_JARS;
		String TEST_FILE_NAME = TEST_FILE;
		GUIDING_TC_DATA = new GuidingTestCaseData(
				TEST_FILE_NAME, "()V", "test0", 
				Paths.get(TEST_DIR));
		int APC_ID = apcId;
		int APC_ID_suffix = apcIdSuffix;

		final CalculatorRewriting calc = new CalculatorRewriting();
		calc.addRewriter(new RewriterExpressionOrConversionOnSimplex());

		JBSERunner runner = new JBSERunner(); 
		runner.runProgram(calc);	
		if (runner.finalState != null) {
			String evaluatorName = emitAndCompilePathConditionEvaluator(
					APC_ID, APC_ID_suffix, runner.initialState, runner.finalState, runner.clauseLocations, runner.stringLiterals, calc, evaluatorDependencySpec);
			String successString = "SUCCESS";
			successString += ":" + evaluatorName;
			System.out.println(successString);
			return evaluatorName;
		}
		System.out.println("DONE");
		return null;
	}
	
	public JBSERunner() {		
		String[] targerDirs = TARGET_BIN_PATH.split(File.pathSeparator);
		String[] classpath = Arrays.copyOf(targerDirs, targerDirs.length + 2);
		classpath[targerDirs.length] = TEST_DIR;
		classpath[targerDirs.length + 1] = extractClassPathEntry(jbse.jvm.RunnerBuilder.class);
		
		System.out.println("Using classpath: " + Arrays.toString(classpath));
		//LoggingUtils.getEvoLogger().info("Using classpath: " + Arrays.toString(classpath));
		
		//builds the template parameters object for the guided (symbolic) execution
		this.commonParamsGuided = new RunnerParameters();
		this.commonParamsGuided.addUserClasspath(classpath);
		this.commonParamsGuided.setCountScope(100000); // To avoid infinte loops

		//builds the template parameters object for the guiding (concrete) execution
		this.commonParamsGuiding = new RunnerParameters();
		this.commonParamsGuiding.addUserClasspath(classpath);
		this.commonParamsGuiding.setStateIdentificationMode(StateIdentificationMode.COMPACT);
	}

	
	/**
	 * Performs symbolic execution of the target method guided by a test case,
	 * and returns the final state. Equivalent to {@link #runProgram(int) runProgram}{@code (-1).}
	 * {@link List#get(int) get}{@code (0)}.
	 * @param branch 
	 * 
	 * @param testCase a {@link GuidingTestCaseData}, it will guide symbolic execution.
	 * @return the final {@link State}.
	 * @throws DecisionException
	 * @throws CannotBuildEngineException
	 * @throws InitializationException
	 * @throws InvalidClassFileFactoryClassException
	 * @throws NonexistingObservedVariablesException
	 * @throws ClasspathException
	 * @throws CannotBacktrackException
	 * @throws CannotManageStateException
	 * @throws ThreadStackEmptyException
	 * @throws ContradictionException
	 * @throws EngineStuckException
	 * @throws FailureException
	 * @throws InvalidInputException 
	 */
	public void runProgram(CalculatorRewriting calc)
			throws DecisionException, CannotBuildEngineException, InitializationException, 
			InvalidClassFileFactoryClassException, NonexistingObservedVariablesException, 
			ClasspathException, CannotBacktrackException, CannotManageStateException, 
			ThreadStackEmptyException, ContradictionException, EngineStuckException, 
			FailureException, InvalidInputException {

		//builds the parameters
		final RunnerParameters pGuided = this.commonParamsGuided.clone();
		final RunnerParameters pGuiding = this.commonParamsGuiding.clone();

		//sets the calculator
		pGuided.setCalculator(calc);
		pGuiding.setCalculator(calc);
		
		//sets the decision procedures
		final ClassInitRulesRepo initRules = new ClassInitRulesRepo();
		//initRules.addNotInitializedClassPattern(".*");
		pGuided.setDecisionProcedure(new DecisionProcedureAlgorithms(new DecisionProcedureClassInit(new DecisionProcedureAlwSat(calc), initRules)));
		/*pGuided.setDecisionProcedure(new DecisionProcedureAlgorithms(
				new DecisionProcedureClassInit( //useless?
						new DecisionProcedureLICS( //useless?
								new DecisionProcedureSMTLIB2_AUFNIRA(
										new DecisionProcedureAlwSat(), 
										calc, this.z3Path + COMMANDLINE_LAUNCH_Z3), 
								calc, new LICSRulesRepo()), 
						calc, new ClassInitRulesRepo()), calc));*/
		pGuiding.setDecisionProcedure(
				new DecisionProcedureAlgorithms(
						new DecisionProcedureClassInit(
								new DecisionProcedureAlwSat(calc), initRules))); //for concrete execution

		//sets the guiding method (to be executed concretely) and the entry method (symbolically)
		pGuiding.setMethodSignature(GUIDING_TC_DATA.getClassName(), GUIDING_TC_DATA.getMethodDescriptor(), GUIDING_TC_DATA.getMethodName());
		pGuided.setMethodSignature(ENTRY_METHOD_DATA.getClassNameSlashed(), ENTRY_METHOD_DATA.getMethodDescriptor(), ENTRY_METHOD_DATA.getMethodName());
		
		//creates the guidance decision procedure and sets it
		/*int numberOfHits = countNumberOfInvocations(GUIDING_TC_DATA.getSourcePath(), ENTRY_METHOD_DATA.getMethodName(), ENTRY_METHOD_DATA.getMethodDescriptor());
		System.out.println("Entry point method called " + numberOfHits + " times in test case; starting guidance until last call");
		if (numberOfHits == 0) {
			numberOfHits = 1; //the method is called indirectly from the test code, we arbitrarily assume it suffices to stop at the first occurrence 
		}*/
		
		final DecisionProcedureGuidanceJDI guid = new DecisionProcedureGuidanceJDI(pGuided.getDecisionProcedure(),
				pGuided.getCalculator(), pGuiding, pGuided.getMethodSignature(), ENTRY_METHOD_OCCURRENCES);
		pGuided.setDecisionProcedure(guid);
		System.out.println("Guidance test successfully started");

		/*SettingsReader rd = null;
		try {
			rd = new SettingsReader("/Users/denaro/Documents/workspace.luna/sushi-experiments-closure72/sushi/settings/closure_parse_tree_hex_minimal.jbse");
		} catch (IOException | ParseException e) {
			e.printStackTrace();
		}
		rd.fillRunnerParameters(pGuided);*/
		
		//sets the actions
		final ActionsRunner actions = new ActionsRunner(guid);
		pGuided.setActions(actions);

		/*((CalculatorRewriting) pGuided.getCalculator()).addRewriter(new RewriterPolynomials());
		((CalculatorRewriting) pGuided.getCalculator()).addRewriter(new RewriterSinCos());
		((CalculatorRewriting) pGuided.getCalculator()).addRewriter(new RewriterSqrt());
		((CalculatorRewriting) pGuided.getCalculator()).addRewriter(new RewriterAbsSum());*/

		// Uninterpreted functions   
		pGuided.addUninterpreted("java/lang/String", "(Ljava/lang/Object;)Z", "equals");
		pGuided.addUninterpreted("java/util/HashMap", "(Ljava/lang/Object;)Z", "containsKey");
		pGuided.addUninterpreted("java/util/HashSet", "(Ljava/lang/Object;)Z", "contains");
		pGuided.addUninterpreted("java/util/HashSet", "(Ljava/lang/Object;)Ljava/lang/Object;", "get");
		pGuided.addUninterpreted("java/util/ArrayList", "(I)Ljava/lang/Object;", "get");

		
		//builds the runner and runs it
		final RunnerBuilder rb = new RunnerBuilder();
		final Runner r = rb.build(pGuided);
		r.run();

		//outputs
		this.initialState = rb.getEngine().getInitialState();
		
		//finalizes
		rb.getEngine().close();
		this.stringLiterals = actions.stringLiterals;
		this.clauseLocations = actions.clauseInstr;
		this.finalState = actions.getFinalState();
		System.out.println("done");
	}
	
/*	private static class CountVisitor extends VoidVisitorAdapter<Object> {
		final String methodName;
		final int numArgs;
		int methodCallCounter = 0;
		final String methodDescriptor; //not used at the moment, we check only on num of params

		public CountVisitor(String methodName, String methodDescriptor) {
			this.methodName = methodName;
			this.methodDescriptor = methodDescriptor;
			
			int numArgs = 0;
			String[] parts = methodDescriptor.substring(1, methodDescriptor.indexOf(')')).split(";");
			for (String p : parts) {
				if (p.indexOf('L') >= 0) {
					p = p.substring(0, p.indexOf('L') + 1);
				}
				numArgs += p.length();
			}
			this.numArgs = numArgs;
		}

		@Override
		public void visit(MethodCallExpr n, Object arg) {
			super.visit(n, arg);
			if (n.getNameAsString().equals(this.methodName) && n.getArguments().size() == numArgs) {
				this.methodCallCounter++;
			}
		}
	}

	private int countNumberOfInvocations(Path sourcePath, String methodName, String methodDescriptor){
		// T ODO use the whole signature of the target method to avoid ambiguities (that's quite hard)
		final CountVisitor v = new CountVisitor(methodName, methodDescriptor);
		try {
			final FileInputStream in = new FileInputStream(sourcePath.toFile());
			v.visit(JavaParser.parse(in), null);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		return v.methodCallCounter;
	}
*/
	private static class ActionsRunner extends Actions {
		private State finalState = null;
		private boolean postInitial = false;
		private boolean atJump = false;
		private boolean atLoadConstant = false;
		private int loadConstantStackSize = 0;
        private final HashMap<Long, String> stringLiterals = new HashMap<>();
		private int targetBranchOccurrences = 0;
		private final DecisionProcedureGuidance guid;
		private HashMap<Clause, String> clauseInstr = new HashMap<>();
		private int pathConditionSizeStepPre = -1;
		private int programCounterStepPre = 0;
		private int stackSizeStepPre = 0;
		private ArrayList<Integer> context = new ArrayList<>();
		
		public ActionsRunner(DecisionProcedureGuidance guid) {
			this.guid = guid;
		}
		
		public jbse.mem.State  getFinalState() {
			return finalState;
		}
						
		@Override
		public boolean atInitial() {
			/*final State currentState = getEngine().getCurrentState();
			try {
				System.out.println(currentState);
				System.out.println(currentState.getIdentifier() + "[" + currentState.getSequenceNumber() + "] " + currentState.getCurrentMethodSignature() + " " + currentState.getPC());
			} catch (FrozenStateException | ThreadStackEmptyException e) {
				e.printStackTrace();
			}*/
			this.postInitial = true;
			return super.atInitial();
		}
		
		@Override
		public boolean atStepPre() {
			if (this.postInitial) {
				try {
					final State  currentState = getEngine().getCurrentState();
					//System.out.println(currentState.getIdentifier() + "[" + currentState.getSequenceNumber() + "] " + currentState.getCurrentMethodSignature() + " " + currentState.getPC());
				
		            int stackSize = currentState.getStackSize();
		            if (stackSize > stackSizeStepPre) {
		            	context.add(programCounterStepPre);
		            } else if (stackSize < stackSizeStepPre) {
		            	if (!context.isEmpty()) {
		            		context.remove(context.size() - 1);
		            	}
		            }
	            	stackSizeStepPre = stackSize;
					pathConditionSizeStepPre = currentState.getPathCondition().size();
					programCounterStepPre = currentState.getCurrentProgramCounter();
							
                    //if at a load constant bytecode, saves the stack size
                    this.atLoadConstant = bytecodeLoadConstant(currentState.getInstruction());
                    if (this.atLoadConstant) {
                        this.loadConstantStackSize = currentState.getStackSize();
                    }

					
					String searchedSig = TARGET_BRANCH_CLASS.replace('.', '/') + ":" +
							TARGET_BRANCH_METHOD;
					String currentSig = currentState.getCurrentMethodSignature().getClassName() + ":" +
							currentState.getCurrentMethodSignature().getName() + 
							currentState.getCurrentMethodSignature().getDescriptor();
					//System.out.println(currentState.getCurrentProgramCounter() + ": " + currentState.getCurrentMethodSignature());						
					if (!currentSig.equals(searchedSig)) {
						if (currentSig.contains(TARGET_BRANCH_METHOD)) {
							System.out.println("DIFFERENT? " + currentSig);	
						}
						return super.atStepPre();
					}
					//System.out.println(currentState.getCurrentProgramCounter() + ": " + currentState.getCurrentMethodSignature());						
					this.atJump = bytecodeJump(currentState.getInstruction());
					if (this.atJump) {
						//System.out.println(currentState.getPC() + ": Jump instr in target method");						
						this.atJump = currentState.getCurrentProgramCounter() >= TARGET_BRANCH_BYTECODE_OFFSET - 3 && currentState.getCurrentProgramCounter() <= TARGET_BRANCH_BYTECODE_OFFSET + 3; //TODO: identify precise bytecode offset
						if (this.atJump) {
							targetBranchOccurrences++;
						}
						this.atJump = targetBranchOccurrences == TARGET_BRANCH_OCCURRENCES;
						/*if (this.atJump) {
							System.out.println("FOUND: " + currentState.getCurrentMethodSignature());
						}*/
					}
				} catch (ThreadStackEmptyException | FrozenStateException e) {
					//this should never happen
					throw new RuntimeException(e); //TODO better exception!
				}
			}
			return super.atStepPre();
		}
		
		private int atBranchCount = 0;
		@Override
		public boolean atBranch(BranchPoint bp) {
			final State currentState = getEngine().getCurrentState();
			++atBranchCount;
			return super.atBranch(bp);
		}
		
		@Override
		public boolean atStepPost() {
			final State currentState = getEngine().getCurrentState();
            //steps guidance

            if (this.postInitial && this.atJump) {
				this.finalState = currentState.clone();				
				getEngine().stopCurrentPath();
				return true;
			} 
            
            if (!currentState.isStuck()) {
				try {
					//System.out.println(currentState.getSequenceNumber());
					this.guid.postStep(currentState);
				} catch (GuidanceException e) {
					throw new RuntimeException(e); //TODO better exception!
				}
				//if (currentState.getStackSize() > 1000) getEngine().stopCurrentTrace(); //TODO
			}
            
            int pcSize = currentState.getPathCondition().size();
            if (pathConditionSizeStepPre >= 0 &&  pcSize > pathConditionSizeStepPre) {
            	for (int i = pathConditionSizeStepPre; i < pcSize; ++i) {
            		Clause clause = currentState.getPathCondition().get(i);
            		clauseInstr.put(clause, context.toString() + programCounterStepPre);
            	}
            	pathConditionSizeStepPre = -1;
            }
            
            //manages constant loading
			if (currentState.phase() != Phase.PRE_INITIAL && this.atLoadConstant) {
				try {
					if (this.loadConstantStackSize == currentState.getStackSize()) {
						Value operand = currentState.getCurrentFrame().operands(1)[0];
						if (operand instanceof Reference) {
							final Reference r = (Reference) operand;
							final Objekt o = currentState.getObject(r);
							if (o != null && "java/lang/String".equals(o.getType().getClassName())) {
								final String s = jbse.algo.Util.valueString(currentState, r);
								final long heapPosition = (r instanceof ReferenceConcrete ? ((ReferenceConcrete) r).getHeapPosition() : currentState.getResolution((ReferenceSymbolic) r));
								this.stringLiterals.put(heapPosition, s);
							}
						}					
					}
				} catch (FrozenStateException | InvalidNumberOfOperandsException | ThreadStackEmptyException e) {
					throw new RuntimeException(e); //TODO better exception!
				} 
			}

			return super.atStepPost();
		}
		
		@Override
		public boolean atPathEnd() {
			if (!this.atJump) {
				System.out.println("WARNING: JBSE GOT TO END-OF-TRACE WITHOUT TRAVERSING THE TARGET BRANCH: POSSIBLE CAUSE IS THAT "
						+ "JDI GUIDANCE IS INCOMPLETE ON ARRAY-RANGE BRANCHES. THERE ARE " + (atBranchCount - 1) + " SPURIOUS BRANCHES IN THIS TRACE");
				this.finalState = getEngine().getCurrentState();
			} else if (atBranchCount > 1) {
				System.out.println("WARNING: THERE ARE " + (atBranchCount - 1) + " SPURIOUS BRANCHES IN THIS TRACE: POSSIBLE CAUSE IS THAT " + 
						"JDI GUIDANCE IS INCOMPLETE ON ARRAY-RANGE BRANCHES."); 
			}
			return true; //stop to the first trace anyway
		}

		@Override
		public void atEnd() {
			super.atEnd();
		}
	}

	
	private static String emitAndCompileGuidingTestCase(TestCase tc, int id) {		
		//write the source of the test case in the output directory
		String testClassName = "TemporaryTestForBranch_" + id + "_Test";
		TestSuiteWriter suiteWriter = new TestSuiteWriter();
		suiteWriter.insertTest(tc, "Reach frontier of (even though does not cover) coverage goal");
		List<?> testFiles = suiteWriter.writeTestSuite(testClassName, Properties.TMP_TEST_DIR, new ArrayList<ExecutionResult>());
		LoggingUtils.getEvoLogger().info("[JBSE] WRITTEN TEMPORARY TEST CASE FOR JBSE: " + testFiles.toString());	
		
		//compile the test case
		final Path javacLogFilePath = Paths.get(Properties.TMP_TEST_DIR).resolve("javac-log-test_" + id + ".txt");
		try (final OutputStream w = new BufferedOutputStream(Files.newOutputStream(javacLogFilePath))) {
			final String classpathCompilationTest = Properties.TMP_TEST_DIR + 
					File.pathSeparator + ClassPathHandler.getInstance().getTargetProjectClasspath().replace("\\", "/") +
					File.pathSeparator + extractClassPathEntry(org.junit.Test.class) + //junit.jar"
					File.pathSeparator + extractClassPathEntry(org.evosuite.runtime.Runtime.class); //evosuite-runtime/target/classes;
			for (int i = 0; i < testFiles.size(); i++) {
				compiler.run(null, w, w, new String[] { "-cp", classpathCompilationTest, "-d", Properties.TMP_TEST_DIR, testFiles.get(i).toString() });
			}
		} catch (IOException e) {
			LoggingUtils.getEvoLogger().info("[JBSE] CANNOT GENERATE AIDING PATH CONDITION: Unexpected I/O error while creating log file " + javacLogFilePath + ": " + e);
			return null; //TODO throw an exception?
		}
		
		//extract the qualified name of the test class
		String testClass = testFiles.get(0).toString();
		testClass = testClass.substring(Properties.TMP_TEST_DIR.length() + 1, testClass.length() - 5).replace('/',  '.');
		
		//check the compiled code includes method test0
		/*try {
			final URLClassLoader cloader = URLClassLoader.newInstance(new URL[]{ Paths.get(Properties.TMP_TEST_DIR).toUri().toURL() }); 
			cloader.loadClass(testClass).getDeclaredMethod("test0");
			LoggingUtils.getEvoLogger().info("[JBSE] COMPILED TEST CASE: " + testClass + ".class");		
		} catch (NoSuchMethodException | MalformedURLException | SecurityException | ClassNotFoundException e) { 
			//EvoSuite failed to generate a valid test case, thus we just ignore it 
			LoggingUtils.getEvoLogger().info("[JBSE] CANNOT GENERATE AIDING PATH CONDITION: Failed to generate a valid the test case " + testClass + ": exception is: " + e);
			return null; //TODO throw an exception
		}*/
		
		return testClass.replace('.', '/');
	}
	
	/**
	 * Emits the EvoSuite wrapper (file .java) for the path condition of some state.
	 * @param idSuffix 
	 * 
	 * @param testCount an {@code int}, the number used to identify the test.
	 * @param initialState a {@link State}; must be the initial state in the execution 
	 *        for which we want to generate the wrapper.
	 * @param finalState a {@link State}; must be the final state in the execution 
	 *        for which we want to generate the wrapper.
	 * @param clauseLocations 
	 * @param stringLiterals2 
	 * @param calc 
	 * @return a {@link Path}, the file path of the generated EvoSuite wrapper.
	 */
	private static String emitAndCompilePathConditionEvaluator(int id, int idSuffix, State initialState, jbse.mem.State finalState, HashMap<Clause, String> clauseLocations, HashMap<Long, String> stringLiterals, CalculatorRewriting calc, String evaluatorDependencySpec) {
		final String evaluatorName = "APCFitnessEvaluator_" + id;
		String packageString = ENTRY_METHOD_DATA.getClassNameDotted();
		int lastDotIndex = packageString.lastIndexOf('.');
		if (lastDotIndex > 0) {
			packageString = packageString.substring(0, lastDotIndex);
		} else {
			packageString = null; //default package
		}

		
		final StateFormatterAidingPathCondition fmt = new StateFormatterAidingPathCondition(id, packageString, () -> initialState, calc, stringLiterals);
		fmt.refineFormula(finalState);
		fmt.formatPrologue(idSuffix);
		fmt.formatState(finalState, clauseLocations, evaluatorDependencySpec);
		fmt.formatEpilogue();
		
		final Path evaluatorFolderPath = Paths.get(TEST_DIR).resolve(packageString.replace('.',  '/'));
		final Path evaluatorFilePath = evaluatorFolderPath.resolve(evaluatorName + "_" + idSuffix + ".java");
		try (final BufferedWriter w = Files.newBufferedWriter(evaluatorFilePath)) {
			String evaluatorJavaCode = fmt.emit();
			w.write(evaluatorJavaCode);
			//System.out.println(evaluatorJavaCode);
		} catch (IOException e) {
			System.out.println("[JBSE] Unexpected I/O error while creating fitness evaluator for path conditon " + evaluatorFilePath.toString() + ": " + e);
			return null;
			//TODO throw an exception
		}
		fmt.cleanup();
	
		//compile the evaluator
			
		final Path javacLogFilePath = Paths.get(TEST_DIR).resolve("javac-log-APCFitnessEvaluator_" + id + "_" + idSuffix + ".txt");
		try (final OutputStream w = new BufferedOutputStream(Files.newOutputStream(javacLogFilePath))) {
			final String classpathCompilationWrapper = System.getProperty("java.class.path").replace("\\", "/") +
					File.pathSeparator + extractClassPathEntry(sushi.compile.path_condition_distance.DistanceBySimilarityWithPathCondition.class); //sushi-lib
			final String[] javacParameters = { "-cp", classpathCompilationWrapper, "-d", TEST_DIR, evaluatorFilePath.toString() };
			compiler.run(null, w, w, javacParameters);
			w.flush();
			w.close();
			return packageString + "." + evaluatorName + "_" + idSuffix;
		} catch (IOException e) {
			System.out.println("[JBSE] Unexpected I/O error while creating evaluator compilation log file " + javacLogFilePath.toString() + ": " + e);
			return null;
			//TODO throw an exception
		}
	}

}
