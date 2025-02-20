/**
 * Copyright (C) 2010-2015 Gordon Fraser, Andrea Arcuri and EvoSuite
 * contributors
 *
 * This file is part of EvoSuite.
 *
 * EvoSuite is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser Public License as published by the
 * Free Software Foundation, either version 3.0 of the License, or (at your
 * option) any later version.
 *
 * EvoSuite is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser Public License for more details.
 *
 * You should have received a copy of the GNU Lesser Public License along
 * with EvoSuite. If not, see <http://www.gnu.org/licenses/>.
 */
/**
 *
 */
package org.evosuite.instrumentation.coverage;

import java.util.ListIterator;
import java.util.Set;

import org.evosuite.Properties;
import org.evosuite.Properties.Criterion;
import org.evosuite.graphs.GraphPool;
import org.evosuite.graphs.cfg.BytecodeInstruction;
import org.evosuite.graphs.cfg.RawControlFlowGraph;
import org.evosuite.testcase.execution.ExecutionTracer;
import org.evosuite.utils.ArrayUtil;
import org.evosuite.utils.LoggingUtils;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.InsnList;
import org.objectweb.asm.tree.InsnNode;
import org.objectweb.asm.tree.IntInsnNode;
import org.objectweb.asm.tree.LdcInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.VarInsnNode;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * <p>
 * BranchInstrumentation class.
 * </p>
 *
 * @author Copied from CFGMethodAdapter
 */
public class PathConditonInstrumentation implements MethodInstrumentation {  /*SUSHI: Path condition fitness*/

	/** Constant <code>logger</code> */
	protected static final Logger logger = LoggerFactory.getLogger(PathConditonInstrumentation.class);

    private static final String EXECUTION_TRACER = Type.getInternalName(ExecutionTracer.class);
    
	/*
	 * (non-Javadoc)
	 *
	 * @see
	 * org.evosuite.cfg.MethodInstrumentation#analyze(org.objectweb
	 * .asm.tree.MethodNode, org.jgrapht.Graph, java.lang.String,
	 * java.lang.String, int)
	 */
	/** {@inheritDoc} */
	@Override
	public void analyze(ClassLoader classLoader, MethodNode mn, String className,
			String methodName, int access) {
		RawControlFlowGraph completeCFG = GraphPool.getInstance(classLoader).getRawCFG(className, methodName);
	
		if (ArrayUtil.contains(Properties.CRITERION, Criterion.BRANCH_WITH_AIDING_PATH_CONDITIONS)) {
			if (!(className.startsWith(Properties.TARGET_CLASS))) {
				return;
			}
		}
		LoggingUtils.getEvoLogger().info("Instrumenting {}::{}", className, methodName);
		
		InsnList instrumentation = getInstrumentation(mn, className, methodName, access);
		if (instrumentation == null)
			throw new IllegalStateException("error instrumenting method " + className + "::" + methodName);

		// in this case we activate the instrumentation for checking post conditions at the exit of the method
		if (Properties.POST_CONDITION_CHECK) {
			instrumentExitPointsForPostconditions(instrumentation, mn, completeCFG); 
		}
		
		if (Properties.PATH_CONDITION_CHECK_AT_METHOD_EXIT) {
			/* TODO: PATH_CONDITION_CHECK_AT_METHOD_EXIT is now deprecated: we should use POST_CONDITION_CHECK 
			 * when this is needed. For now, we keep it for backward compatibility with SEEPEP */
			Set<BytecodeInstruction> exitPoints = completeCFG.determineExitPoints();
			for (BytecodeInstruction exitP: exitPoints) {
				mn.instructions.insertBefore(exitP.getASMNode(), cloneInstrumentation(instrumentation));					
			}
			//LoggingUtils.getEvoLogger().info("Instrumentation set to check path condition at method exit ");
		} else {
			final boolean isConstructor = methodName.startsWith("<init>");
			for (BytecodeInstruction v : completeCFG.vertexSet()) {
				final AbstractInsnNode node = v.getASMNode();
				if (isConstructor) {
					if ( node instanceof MethodInsnNode &&
						((MethodInsnNode) node).name.equals("<init>") &&
						((MethodInsnNode) node).owner.equals("java/lang/Object")) {
						mn.instructions.insertBefore(node.getNext(), instrumentation);				
						break;
					}
				} else if (mn.instructions.getFirst().equals(node)) {
					mn.instructions.insertBefore(node, instrumentation); /* this should be the default behavior */					
					break;
				}
			}
			mn.maxStack += 7;
		}
	}
	
	private void instrumentExitPointsForPostconditions(InsnList instrumentation, MethodNode mn, RawControlFlowGraph completeCFG) {
		char retType = mn.desc.charAt(mn.desc.indexOf(')') + 1);
		BytecodeInstruction instrumentedAllExitingExceptionThrow = null;
		for (BytecodeInstruction exitP : completeCFG.vertexSet()) {
			if (exitP.canBeExitPoint()) {
				InsnList instrumentationPostCond = cloneInstrumentation(instrumentation, instrumentation.size() - 1);
				InsnList instr = new InsnList();
				if (exitP.isThrow()) {
					instrumentedAllExitingExceptionThrow = exitP; // postpone instrumentation (see below)
					continue;
				} else if (retType == 'V') {
					instr.add(new InsnNode(Opcodes.ACONST_NULL)); // instrument with null return value
				} else {
					if (retType == 'J' || retType == 'D') {
						instr.insert(new InsnNode(Opcodes.DUP2));						
					} else {
						instr.insert(new InsnNode(Opcodes.DUP));
					}
					addBoxingForPrimitiveValueIfNeeded(instr, retType); // instrument with (possibly boxed) return value
				}
				instrumentationPostCond.insert(instr);
				instrumentationPostCond.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
						EXECUTION_TRACER, "passedMethodExit", "(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;[Ljava/lang/Object;)V", false));
				mn.instructions.insertBefore(exitP.getASMNode(), instrumentationPostCond);					
			}
		}
		if (instrumentedAllExitingExceptionThrow != null) { 
			InsnList instrumentationPostCond = cloneInstrumentation(instrumentation, instrumentation.size() - 1);
			InsnList instr = new InsnList();
			instr.insert(new InsnNode(Opcodes.DUP)); //instrument with the exception as return value					
			instrumentationPostCond.insert(instr);
			instrumentationPostCond.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
					EXECUTION_TRACER, "passedMethodExit", "(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;[Ljava/lang/Object;)V", false));
			mn.instructions.insertBefore(instrumentedAllExitingExceptionThrow.getASMNode(), instrumentationPostCond);					
		}
	}

	private InsnList cloneInstrumentation(InsnList instrumentation) {
		return cloneInstrumentation(instrumentation, instrumentation.size());
	}

	private InsnList cloneInstrumentation(InsnList instrumentation, int lengthToCopy) {
		InsnList clone = new InsnList();
		ListIterator<AbstractInsnNode> it = instrumentation.iterator();
		for (int i = 0; i < lengthToCopy && it.hasNext(); i++) {
			clone.add(it.next().clone(null)); //passing null as clonedLabels should be fine for the type of nodes in our instrumentation
		}
		return clone;
	}

	/**
	 * <p>
	 * getInstrumentation
	 * </p>
	 *
	 * @param instruction
	 *            a {@link org.evosuite.graphs.cfg.BytecodeInstruction} object.
	 * @return a {@link org.objectweb.asm.tree.InsnList} object.
	 */
	protected InsnList getInstrumentation(MethodNode mn, String className,
	        String methodName, int access) {

		InsnList instrumentation = new InsnList();
		
		instrumentation.add(new LdcInsnNode(className));
		instrumentation.add(new LdcInsnNode(methodName));
				
		//count parameters out of the signature
		/*int numOfParams = 0;
		String sig = mn.desc;
		sig = sig.substring(1, sig.lastIndexOf(')'));
		if (sig.contains("["))
			sig = sig.replaceAll("\\[", "");
		String[] params = sig.split(";");
		for (String p : params) {
			int indexL = p.indexOf('L');
			if (indexL < 0)
				numOfParams += p.length();
			else 
				numOfParams += indexL + 1;
		}
		if ((mn.access & Opcodes.ACC_STATIC) <= 0) { //non static: receiver object is part of parameters
			numOfParams++;
		}*/
		
		try {
			addArrayOfParams(instrumentation, mn.desc, (mn.access & Opcodes.ACC_STATIC) > 0);
		} catch(IllegalStateException e) {
			throw new IllegalStateException("Method " + className + "." + mn.name + ":" + e.getMessage());
		}
		
		instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC,
				EXECUTION_TRACER, "passedMethodCall", "(Ljava/lang/String;Ljava/lang/String;[Ljava/lang/Object;)V", false));
		logger.debug("Adding passedMethodCall");
		
		return instrumentation;
	}

	/*private LocalVariableNode getVariableByIndex(List<LocalVariableNode> paramList, int varIndex) {
		List<LocalVariableNode> toSort = new ArrayList<>();
		for (LocalVariableNode var : paramList) {
			toSort.add(var);
			/*if (var.index == varIndex) {
				return var;
			}* /
		}
		
		Collections.sort(toSort, new Comparator<LocalVariableNode>() {
			@Override
			public int compare(LocalVariableNode o1, LocalVariableNode o2) {
				if (o1.index < o2.index) return -1;
				else if (o1.index == o2.index) return 0;
				else return 1;
			}
		});
		
		try {
			return toSort.get(varIndex);
		} catch(Exception e) {
			String msg = "";
			for (LocalVariableNode var : paramList) {
				msg += " var " + var.name + "(index is " + var.index + ")";
			}
			throw new IllegalStateException("error instrumenting node "
				+ "MISS" + " since no local var has index " + varIndex + " that should corresponds to an input parameter: " + msg + ", cause is: " + e);
		}
	}*/

	private void addArrayOfParams(InsnList instrumentation, String methodDescr, boolean isStatic) {

		String simplifiedDescriptor = isStatic ? "" : "L"; //simplified descriptor, with a single char for each parameter: either L or [ to refer to non primitive objects or arrays, respectively.
		int nextParamInDescriptor = 1;
		while (methodDescr.charAt(nextParamInDescriptor) != ')') {
			char paramType = methodDescr.charAt(nextParamInDescriptor++);
			simplifiedDescriptor += paramType;
			if (paramType == '[') {
				while (methodDescr.charAt(nextParamInDescriptor) == '[') {
					++nextParamInDescriptor;
				}
			} 
			if (paramType == '[' && methodDescr.charAt(nextParamInDescriptor) != 'L') {
				++nextParamInDescriptor;
			} else if (paramType == 'L' || (paramType == '[' &&  methodDescr.charAt(nextParamInDescriptor) == 'L')) {
				nextParamInDescriptor = methodDescr.indexOf(';', nextParamInDescriptor) + 1;
			}		
		}

		// Create array with length equal to paramLength 
		instrumentation.add(new IntInsnNode(Opcodes.BIPUSH, simplifiedDescriptor.length()));
		instrumentation.add(new TypeInsnNode(Opcodes.ANEWARRAY, "java/lang/Object"));

		// Fill the created array with method parameters
		for (int paramIndex = 0, paramByteCodeIndex = 0; paramIndex < simplifiedDescriptor.length(); paramIndex++, paramByteCodeIndex++)  {
			char paramType = simplifiedDescriptor.charAt(paramIndex);

			instrumentation.add(new InsnNode(Opcodes.DUP));////instrumentation.add(new VarInsnNode(Opcodes.ALOAD, paramList.size()));
			instrumentation.add(new IntInsnNode(Opcodes.BIPUSH, paramIndex));

			if (paramType == 'Z') {
				instrumentation.add(new VarInsnNode(Opcodes.ILOAD, paramByteCodeIndex));
			} else if (paramType == 'B') {
				instrumentation.add(new VarInsnNode(Opcodes.ILOAD, paramByteCodeIndex));
			} else if (paramType == 'C') {
				instrumentation.add(new VarInsnNode(Opcodes.ILOAD, paramByteCodeIndex));
			} else if (paramType == 'S') {
				instrumentation.add(new VarInsnNode(Opcodes.ILOAD, paramByteCodeIndex));
			} else if (paramType == 'I') {
				instrumentation.add(new VarInsnNode(Opcodes.ILOAD, paramByteCodeIndex));
			} else if (paramType == 'J') {
				instrumentation.add(new VarInsnNode(Opcodes.LLOAD, paramByteCodeIndex));
				paramByteCodeIndex++;
			} else if (paramType == 'F') {
				instrumentation.add(new VarInsnNode(Opcodes.FLOAD, paramByteCodeIndex));
			} else if (paramType == 'D') {
				instrumentation.add(new VarInsnNode(Opcodes.DLOAD, paramByteCodeIndex));
				paramByteCodeIndex++;
			} else {
				instrumentation.add(new VarInsnNode(Opcodes.ALOAD, paramByteCodeIndex));
			}
			addBoxingForPrimitiveValueIfNeeded(instrumentation, paramType); 
			
			instrumentation.add(new InsnNode(Opcodes.AASTORE));
		}

	}

	private void addBoxingForPrimitiveValueIfNeeded(InsnList instrumentation, char valueType) {
		if (valueType == 'Z') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Boolean", "valueOf", "(Z)Ljava/lang/Boolean;"));
		} else if (valueType == 'B') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Byte", "valueOf", "(B)Ljava/lang/Byte;"));
		} else if (valueType == 'C') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Character", "valueOf", "(C)Ljava/lang/Character;"));
		} else if (valueType == 'S') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Short", "valueOf", "(S)Ljava/lang/Short;"));
		} else if (valueType == 'I') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;"));
		} else if (valueType == 'J') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Long", "valueOf", "(J)Ljava/lang/Long;"));
		} else if (valueType == 'F') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Float", "valueOf", "(F)Ljava/lang/Float;"));
		} else if (valueType == 'D') {
			instrumentation.add(new MethodInsnNode(Opcodes.INVOKESTATIC, "java/lang/Double", "valueOf", "(D)Ljava/lang/Double;"));
		} else {
			/* non primitive type: add nothing */
		}
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see
	 * org.evosuite.cfg.MethodInstrumentation#executeOnExcludedMethods
	 * ()
	 */
	/** {@inheritDoc} */
	@Override
	public boolean executeOnExcludedMethods() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see
	 * org.evosuite.cfg.MethodInstrumentation#executeOnMainMethod()
	 */
	/** {@inheritDoc} */
	@Override
	public boolean executeOnMainMethod() {
		return false;
	}

}
