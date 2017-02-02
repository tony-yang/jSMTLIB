/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.io.File;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;

import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Response;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.solvers.Solver_yices.Translator;

/** This class is a Solver implementation that simply type-checks formulae and checks that
 * commands are used correctly; it does not do any proving.
 */
public class Solver_peticodiac extends Solver_test implements ISolver {
		
	/** Track the number of variables and bounds to be used in the tableau */
	protected int numVars;
	protected int numConstrs;
	protected SortedSet<String> expressionVariables;
	
	/** The intermediate output file path using our input format */
	protected File outputFile;
	protected StringWriter stringOutput;
	protected BufferedWriter outputWriter;
	
	
	
	/** Constructor for an instance of this test solver class; the second argument is ignored - it is 
	 * present just for uniformity with other solvers, for which that argument is a path to the relevant
	 * executable.  This constructor is called by reflection, upon knowing the name of the solver ("test").
	 * @param smtConfig a reference to the configuration instance in use
	 * @param exec the executable for the solver, ignored for the case of this test solver
	 */
	public Solver_peticodiac(SMT.Configuration smtConfig, String exec) {
		super(smtConfig, "");
		numVars = 0;
		numConstrs = 0;
		expressionVariables = new TreeSet<String>();
		if (!this.smtConfig.files.isEmpty()) {
			String inputFile = this.smtConfig.files.get(0).toString();
			String inputFilename = inputFile.substring(inputFile.lastIndexOf('/') + 1);
			System.out.println("smtConfig.files not empty with file = " + inputFilename);
			
			if (this.smtConfig.peticodiacout == null) {
				outputFile = new File("/tmp/" + inputFilename + ".peticodiac");
			} else {
				outputFile = new File(this.smtConfig.peticodiacout.toString().toLowerCase() + "/" + inputFilename + ".peticodiac");
			}
			
			if (outputFile.exists()) {
				outputFile.delete();
			}
			try {
				outputWriter = new BufferedWriter(new FileWriter(outputFile));
			} catch (IOException e) {
				// ignore Error
			}
		} else {
			System.out.println("smtConfig.files empty");
			outputWriter = new BufferedWriter(new StringWriter());
		}
	}
	
	@Override
	public IResponse start() {
		IResponse status = super.start();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac start success");
		return smtConfig.responseFactory.success();
	}

	@Override
	public void comment(String comment) {
		// No action
		System.out.println("Peticodiac comment = " + comment.toString() + " with no action");
	}

	@Override
	public IResponse exit() {
		IResponse status = super.exit();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac exit success");
		try {
			this.outputWriter.close();
			System.out.println("Peticodiac outputWriter closed");
		} catch (IOException e) {
			// ignore
			System.out.println("Peticodiac outputWriter close failed");
		}
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse echo(IStringLiteral arg) {
		IResponse status = super.echo(arg);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac echo arg = " + arg.toString());
		return arg;
	}

	@Override
	public IResponse assertExpr(IExpr expr) {
		IResponse status = super.assertExpr(expr);
		if (status.isError()) {return status;}
		
		//TODO: Write simplified output to file and determine the NUM_CONSTRS
		System.out.println("Peticodiac Assert Expression with expr = " + expr.toString());
		// Simplify the expression
		
		List<ArrayList<String>> simplifiedExpression;
		
		try {
			simplifiedExpression = translate(expr, expressionVariables);
		} catch (IVisitor.VisitorException e) {
			System.out.println("Error: Peticodiac assert failed: " + e.getMessage());
			return smtConfig.responseFactory.error("Peticodiac assert command failed: " + e.getMessage());
		}
		
		try {
			// Output the first line "p cnf NUM_VARS NUM_CONSTRS" to indicate the number of constraints and bounds
			// We always subtract 2 here. We leave the first row out for the header and the last row out
			// since the last row is always empty, created for the next potential expression during Translation
			this.numConstrs = simplifiedExpression.size() - 2;
			this.outputWriter.write("p cnf " + this.numVars + " " + this.numConstrs);
			this.outputWriter.newLine();
			
			// Output the simplified expression in terms of tableau coefficient and bounds
			// Format is
			// c <list of coefficient for tableau delimited by one space>
			// b slack_var_index lower_bound upper_bound
			String output = "";
			int boundIndex = 0;
			for (int i = 1; i <= numConstrs; i++) {
				output += "c";
				for (int j = 0; j < this.numVars; j++) {
					String value = simplifiedExpression.get(i).get(j).equals("na") ? "0.0" : simplifiedExpression.get(i).get(j);
					output += " " + value;
				}
				output += "\nb " + (this.numVars + boundIndex)
						+ " "    + simplifiedExpression.get(i).get(this.numVars)
						+ " "	 + simplifiedExpression.get(i).get(this.numVars+1) + "\n";
				boundIndex += 1;
			}
			this.outputWriter.write(output);
			
		} catch (IOException e) {
			// ignore
		}
		
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse get_assertions() {
		IResponse status = super.get_assertions();
		if (status.isError()) {return status;}
		
		//Not supported since we don't need interactive mode
		System.out.println("Peticodiac get_assertions not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse check_sat() {
		IResponse status = super.check_sat();
		if (status.isError()) {return status;}
		
		// We use this adapter only to generate the intermediate input format for peticodaic
		System.out.println("Peticodiac check_sat not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse check_sat_assuming(IExpr ... exprs) {
		IResponse status = super.check_sat_assuming(exprs);
		if (status.isError()) {return status;}
		
		// We use this adapter only to generate the intermediate input format for peticodaic
		System.out.println("Peticodiac check_sat_assuming not supported with exprs = " + exprs.toString());
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse get_value(IExpr... terms) {
		IResponse status = super.get_value(terms);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_value not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_assignment() {
		IResponse status = super.get_assignment();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_assignment not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse get_proof() {
		IResponse status = super.get_proof();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_proof not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_model() {
		IResponse status = super.get_model();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_model not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_unsat_core() {
		IResponse status = super.get_unsat_core();
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_unsat_core not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse pop(int number) {
		IResponse status = super.pop(number);
		if (status.isError()) {return status;}
		
		//TODO: Figure out if we need to support the pop() method in our benchmark
		System.out.println("Peticodiac pop number = " + number + " with action success");
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse push(int number) {
		IResponse status = super.push(number);
		if (status.isError()) {return status;}
		
		//TODO: Figure out if we need to support the push() method in our benchmark
		System.out.println("Peticodiac push number = " + number + " with action success");
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		IResponse status = super.set_logic(logicName, pos);
		if (status.isError()) {return status;}
		
		try {
			this.outputWriter.write("# set_logic: " + logicName);
			this.outputWriter.newLine();
		} catch (IOException e) {
			// ignore
		}
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		IResponse status = super.set_option(key,  value);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac set_option not supported with key = [" + key.toString() + "] and value <" + value.toString() + ">");
		try {
			this.outputWriter.write("# " + key.toString() + ": " + value.toString());
			this.outputWriter.newLine();
		} catch (IOException e) {
			// ignore
		}
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_option(IKeyword key) {
		IResponse status = super.get_option(key);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_option not supported with key = [" + key.toString() + "]");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		IResponse status = super.set_info(key,  value);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac set_info with key = [" + key.toString() + "] and value = <" + value.toString() + "> with success");
		try {
			this.outputWriter.write("# " + key.toString() + ": " + value.toString());
			this.outputWriter.newLine();
		} catch (IOException e) {
			// ignore
		}
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse get_info(IKeyword key) {
		IResponse status = super.get_info(key);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac get_info not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	protected String encode(IIdentifier id) {
		return id.toString(); // FIXME composite definitions; encode the String?
	}

	private String parseSymbolFromCommand(String cmd) {
		String[] cmdArray = cmd.split(" ");
		return cmdArray[1];
	}
	
	@Override 
	public IResponse declare_const(Ideclare_const cmd) {
		IResponse status = super.declare_const(cmd);
		if (status.isError()) {return status;}
		
		this.numVars += 1;
		this.expressionVariables.add(parseSymbolFromCommand(cmd.toString()));
		System.out.println("Peticodiac declare_const has " + numVars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override 
	public IResponse declare_fun(Ideclare_fun cmd) {
		IResponse status = super.declare_fun(cmd);
		if (status.isError()) {return status;}
		
		this.numVars += 1;
		this.expressionVariables.add(parseSymbolFromCommand(cmd.toString()));
		System.out.println("Peticodiac declare_fun has " + numVars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		IResponse status = super.define_fun(cmd);
		if (status.isError()) {return status;}
		
		this.numVars += 1;
		this.expressionVariables.add(parseSymbolFromCommand(cmd.toString()));
		System.out.println("Peticodiac define_fun has " + numVars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}
	
	@Override 
	public IResponse declare_sort(Ideclare_sort cmd) {
		IResponse status = super.declare_sort(cmd);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac declare_sort with cmd = " + cmd.toString() + " not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		IResponse status = super.define_sort(cmd);
		if (status.isError()) {return status;}
		
		System.out.println("Peticodiac define_sort with cmd = " + cmd.toString() + " not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	public /*@Nullable*/ List<ArrayList<String>> translate(IExpr expr, SortedSet<String> expressionVariables) throws IVisitor.VisitorException {
		Translator exprTranslator = new Translator(expressionVariables);
		System.out.println("Calling translate with expr => " + expr.toString());
		IExpr returnedExpr = expr.accept(exprTranslator);
		System.out.println("returnedExpr = " + returnedExpr);
		System.out.println("==== translator queue = " + exprTranslator.getExpressionQueue());
		
		List<ArrayList<String>> peticodiacExpression2 = exprTranslator.getPeticodiacFormat2();
		System.out.println("==== expressions2 = " + peticodiacExpression2.toString());
		
		List<ArrayList<String>> peticodiacExpression = exprTranslator.getPeticodiacFormat();
		System.out.println("==== expressions = " + peticodiacExpression.toString());
		return peticodiacExpression;
	}
	
	public class Translator extends IVisitor.NullVisitor<IExpr> {
		private Deque<String> expressionQueue;;
		private List<ArrayList<String>> expressions;
		private HashMap<String, Deque<String>> letSymbolHash;
		
		private Deque<Deque> expressionQueues;
		private List<ArrayList<String>> expressions2;
		private HashMap<String, Deque<String>> letSymbolHash2;
		public Translator(SortedSet<String> expressionVariables) {
			System.out.println("In Translator creating visitor");
			expressionQueue = new ArrayDeque<String>();
			expressions = new ArrayList<ArrayList<String>>();
			expressions.add(new ArrayList<String>(expressionVariables)); // For first row symbol list
			expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na"))); // For second row first expression
			letSymbolHash = new HashMap<String, Deque<String>>();
			
			expressionQueues = new ArrayDeque<Deque>();
			expressions2 = new ArrayList<ArrayList<String>>();
			expressions2.add(new ArrayList<String>(expressionVariables)); // For first row symbol list
			expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na"))); // For second row first expression
			letSymbolHash2 = new HashMap<String, Deque<String>>();
		}
		
		public String getExpressionQueue() {
			return expressionQueue.toString();
		}
		
		private void convertExpression(Stack<String> expressionStack) {
			while(!expressionStack.isEmpty()) {
				String exprOperand = expressionStack.pop();
				String[] operandArray = exprOperand.split("\\*");
				String exprSymbol = operandArray[0];
				String exprCoefficient = (operandArray.length > 1) ? operandArray[1] : "1.0";
				if ("-".equals(exprSymbol.substring(0, 1))) {
					if ("-".equals(exprCoefficient.substring(0, 1))) {
						exprCoefficient = exprCoefficient.substring(1);
					} else {
						exprCoefficient = "-" + exprCoefficient;
					}
					exprSymbol = exprSymbol.substring(1);
				}
				updateCoefficient(exprSymbol, exprCoefficient);
			}
		}
		
		private void updateCoefficient(String exprSymbol, String exprCoefficient) {
			System.out.println("=== DEBUG: symbol = " + exprSymbol + " coeff = " + exprCoefficient);
			int index = expressions.get(0).indexOf(exprSymbol);
			int listSize = expressions.size();
			Double existingCoeff = Double.valueOf(expressions.get(listSize-1).get(index));
			Double newCoeff = existingCoeff + Double.valueOf(exprCoefficient);
			expressions.get(listSize-1).set(index, newCoeff.toString());
		}
		
		private void updateBound(String lowerBound, String upperBound) {
			int lowerBoundIndex = expressions.get(0).indexOf("LowerBound");
			int listSize = expressions.size();
			expressions.get(listSize-1).set(lowerBoundIndex, lowerBound);
			expressions.get(listSize-1).set(lowerBoundIndex+1, upperBound);
		}
		
		public List<ArrayList<String>> getPeticodiacFormat2() {
			expressions2.get(0).add("LowerBound");
			expressions2.get(0).add("UpperBound");
			Stack<String> expressionStack2 = new Stack<String>();
			while (!expressionQueues.isEmpty()) {
				System.out.println(">> The expression Stack >> " + expressionStack2.toString());
				Deque<IExpr> subexpression = expressionQueues.poll();
				System.out.println("       ==  subexpression = " + subexpression.toString());
				
				int subexpressionLength = subexpression.size();
				String operatorExpr = subexpression.getLast().toString();
				String operator = "";
				
				if (operatorExpr.startsWith("(") &&
						("<=".equals(operatorExpr.substring(1, 3))  ||
						 ">=".equals(operatorExpr.substring(1, 3))  )) {
					operator = operatorExpr.substring(1, 3);
				} else if (operatorExpr.startsWith("(") &&
						("<".equals(operatorExpr.substring(1, 2))  ||
						 ">".equals(operatorExpr.substring(1, 2))  )) {
					operator = operatorExpr.substring(1, 2);
				} else if (operatorExpr.startsWith("(") &&
						("*".equals(operatorExpr.substring(1, 2))  ||
						 "/".equals(operatorExpr.substring(1, 2))  ||
						 "+".equals(operatorExpr.substring(1, 2))  ||
						 "-".equals(operatorExpr.substring(1, 2))  ||
						 "=".equals(operatorExpr.substring(1, 2))  ||
						 "%".equals(operatorExpr.substring(1, 2))  )) {
					operator = operatorExpr.substring(1, 2);
				}
				
				// Parse the variable to handle the edge case when a symbol has no coefficient
				// Set all variable coefficients to 1 to begin with
				String symbolPattern = "[a-zA-Z_\\-\\~\\!\\$\\^\\&\\*\\+\\=\\.\\?\\/\\<\\>@%][0-9a-zA-Z_\\-\\~\\!\\$\\^\\&\\*\\+\\=\\.\\?\\/\\<\\>@%]*";
				Pattern r = Pattern.compile(symbolPattern);
				//Matcher m = r.matcher(subexpression);
				
				
				if ("*".equals(operator)) {
					String exprSymbol = expressionStack2.pop();
					String exprCoefficient = expressionStack2.pop();
					String finalSymbol = exprSymbol + "*" + exprCoefficient;
					expressionStack2.push(finalSymbol);
				} else if ("/".equals(subexpression)) {
					Double exprDenominator = Double.valueOf(expressionStack2.pop());
					Double exprNumerator = Double.valueOf(expressionStack2.pop());
					Double fraction = exprNumerator/exprDenominator;
					expressionStack2.push(fraction.toString());
				} else if ("-".equals(subexpression)) {
					String exprSymbol = expressionStack2.pop();
					String negatedSymbol = "-" + exprSymbol;
					if ("-".equals(exprSymbol.substring(0, 1))) {
						negatedSymbol = exprSymbol.substring(1);
					}
					expressionStack2.push(negatedSymbol);
				} else if ("+".equals(subexpression)) {
					// Do nothing as everything is normalized to standard form with "+" as the operator
				} else if (">=".equals(subexpression)) {
					String lowerBound = ">=:" + expressionStack2.pop();
					updateBound(lowerBound, "NO_BOUND");
					convertExpression(expressionStack2);
					expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("<=".equals(subexpression)) {
					String upperBound = "<=:" + expressionStack2.pop();
					updateBound("NO_BOUND", upperBound);
					convertExpression(expressionStack2);
					expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if (">".equals(subexpression)) {
					String lowerBound = ">:" + expressionStack2.pop();
					updateBound(lowerBound, "NO_BOUND");
					convertExpression(expressionStack2);
					expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("<".equals(subexpression)) {
					String upperBound = "<:" + expressionStack2.pop();
					updateBound("NO_BOUND", upperBound);
					convertExpression(expressionStack2);
					expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("=".equals(subexpression)) {
					String bound = "=:" + expressionStack2.pop();
					updateBound(bound, bound);
					convertExpression(expressionStack2);
					expressions2.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("and".equals(subexpression.toString().toLowerCase())) {
					// Do nothing as everything is normalized to standard conjugate form
				} else if (false) {
					int index = expressions2.get(0).indexOf(subexpression);
					int listSize = expressions2.size();
					if ("na".equals(expressions2.get(listSize-1).get(index).toLowerCase())) {
						expressions2.get(listSize-1).set(index, "0.0");
					}
					expressionStack2.push(subexpression.toString());
				} else {
					expressionStack2.push(subexpression.toString());
				}
				
				System.out.println(">>>>> After push the expression Stack >> " + expressionStack2.toString());
			}
			System.out.println("=== expressionStack 2 = " + expressionStack2);
			
			return expressions2;
		}
		
		public List<ArrayList<String>> getPeticodiacFormat() {
			expressions.get(0).add("LowerBound");
			expressions.get(0).add("UpperBound");
			Stack<String> expressionStack = new Stack<String>();
			while (!expressionQueue.isEmpty()) {
				System.out.println(">> The expression Stack >> " + expressionStack.toString());
				String item = expressionQueue.poll();
				
				// Parse the variable to handle the edge case when a symbol has no coefficient
				// Set all variable coefficients to 1 to begin with
				String symbolPattern = "[a-zA-Z_\\-\\~\\!\\$\\^\\&\\*\\+\\=\\.\\?\\/\\<\\>@%][0-9a-zA-Z_\\-\\~\\!\\$\\^\\&\\*\\+\\=\\.\\?\\/\\<\\>@%]*";
				Pattern r = Pattern.compile(symbolPattern);
				Matcher m = r.matcher(item);
				
				if ("*".equals(item)) {
					String exprSymbol = expressionStack.pop();
					String exprCoefficient = expressionStack.pop();
					String finalSymbol = exprSymbol + "*" + exprCoefficient;
					expressionStack.push(finalSymbol);
				} else if ("/".equals(item)) {
					Double exprDenominator = Double.valueOf(expressionStack.pop());
					Double exprNumerator = Double.valueOf(expressionStack.pop());
					Double fraction = exprNumerator/exprDenominator;
					expressionStack.push(fraction.toString());
				} else if ("-".equals(item)) {
					String exprSymbol = expressionStack.pop();
					String negatedSymbol = "-" + exprSymbol;
					if ("-".equals(exprSymbol.substring(0, 1))) {
						negatedSymbol = exprSymbol.substring(1);
					}
					expressionStack.push(negatedSymbol);
				} else if ("+".equals(item)) {
					// Do nothing as everything is normalized to standard form with "+" as the operator
				} else if (">=".equals(item)) {
					String lowerBound = ">=:" + expressionStack.pop();
					updateBound(lowerBound, "NO_BOUND");
					convertExpression(expressionStack);
					expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("<=".equals(item)) {
					String upperBound = "<=:" + expressionStack.pop();
					updateBound("NO_BOUND", upperBound);
					convertExpression(expressionStack);
					expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if (">".equals(item)) {
					String lowerBound = ">:" + expressionStack.pop();
					updateBound(lowerBound, "NO_BOUND");
					convertExpression(expressionStack);
					expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("<".equals(item)) {
					String upperBound = "<:" + expressionStack.pop();
					updateBound("NO_BOUND", upperBound);
					convertExpression(expressionStack);
					expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("=".equals(item)) {
					String bound = "=:" + expressionStack.pop();
					updateBound(bound, bound);
					convertExpression(expressionStack);
					expressions.add(new ArrayList<String>(Collections.nCopies(expressionVariables.size() + 2, "na")));
				} else if ("and".equals(item.toLowerCase())) {
					// Do nothing as everything is normalized to standard conjugate form
				} else if (m.find()) {
					int index = expressions.get(0).indexOf(item);
					int listSize = expressions.size();
					if ("na".equals(expressions.get(listSize-1).get(index).toLowerCase())) {
						expressions.get(listSize-1).set(index, "0.0");
					}
					expressionStack.push(item);
				} else {
					expressionStack.push(item);
				}
			}
			
			return expressions;
		}
		
		@Override
		public INumeral visit(INumeral e) throws IVisitor.VisitorException {
			System.out.println("Visiting numeral = " + e.toString());
			expressionQueue.add(e.toString());
			//return e.value().toString();
			return e;
		}
		
		@Override
		public IExpr visit(IFcnExpr e) throws IVisitor.VisitorException {
			System.out.println("    Visiting FcnExpr = " + e.toString());
			Deque<IExpr> fcnQueue = new ArrayDeque<IExpr>();
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) {
				throw new VisitorException("Peticodiac did not expect an empty argument list", e.pos());
			}
			
			while (iter.hasNext()) {
				System.out.println("== Iteration has next and iter = " + iter.toString());
				IExpr expr = iter.next();
				System.out.println("    = The next expr = " + expr.toString());
				IExpr fcnname = expr.accept(this);
				System.out.println("    ===> return from accept fcnname = " + fcnname);
				fcnQueue.add(fcnname);
			}
			System.out.println("	Visiting FcnExpr from return after accept = " + e.toString());
			
			if (e.toString().startsWith("(") &&
					("<=".equals(e.toString().substring(1, 3))  ||
					 ">=".equals(e.toString().substring(1, 3))  )) {
				expressionQueue.add(e.toString().substring(1, 3));
				if ("numeral".equals(fcnQueue.peek().kind())) {
					IExpr firstElement = fcnQueue.poll();
					fcnQueue.add(firstElement);
				}
				fcnQueue.add(e);
			} else if (e.toString().startsWith("(") &&
					("<".equals(e.toString().substring(1, 2))  ||
					 ">".equals(e.toString().substring(1, 2))  )) {
				expressionQueue.add(e.toString().substring(1, 2));
				if ("numeral".equals(fcnQueue.peek().kind())) {
					IExpr firstElement = fcnQueue.poll();
					fcnQueue.add(firstElement);
				}
				fcnQueue.add(e);
			} else if (e.toString().startsWith("(") &&
					("*".equals(e.toString().substring(1, 2))  ||
					 "/".equals(e.toString().substring(1, 2))  ||
					 "+".equals(e.toString().substring(1, 2))  ||
					 "-".equals(e.toString().substring(1, 2))  ||
					 "=".equals(e.toString().substring(1, 2))  ||
					 "%".equals(e.toString().substring(1, 2))  )) {
				expressionQueue.add(e.toString().substring(1, 2));
				fcnQueue.add(e);
			} else if (e.toString().startsWith("(") && "and ".equals(e.toString().substring(1,  5).toLowerCase())) {
				expressionQueue.add(e.toString().substring(1, 4));
				fcnQueue.add(e);
			} else {
				expressionQueue.add(e.toString());
				fcnQueue.add(e);
			}
			
			expressionQueues.addLast(fcnQueue);
			System.out.println("### The expressionQueues = " + expressionQueues);
			System.out.println("### The fcnQueue = " + fcnQueue);
			return e;
		}
		
		@Override
		public ISymbol visit(ISymbol e) throws IVisitor.VisitorException {
			System.out.println("Symbol is " + e.value());
			if (letSymbolHash.containsKey(e.value())) {
				Deque<String> substituteValue = letSymbolHash.get(e.value());
				while (!substituteValue.isEmpty()) {
					expressionQueue.add(substituteValue.poll());
				}
			} else {
				expressionQueue.add(e.value());
			}
			return e;
		}
		
		@Override
		public IExpr visit(ILet e) throws IVisitor.VisitorException {
			System.out.println("Let expr is " + e.bindings().toString());
			StringBuffer sb = new StringBuffer();
			
			for (IBinding d: e.bindings()) {
				System.out.println("==>>> binding d = " + d.toString());
				String variableKey = d.parameter().toString();
				d.expr().accept(this);
				Deque<String> variableValueQueue = new ArrayDeque<String>(expressionQueue);
				expressionQueue.clear();
				System.out.println("    bind key = " + variableKey + " value = " + variableValueQueue.toString());
				letSymbolHash.put(variableKey, variableValueQueue);
			}
			IExpr result = e.expr().accept(this);
			System.out.println("=== >>> Return from the let " + result);
			return result;
		}
	}
}
