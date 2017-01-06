/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;
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
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
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
			simplifiedExpression = translate(expr);
		} catch (IVisitor.VisitorException e) {
			System.out.println("Error: Peticodiac assert failed: " + e.getMessage());
			return smtConfig.responseFactory.error("Peticodiac assert command failed: " + e.getMessage());
		}
		
		try {
			// Output the first line "p cnf NUM_VARS NUM_CONSTRS" to indicate the number of contraints and bounds
			this.numConstrs = simplifiedExpression.size() - 1;
			this.outputWriter.write("p cnf " + this.numVars + " " + this.numConstrs);
			this.outputWriter.newLine();
			
			// Output the simplified expression in terms of tableau coefficient and bounds
			// Format is
			// c <list of coefficient for tableau delimited by one space>
			// b slack_var_index lower_bound upper_bound
			String output = "";
			for (int i = 1; i <= numConstrs; i++) {
				output += "c";
				for (int j = 0; j < this.numVars; j++) {
					output += " " + simplifiedExpression.get(i).get(j);
				}
				output += "\nb " + (i+1)
						+ " "    + simplifiedExpression.get(i).get(this.numVars)
						+ " "	 + simplifiedExpression.get(i).get(this.numVars+1) + "\n";
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
		
		//TODO: Output the logic used in the comment section of our input format
		//System.out.println("Peticodiac set_logic with name = [" + logicName + "] position = <" + pos.toString() + "> with success");
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
		
		//TODO: Output the info in the comment section of our input format
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

	@Override 
	public IResponse declare_const(Ideclare_const cmd) {
		IResponse status = super.declare_const(cmd);
		if (status.isError()) {return status;}
		
		//TODO: Output the NUM_VARS
		this.numVars += 1;
		System.out.println("Peticodiac declare_const has " + numVars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override 
	public IResponse declare_fun(Ideclare_fun cmd) {
		IResponse status = super.declare_fun(cmd);
		if (status.isError()) {return status;}
		
		//TODO: Output the NUM_VARS
		this.numVars += 1;
		System.out.println("Peticodiac declare_fun has " + numVars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		IResponse status = super.define_fun(cmd);
		if (status.isError()) {return status;}
		
		//TODO: Output the NUM_VARS
		this.numVars += 1;
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
	
	public /*@Nullable*/ List<ArrayList<String>> translate(IExpr expr) throws IVisitor.VisitorException {
		Translator exprTranslator = new Translator();
		String returnedExpr = expr.accept(exprTranslator);
		System.out.println("returnedExpr = " + returnedExpr);
		System.out.println("==== translator queue = " + exprTranslator.getExpressionQueue());
		System.out.println("==== expressions = " + exprTranslator.getPeticodiacFormat().toString());
		return exprTranslator.getPeticodiacFormat();
	}
	
	public class Translator extends IVisitor.NullVisitor<String> {
		private Queue<String> expressionQueue;
		private List<ArrayList<String>> expressions;
		public Translator() {
			System.out.println("In Translator creating visitor");
			expressionQueue = new ArrayDeque<String>();
			expressions = new ArrayList<ArrayList<String>>();
			expressions.add(new ArrayList<String>()); // For first row symbol list
			expressions.add(new ArrayList<String>()); // For second row first expression
		}
		
		public String getExpressionQueue() {
			return expressionQueue.toString();
		}
		
		public List<ArrayList<String>> getPeticodiacFormat() {
			expressions.get(0).add("LowerBound");
			expressions.get(0).add("UpperBound");
			Stack<String> expressionStack = new Stack<String>();
			while (!expressionQueue.isEmpty()) {
				String item = expressionQueue.poll();
				if ("*".equals(item)) {
					String exprSymbol = expressionStack.pop();
					String exprCoefficient = expressionStack.pop();
					int index = expressions.get(0).indexOf(exprSymbol);
					int listSize = expressions.size();
					expressions.get(listSize-1).add(index, exprCoefficient);
				} else if ("/".equals(item)) {
					String exprDenominator = expressionStack.pop();
					String exprNumerator = expressionStack.pop();
					String fraction = exprNumerator + "/" + exprDenominator;
					expressionStack.push(fraction);
				} else if ("-".equals(item)) {
					String exprCoefficient = expressionStack.pop();
					String negateCoefficient = "-" + exprCoefficient;
					expressionStack.push(negateCoefficient);
				} else if (">".equals(item)) {
					String lowerBound = expressionStack.pop();
					int lowerBoundIndex = expressions.get(0).indexOf("LowerBound");
					int listSize = expressions.size();
					if (expressions.get(listSize-1).size() <= 0) {
						expressions.get(listSize-1).add(0, "1");
					}
					expressions.get(listSize-1).add(lowerBoundIndex, lowerBound);
					expressions.get(listSize-1).add(lowerBoundIndex+1, "NO_BOUND");
				} else if ("<".equals(item)) {
					String upperBound = expressionStack.pop();
					int lowerBoundIndex = expressions.get(0).indexOf("LowerBound");
					int listSize = expressions.size();
					if (expressions.get(listSize-1).size() <= 0) {
						expressions.get(listSize-1).add(0, "1");
					}
					expressions.get(listSize-1).add(lowerBoundIndex, "NO_BOUND");
					expressions.get(listSize-1).add(lowerBoundIndex+1, upperBound);
				} else {
					expressionStack.push(item);
				}
			}
			return expressions;
		}
		
		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			System.out.println("Visiting numeral = " + e.toString());
			expressionQueue.add(e.toString());
			return e.value().toString();
		}
		
		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			//System.out.println("Visiting FcnExpr = " + e.toString());
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) {
				throw new VisitorException("Peticodiac did not expect an empty argument list", e.pos());
			}
			
			while (iter.hasNext()) {
				System.out.println("== Iteration has next: ");
				String fcnname = iter.next().accept(this);
			}
			System.out.println("Visiting FcnExpr = " + e.toString());
			
			if (e.toString().startsWith("(") &&
					("*".equals(e.toString().substring(1, 2)) ||
					 "/".equals(e.toString().substring(1, 2)) ||
					 "+".equals(e.toString().substring(1, 2)) ||
					 "-".equals(e.toString().substring(1, 2)) ||
					 "=".equals(e.toString().substring(1, 2)) ||
					 "<".equals(e.toString().substring(1, 2)) ||
					 ">".equals(e.toString().substring(1, 2)) ||
					 "<=".equals(e.toString().substring(1, 2)) ||
					 ">=".equals(e.toString().substring(1, 2)) ||
					 "%".equals(e.toString().substring(1, 2)) )) {
				expressionQueue.add(e.toString().substring(1, 2));
			} else {
				expressionQueue.add(e.toString());
			}
			return e.toString();
		}
		
		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			System.out.println("Symbol is " + e.value());
			expressionQueue.add(e.value());
			expressions.get(0).add(e.value());
			return e.value();
		}
	}
}
