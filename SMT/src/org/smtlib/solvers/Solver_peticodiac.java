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
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IPos.IPosable;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Response;

/** This class is a Solver implementation that simply type-checks formulae and checks that
 * commands are used correctly; it does not do any proving.
 */
public class Solver_peticodiac implements ISolver {
	
	/** A reference to the configuration used by this SMT instance. */
	protected SMT.Configuration smtConfig;
	
	/** Returns the reference to the configuration currently in use. */
	public SMT.Configuration smt() { return smtConfig; }

	/** The symbol table used by this solver */
	public SymbolTable symTable; // TODO - public for the sake of C_what - change to protected
	
	/** The data structure that maintains the solver's assertion set stack */
	protected List<List<IExpr>> assertionSetStack = new LinkedList<List<IExpr>>();
	
	/** Internal state variable - set non-null once the logic is set. */
	protected String logicSet = null;
	
	/** Internal state variable - set to the value of :global-declarations */
	protected boolean globalDeclarations = false;
	
	/** Internal state variable - set to sat, unsat, unknown when check-sat is run
	 * and then to null whenever an additional push, popo, assert, declare- or define-
	 * command is executed.  This is used in checking those commands that depend on the
	 * above set of conditions.
	 */
	protected /*@Nullable*/IResponse checkSatStatus;
	
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** A map holding the sorts of subexpressions, used for distinguishing formulas and terms
	 * for solvers for which that needs to be done.
	 */
	protected Map<IExpr,ISort> typemap = new HashMap<IExpr,ISort>();
	
	/** The data structure that maintains the current values of options and info items for this solver. */
	protected Map<String,IAttributeValue> options = new HashMap<String,IAttributeValue>();
	{ 
		options.putAll(Utils.defaults);
	}
	
	/** Track the number of variables and bounds to be used in the tableau */
	protected int num_vars;
	protected int num_constrs;
	
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
		System.out.println("Start peticodiac");
		this.smtConfig = smtConfig;
		this.symTable = new SymbolTable(smtConfig);
		checkSatStatus = null;
		num_vars = 0;
		num_constrs = 0;
		if (!this.smtConfig.files.isEmpty()) {
			outputFile = new File("/tmp/peticodiac/" + this.smtConfig.files.get(0).toString() + ".peticodiac");
			if (outputFile.exists()) {
				outputFile.delete();
			}
			try {
				outputWriter = new BufferedWriter(new FileWriter(outputFile));
			} catch (IOException e) {
				// ignore Error
			}
		} else {
			outputWriter = new BufferedWriter(new StringWriter());
		}
	}
	
	@Override
	public IResponse start() {
		assertionSetStack.add(0,new LinkedList<IExpr>());
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#start");
		System.out.println("Peticodiac start success");
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse reset() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset");
		assertionSetStack.clear();
		assertionSetStack.add(0,new LinkedList<IExpr>());
		symTable.clear();
		typemap.clear();
		logicSet = null;
		// Set all options and info to default values
		options.putAll(Utils.defaults);
		((Response.Factory)smtConfig.responseFactory).printSuccess = true;
		smtConfig.verbose = 0;
		smtConfig.log.out = System.out;
		smtConfig.log.diag = System.err;
		globalDeclarations = false;
		checkSatStatus = null;

		return smtConfig.responseFactory.success();
	}

	@Override public void comment(String comment) {
		// No action
		System.out.println("Peticodiac comment = " + comment.toString() + " with no action");
	}
	
	@Override
	public IResponse reset_assertions() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#reset-assertions");
		// Remove all pushed frames
		IResponse r = pop(assertionSetStack.size()-1);
		// Remove assertions, but necessarily global declarations
		assertionSetStack.get(0).clear();
		if (!globalDeclarations) {
			symTable.clear();
			r = smtConfig.utils.loadLogic(logicSet,symTable,null);
		}
		return r;
	}

	@Override
	public IResponse exit() {
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#exit");
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
		System.out.println("Peticodiac echo arg = " + arg.toString());
		return arg;
	}

	@Override
	public IResponse assertExpr(IExpr expr) {
		//TODO: Write simplified output to file and determine the NUM_CONSTRS
		System.out.println("Peticodiac Assert Expression with expr = " + expr.toString());
		// Simplify the expression
		
		
		try {
			// Output the first line "p cnf NUM_VARS NUM_CONSTRS" to indicate the number of contraints and bounds
			this.outputWriter.write("p cnf " + this.num_vars + " " + this.num_constrs);
			this.outputWriter.newLine();
			
			// Output the simplified expression in terms of tableau coefficient and bounds
			
		} catch (IOException e) {
			// ignore
		}
		
		return smtConfig.responseFactory.success();
	}
	
	@Override
	public IResponse get_assertions() {
		//Not supported since we don't need interactive mode
		System.out.println("Peticodiac get_assertions not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	/** This method adds all the IExpr items in the lists produced from the iter argument into
	 * the list referenced by the combined argument; the resulting order is to have the items on the
	 * end of the iter sequence added first into the combined list.
	 * @param combined the resulting combined, in-order, sequence of 
	 * @param iter an iterator producing a sequence of Lists of IExpr
	 */
	private void addAssertions(List<IExpr> combined, Iterator<List<IExpr>> iter) {
		if (iter.hasNext()) {
			List<IExpr> list = iter.next();
			addAssertions(combined,iter);
			combined.addAll(list);
		}
	}

	@Override
	public IResponse check_sat() {
		// We use this adapter only to generate the intermediate input format for peticodaic
		System.out.println("Peticodiac check_sat not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse check_sat_assuming(IExpr ... exprs) {
		// We use this adapter only to generate the intermediate input format for peticodaic
		System.out.println("Peticodiac check_sat_assuming not supported with exprs = " + exprs.toString());
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse get_value(IExpr... terms) {
		System.out.println("Peticodiac get_value not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_assignment() {
		System.out.println("Peticodiac get_assignment not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse get_proof() {
		System.out.println("Peticodiac get_proof not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_model() {
		System.out.println("Peticodiac get_model not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse get_unsat_core() {
		System.out.println("Peticodiac get_unsat_core not supported");
		return smtConfig.responseFactory.unsupported();
	}

	@Override
	public IResponse pop(int number) {
		//TODO: Figure out if we need to support the pop() method in our benchmark
		System.out.println("Peticodiac pop number = " + number + " with action success");
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse push(int number) {
		//TODO: Figure out if we need to support the push() method in our benchmark
		System.out.println("Peticodiac push number = " + number + " with action success");
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		//TODO: Output the logic used in the comment section of our input format
		System.out.println("Peticodiac set_logic with name = [" + logicName + "] position = <" + pos.toString() + "> with success");
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
		System.out.println("Peticodiac get_option not supported with key = [" + key.toString() + "]");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
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
		System.out.println("Peticodiac get_info not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	protected String encode(IIdentifier id) {
		return id.toString(); // FIXME composite definitions; encode the String?
	}

	@Override 
	public IResponse declare_const(Ideclare_const cmd) {
		//TODO: Output the NUM_VARS
		this.num_vars += 1;
		System.out.println("Peticodiac declare_const has " + num_vars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override 
	public IResponse declare_fun(Ideclare_fun cmd) {
		//TODO: Output the NUM_VARS
		this.num_vars += 1;
		System.out.println("Peticodiac declare_fun has " + num_vars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		//TODO: Output the NUM_VARS
		this.num_vars += 1;
		System.out.println("Peticodiac define_fun has " + num_vars + " variables with cmd = " + cmd.toString());
		return smtConfig.responseFactory.success();
	}
	
	@Override 
	public IResponse declare_sort(Ideclare_sort cmd) {
		System.out.println("Peticodiac declare_sort with cmd = " + cmd.toString() + " not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		System.out.println("Peticodiac define_sort with cmd = " + cmd.toString() + " not supported");
		return smtConfig.responseFactory.unsupported();
	}
	
}
