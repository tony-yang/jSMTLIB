package org.smtlib.test;

import java.util.List;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.*;
import org.smtlib.IResponse;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.Utils;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.impl.Response;

@RunWith(ParameterizedWithNames.class)
public class InfoOptions  extends LogicTests {

	boolean isTest;
	
    public InfoOptions(String solvername, String version) {
    	this.solvername = solvername; 
    	this.version = version;
    	this.isTest = "test".equals(solvername);
    }
    
    public void checkGetInfo(String keyword, String expected) {
		IResponse r = doCommand("(get-info " + keyword + ")");
		if (r instanceof Response.Seq) {
			List<IAttribute<?>> list = ((Response.Seq)r).attributes();
			Object o = list.get(0).attrValue();
			if (o instanceof IStringLiteral) {
				String n = ((IStringLiteral)o).value();
				if (expected != null) Assert.assertEquals(expected,n);
				else Assert.assertTrue(n != null);
				return;
			}
		}
		Assert.assertTrue("Response is wrong " + r,false);
    }
    
	@Test
	public void checkAuthors() {
		checkGetInfo(":authors",
				(solvername.equals("test") ? "David R. Cok"
				: solvername.equals("simplify") ? "David Detlefs and Greg Nelson and James B. Saxe"
				: solvername.startsWith("yices") ? "Bruno Dutertre"
				: solvername.equals("cvc") ? "Clark Barrett, Cesare Tinelli, and others"
				: solvername.equals("cvc4") ? null // Long text that we don't check // TODO
				: solvername.equals("cvc4b") ? null // Long text that we don't check // TODO
				: solvername.startsWith("z3") ? "Leonardo de Moura and Nikolaj Bjorner"
				: "???" )
				);
	}
    
	@Test
	public void checkVersion() {
		checkGetInfo(":version",
				(solvername.equals("test") ? "0.0"
				: solvername.equals("simplify") ? "1.5.4"
				: solvername.equals("yices") ? "1.0.28"
				: solvername.equals("yices2") ? "2.3.1"
				: solvername.equals("cvc") ? "2.2"
				: solvername.equals("cvc4") ? "1.4"
				: solvername.equals("cvc4b") ? "1.5-prerelease"
				: solvername.equals("z3_4_3") ? "4.3"
				: solvername.equals("z3_4_4") ? "4.4.0"
				: solvername.equals("z3_2_11") ? "2.11"
				: "???" )
				);
	}
    
	@Test
	public void checkName() {
		checkGetInfo(":name",
						solvername.equals("test") ? "test"
						: solvername.equals("simplify") ? "simplify"
						: solvername.equals("yices") ? "yices"
						: solvername.equals("yices2") ? "Yices"
						: solvername.equals("cvc") ? "CVC3"
						: solvername.startsWith("cvc4") ? "cvc4"
						: solvername.equals("z3_4_3") ? "Z3"
						: solvername.equals("z3_4_4") ? "Z3"
						: solvername.equals("z3_2_11") ? "z3-2.11"
						: "???" );
	}
    
	// FIXME - no sure what this really should be
//	@Test
//	public void checkErrorBehavior() {
//		doCommand("(get-info :error-behavior)","(:error-behavior continued-execution )");
//	}
	
	// FIXME - need a test for :reason-unknown

	@Test
	public void checkSetName() {
		doCommand("(set-info :name \"xx\")",
//				solvername.equals("z3_4_4") ? "success" :
				solvername.equals("yices2") ? "(error \"can't overwrite :name\")" :
				"(error \"Setting the value of a pre-defined keyword is not permitted: :name\")");
	}
	
	@Test
	public void checkSetAuthors() {
		doCommand("(set-info :authors \"xx\")",
//				solvername.equals("z3_4_4") ? "success" :
				solvername.equals("yices2") ?
				"(error \"can't overwrite :authors\")" :
				"(error \"Setting the value of a pre-defined keyword is not permitted: :authors\")");
	}
	
	@Test
	public void checkPrintSuccess() {
		doCommand("(get-option :print-success)", 
				"true"
				);
	}
	
	@Test
	public void checkSetPrintSuccess() {
		doCommand("(set-option :print-success false)", 
				"");
		doCommand("(get-option :print-success)", 
				"false");
		doCommand("(set-option :print-success true)", 
				"success");
		doCommand("(get-option :print-success)", 
				"true");
	}
	
	@Test
	public void checkRegularOutput() {
		// The correct result is a quote-delimited string
		doCommand("(get-option :regular-output-channel)", 
				solvername.startsWith("cvc4")? "unsupported" :
						"\"stdout\""
				);
	}
	
	@Test
	public void checkSetRegularOutput() {
		Assume.assumeTrue(false);
		doCommand("(set-option :regular-output-channel \"test-output\")", "success"); // FIXME - writes success to test-output? - hangs for z3_4_3 ?
		doCommand("(get-option :regular-output-channel)", "\"test-output\"");
		doCommand("(set-option :regular-output-channel \"stdout\")", "success");
		doCommand("(get-option :regular-output-channel)", "\"stdout\"");
	}
	
	@Test
	public void checkDiagnosticOutput() {
		// The correct result is a quote-delimited string
		doCommand("(get-option :diagnostic-output-channel)", 
				solvername.startsWith("cvc4")? "unsupported" :
//				solvername.equals("z3_4_4")? "stderr" :
						"\"stderr\""
				);
	}
	
	@Test
	public void checkSetDiagnosticOutput() {
		Assume.assumeTrue(false);
		doCommand("(set-option :regular-diagnostic-channel \"test-output\")", "success"); // FIXME - writes success to test-output? - hangs for z3_4_3 ?
		doCommand("(get-option :regular-diagnostic-channel)", "\"test-output\"");
		doCommand("(set-option :regular-diagnostic-channel \"stderr\")", "success");
		doCommand("(get-option :regular-diagnostic-channel)", "\"stderr\"");
	}
	
	@Test
	public void checkInteractiveMode() {
		boolean supported = !solvername.equals("yices2");
		doCommand("(get-option :interactive-mode)", 
				!supported ? "unsupported" : "cvc4".equals(solvername) ? "true" : "false"
				);
	}
	
	@Test
	public void checkSetInteractiveMode() {
		doCommand("(set-option :interactive-mode true)", 
			    solvername.equals("yices2") ? "unsupported" :
				"success");
		doCommand("(get-option :interactive-mode)", 
			    solvername.equals("yices2") ? "unsupported" :
				"true");
		doCommand("(set-option :interactive-mode false)", 
			    solvername.equals("yices2") ? "unsupported" :
				"success");
		doCommand("(get-option :interactive-mode)", 
			    solvername.equals("yices2") ? "unsupported" :
				"false");
	}
	
	@Test
	public void checkProduceProofs() {
		boolean supported = !solvername.equals("yices2");
		doCommand("(get-option :produce-proofs)", 
				!supported ? "unsupported" : "false"
				);
	}
	
	@Test
	public void checkSetProduceProofs() {
		doCommand("(set-option :produce-proofs true)", 
				isTest ? "success" 
						: solvername.startsWith("cvc4")? "(error \"Error in option parsing: option `produce-proofs' requires a proofs-enabled build of CVC4; this binary was not built with proof support\")"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)", 
				isTest ? "true"
			    : solvername.equals("yices2") ? "unsupported"
				:  "false");
		doCommand("(set-option :produce-proofs false)", 
				isTest ? "success" 
						: solvername.startsWith("cvc4")? "success"
						:  "unsupported");
		doCommand("(get-option :produce-proofs)", 
			    solvername.equals("yices2") ? "unsupported" :
				"false");
	}
	
	@Test
	public void checkProduceModels() {
		doCommand("(get-option :produce-models)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceModels() {
		boolean support = isTest || solvername.startsWith("z3") || "cvc".equals(solvername) || "cvc4".equals(solvername)  || "cvc4b".equals(solvername) || "yices2".equals(solvername);
		doCommand("(set-option :produce-models true)", 
				support? "success" 
						: "unsupported");
		doCommand("(get-option :produce-models)", 
				support? "true" 
						:  "false");
		doCommand("(set-option :produce-models false)", 
				support? "success" 
						: "unsupported");
		doCommand("(get-option :produce-models)", 
				"false");
	}
	
	@Test
	public void checkProduceAssignments() {
		doCommand("(get-option :produce-assignments)", 
				"false"
				);
	}
	
	@Test
	public void checkSetProduceAssignments() {
		boolean supported = isTest || solvername.startsWith("cvc4") || solvername.equals("yices2") ;
		
		doCommand("(set-option :produce-assignments true)",
					supported? "success" 
						: "unsupported");
		doCommand("(get-option :produce-assignments)", 
				supported? "true" 
						:"false");
		doCommand("(set-option :produce-assignments false)",
						supported? "success" 
						: "unsupported");
		doCommand("(get-option :produce-assignments)", 
				"false");
	}
	
	@Test
	public void checkProduceUnsatCores() {
		boolean unsupported = solvername.equals("yices2");
		doCommand("(get-option :produce-unsat-cores)", 
				unsupported ? "unsupported" : "false"
				);
	}
	
	@Test
	public void checkSetProduceUnsatCores() {
		boolean supported = isTest;
		doCommand("(set-option :produce-unsat-cores true)",
				supported ? "success" 
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", 
				solvername.equals("yices2") ? "unsupported" :
				supported? "true" 
						: "false");
		doCommand("(set-option :produce-unsat-cores false)",
				supported? "success" 
						: solvername.startsWith("cvc4") ? "success"
						:  "unsupported");
		doCommand("(get-option :produce-unsat-cores)", 
				solvername.equals("yices2") ? "unsupported" :
				"false");
	}
	
	@Test
	public void checkExpandDefinitions() {
		// What's the difference between feature supported == false and feature supported = unsupported?
		// This test is failing on my mac and I'm going to change the result to unsupported.
		boolean supported = smt.smtConfig.isVersion(SMT.Configuration.SMTLIB.V20) && !solvername.equals("yices2") && !solvername.equals("test");
		doCommand("(get-option :expand-definitions)", 
				supported ? "false" : "unsupported"
				);
	}
		
	@Test
	public void checkSetExpandDefinitions() {
		boolean supported = (smt.smtConfig.isVersion(SMT.Configuration.SMTLIB.V20)
							|| smt.smtConfig.isVersion(SMT.Configuration.SMTLIB.V25))
							&& !solvername.equals("yices2");
		doCommand("(set-option :expand-definitions true)", 
				!supported ? "unsupported" : "success");
		doCommand("(get-option :expand-definitions)", 
				!supported ? "unsupported" : "true");
		doCommand("(set-option :expand-definitions false)", 
				!supported ? "unsupported" : "success");
		doCommand("(get-option :expand-definitions)", 
				!supported ? "unsupported" : "false");
	}
	
	@Test
	public void checkSetExpandDefinitions2() {
		Assume.assumeTrue(smtlib_version >= v25);
		doCommand("(set-option :expand-definitions true)", "success");
		doCommand("(get-option :expand-definitions)", 
				(solvername.startsWith("z3")) ? "true" : "unsupported");
		doCommand("(set-option :expand-definitions false)", "success");
		doCommand("(get-option :expand-definitions)", 
				(solvername.startsWith("z3")) ? "false" : "unsupported");
	}
	
	@Test
	public void checkRandomSeed() {
		Assume.assumeTrue(!"cvc4".equals(solvername)); // FIXME - cvc4 does not handle randome seed correctly
		doCommand("(get-option :random-seed)", 
				"0"
				);
	}
	
	@Test
	public void checkSetRandomSeed() {
		Assume.assumeTrue(!"cvc4".equals(solvername)); // FIXME - cvc4 does not handle randome seed correctly
		doCommand("(set-option :random-seed 1)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc4".equals(solvername) ? "0" :
				"1");
		doCommand("(set-option :random-seed 2)", "success");
		doCommand("(get-option :random-seed)", 
				"cvc4".equals(solvername) ? "0" :
				"2");
	}
	
	@Test
	public void checkVerbosity() {
		doCommand("(get-option :verbosity)", 
				"0"
				);
	}
	
	@Test
	public void checkSetVerbosity() {
		doCommand("(set-option :verbosity 1)", 
				"success");
		doCommand("(get-option :verbosity)", 
				"1");
		doCommand("(set-option :verbosity 2)", 
				"success");
		doCommand("(get-option :verbosity)", 
				"2");
	}
}

