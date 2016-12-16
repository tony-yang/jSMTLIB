package org.smtlib.test;

import java.util.LinkedList;
import java.util.List;

import org.smtlib.IResponse;
import org.smtlib.Log;


public class JUnitListener implements Log.IListener {
	
	List<IResponse> msgs = new LinkedList<IResponse>();
	
	@Override
	public void logError(IResponse.IError msg) {
		this.msgs.add(msg);
	}

	@Override
	public void logOut(String msg) {
	}

	@Override
	public void logOut(IResponse result) {
	}

	@Override
	public void logError(String msg) {
	}

	@Override
	public void logDiag(String msg) {
	}

	@Override
	public void indent(String msg) {
	}
}