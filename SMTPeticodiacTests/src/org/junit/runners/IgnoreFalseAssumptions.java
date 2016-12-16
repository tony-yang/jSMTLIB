package org.junit.runners;

import org.junit.Ignore;
import org.junit.internal.AssumptionViolatedException;
import org.junit.internal.runners.model.EachTestNotifier;
import org.junit.runner.Description;
import org.junit.runner.notification.RunNotifier;
import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.Statement;

public class IgnoreFalseAssumptions extends BlockJUnit4ClassRunner {
    
    public IgnoreFalseAssumptions(Class<?> klass) throws InitializationError {
        super(klass);
    }

    @Override
    protected void runChild(final FrameworkMethod method, RunNotifier notifier) {
        Description description= describeChild(method);
        if (method.getAnnotation(Ignore.class) != null) {
            notifier.fireTestIgnored(description);
        } else {
            //runLeaf(methodBlock(method), description, notifier);
            Statement statement = methodBlock(method);
            EachTestNotifier eachNotifier= new EachTestNotifier(notifier, description);
            eachNotifier.fireTestStarted();
            try {
                statement.evaluate();
            } catch (AssumptionViolatedException e) {
                //eachNotifier.addFailedAssumption(e);
                eachNotifier.fireTestIgnored();
            } catch (Throwable e) {
                eachNotifier.addFailure(e);
            } finally {
                eachNotifier.fireTestFinished();
            }
        }
    }


}
