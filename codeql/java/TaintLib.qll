/**
 *
 * @description extended predict for taint propagation
 */

import java
import semmle.code.java.dataflow.FlowSources
import DataFlow

/**
 * Holds if `n1` to `n2` is a dataflow step that an assign to expression,
 * ie. String var = method(tainted), String var = tools.method(tainted)
 */
predicate methodResult(ExprNode n1, ExprNode n2) {
  exists(MethodAccess ma |
    //str = method(tainted)
    //str = method(tainted).method()
    n1.asExpr() = ma.getAChildExpr() and
    (n2.asExpr() = ma or n2.asExpr() = ma.getQualifier())
  )
}

predicate classInitialization(ExprNode n1, ExprNode n2) {
  exists(ClassInstanceExpr clse | clse.getAnArgument() = n1.asExpr() and n2.asExpr() = clse)
}
