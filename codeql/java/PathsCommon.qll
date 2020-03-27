import java
import semmle.code.java.controlflow.Guards

abstract class PathCreation extends Expr {
  abstract Expr getInput();
}

boolean isSpringResource(Expr expr) {
  expr.getType().(RefType).getQualifiedName() = "org.springframework.core.io.Resource" and
  result = true
}

/** The class `org.springframework.core.io.Resource`. */
class SpringResource extends Class {
  SpringResource() { this.hasQualifiedName("org.springframework.core.io", "Resource") }
}

/** The class `org.springframework.core.io.ResourceLoader`. */
class SpringResourceLoader extends Class {
  SpringResourceLoader() { this.hasQualifiedName("org.springframework.core.io", "ResourceLoader") }
}

/** The class `org.springframework.context.ApplicationContext`. */
class SpringApplicationContext extends Class {
  SpringApplicationContext() { this.hasQualifiedName("org.springframework.context", "ApplicationContext") }
}


// -----------------------------------------------------------------------------------
// Method access
class SpringGetResource extends PathCreation, MethodAccess {
  SpringGetResource() {
    exists(Method m | m = this.getMethod() |
      // m.getDeclaringType() instanceof SpringResourceLoader and
      m.getDeclaringType().getQualifiedName() = "org.springframework.core.io.ResourceLoader" and
      m.getName() = "getResource"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

class SpringGetRelativeResource extends PathCreation, MethodAccess {
  SpringGetRelativeResource() {
    exists(Method m | m = this.getMethod() |
      // m.getDeclaringType() instanceof SpringResource and
      m.getDeclaringType().getQualifiedName() = "org.springframework.core.io.Resource" and
      m.getName() = "createRelative"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

class ApplicationContextResource extends PathCreation, MethodAccess {
  ApplicationContextResource() {
    exists(Method m | m = this.getMethod() |
      // m.getDeclaringType() instanceof SpringApplicationContext and
      m.getDeclaringType().getQualifiedName() = "org.springframework.context.ApplicationContext" and
      m.getName() = "getResource"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

// -----------------------------------------------------------------------------------
// -----------------------------------------------------------------------------------
//Class consturct
class ClassPathResource extends PathCreation, ClassInstanceExpr {
  ClassPathResource() {
    this.getConstructedType().getQualifiedName() = "org.springframework.core.io.ClassPathResource"
  }

  override Expr getInput() {
    result = this.getAnArgument() and
    // Relevant arguments are those of type `String`.
    result.getType() instanceof TypeString
  }
}

// -----------------------------------------------------------------------------------
// File contetnt from original qlboolean
class PathsGet extends PathCreation, MethodAccess {
  PathsGet() {
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType() instanceof TypePaths and
      m.getName() = "get"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

class FileSystemGetPath extends PathCreation, MethodAccess {
  FileSystemGetPath() {
    exists(Method m | m = this.getMethod() |
      m.getDeclaringType() instanceof TypeFileSystem and
      m.getName() = "getPath"
    )
  }

  override Expr getInput() { result = this.getAnArgument() }
}

class FileCreation extends PathCreation, ClassInstanceExpr {
  FileCreation() { this.getConstructedType() instanceof TypeFile }

  override Expr getInput() {
    result = this.getAnArgument() and
    // Relevant arguments include those that are not a `File`.
    not result.getType() instanceof TypeFile
  }
}

class FileWriterCreation extends PathCreation, ClassInstanceExpr {
  FileWriterCreation() { this.getConstructedType().getQualifiedName() = "java.io.FileWriter" }

  override Expr getInput() {
    result = this.getAnArgument() and
    // Relevant arguments are those of type `String`.
    result.getType() instanceof TypeString
  }
}
// -----------------------------------------------------------------------------------

predicate inWeakCheck(Expr e) {
  // None of these are sufficient to guarantee that a string is safe.
  exists(MethodAccess m, Method def | m.getQualifier() = e and m.getMethod() = def |
    def.getName() = "startsWith" or
    def.getName() = "endsWith" or
    def.getName() = "isEmpty" or
    def.getName() = "equals"
  )
  or
  // Checking against `null` has no bearing on path traversal.
  exists(EqualityTest b | b.getAnOperand() = e | b.getAnOperand() instanceof NullLiteral)
}

// Ignore cases where the variable has been checked somehow,
// but allow some particularly obviously bad cases.
predicate guarded(VarAccess e) {
  exists(PathCreation p | e = p.getInput()) and
  exists(ConditionBlock cb, Expr c |
    cb.getCondition().getAChildExpr*() = c and
    c = e.getVariable().getAnAccess() and
    cb.controls(e.getBasicBlock(), true) and
    // Disallow a few obviously bad checks.
    not inWeakCheck(c)
  )
}
