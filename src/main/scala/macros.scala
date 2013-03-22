package org.brianmckenna.wartremover

import language.experimental.{ macros => scalaMacros }
import reflect.macros.Context

object macros {
  def safe[A](expr: A) = macro safeImpl[A]

  def safeImpl[A](c: Context)(expr: c.Expr[A]): c.Expr[A] = {
    import c.universe._

    def isIgnoredStatement(tree: Tree) = tree match {
      // Scala creates synthetic blocks with <init> calls on classes.
      // The calls return Object so we need to ignore them.
      case Apply(Select(_, nme.CONSTRUCTOR), _) => true
      case _ => false
    }

    object NoNonUnitStatements extends Traverser {
      def checkUnitLike(statements: List[Tree]) {
        statements.foreach { stat =>
          val unitLike = stat.isEmpty || stat.tpe == null || stat.tpe =:= typeOf[Unit] || stat.isDef || isIgnoredStatement(stat)
          if (!unitLike)
            c.error(stat.pos, "Statements must return Unit")
        }
      }

      override def traverse(tree: Tree) {
        tree match {
          case Block(statements, _) =>
            checkUnitLike(statements)
          case ClassDef(_, _, _, Template((_, _, statements))) =>
            checkUnitLike(statements)
          case ModuleDef(_, _, Template((_, _, statements))) =>
            checkUnitLike(statements)
          case _ =>
        }
        super.traverse(tree)
      }
    }
    NoNonUnitStatements.traverse(expr.tree)

    object NoNull extends Traverser {
      override def traverse(tree: Tree) {
        tree match {
          case Literal(Constant(null)) =>
            c.error(tree.pos, "null is disabled")
          case _ =>
        }
        super.traverse(tree)
      }
    }
    NoNull.traverse(expr.tree)

    /**
     * Rudimentary implementation of safe (aka well-defined) traits as described here:
     * http://blog.rintcius.nl/post/scala-traits-as-well-defined-modules-and-a-crime-scene-investigation.html
     */
    object SafeTraits extends Traverser {

      def getAbstractVals(statement: Tree): List[DefDef] = statement match {
        case d@DefDef(modifiers, name, _, _, _, EmptyTree) if modifiers.hasFlag(Flag.DEFERRED) => {
          //c.echo(statement.pos, "Abstract val: " + name)
          List(d)
        }
        case _ => Nil
      }

      def getConcreteVals(statement: Tree): List[ValDef] = statement match {
        case v@ValDef(modifiers, name, _, _) if !modifiers.hasFlag(Flag.LAZY) => {
          //c.echo(statement.pos, "Concrete non lazy val: " + name)
          List(v)
        }
        case _ => Nil
      }

      def getInits(statement: Tree): List[Apply] = statement match {
        case a@Apply(_, _) => {
          //c.echo(statement.pos, "Init found")
          List(a)
        }
        case _ => Nil
      }

      case class QualifiedName(qualifier: TypeName, tpe: Type, name: Name)

      class RefsCollector(namesToCollect: List[QualifiedName]) extends Traverser {
        //TODO how to get rid of var here?
        var collected = collection.mutable.Seq[Select]()

        //TODO this is very incomplete; just checking on name for now
        def selects(s: Select): Option[Select] = namesToCollect find (_.name == s.name) map (x => s)

        override def traverse(tree: Tree) {
          tree match {
            case s@Select(q, n) => collected = collected ++ selects(s)
            case _ =>
          }
          super.traverse(tree)
        }
      }

      def allRefsToAbstractVals(tree: Tree, enclosingTypeName: TypeName, abstractVals: List[DefDef]): List[Select] = {
        val collector = new RefsCollector(abstractVals map (defDef => QualifiedName(enclosingTypeName, defDef.tpe, defDef.name)))
        collector.traverse(tree)
        collector.collected.toList
      }

      override def traverse(tree: Tree) {
        tree match {
          case ClassDef(_, typeName, _, Template((_, _, statements))) => {
            val abstractVals: List[DefDef] = statements flatMap (getAbstractVals(_))
            val concreteVals: List[ValDef] = statements flatMap (getConcreteVals(_))
            val inits: List[Apply] = statements flatMap (getInits(_))

            val illegalRefsFromVal = concreteVals map (_.rhs) flatMap (allRefsToAbstractVals(_, typeName, abstractVals))
            illegalRefsFromVal.foreach { ref =>
              c.error(ref.pos, "Value refers to abstract value")
            }

            val illegalRefsFromInit = inits flatMap (_.args) flatMap (allRefsToAbstractVals(_, typeName, abstractVals))
            illegalRefsFromInit.foreach { ref =>
              c.error(ref.pos, "Init code refers to abstract value")
            }
          }
          case _ =>
        }
        super.traverse(tree)
      }
    }
    SafeTraits.traverse(expr.tree)

    object NoVar extends Traverser {
      override def traverse(tree: Tree) {
        tree match {
          case ValDef(m, _, _, _) if m.hasFlag(Flag.MUTABLE) =>
            c.error(tree.pos, "var is disabled")
          case _ =>
        }
        super.traverse(tree)
      }
    }
    NoVar.traverse(expr.tree)

    object NoNothing extends Traverser {
      val nothingSymbol = typeOf[Nothing].typeSymbol
      override def traverse(tree: Tree) {
        def error() = c.error(tree.pos, "Inferred type containing Nothing from assignment")
        tree match {
          case ValDef(_, _, tpt, _) if tpt.tpe.contains(nothingSymbol) =>
            error()
          case DefDef(_, _, _, _, tpt, _) if tpt.tpe.contains(nothingSymbol) =>
            error()
          case _ =>
        }
        super.traverse(tree)
      }
    }
    NoNothing.traverse(expr.tree)

    expr
  }
}
