/**
 *Author: Weijie Huo, Minhao Zhang
*/
package bixie.checker.inconsistency_checker;

import java.util.HashSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Random;

import ap.parser.IFormula;
import bixie.Bixie;
import bixie.checker.report.MyReport;
import bixie.checker.report.Report;
import bixie.checker.transition_relation.TransitionRelation;
import bixie.prover.Prover;
import bixie.prover.ProverExpr;
import bixie.prover.ProverResult;
import bixie.prover.princess.PrincessProver;
import bixie.util.Log;
import boogie.controlflow.AbstractControlFlowFactory;
import boogie.controlflow.BasicBlock;
import boogie.controlflow.CfgAxiom;
import boogie.controlflow.CfgProcedure;
import boogie.controlflow.util.PartialBlockOrderNode;
import boogie.ast.Attribute;
import boogie.ast.location.ILocation;
import boogie.controlflow.statement.CfgStatement;
import bixie.checker.reportprinter.SourceLocation;
import boogie.controlflow.statement.CfgAssertStatement;
import boogie.controlflow.statement.CfgAssignStatement;
import boogie.controlflow.statement.CfgAssumeStatement;
import boogie.controlflow.statement.CfgCallStatement;
import boogie.controlflow.statement.CfgHavocStatement;
import boogie.controlflow.expression.CfgBooleanLiteral;

/**
* MyNode is a node of the new graph we build,
* It contians more information than the control flow graph
* i.e predecessors and ancestors
* @author  Weijie Huo, Minhao Zhang
* @version 1.0
* @since   2015-11-24
*/
class MyNode {
  private BasicBlock b;
  //successors:
  //contains all the childs node
  private Set<MyNode> successors;
  //predecessors
  private Set<MyNode> predecessors;

  public MyNode(BasicBlock b) {
    this.b = b;
    successors = new HashSet<MyNode>();
    predecessors = new HashSet<MyNode>();
  }
  //Setter
  public void addSuccessors(MyNode nd) {
    successors.add(nd);
  }
  public void addPredecessors(MyNode nd) {
    predecessors.add(nd);
  }
  //Getter
  public BasicBlock getBlock() {
    return b;
  }
  public Set<MyNode> getSuccessors() {
    return successors;
  }
  public Set<MyNode> getPredecessors() {
    return predecessors;
  }
}

/**
* MyChecker is the main class of the algorithm that analysis
* whether the given proceduce contains infeasible code
* @author  Weijie Huo, Minhao Zhang
* @version 1.0
* @since   2015-11-24
*/
public class MyChecker extends AbstractChecker {
  boolean debugMode = false;
  TransitionRelation tr;

  Set<BasicBlock> allReachableBlocks = new HashSet<BasicBlock>();
  Set<BasicBlock> unCoveredBlocks = new HashSet<BasicBlock>();
  Map<BasicBlock, MyNode> blockToMyNode = new HashMap<BasicBlock, MyNode>();
  Map<Integer, List<BasicBlock>> lineToBlocks = new HashMap<Integer, List<BasicBlock>>();
  Map<String, BasicBlock> labelToBlock = new HashMap<String, BasicBlock>();

  public MyChecker(AbstractControlFlowFactory cff, CfgProcedure p) {
		super(cff, p);
	}

  /**
  * runAnalysis is the main procedure of the algorithm that analysis
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  @Override
	public Report runAnalysis(Prover prover) {
    this.tr = new TransitionRelation(this.procedure, this.cff, prover);
    this.prover = prover;

    prover.push();
    addVertificationCondition();
    addPreCondition();

    MyNode root = buildGraph(this.procedure.getRootNode(), blockToMyNode, new ArrayList<MyNode>(), 0);

    for(MyNode mN : blockToMyNode.values()) {
      unCoveredBlocks.add(mN.getBlock());
      labelToBlock.put(mN.getBlock().getLabel(), mN.getBlock());
      allReachableBlocks.add(mN.getBlock());
    }

    Set<Integer> infeasibleCandidates = getInfeasibleCodeCandidate(allReachableBlocks, lineToBlocks);
    Set<Integer> allLines = new HashSet<Integer>(infeasibleCandidates);

    removeCoveredBlock(blockToMyNode.get(this.procedure.getRootNode()), unCoveredBlocks, infeasibleCandidates, new HashSet<MyNode>(), 0);

    prover.pop();

    Map<Integer, Set<Integer>> contradictSet = new HashMap<Integer, Set<Integer>>();
    findContradict(infeasibleCandidates, contradictSet);

    MyReport myReport = Bixie.myReport;
    myReport.setUnreachableLines(infeasibleCandidates);
    myReport.setReasonMap(contradictSet);

    Report report = new Report(tr);
    //  report.reportInconsistentCode(1, unCoveredBlocks);
    return report;
	}

  /**
  * Print Procedure
  * @author  Weijie Huo, Minhao Zhang
  * return ture if success
  * otherwise false
  */
  public boolean printProcedure() {
    if(this.procedure == null) {
      return false;
    }
    System.out.println(this.procedure.toString());
    return true;
  }

  /**
  * add preCondition to the prover stack
  * @author  Weijie Huo, Minhao Zhang
  * return ture if success
  * otherwise false
  */
  public boolean addPreCondition() {
    if(this.prover == null) {
      return false;
    }
    this.prover.addAssertion(tr.getRequires());
    this.prover.addAssertion(tr.getEnsures());
    return true;
  }

  /**
  * add vertification condition to the prover stack
  * @author  Weijie Huo, Minhao Zhang
  * return ture if success
  * otherwise false
  */
  public boolean addVertificationCondition() {
    if(this.prover == null) {
      return false;
    }
    for (Entry<CfgAxiom, ProverExpr> entry : tr.getPreludeAxioms()
				.entrySet()) {
			this.prover.addAssertion(entry.getValue());
		}
    return true;
  }

  /**
  * Build the graph i.e. Node: MyNode
  * Note: the predecessors are used to analysis the cause
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  * return the root of the graph
  */
  public MyNode buildGraph(BasicBlock b, Map<BasicBlock, MyNode> blockToMyNode, List<MyNode> curPath, int t) {
    //Only concerns the block that are in effectual set
    MyNode cur;
    boolean reachBefore = false;
    if(blockToMyNode.containsKey(b)) {
      cur = blockToMyNode.get(b);
      reachBefore = true;
    } else {
      cur = new MyNode(b);
      blockToMyNode.put(b, cur);
    }
    if(curPath.size() > 0) {
        cur.addPredecessors(curPath.get(curPath.size() - 1));
    }
    if(reachBefore) {
      return cur;
    }
    //If there is a loop in the control graph
    if(curPath.contains(cur)) {
      return null;
    }
    if(debugMode) {
      //For debuging
      for(int i = 0; i < t; i++) {
        System.out.print("\t");
      }
      System.out.println(b.getLabel());
    }

    Set<BasicBlock> successors = b.getSuccessors();
    curPath.add(cur);
    for(BasicBlock suc : successors) {
      MyNode child = buildGraph(suc, blockToMyNode, curPath, t + 1);
      if(child != null) {
        cur.getSuccessors().add(child);
      }
    }
    curPath.remove(curPath.size() - 1);
    return cur;
  }

  /**
  * get Infeasible Code Candidates
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  * return a set of infeasible code candidates
  */
  public Set<Integer> getInfeasibleCodeCandidate(Set<BasicBlock> blocks, Map<Integer, List<BasicBlock>> lineToBlocks) {
    Set<Integer> infeasibleCandidates = new HashSet<Integer>();
    for(BasicBlock bl : blocks) {
      List<CfgStatement> listSt = bl.getStatements();
      for(CfgStatement statement : listSt) {
        Attribute[] attrArr = statement.getAttributes();
        if(attrArr == null) {
          continue;
        }
        SourceLocation loc = SourceLocation.readSourceLocationFromAttributes(attrArr);
        if(loc != null && loc.StartLine >= 0) {
          infeasibleCandidates.add(loc.StartLine);
          if(!lineToBlocks.containsKey(loc.StartLine)) {
            lineToBlocks.put(loc.StartLine, new ArrayList<BasicBlock>());
          }
          lineToBlocks.get(loc.StartLine).add(bl);
        }
      }
    }
    return infeasibleCandidates;
  }

  /**
  * The removeCoveredBlock use Dfs to explored the path.
  * Parameter infeasibleCandidates remove all the lines that
  * can be covered by feasible path so far.
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public void removeCoveredBlock(MyNode cur, Set<BasicBlock> unCoveredBlocks, Set<Integer> infeasibleCandidates, Set<MyNode> checked, int t) {
    //Sanity Check
    if(cur == null) {
      return;
    }
    if(checked.contains(cur)) {
      return;
    }
    checked.add(cur);
    prover.push();
    //Get Statements in the current block
    List<ProverExpr> stmts = tr.statements2proverExpression(cur.getBlock().getStatements());
    ProverExpr[] conj = stmts.toArray(new ProverExpr[stmts.size()]);
    prover.addAssertion(this.prover.mkAnd(conj));

    ProverResult res = prover.checkSat(true);

    //For Debug
    if(debugMode) {
      for(int i = 0; i < t; i++) {
        System.out.print("\t");
      }
      for(int i = 0; i < conj.length; i++) {
        System.out.print(conj[i].toString() + " ");
      }
      if(res == ProverResult.Sat) {
        System.out.print("\t|\t" + cur.getBlock().getLabel() + " true");
      } else {
        System.out.print("\t|\t" + cur.getBlock().getLabel() + " false");
      }
      System.out.println();
    }

    if(res == ProverResult.Sat) {
      unCoveredBlocks.remove(cur.getBlock());
      BasicBlock curBlock = cur.getBlock();
      String blockLabel = curBlock.getLabel();
      for(CfgStatement statement : curBlock.getStatements()) {
        Attribute[] attrArr = statement.getAttributes();
        if(attrArr == null) {
          continue;
        }
        SourceLocation loc = SourceLocation.readSourceLocationFromAttributes(attrArr);
        if(loc != null && loc.StartLine >= 0) {
          infeasibleCandidates.remove(loc.StartLine);
        }
      }
    } else {
      prover.pop();
      return;
    }
    for(MyNode child : cur.getSuccessors()) {
      removeCoveredBlock(child, unCoveredBlocks, infeasibleCandidates, checked, t + 1);
    }

    prover.pop();
  }

  /**
  * printBlockLinesWithSet
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public String getStatementType(CfgStatement statement) {
    if(statement instanceof CfgAssertStatement) {
      return "CfgAssertStatement";
    } else if(statement instanceof CfgAssignStatement) {
      return "CfgAssignStatement";
    } else if(statement instanceof CfgAssumeStatement) {
      return "CfgAssumeStatement";
    } else if(statement instanceof CfgCallStatement) {
      return "CfgCallStatement";
    } else if(statement instanceof CfgHavocStatement) {
      return "CfgHavocStatement";
    } else {
      return "no specific type";
    }
  }

  /**
  * printBlockLinesWithSet
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public void printBlockLinesWithSet(Set<BasicBlock> blocks) {
    for(BasicBlock bl : blocks) {
      List<CfgStatement> listSt = bl.getStatements();
      for(CfgStatement statement : listSt) {
        Attribute[] attrArr = statement.getAttributes();
        if(attrArr == null) {
          System.out.println(getStatementType(statement) + " | no attrArr");
          System.out.println(statement.toString());
          continue;
        }
        SourceLocation loc = SourceLocation.readSourceLocationFromAttributes(attrArr);
        if(loc == null) {
          System.out.println(getStatementType(statement) + " | location has not been initialized..");
          System.out.println(statement.toString());
        } else {
          System.out.println(getStatementType(statement) + " | start: " + loc.StartLine + " end: " + loc.EndLine);
        }
      }
    }
  }

  /**
  * findContradict will just call the analyzeContradiction for any basicBlocks that are found to be infeasible
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public void findContradict(Set<Integer> infeasibleCandidates, Map<Integer, Set<Integer>> result) {
    for(int infeasibleLine : infeasibleCandidates) {
      result.put(infeasibleLine, new HashSet<Integer>());
      for(BasicBlock bl : lineToBlocks.get(infeasibleLine)) {
        //System.out.println(infeasibleLine);
        analyzeContradiction(bl, infeasibleLine, result);
      }
    }
  }

  /**
  * analyzeContradiction use backward checking to find the corresponding line of code that cause the path infeasible.
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public void analyzeContradiction(BasicBlock bl, int infeasibleLine, Map<Integer, Set<Integer>> result) {
    List<CfgStatement> statementsPath = new ArrayList<CfgStatement>();
    List<ProverExpr> proverExprPath = new ArrayList<ProverExpr>();
    MyNode curNode = blockToMyNode.get(bl);
    for(MyNode predecessor : curNode.getPredecessors()) {
      prover.push();
      analyzeHelper(predecessor, statementsPath, proverExprPath, infeasibleLine, result, new HashMap<CfgStatement, CfgStatement>());
      prover.pop();
    }
  }

  /**
  * analyzeHelper is a helper function of analyzeContradiction. It just dfs backward to find the cloest lines that
  * cause the unreachable/infeasible
  * @author  Weijie Huo, Minhao Zhang
  * @version 1.0
  * @since   2015-11-24
  */
  public void analyzeHelper(MyNode curNode, List<CfgStatement> statementsPath, List<ProverExpr> proverExprPath, int infeasibleLine, Map<Integer, Set<Integer>> result, Map<CfgStatement, CfgStatement> toAssertion) {
    List<CfgStatement> stmts = curNode.getBlock().getStatements();
    for (int i = 0; i < stmts.size(); i++) {
      CfgStatement s = stmts.get(i);
      if (s instanceof CfgAssumeStatement
          && ((CfgAssumeStatement)s).getCondition() instanceof CfgBooleanLiteral
          && ((CfgBooleanLiteral)((CfgAssumeStatement)s).getCondition()).getValue()==true) {
        //do nothing
        continue;
      }
      if (s instanceof CfgAssertStatement
          && ((CfgAssertStatement)s).getCondition() instanceof CfgBooleanLiteral
          && ((CfgBooleanLiteral)((CfgAssertStatement)s).getCondition()).getValue()==true) {
        //do nothing
        continue;
      }
      ProverExpr pe = tr.statement2proverExpression(s);
      if(s instanceof CfgAssumeStatement) {
        if(i == 0) {
          String target = curNode.getBlock().getLabel();
          if(target.length() > 4) {
            target = target.substring(0, target.length() - 5);
          }
          //System.out.println(target);
          // while(target.length() > 4 && target.substring(target.length() - 4, target.length()).equals("join")) {
          //   target = target.substring(0, target.length() - 5);
          //   //System.out.println(target);
          // }
          if(labelToBlock.get(target) != null) {
            List<CfgStatement> targetStmts = labelToBlock.get(target).getStatements();
            if(targetStmts.size() > 0 && targetStmts.get(targetStmts.size() - 1) instanceof CfgAssertStatement) {
              toAssertion.put(s, targetStmts.get(targetStmts.size() - 1));
            }
          }
        } else if(i - 1 >= 0 && stmts.get(i - 1) instanceof CfgAssertStatement) {
          toAssertion.put(s, stmts.get(i - 1));
        }
      } else {
        if(i - 1 >= 0 && stmts.get(i - 1) instanceof CfgAssertStatement) {
            toAssertion.put(s, stmts.get(i - 1));
        }
      }
      statementsPath.add(s);
      proverExprPath.add(pe);
    }
    if(curNode.getPredecessors().size() == 0) {
      for(int i = 0; i < statementsPath.size(); i++) {
        boolean contradictFounded = false;
        CfgStatement iAssertStat = toAssertion.get(statementsPath.get(i));
        Attribute[] iAttrArr = (iAssertStat == null? null : iAssertStat.getAttributes());
        SourceLocation iLoc = null;
        if(iAttrArr != null) {
          iLoc = SourceLocation.readSourceLocationFromAttributes(iAttrArr);
        }
        if(iLoc != null && iLoc.StartLine >= 0) {
          for(int j = i + 1; j < statementsPath.size(); j++) {
            CfgStatement jAssertStat = toAssertion.get(statementsPath.get(j));
            Attribute[] jAttrArr = (jAssertStat == null? null : jAssertStat.getAttributes());
            SourceLocation jLoc = null;
            if(jAttrArr != null) {
              jLoc =  SourceLocation.readSourceLocationFromAttributes(jAttrArr);
            }
            if(jLoc != null && jLoc.StartLine >= 0) {
              prover.push();
              prover.addAssertion(proverExprPath.get(i));
              prover.addAssertion(proverExprPath.get(j));
              ProverResult res = prover.checkSat(true);
              if(res != ProverResult.Sat) {
                contradictFounded = true;
                result.get(infeasibleLine).add(iLoc.StartLine);
                // System.out.println(iLoc.StartLine + " " + statementsPath.get(i).toString());
                // System.out.println(jLoc.StartLine + " " + statementsPath.get(j).toString());
                // System.out.println("-----------------------");
                result.get(infeasibleLine).add(jLoc.StartLine);
                prover.pop();
                break;
              }
              prover.pop();
            }
          }
        }
        if(contradictFounded) {
          break;
        }
      }
      return;
    }
    for(MyNode predecessor : curNode.getPredecessors()) {
      analyzeHelper(predecessor, statementsPath, proverExprPath, infeasibleLine, result, toAssertion);
    }
  }
}
