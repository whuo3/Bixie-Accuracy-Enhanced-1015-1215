package bixie.checker.report;

import java.util.Set;
import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map.Entry;

public class MyReport {
  public ArrayList<Integer> unreachableLines;
  public HashMap<Integer, Set<Integer>> reasonMap;
  public void setUnreachableLines(Set<Integer> result) {
    unreachableLines = new ArrayList<Integer>(result);
  }
  public void setReasonMap(Map<Integer, Set<Integer>> result) {
    reasonMap = new HashMap<Integer, Set<Integer>>(result);
  }
  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    if(unreachableLines == null || reasonMap == null) {
      System.out.println("My report has not been initialized");
      return "";
    }
    s.append("unreachable code: ");
    for(int line : unreachableLines) {
      s.append(line + " ");
    }
    s.append("\n");
    for(Map.Entry<Integer, Set<Integer>> lineEntry: reasonMap.entrySet()) {
      Set<Integer> contradicts = lineEntry.getValue();
      int infeasibleLine = lineEntry.getKey();
      s.append(infeasibleLine + ": ");
      for(int contradict : contradicts) {
        if(contradict < infeasibleLine) {
          s.append(contradict + " ");
        }
      }
      s.append("\n");
    }
    return s.toString();
    // Random rand = new Random();
    // List<MyPoint> graphToDraw = new ArrayList<MyPoint>();
    // for(int line : allLines) {
    //   // if(infeasibleCandidates.contains(line)) {
    //   //   graphToDraw.add(new MyPoint(rand.nextInt(GridsCanvas.GridSize), rand.nextInt(GridsCanvas.GridSize)));
    //   //   graphToDraw.get(graphToDraw.size() - 1).color = 4;
    //   // } else {
    //   //
    //   // }
    // }
  }
}
