import java.util.HashSet;
import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.PriorityQueue;

public class MyPoint {
	private int x;
	private int y;
	//0: no color
	//1: color yellow
	//2: color green
	//3: color blue
	//4: color red
	private int color;
	private int remainValues;
	List<MyPoint> neighbors;
	private PriorityQueue<MyPoint> neighborCandidates;
	public MyPoint(int x, int y) {
		this.x = x;
		this.y = y;
		this.color = 0;
		this.remainValues = 4;
		final int tx = x;
		final int ty = y;
		neighbors = new ArrayList<MyPoint>();
	}
	public void setX(int x) {
		this.x = x;
	}
	public void setY(int y) {
		this.y = y;
	}
	public void setColor(int color) {
		this.color = color;
	}
	public int getColor() {
		return color;
	}
	public int getX() {
		return x;
	}
	public int getY() {
		return y;
	}
	public void addNeighbor(MyPoint nei) {
		this.neighbors.add(nei);
	}
	public boolean isColored() {
		return color <= 4 && color >= 1;
	}
}
