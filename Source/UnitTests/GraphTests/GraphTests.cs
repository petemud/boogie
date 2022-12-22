using NUnit.Framework;
using System.Numerics;
using System.Collections.Generic;
using Microsoft.Boogie.GraphUtil;
using System.Linq;

namespace GraphTests
{
  [TestFixture()]
  public class MergeTests
  {
    [Test()]
    public void MergeTest1()
    {
      var o1 = 1;
      var o2 = 2;
      var o3 = new int[] { 1, 2 };
      var o4 = o3;
      var o5 = 3;
      var edges = new Dictionary<object, List<object>>()
      {
        { o1, new List<object> { o3 } },
        { o2, new List<object> { o3 } },
        { o4, new List<object>() { o5 } }
      };
      var roots = new List<object> { 1, 2 };
      var reachableNodes = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(edges, roots).ToHashSet<object>();
      Assert.IsTrue(reachableNodes.Contains(o5));
    }
    
    [Test()]
    public void MergeTest2()
    {
      var o1 = 1;
      var o2 = 2;
      var o3 = new int[] { 1, 2 };
      var o4 = new int[] { 2, 1 };
      var o5 = 3;
      var edges = new Dictionary<object, List<object>>()
      {
        { o1, new List<object> { o3 } },
        { o2, new List<object> { o3 } },
        { o4, new List<object>() { o5 } }
      };
      var roots = new List<object> { 1, 2 };
      var reachableNodes = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(edges, roots).ToHashSet<object>();
      Assert.IsTrue(reachableNodes.Contains(o5));
    }
    
    [Test()]
    public void MergeTest3()
    {
      var o1 = 1;
      var o2 = 2;
      var o3 = new int[] { 1, 2 };
      var o4 = new int[] { 1, 2 };
      var o5 = 3;
      var edges = new Dictionary<object, List<object>>()
      {
        { o1, new List<object> { o3 } },
        { o2, new List<object> { o3 } },
        { o4, new List<object>() { o5 } }
      };
      var roots = new List<object> { 1, 2 };
      var reachableNodes = GraphAlgorithms.FindReachableNodesInGraphWithMergeNodes(edges, roots).ToHashSet<object>();
      Assert.IsTrue(reachableNodes.Contains(o5));
    }
  }
}
