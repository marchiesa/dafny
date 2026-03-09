//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Serialization;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

// ============================================================================
// Expression AST Serializer
// ============================================================================

/// <summary>
/// Serializes Dafny Expression AST nodes to a JSON-compatible format with unique IDs.
/// This allows mapping Z3 proof terms back to specific subexpressions.
/// </summary>
public class ExpressionSerializer {
  private int nextNodeId = 0;
  private readonly Dictionary<string, ExprAstNode> nodes = new();
  private readonly HashSet<string> referencedVariables = new();
  private readonly HashSet<string> referencedFunctions = new();

  /// <summary>
  /// Serialize an expression tree, returning the root node ID.
  /// </summary>
  public string Serialize(Expression expr) {
    if (expr == null) return null;
    return SerializeNode(expr);
  }

  /// <summary>
  /// Get all serialized nodes.
  /// </summary>
  public Dictionary<string, ExprAstNode> GetNodes() => nodes;

  /// <summary>
  /// Get all variable names referenced in the expression.
  /// </summary>
  public List<string> GetReferencedVariables() => referencedVariables.ToList();

  /// <summary>
  /// Get all function names referenced in the expression.
  /// </summary>
  public List<string> GetReferencedFunctions() => referencedFunctions.ToList();

  private string SerializeNode(Expression expr) {
    // Handle ConcreteSyntaxExpression by using its resolved form
    if (expr is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null) {
      expr = cse.ResolvedExpression;
    }

    var nodeId = $"e{nextNodeId++}";
    var node = new ExprAstNode { Id = nodeId };

    switch (expr) {
      case IdentifierExpr ie:
        node.NodeType = "Identifier";
        node.Name = ie.Name;
        if (ie.Var != null) {
          node.Variable = ie.Var.Name;
          referencedVariables.Add(ie.Var.Name);
        }
        break;

      case LiteralExpr le:
        node.NodeType = "Literal";
        node.Value = le.Value?.ToString();
        break;

      case BinaryExpr be:
        node.NodeType = "BinaryExpr";
        node.Op = be.Op.ToString();
        node.Children = new List<string> {
          SerializeNode(be.E0),
          SerializeNode(be.E1)
        };
        break;

      case UnaryOpExpr ue:
        node.NodeType = "UnaryExpr";
        node.Op = ue.Op.ToString();
        node.Children = new List<string> { SerializeNode(ue.E) };
        break;

      case FunctionCallExpr fce:
        node.NodeType = "FunctionCall";
        node.Name = fce.Name;
        if (fce.Function != null) {
          node.Function = fce.Function.Name;
          referencedFunctions.Add(fce.Function.Name);
        }
        node.Children = fce.Args.Select(SerializeNode).ToList();
        break;

      case SeqSelectExpr sse:
        node.NodeType = sse.SelectOne ? "SeqIndex" : "SeqSlice";
        var children = new List<string> { SerializeNode(sse.Seq) };
        if (sse.E0 != null) children.Add(SerializeNode(sse.E0));
        if (sse.E1 != null) children.Add(SerializeNode(sse.E1));
        node.Children = children;
        break;

      case SeqUpdateExpr sue:
        node.NodeType = "SeqUpdate";
        node.Children = new List<string> {
          SerializeNode(sue.Seq),
          SerializeNode(sue.Index),
          SerializeNode(sue.Value)
        };
        break;

      case ITEExpr ite:
        node.NodeType = "IfThenElse";
        node.Children = new List<string> {
          SerializeNode(ite.Test),
          SerializeNode(ite.Thn),
          SerializeNode(ite.Els)
        };
        break;

      case ForallExpr fe:
        node.NodeType = "Forall";
        node.BoundVars = fe.BoundVars.Select(v => v.Name).ToList();
        var forallChildren = new List<string>();
        if (fe.Range != null) forallChildren.Add(SerializeNode(fe.Range));
        forallChildren.Add(SerializeNode(fe.Term));
        node.Children = forallChildren;
        break;

      case ExistsExpr ee:
        node.NodeType = "Exists";
        node.BoundVars = ee.BoundVars.Select(v => v.Name).ToList();
        var existsChildren = new List<string>();
        if (ee.Range != null) existsChildren.Add(SerializeNode(ee.Range));
        existsChildren.Add(SerializeNode(ee.Term));
        node.Children = existsChildren;
        break;

      case MemberSelectExpr mse:
        node.NodeType = "MemberSelect";
        node.Name = mse.MemberName;
        node.Children = new List<string> { SerializeNode(mse.Obj) };
        break;

      case ThisExpr:
        node.NodeType = "This";
        break;

      case OldExpr oe:
        node.NodeType = "Old";
        node.Children = new List<string> { SerializeNode(oe.Expr) };
        break;

      case LetExpr le:
        node.NodeType = "Let";
        node.BoundVars = le.BoundVars.Select(v => v.Name).ToList();
        var letChildren = le.RHSs.Select(SerializeNode).ToList();
        letChildren.Add(SerializeNode(le.Body));
        node.Children = letChildren;
        break;

      default:
        // Fallback for other expression types
        node.NodeType = expr.GetType().Name;
        var subExprs = expr.SubExpressions.ToList();
        if (subExprs.Any()) {
          node.Children = subExprs.Select(SerializeNode).ToList();
        }
        break;
    }

    nodes[nodeId] = node;
    return nodeId;
  }
}

/// <summary>
/// Represents a serialized AST node.
/// </summary>
public class ExprAstNode {
  [JsonPropertyName("id")]
  public string Id { get; set; }

  [JsonPropertyName("type")]
  public string NodeType { get; set; }

  [JsonPropertyName("name")]
  public string Name { get; set; }

  [JsonPropertyName("op")]
  public string Op { get; set; }

  [JsonPropertyName("value")]
  public string Value { get; set; }

  [JsonPropertyName("variable")]
  public string Variable { get; set; }

  [JsonPropertyName("function")]
  public string Function { get; set; }

  [JsonPropertyName("boundVars")]
  public List<string> BoundVars { get; set; }

  [JsonPropertyName("children")]
  public List<string> Children { get; set; }
}

/// <summary>
/// Tracks the mapping from Dafny AST nodes to Boogie constructs.
/// This enables tracing from source code through Boogie to SMT/Z3.
/// </summary>
public class AstMappingManager {

  // Track all mappings by method/function
  public Dictionary<string, MethodMapping> Methods { get; } = new();
  public Dictionary<string, FunctionMapping> Functions { get; } = new();

  // Current context
  private string currentMethod;
  private string currentFile;

  public void SetCurrentMethod(string methodName, string fileName) {
    currentMethod = methodName;
    currentFile = fileName;
    if (!Methods.ContainsKey(methodName)) {
      Methods[methodName] = new MethodMapping {
        Name = methodName,
        File = fileName
      };
    }
  }

  public void SetCurrentFunction(string functionName, string fileName) {
    if (!Functions.ContainsKey(functionName)) {
      Functions[functionName] = new FunctionMapping {
        DafnyName = functionName,
        File = fileName
      };
    }
  }

  /// <summary>
  /// Record a variable mapping (Dafny var -> Boogie var)
  /// </summary>
  public void AddVariable(IVariable dafnyVar, string boogieName, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    var varName = dafnyVar.Name;
    if (!method.Variables.ContainsKey(varName)) {
      method.Variables[varName] = new VariableMapping {
        DafnyName = varName,
        BoogieName = boogieName,
        Type = dafnyVar.Type?.ToString() ?? "unknown",
        Location = LocationFromOrigin(location)
      };
    }

    // Track SSA versions
    if (!method.Variables[varName].SsaVersions.Contains(boogieName)) {
      method.Variables[varName].SsaVersions.Add(boogieName);
    }
  }

  /// <summary>
  /// Record a function mapping (Dafny function -> Boogie function)
  /// </summary>
  public void AddFunction(Function dafnyFunc, string boogieName) {
    var funcName = dafnyFunc.Name;
    if (!Functions.ContainsKey(funcName)) {
      Functions[funcName] = new FunctionMapping {
        DafnyName = funcName,
        BoogieName = boogieName,
        File = dafnyFunc.Origin?.filename ?? "unknown",
        Location = LocationFromOrigin(dafnyFunc.Origin)
      };
    } else {
      Functions[funcName].BoogieName = boogieName;
    }
  }

  /// <summary>
  /// Record a loop invariant mapping
  /// </summary>
  public void AddInvariant(Expression invariantExpr, string boogieId, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    // Serialize the expression AST
    var serializer = new ExpressionSerializer();
    var rootNodeId = serializer.Serialize(invariantExpr);

    method.Invariants.Add(new InvariantMapping {
      BoogieId = boogieId,
      Text = invariantExpr.ToString(),
      Location = LocationFromOrigin(location),
      SmtEstablished = $"assert$${boogieId}$established",
      SmtMaintained = $"assert$${boogieId}$maintained",
      ExpressionId = rootNodeId,
      ExpressionAst = serializer.GetNodes(),
      ReferencedVariables = serializer.GetReferencedVariables(),
      ReferencedFunctions = serializer.GetReferencedFunctions()
    });
  }

  /// <summary>
  /// Record an assertion mapping
  /// </summary>
  public void AddAssertion(Expression assertExpr, string boogieId, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    // Serialize the expression AST
    var serializer = new ExpressionSerializer();
    var rootNodeId = serializer.Serialize(assertExpr);

    method.Assertions.Add(new AssertionMapping {
      BoogieId = boogieId,
      Text = assertExpr.ToString(),
      Location = LocationFromOrigin(location),
      ExpressionId = rootNodeId,
      ExpressionAst = serializer.GetNodes(),
      ReferencedVariables = serializer.GetReferencedVariables(),
      ReferencedFunctions = serializer.GetReferencedFunctions()
    });
  }

  /// <summary>
  /// Record an ensures clause mapping
  /// </summary>
  public void AddEnsures(Expression ensuresExpr, string boogieId, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    // Serialize the expression AST
    var serializer = new ExpressionSerializer();
    var rootNodeId = serializer.Serialize(ensuresExpr);

    method.Ensures.Add(new EnsuresMapping {
      BoogieId = boogieId,
      Text = ensuresExpr.ToString(),
      Location = LocationFromOrigin(location),
      ExpressionId = rootNodeId,
      ExpressionAst = serializer.GetNodes(),
      ReferencedVariables = serializer.GetReferencedVariables(),
      ReferencedFunctions = serializer.GetReferencedFunctions()
    });
  }

  /// <summary>
  /// Record a requires clause mapping
  /// </summary>
  public void AddRequires(Expression requiresExpr, string boogieId, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    // Serialize the expression AST
    var serializer = new ExpressionSerializer();
    var rootNodeId = serializer.Serialize(requiresExpr);

    method.Requires.Add(new RequiresMapping {
      BoogieId = boogieId,
      Text = requiresExpr.ToString(),
      Location = LocationFromOrigin(location),
      ExpressionId = rootNodeId,
      ExpressionAst = serializer.GetNodes(),
      ReferencedVariables = serializer.GetReferencedVariables(),
      ReferencedFunctions = serializer.GetReferencedFunctions()
    });
  }

  /// <summary>
  /// Record a call (lemma/method invocation) mapping
  /// </summary>
  public void AddCall(CallStmt callStmt, string calleeName, string boogieId, IOrigin location) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    method.Calls.Add(new CallMapping {
      BoogieId = boogieId,
      CalleeName = calleeName,
      Location = LocationFromOrigin(location)
    });
  }

  /// <summary>
  /// Record a forall statement mapping
  /// </summary>
  public void AddForall(ForallStmt forallStmt, string kind, string boogieId, IOrigin location,
                        string callee = null, string ensures = null) {
    if (currentMethod == null || !Methods.TryGetValue(currentMethod, out var method)) {
      return;
    }

    var boundVars = forallStmt.BoundVars.Select(v => v.Name).ToList();
    method.Foralls.Add(new ForallMapping {
      BoogieId = boogieId,
      Kind = kind,
      Text = forallStmt.Body?.ToString() ?? "",
      Range = forallStmt.Range?.ToString() ?? "",
      BoundVars = boundVars,
      Callee = callee,
      Ensures = ensures,
      Location = LocationFromOrigin(location)
    });
  }

  private static SourceLocation LocationFromOrigin(IOrigin origin) {
    if (origin == null) {
      return new SourceLocation { Line = 0, Col = 0 };
    }
    var endToken = origin.ReportingRange.EndToken;
    return new SourceLocation {
      Line = origin.line,
      Col = origin.col,
      EndLine = endToken?.line ?? origin.line,
      EndCol = endToken?.col ?? origin.col
    };
  }

  /// <summary>
  /// Export the complete mapping to a JSON file
  /// </summary>
  public void ExportToFile(string filePath) {
    var output = new AstMappingOutput {
      Methods = new List<MethodMapping>(Methods.Values),
      Functions = new List<FunctionMapping>(Functions.Values)
    };

    var options = new JsonSerializerOptions {
      WriteIndented = true,
      DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull
    };

    var json = JsonSerializer.Serialize(output, options);
    File.WriteAllText(filePath, json);
  }

  /// <summary>
  /// Get the mapping as a JSON string
  /// </summary>
  public string ToJson() {
    var output = new AstMappingOutput {
      Methods = new List<MethodMapping>(Methods.Values),
      Functions = new List<FunctionMapping>(Functions.Values)
    };

    var options = new JsonSerializerOptions {
      WriteIndented = true,
      DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull
    };

    return JsonSerializer.Serialize(output, options);
  }
}

// ============================================================================
// Data classes for the mapping
// ============================================================================

public class AstMappingOutput {
  [JsonPropertyName("methods")]
  public List<MethodMapping> Methods { get; set; } = new();

  [JsonPropertyName("functions")]
  public List<FunctionMapping> Functions { get; set; } = new();
}

public class MethodMapping {
  [JsonPropertyName("name")]
  public string Name { get; set; }

  [JsonPropertyName("file")]
  public string File { get; set; }

  [JsonPropertyName("variables")]
  public Dictionary<string, VariableMapping> Variables { get; set; } = new();

  [JsonPropertyName("invariants")]
  public List<InvariantMapping> Invariants { get; set; } = new();

  [JsonPropertyName("assertions")]
  public List<AssertionMapping> Assertions { get; set; } = new();

  [JsonPropertyName("ensures")]
  public List<EnsuresMapping> Ensures { get; set; } = new();

  [JsonPropertyName("requires")]
  public List<RequiresMapping> Requires { get; set; } = new();

  [JsonPropertyName("calls")]
  public List<CallMapping> Calls { get; set; } = new();

  [JsonPropertyName("foralls")]
  public List<ForallMapping> Foralls { get; set; } = new();
}

public class FunctionMapping {
  [JsonPropertyName("dafnyName")]
  public string DafnyName { get; set; }

  [JsonPropertyName("boogieName")]
  public string BoogieName { get; set; }

  [JsonPropertyName("file")]
  public string File { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }
}

public class VariableMapping {
  [JsonPropertyName("dafnyName")]
  public string DafnyName { get; set; }

  [JsonPropertyName("boogieName")]
  public string BoogieName { get; set; }

  [JsonPropertyName("ssaVersions")]
  public List<string> SsaVersions { get; set; } = new();

  [JsonPropertyName("type")]
  public string Type { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }
}

public class InvariantMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("text")]
  public string Text { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }

  [JsonPropertyName("smtEstablished")]
  public string SmtEstablished { get; set; }

  [JsonPropertyName("smtMaintained")]
  public string SmtMaintained { get; set; }

  [JsonPropertyName("expressionId")]
  public string ExpressionId { get; set; }

  [JsonPropertyName("expressionAst")]
  public Dictionary<string, ExprAstNode> ExpressionAst { get; set; }

  [JsonPropertyName("referencedVariables")]
  public List<string> ReferencedVariables { get; set; }

  [JsonPropertyName("referencedFunctions")]
  public List<string> ReferencedFunctions { get; set; }
}

public class AssertionMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("text")]
  public string Text { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }

  [JsonPropertyName("expressionId")]
  public string ExpressionId { get; set; }

  [JsonPropertyName("expressionAst")]
  public Dictionary<string, ExprAstNode> ExpressionAst { get; set; }

  [JsonPropertyName("referencedVariables")]
  public List<string> ReferencedVariables { get; set; }

  [JsonPropertyName("referencedFunctions")]
  public List<string> ReferencedFunctions { get; set; }
}

public class EnsuresMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("text")]
  public string Text { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }

  [JsonPropertyName("expressionId")]
  public string ExpressionId { get; set; }

  [JsonPropertyName("expressionAst")]
  public Dictionary<string, ExprAstNode> ExpressionAst { get; set; }

  [JsonPropertyName("referencedVariables")]
  public List<string> ReferencedVariables { get; set; }

  [JsonPropertyName("referencedFunctions")]
  public List<string> ReferencedFunctions { get; set; }
}

public class RequiresMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("text")]
  public string Text { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }

  [JsonPropertyName("expressionId")]
  public string ExpressionId { get; set; }

  [JsonPropertyName("expressionAst")]
  public Dictionary<string, ExprAstNode> ExpressionAst { get; set; }

  [JsonPropertyName("referencedVariables")]
  public List<string> ReferencedVariables { get; set; }

  [JsonPropertyName("referencedFunctions")]
  public List<string> ReferencedFunctions { get; set; }
}

public class SourceLocation {
  [JsonPropertyName("line")]
  public int Line { get; set; }

  [JsonPropertyName("col")]
  public int Col { get; set; }

  [JsonPropertyName("endLine")]
  public int EndLine { get; set; }

  [JsonPropertyName("endCol")]
  public int EndCol { get; set; }
}

public class CallMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("calleeName")]
  public string CalleeName { get; set; }

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }
}

public class ForallMapping {
  [JsonPropertyName("boogieId")]
  public string BoogieId { get; set; }

  [JsonPropertyName("kind")]
  public string Kind { get; set; }  // "assign", "call", or "proof"

  [JsonPropertyName("text")]
  public string Text { get; set; }

  [JsonPropertyName("range")]
  public string Range { get; set; }  // The range predicate

  [JsonPropertyName("boundVars")]
  public List<string> BoundVars { get; set; } = new();

  [JsonPropertyName("callee")]
  public string Callee { get; set; }  // For "call" kind: the lemma being called

  [JsonPropertyName("ensures")]
  public string Ensures { get; set; }  // For "proof" kind: the ensures clause

  [JsonPropertyName("location")]
  public SourceLocation Location { get; set; }
}
