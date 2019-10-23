defmodule ExSMT do
  alias ExSMT.Expression
  alias ExSMT.Variable
  alias ExSMT.Solver

  def expr(op), do:
    Expression.new(op, [])
  def expr(op, arg_a), do:
    Expression.new(op, [arg_a])
  def expr(op, arg_a, arg_b), do:
    Expression.new(op, [arg_a, arg_b])
  def expr(op, arg_a, arg_b, arg_c), do:
    Expression.new(op, [arg_a, arg_b, arg_c])

  def env_var(name, i \\ nil), do:
    Variable.new(:env, name, i)
  def ssa_var(name, i \\ nil), do:
    Variable.new(:ssa, name, i)

  def solve(expr) do
    ser_f = ExSMT.Serializable.serialize(expr)

    case Solver.query([ser_f, "(check-sat)\n", "(get-model)\n"]) do
      [:sat, [:model | model_parts]] ->
        model = parse_model_parts(model_parts)
        {:sat, model}

      [:unsat, [:error, err]] ->
        {:unsat, err}
    end
  end

  defp parse_model_parts(l) when is_list(l), do:
    Expression.new(:conj, Enum.map(l, &parse_model_part/1))

  defp parse_model_part([:"define-fun", var, [], _sort, value]), do:
    Expression.new(:=, [var, value])

  @simplifier_command """
    (apply
      (then ctx-solver-simplify propagate-values
        (par-then
          (repeat
            (or-else
              split-clause
              skip))
          propagate-ineqs)))
  """

  def simplify(expr) do
    ser_f = ExSMT.Serializable.serialize(expr)

    case Solver.query([ser_f, @simplifier_command]) do
      [[:goals, [:goal, false | _]]] ->
        :unsat

      [[:goals, [:goal | goal_parts]]] ->
        goals = parse_goal_parts(goal_parts)
        {:sat, goals}
    end
  end

  defp parse_goal_parts(goals) when is_list(goals), do:
    Expression.new(:conj, parse_goal_parts(goals, []))

  defp parse_goal_parts([], acc), do:
    Enum.reverse(acc)
  defp parse_goal_parts([[op, var, value] | rest], acc) when is_atom(op), do:
    parse_goal_parts(rest, [Expression.new(op, [var, value]) | acc])
  defp parse_goal_parts([_ | _], acc), do:
    Enum.reverse(acc)
end
