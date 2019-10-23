defmodule ExSMT do
  alias ExSMT.Formula
  alias ExSMT.Variable
  alias ExSMT.Solver

  def formula(op, arg_a), do:
    Formula.new(op, [arg_a])
  def formula(op, arg_a, arg_b), do:
    Formula.new(op, [arg_a, arg_b])
  def formula(op, arg_a, arg_b, arg_c), do:
    Formula.new(op, [arg_a, arg_b, arg_c])

  def env_var(name, i \\ nil), do:
    Variable.new(:env, name, i)
  def ssa_var(name, i \\ nil), do:
    Variable.new(:ssa, name, i)

  def solve(formula) do
    ser_f = ExSMT.Serializable.serialize(formula)

    case Solver.query([ser_f, "(check-sat)\n", "(get-model)\n"]) do
      [:sat, [:model | model_parts]] ->
        model = parse_model_parts(model_parts)
        {:sat, model}

      [:unsat, [:error, err]] ->
        {:unsat, err}
    end
  end

  defp parse_model_parts(l) when is_list(l), do:
    Formula.new(:conj, Enum.map(l, &parse_model_part/1))

  defp parse_model_part([:"define-fun", var, [], _sort, value]), do:
    Formula.new(:=, [var, value])

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

  def simplify(formula) do
    ser_f = ExSMT.Serializable.serialize(formula)

    case Solver.query([ser_f, @simplifier_command]) do
      [[:goals, [:goal, false | _]]] ->
        :unsat

      [[:goals, [:goal | goal_parts]]] ->
        goals = parse_goal_parts(goal_parts)
        {:sat, goals}
    end
  end

  defp parse_goal_parts(goals) when is_list(goals), do:
    Formula.new(:conj, parse_goal_parts(goals, []))

  defp parse_goal_parts([], acc), do:
    Enum.reverse(acc)
  defp parse_goal_parts([[op, var, value] | rest], acc) when is_atom(op), do:
    parse_goal_parts(rest, [Formula.new(op, [var, value]) | acc])
  defp parse_goal_parts([_ | _], acc), do:
    Enum.reverse(acc)
end
