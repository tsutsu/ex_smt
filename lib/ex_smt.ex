defmodule ExSMT do
  require Logger

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
    # Logger.debug(["solving:\n", inspect(expr, IEx.inspect_opts())])

    ser_f =
      Expression.new(:toplevel, [expr])
      |> ExSMT.Expression.serialize()

    case Solver.query([ser_f, "(check-sat)\n", "(get-model)\n"]) do
      [:sat, [:model | model_parts]] ->
        model = parse_model_parts(model_parts)
        {:sat, model}

      [:unsat, [:error, err]] ->
        {:unsat, err}
    end
  end

  defp parse_model_parts(l) when is_list(l), do:
    Expression.new(:and, Enum.map(l, &parse_model_part/1))

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
    # Logger.debug(["simplifying:\n", inspect(expr, IEx.inspect_opts())])

    ser_f =
      Expression.new(:toplevel, [expr])
      |> ExSMT.Expression.serialize()

    case Solver.query([ser_f, @simplifier_command]) do
      [[:goals, [:goal, false | _]]] ->
        :unsat

      [[:goals | sat_goals]] ->
        sat_goal_exprs = Enum.map(sat_goals, fn [:goal | goal_parts] ->
          parse_goal_parts(goal_parts)
        end)

        sat_goals_expr = case sat_goal_exprs do
          [g_expr] ->
            g_expr
          args when length(args) > 1 ->
            Expression.new(:or, args)
        end

        {:sat, sat_goals_expr}

      [[:error, err] | _goals] ->
        Logger.error(err)
        IO.puts(ser_f)
        :unsat
    end
  end

  defp parse_goal_parts(goals) when is_list(goals), do:
    Expression.new(:and, parse_goal_parts(goals, []))

  defp parse_goal_parts([], acc), do:
    Enum.reverse(acc)
  defp parse_goal_parts([[op | _] = expr | rest], acc) when is_atom(op), do:
    parse_goal_parts(rest, [parse_goal_expr(expr) | acc])
  defp parse_goal_parts([_ | _], acc), do:
    Enum.reverse(acc)

  defp parse_goal_expr([op | args]) when is_atom(op), do:
    Expression.new(op, Enum.map(args, &parse_goal_expr/1))
  defp parse_goal_expr(t), do: t
end
