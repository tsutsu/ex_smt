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
      {:ok, ["sat\n" | model_lns]} ->
        {:sat, Solver.ResponseParser.model(model_lns)}

      {:ok, ["unsat\n" | _]} ->
        :unsat
    end
  end
end
