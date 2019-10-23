defmodule ExSMT.Expression do
  defstruct [op: nil, args: [], var_decls: MapSet.new()]

  def new(op, args), do:
    %__MODULE__{op: op, args: args, var_decls: var_decls(args)}

  def append(%__MODULE__{args: args, var_decls: vd} = f, new_arg), do:
    %__MODULE__{f | args: args ++ [new_arg], var_decls: var_decls_add(vd, new_arg)}

  defp var_decls(%__MODULE__{var_decls: vd}), do: Enum.to_list(vd)
  defp var_decls(%ExSMT.Variable{} = var), do: [var]
  defp var_decls(l) when is_list(l) do
    Enum.flat_map(l, &var_decls/1)
    |> Enum.into(MapSet.new())
  end
  defp var_decls(_), do: []

  defp var_decls_add(vd1, %__MODULE__{var_decls: vd2}), do:
    MapSet.union(vd1, vd2)
  defp var_decls_add(vd, %ExSMT.Variable{} = var), do:
    MapSet.put(vd, var)
  defp var_decls_add(vd, _), do:
    vd
end

defimpl ExSMT.Serializable, for: ExSMT.Expression do
  def serialize(%ExSMT.Expression{op: :conj, args: args, var_decls: var_decls}) do
    var_decls = Enum.map(var_decls, fn var ->
      ["(declare-const ", ExSMT.Serializable.serialize(var), " Int)\n"]
    end)
    assertions = Enum.map(args, fn f ->
      ["(assert ", ExSMT.Serializable.serialize(f), ")\n"]
    end)
    [var_decls, assertions]
  end

  def serialize(%ExSMT.Expression{op: op, args: args}) do
    ser_args =
      Enum.map(args, &ExSMT.Serializable.serialize/1)
      |> Enum.intersperse(" ")
    ["(", to_string(op), " ", ser_args, ")"]
  end
end

defimpl Inspect, for: ExSMT.Expression do
  import Inspect.Algebra

  def inspect(%ExSMT.Expression{op: :true}, opts) do
    color("⊤", :number, opts)
  end

  def inspect(%ExSMT.Expression{op: :conj, args: args}, opts) do
    pre = color("(", :tuple, opts)
    post = color(")", :tuple, opts)
    sep = color(" ∧", :operator, opts)
    nest(container_doc(pre, args, post, opts, &to_doc/2, separator: sep, break: :flex), 2)
  end

  def inspect(%ExSMT.Expression{op: op, args: args}, opts) do
    pre = color("(", :hidden, opts)
    post = color(")", :hidden, opts)
    sep = color("", :tuple, opts)
    args = [op | args]
    nest(container_doc(pre, args, post, opts, &to_doc_or_operator/2, separator: sep, break: :flex), 2)
  end

  defp to_doc_or_operator(op_name, opts) when is_atom(op_name), do:
    color(to_string(op_name), :operator, opts)
  defp to_doc_or_operator(t, opts), do:
    to_doc(t, opts)
end
