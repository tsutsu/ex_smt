defmodule ExSMT.Expression do
  defstruct [op: nil, args: [], var_decls: MapSet.new()]

  def new(op, args) do
    case simplify_trivial(op, args) do
      {:ok, concrete_t} -> concrete_t
      :error -> %__MODULE__{op: op, args: args, var_decls: var_decls(args)}
    end
  end

  def append(%__MODULE__{args: args, var_decls: vd} = f, new_arg), do:
    %__MODULE__{f | args: args ++ [new_arg], var_decls: var_decls_add(vd, new_arg)}

  defp var_decls(%__MODULE__{var_decls: vd}), do: Enum.to_list(vd)
  defp var_decls(%ExSMT.Variable{} = var), do: [var]
  defp var_decls(l) when is_list(l) do
    Enum.flat_map(l, &var_decls/1)
    |> Enum.into(MapSet.new())
  end
  defp var_decls(_), do: MapSet.new()

  defp var_decls_add(vd1, %__MODULE__{var_decls: vd2}), do:
    MapSet.union(vd1, vd2)
  defp var_decls_add(vd, %ExSMT.Variable{} = var), do:
    MapSet.put(vd, var)
  defp var_decls_add(vd, _), do:
    MapSet.new([vd])

  defp simplify_trivial(op, l) do
    case concretize_args(l, []) do
      {:ok, concrete_args} ->
        simplify_trivial_op(op, concrete_args)
      :error ->
        :error
    end
  end

  defp concretize_args([], acc), do: {:ok, Enum.reverse(acc)}
  defp concretize_args([t | rest], acc) do
    case concretize(t) do
      {:ok, concrete_t} -> concretize_args(rest, [concrete_t | acc])
      :error -> :error
    end
  end

  def simplify_trivial_op(:=, [a, a]), do:
    {:ok, true}
  def simplify_trivial_op(:=, [a, b]) when a != b, do:
    {:ok, false}
  def simplify_trivial_op(:+, els), do:
    {:ok, Enum.reduce(els, 0, &(&1 + &2))}
  def simplify_trivial_op(:-, [a, b]), do:
    {:ok, a - b}
  def simplify_trivial_op(:*, els), do:
    {:ok, Enum.reduce(els, 1, &(&1 * &2))}
  def simplify_trivial_op(:/, [a, b]) when b != 0, do:
    {:ok, div(a, b)}
  def simplify_trivial_op(:%, [a, b]) when b != 0, do:
    {:ok, rem(a, b)}
  def simplify_trivial_op(:not, [0]), do:
    {:ok, true}
  def simplify_trivial_op(:not, [n]) when is_integer(n), do:
    {:ok, false}
  def simplify_trivial_op(:not, [true]), do:
    {:ok, false}
  def simplify_trivial_op(:not, [false]), do:
    {:ok, true}
  def simplify_trivial_op(_, _), do:
    :error

  @predicate_ops [:=, :>=, :<=, :>, :<, :not]
  def predicate?(%__MODULE__{op: op}) when op in @predicate_ops, do: true
  def predicate?(true), do: true
  def predicate?(false), do: true
  def predicate?(_), do: false

  def concretize(true), do: {:ok, true}
  def concretize(false), do: {:ok, false}
  def concretize(n) when is_integer(n), do: {:ok, n}
  def concretize(str) when is_binary(str), do: {:ok, str}
  def concretize(_), do: :error
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

  def serialize(%ExSMT.Expression{op: :not, args: [arg]}) do
    if ExSMT.Expression.predicate?(arg) do
      ["(not ", ExSMT.Serializable.serialize(arg), ")"]
    else
      ["(= ", ExSMT.Serializable.serialize(arg), " 0)"]
    end
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

  def inspect(%ExSMT.Expression{op: true}, opts), do:
    color("⊤", :nil, opts)
  def inspect(%ExSMT.Expression{op: false}, opts), do:
    color("⊥", :nil, opts)

  def inspect(%ExSMT.Expression{op: :conj, args: []}, opts), do:
    color("⊤", :nil, opts)
  def inspect(%ExSMT.Expression{op: :conj, args: args}, opts) do
    pre = color("(", :tuple, opts)
    post = color(")", :tuple, opts)
    sep = color(" ∧", :operator, opts)
    nest(container_doc(pre, args, post, opts, &to_doc/2, separator: sep, break: :flex), 2)
  end

  def inspect(%ExSMT.Expression{op: :not, args: [arg]}, opts) do
    concat([
      color("!", :operator, opts),
      to_doc(arg, opts)
    ])
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
