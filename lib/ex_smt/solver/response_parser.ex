defmodule ExSMT.Solver.ResponseParser do
  import NimbleParsec

  number =
    optional(ascii_char([?-]))
    |> ascii_string([?0..?9], min: 1)
    |> tag(:number)

  env_var =
    ignore(string("env_"))
    |> ascii_string([?a..?z, ?A..?Z, ?0..?9, ?-, ?_], min: 1)
    |> tag(:env_var)

  ssa_var =
    ignore(string("ssa_"))
    |> ascii_string([?a..?z, ?A..?Z, ?0..?9, ?-, ?_], min: 1)
    |> tag(:ssa_var)

  identifier =
    ascii_string([?a..?z, ?A..?Z, ?0..?9, ?-, ?_], min: 1)
    |> tag(:identifier)

  operator =
    empty()
    |> choice([
      string("<="),
      string("<"),
      string("="),
      string(">="),
      string(">"),
      string("!")
    ])
    |> tag(:operator)

  sort =
    ascii_char([?A..?Z])
    |> repeat(ascii_char([?a..?z, ?A..?Z, ?0..?9, ?-, ?_]))
    |> tag(:sort)

  empty_list =
    ignore(ascii_char([?(]))
    |> ignore(ascii_char([?)]))
    |> tag(:empty_list)

  sexpr_element =
    empty()
    |> choice([
      number,
      env_var,
      ssa_var,
      operator,
      identifier,
      sort,
      empty_list,
      parsec(:sexpr)
    ])

  flexible_space =
    ignore(ascii_string([?\s], min: 1))

  defparsecp :sexpr,
    ignore(ascii_char([?(]))
    |> optional(flexible_space)
    |> concat(sexpr_element)
    |> repeat(flexible_space |> concat(sexpr_element))
    |> optional(flexible_space)
    |> ignore(ascii_char([?)]))
    |> tag(:list)

  def model(model_lns) when is_list(model_lns) do
    Enum.map(model_lns, &String.trim_trailing(&1, "\n"))
    |> IO.iodata_to_binary()
    |> model()
  end
  def model(model_lns) when is_binary(model_lns) do
    {:ok, [result], "", %{}, _, _} = sexpr(model_lns)

    normalize_types(result)
    |> normalize_model()
  end

  defp normalize_types({:list, l}), do:
    Enum.map(l, &normalize_types/1)
  defp normalize_types({:identifier, [id_str]}), do:
    String.to_atom(id_str)
  defp normalize_types({:env_var, [name]}), do:
    ExSMT.Variable.new(:env, name)
  defp normalize_types({:ssa_var, [name]}), do:
    ExSMT.Variable.new(:ssa, name)
  defp normalize_types({:empty_list, []}), do:
    []
  defp normalize_types({:number, [digits_str]}), do:
    String.to_integer(digits_str)

  defp normalize_model([:model | parts0]) do
    parts1 = Enum.map(parts0, &normalize_model_part/1)
    ExSMT.Formula.new(:conj, parts1)
  end

  defp normalize_model_part([:"define-fun", var, [], _, value]), do:
    ExSMT.Formula.new(:=, [var, value])
end
