defmodule ExSMT.BitVector do
  defstruct [:value]

  def new(n) when is_integer(n), do:
    %__MODULE__{value: n}
  def new(true), do:
    %__MODULE__{value: 1}
  def new(false), do:
    %__MODULE__{value: 0}
  def new(b) when is_binary(b), do:
    %__MODULE__{value: :binary.decode_unsigned(b)}
end

defimpl ExSMT.Serializable, for: ExSMT.BitVector do
  def serialize_bool(%ExSMT.BitVector{value: value}), do:
    ["(not (= #b", pad_to_four(value), "))"]

  def serialize_int(%ExSMT.BitVector{value: value}), do:
    ["#b", pad_to_four(value)]

  defp pad_to_four(value) do
    v_str = Integer.to_string(value, 2)
    pad_len = 4 - rem(byte_size(v_str), 4)
    [List.duplicate(" ", pad_len), v_str]
  end
end

defimpl Inspect, for: ExSMT.BitVector do
  import Inspect.Algebra

  def inspect(%ExSMT.BitVector{value: value}, opts) do
    digits = Integer.to_string(value, 2)

    digits_part = case rle_encode(digits) do
      {:ok, packed} ->
        Enum.map(packed, fn
          {:repeat, digit, times} -> [digit, "(", to_string(times), ")"]
          {:raw, digits} -> digits
        end)
        |> Enum.intersperse(":")
        |> IO.iodata_to_binary()
      :error ->
        digits
    end

    concat([
      color("#b", :number, opts),
      color(digits_part, :number, opts)
    ])
  end

  def rle_encode(digits_str) do
    digits_size = byte_size(digits_str)
    {packed, raw_size} = rle_encode_part(Regex.scan(~r/1+|0+/, digits_str, capture: :first), [], 0)
    case raw_size / digits_size do
      n when n < 0.5 -> {:ok, packed}
      _ -> :error
    end
  end

  defp rle_encode_part([], acc, raw_len), do:
    {:lists.reverse(acc), raw_len}
  defp rle_encode_part([[short] | rest], acc, raw_len) when byte_size(short) < 4, do:
    rle_encode_part(rest, [{:raw, short} | acc], raw_len + byte_size(short))
  defp rle_encode_part([[<<digit::binary-size(1), _::binary>> = long] | rest], acc, raw_len), do:
    rle_encode_part(rest, [{:repeat, digit, byte_size(long)} | acc], raw_len)
end
