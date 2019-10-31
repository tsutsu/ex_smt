defmodule ExSMT.BitVector do
  defstruct [:value, :size, :repr]

  def new(true), do: new(true, 1)
  def new(false), do: new(false, 1)
  def new(""), do: new(0, 8)
  def new(0), do: new(0, 8)
  def new(b) when is_bitstring(b), do: new(:binary.decode_unsigned(b), bit_size(b))
  def new(n) when is_integer(n), do: new(n, bit_size(:binary.encode_unsigned(n)))

  def new(true, sz) when is_integer(sz) and sz >= 1, do:
    %__MODULE__{value: 1, size: sz, repr: repr(sz)}
  def new(false, sz) when is_integer(sz) and sz >= 1, do:
    %__MODULE__{value: 0, size: sz, repr: repr(sz)}

  @max_for_size (
    Stream.iterate(1, &(&1 * 256))
    |> Stream.with_index()
    |> Stream.drop(1)
    |> Enum.take(512)
  )

  for {max, sz} <- @max_for_size do
    @sz sz
    @max max
    @repr if rem(sz, 4) == 0, do: :hex, else: :binary
    def new(n, @sz) when is_integer(n), do:
      %__MODULE__{value: rem(n, @max), size: @sz, repr: @repr}
    def new(b, @sz) when is_bitstring(b), do:
      %__MODULE__{value: rem(:binary.decode_unsigned(b), @max), size: @sz, repr: @repr}
  end

  for sz <- 1..512 do
    @sz sz
    if rem(sz, 4) == 0 do
      defp repr(@sz), do: :hex
    else
      defp repr(@sz), do: :binary
    end
  end

  def digits(%__MODULE__{value: value, size: size, repr: :binary}) do
    digits = Integer.to_string(value, 2)
    pad_len = size - byte_size(digits)
    [String.duplicate("0", pad_len), digits]
  end

  def digits(%__MODULE__{value: value, size: size, repr: :hex}) do
    digits =
      Integer.to_string(value, 16)
      |> String.downcase()

    pad_len = div(size, 4) - byte_size(digits)
    [String.duplicate("0", pad_len), digits]
  end
end

defimpl ExSMT.Serializable, for: ExSMT.BitVector do
  def serialize_bool(%ExSMT.BitVector{repr: :binary} = bv), do:
    ["(not (= #b", ExSMT.BitVector.digits(bv), "))"]
  def serialize_bool(%ExSMT.BitVector{repr: :hex} = bv), do:
    ["(not (= #x", ExSMT.BitVector.digits(bv), "))"]

  def serialize_int(%ExSMT.BitVector{repr: :binary} = bv), do:
    ["#b", ExSMT.BitVector.digits(bv)]
  def serialize_int(%ExSMT.BitVector{repr: :hex} = bv), do:
    ["#x", ExSMT.BitVector.digits(bv)]
end

defimpl Inspect, for: ExSMT.BitVector do
  import Inspect.Algebra

  @repeating_bdigit_pat ~r/0+|1+/
  def inspect(%ExSMT.BitVector{repr: :binary} = bv, opts) do
    digits_part =
      ExSMT.BitVector.digits(bv)
      |> IO.iodata_to_binary()
      |> ExSMT.RLE.encode(@repeating_bdigit_pat, 1)
      |> format_digits_part()

    concat([
      color("#b", :number, opts),
      color(digits_part, :number, opts)
    ])
  end

  @repeating_hpair_pat ~r/([0-9a-f]{2})\1*/
  def inspect(%ExSMT.BitVector{repr: :hex} = bv, opts) do
    digits_part =
      ExSMT.BitVector.digits(bv)
      |> IO.iodata_to_binary()
      |> ExSMT.RLE.encode(@repeating_hpair_pat, 2)
      |> format_digits_part()

    concat([
      color("0x", :number, opts),
      color(digits_part, :number, opts)
    ])
  end

  defp format_digits_part({:uncompressed, digits_str}), do:
    digits_str
  defp format_digits_part({:compressed, packed}) do
    Enum.map(packed, fn
      {:repeat, digit, times} -> [digit, "(", to_string(times), ")"]
      {:raw, digits} -> digits
    end)
    |> Enum.intersperse(":")
    |> IO.iodata_to_binary()
  end
end
