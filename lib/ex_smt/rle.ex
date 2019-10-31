defmodule ExSMT.RLE do
  def encode(bin, %Regex{} = scan_pat, cluster_sz) when is_binary(bin) and is_integer(cluster_sz) and cluster_sz >= 1 do
    {output, raw_size} =
      Regex.scan(scan_pat, bin, capture: :first)
      |> encode_part([], 0, cluster_sz)

    case raw_size / byte_size(bin) do
      n when n < 0.5 -> {:compressed, output}
      _ -> {:uncompressed, bin}
    end
  end

  defp encode_part([], acc, raw_len, _cluster_sz), do:
    {:lists.reverse(acc), raw_len}

  defp encode_part([[short] | rest], acc, raw_len, cluster_sz) when div(byte_size(short), cluster_sz) < 4, do:
    encode_part(rest, [{:raw, short} | acc], raw_len + byte_size(short), cluster_sz)

  defp encode_part([[long] | rest], acc, raw_len, cluster_sz) do
    <<cluster::binary-size(cluster_sz), _::binary>> = long
    encode_part(rest, [{:repeat, cluster, div(byte_size(long), cluster_sz)} | acc], raw_len, cluster_sz)
  end
end
