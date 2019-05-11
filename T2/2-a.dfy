// a) Calcular de forma iterativa o somatório dos valores de um array de números inteiros.
// Definicao recursiva de um somatorio
function somatorio(a: array?<int>, n:int) : int
  requires a != null;
  requires n >= 0 && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then
    0
  else
    somatorio(a, n-1) + a[n-1]
}

// Metodo que computa o somatorio de todos os elementos de um dado array
method somatorioArray(a: array?<int>) returns (result: int)
  requires a != null;
  ensures result == somatorio(a, a.Length);
{
  result := 0;
  var i := 0;
  while i < a.Length
    invariant i >= 0 && i <= a.Length;
    invariant result == somatorio(a, i);
    decreases a.Length - i;
  {
    result := result + a[i];
    i := i + 1;
  }
}
