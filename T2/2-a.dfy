// a) Calcular de forma iterativa o somatório dos valores de um array de números inteiros.
function sum (s: seq<int>, i: int) : int {
  if |s| == 0 || i == 0 then 0 
  else s[0] + sum(s[1..], i - 1)  
}

method sumArray (input : seq<int>) returns (res: int)
ensures res == sum(input, |input|)
{
  var i := 0;
  res := 0;
  while i < |input|
  invariant i <= |input|
  invariant res == sum(input, i)
  { 
   res :=  res + input[i]; 
   i := i + 1;
  }
}