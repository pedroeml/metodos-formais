// link para o doc: https://docs.google.com/document/d/1T4cDDHZ9TdipH2V06sfwq2u6At0O8YTOWKjn9qs9EVs/edit?usp=sharing
// a) Implementar de forma iterativa o cálculo da multiplicação entre dois números naturais usando somente operações de soma e subtração unitárias.
method Multiply(a: nat, b: nat) returns (total: nat)
  requires a >= 0 && b >= 0
  ensures total == a * b
{
  total := 0;
  var i := 0;
  while i < a 
    invariant total == b * i
    invariant i <= a
  {
    total := total + b;
    i := i + 1;
  }
}

method Main() {
    var result := Multiply(3, 2);
}