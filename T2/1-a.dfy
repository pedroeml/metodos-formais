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
    decreases a - i
  {
    total := total + b;
    i := i + 1;
  }
}

method Main() {
    var result := Multiply(3, 2);
}
