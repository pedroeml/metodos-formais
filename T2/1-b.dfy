// Implementar de forma iterativa o cálculo do quociente da divisão inteira entre dois números naturais. 
// Dica: por definição, o quociente da divisão inteira entre 𝑥 e 𝑦 é o único 𝑑 tal que existe um resto 𝑟 tal que 𝑟<𝑦 e 𝑥=𝑑×𝑦+𝑟.

method CalculaQuociente(x: nat, y: nat) returns (d: nat, r: nat)
  requires x >= 0 && y > 0
  ensures x == y * d + r
{
  d := 0;
  r := x;

  while r >= y
    decreases r - y
    invariant x == y * d + r
  {
    r := r - y;
    d := d + 1;
  }
}