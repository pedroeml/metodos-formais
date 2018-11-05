// Implementar de forma iterativa o cálculo do quociente da divisão inteira entre dois números naturais. 
// Dica: por definição, o quociente da divisão inteira entre 𝑥 e 𝑦 é o único 𝑑 tal que existe um resto 𝑟 tal que 𝑟<𝑦 e 𝑥=𝑑×𝑦+𝑟.
function div(x: nat, y: nat): int
{
  if y == 0 then 0 else x / y  
}

method CalculaQuociente(x: nat, y: nat) returns (d: int)
  requires x >= y
  requires x >= 0 && y > 0
  ensures y > 0 ==> d == div(x, y) 
  ensures y == 0 ==> d == 0
{
  d := 0;
  var r := x;
  if y != 0 
  {
    while r >= y
    invariant x == y * d + r 
    {
      r := r - y;
      d := d + 1;
    }
  }
}

method Main() {
    var result := CalculaQuociente(4, 2);
}