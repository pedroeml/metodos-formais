function div(x: nat, y: nat): int
{
  if y == 0 then 0 else x / y  
}

method CalculaQuociente(x: nat, y: nat) returns (d: int)
  requires x >= y
  requires x >= 0 && y >= 0
  ensures d == div(x, y) 
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
