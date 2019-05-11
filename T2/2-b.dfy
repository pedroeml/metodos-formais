// b) Seja o seguinte código Dafny. Complete com as asserções indicadas.
predicate letraA(a:seq<int>, j:int, k:int)
  requires 0 <= j < |a|;
  requires 0 <= k < |a|;
  requires j <= k;
{
  (forall e :: j <= e <= k ==> a[e] == 0)
}

predicate letraB(a:seq<int>, j:int, k:int)
  requires 0 <= j < |a|;
  requires 0 <= k < |a|;
  requires j <= k;
{
  (forall e :: 0 <= e < j && k < e < |a| ==> a[e] != 0)
}

predicate letraC(a:seq<int>, j:int, k:int)
  requires 0 <= j < |a|;
  requires 0 <= k < |a|;
  requires j <= k;
{
  (1 in a[..j] || 1 in a[k..|a|-1])
}

function count(a:seq<int>): int
  decreases a
{
  if |a| == 0 then
    0
  else if a[0] == 0 then
    1 + count(a[1..])
  else
    count(a[1..])
}

predicate letraD(a:seq<int>)
{
  count(a[..]) >= 2
}

predicate letraE(a:seq<int>)
{
  count(a[..]) <= 2
}

method Main()
{
  var a := new int[6];
  a[0], a[1], a[2], a[3], a[4], a[5] := 1, 0, 0, 0, 1, 1;
  var b := new int[3];
  b[0], b[1], b[2] := 1, 0, 1;
  var j, k := 1, 3;
  var p, r := 4, 5;
  assert letraA(a[..], j, k); // a) Todos elementos no intervalor a[j..k] são 0.
  assert letraB(a[..], j, k); // b) Todos zeros em a ocorrem no intervalo a[j..k].
  assert letraC(a[..], j, k); // c) Não é o caso que todos uns de a[0...n-1] (onde n é o tamanho de a) ocorrem no intervalor a[p..r].
  assert letraD(a[..]); // d) a[0..n-1] (onde n é o tamanho de a) possui pelo menos dois zeros.
  assert letraE(b[..]); // e) b[0..n-1] (onde n é o tamanho de b) possui no máximo dois zeros.
}
