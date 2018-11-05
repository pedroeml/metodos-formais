// b) Seja o seguinte código Dafny. Complete com as asserções indicadas.
method problema2b() {
  var a := new int[6];
  a[0],a[1],a[2],a[3],a[4],a[5] := 1,0,0,0,1,1;
  var b := new int[3];
  b[0],b[1],b[2] := 1,0,1;
  var j,k := 1,3;
  var p,r := 4,5;
// a) Todos elementos no intervalor a[j..k] são 0.
// b) Todos zeros em a ocorrem no intervalo a[j..k].
// c) Não é o caso que todos uns de a[0...n-1] (onde n é o tamanho de a) ocorrem no intervalor a[p..r].
// d) a[0..n-1] (onde n é o tamanho de a) possui pelo menos dois zeros.
// e) b[0..n-1] (onde n é o tamanho de b) possui no máximo dois zeros.
}