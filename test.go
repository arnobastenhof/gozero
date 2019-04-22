package main;

const (
  m = 7;
  n = 85;
);

var (
  x, y, z, q, r int;
);

func multiply() {
  var a, b int;
  a = x;
  b = y;
  z = 0;
  for b > 0 {
    if b % 2 != 0 {
      z = z + a;
    };
    a = 2 * a;
    b = b / 2;
  };
};

func divide() {
  var w int;
  r = x;
  q = 0;
  w = y;
  for w <= r {
    w = 2 * w;
  };
  for w > y {
    q = 2 * q;
    w = w / 2;
    if w <= r {
      r = r - w;
      q = q + 1;
    };
  };
};

func gcd() {
  var f, g int;
  f = x;
  g = y;
  for f != g {
    if f < g {
      g = g - f;
    };
    if g < f {
      f = f - g;
    };
  };
  z = f;
};

func main() {
  x = m;
  y = n;
  multiply();

  x = 25;
  y = 3;
  divide();

  x = 84;
  y = 36;
  gcd();
};
