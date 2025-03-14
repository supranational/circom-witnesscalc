pragma circom 2.1.9;

template Main() {
  signal input a,b;
  signal output foo;

  signal x,y,z;
  x <-- ~a;
  y <-- !(x && a);
  z <-- b ** a;

  foo <== x + y + z;

  // some fake constraint so that the above won't be optimied away
  signal nulla;
  nulla <-- 0;
  0 === nulla * (foo - a - b);
}

component main {public [a,b]} = Main();
