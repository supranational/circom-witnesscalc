pragma circom 2.0.0;

template MainTmpl() {
    signal input a[2];
    signal input b;
    signal output c;

    var x = 3;

    var y = 0;
    for (var i = 0; i < 2; i++) {
        y = y + a[i];
    }

    c <== y * b + x;
}

component main = MainTmpl();
