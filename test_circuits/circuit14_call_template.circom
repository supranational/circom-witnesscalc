pragma circom 2.0.0;

include "bitify.circom";

template MainTmpl() {
    signal input a[3];
    signal input b;
    signal output c;

	component b2n = Bits2Num(3);

	for (var i = 0; i < 3; i++) {
		b2n.in[i] <== a[i];
	}

	c <== b2n.out * b;
}

component main = MainTmpl();
