pragma circom 2.0.0;

include "poseidon_constants.circom";

function f1(t, x) {
    var r;
    for (var i = 0; i < 2; i++) {
	    for (var j = 0; j < 2; j++) {
		   r += x[i][j];
		}
	}
    if (t == 2) {
        return
        [
            [
                0x66f6f85d6f68a85ec10345351a23a3aaf07f38af8c952a7bceca70bd2af7ad5,
                0xcc57cdbb08507d62bf67a4493cc262fb6c09d557013fff1f573f431221f8ff9
            ],
            [
                0x2b9d4b4110c9ae997782e1509b1d0fdb20a7c02bbd8bea7305462b9f8125b1e8,
                0x1274e649a32ed355a31a6ed69724e1adade857e86eb5c3a121bcd147943203c8
            ]
        ];
    } else if (t==3) {
        return
        [
            [
                0x109b7f411ba0e4c9b2b70caf5c36a7b194be7c11ad24378bfedb68592ba8118b,
                0x2969f27eed31a480b9c36c764379dbca2cc8fdd1415c3dded62940bcde0bd771,
                0x143021ec686a3f330d5f9e654638065ce6cd79e28c5b3753326244ee65a1b1a7
            ],
            [
                0x16ed41e13bb9c0c66ae119424fddbcbc9314dc9fdbdeea55d6c64543dc4903e0,
                0x2e2419f9ec02ec394c9871c832963dc1b89d743c8c7b964029b2311687b1fe23,
                0x176cc029695ad02582a70eff08a6fd99d057e12e58e7d7b6b16cdfabc8ee2911
            ],
            [
                0x2b90bba00fca0589f617e7dcbfe82e0df706ab640ceb247b791a93b74e36736d,
                0x101071f0032379b697315876690f053d148d4e109f5fb065c8aacc55a0f89bfa,
                0x19a3fc0a56702bf417ba7fee3802593fa644470307043f7773279cd71d25d5e0
            ]
        ];
    } else {
        assert(0);
        return [[0]];
    }
}


template Pos(nInputs) {
    
    signal input a;
    signal input b;
    signal output c;

    var t = nInputs + 1;
	var x[2][2] = [[1, 2], [3, 4]];
	var C[3][3] = f1(t, x);

	c <== a * C[0][0] * b;
}

component main = Pos(2);