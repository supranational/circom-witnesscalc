pragma circom 2.1.1;

include "../test_deps/iden3-circuits-authV2/circuits/linked/multiQuery.circom";

component main = LinkedMultiQuery(10, 32, 64); // 175331 constraints
