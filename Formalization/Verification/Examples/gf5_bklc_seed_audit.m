F := GF(5);

for n in [20, 22, 24] do
    k := n div 2;
    C, available := BKLC(F, n, k);
    print "BKLC", n, k, "available", available;
    assert available;
    print "parameters", Length(C), Dimension(C), MinimumWeight(C);
    print "self_dual", IsSelfDual(C);
    print "lower_upper", BKLCLowerBound(F, n, k), BKLCUpperBound(F, n, k);
end for;

quit;
