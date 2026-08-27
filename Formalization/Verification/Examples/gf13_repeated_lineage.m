// Magma replay for the best-known-distance GF(13) construction.

F := GF(13);
c := F!5;
sourceRow := [3,7,5,5,2,8,5,6,3,0];
A20 := Matrix(F,10,10,
    [F!sourceRow[((j-i) mod 10)+1] : i,j in [1..10]]);
G20 := HorizontalJoin(IdentityMatrix(F,10),A20);
G18 := Matrix(F,9,18,[
  1,0,0,0,0,0,0,0,7,3,1,6,6,4,8,1,3,8,
  0,1,0,0,0,0,0,0,0,3,7,5,5,2,8,5,6,3,
  0,0,1,0,0,0,0,0,7,9,12,8,9,1,5,3,5,1,
  0,0,0,1,0,0,0,0,1,8,5,5,2,10,11,5,8,8,
  0,0,0,0,1,0,0,0,3,8,5,6,1,9,10,1,2,4,
  0,0,0,0,0,1,0,0,10,3,4,10,2,1,2,9,5,6,
  0,0,0,0,0,0,0,0,12,3,0,4,8,8,10,4,5,2,
  0,0,0,0,0,0,1,0,3,4,10,11,4,5,5,12,7,1,
  0,0,0,0,0,0,0,1,3,7,4,1,3,8,8,9,3,3
]);

function ReducePair(G,first,second)
    k := Nrows(G);
    functional := Matrix(F,k,1,
        [G[i,second]-c*G[i,first] : i in [1..k]]);
    basis := Basis(Nullspace(functional));
    assert #basis eq k-1;
    subcode := Matrix(F,k-1,k,&cat[Eltseq(v) : v in basis])*G;
    retained := [j : j in [1..Ncols(G)] | j ne first and j ne second];
    return ColumnSubmatrix(subcode,retained);
end function;

C20 := LinearCode(G20);
C18 := LinearCode(G18);
assert IsSelfDual(C20) and IsSelfDual(C18);
assert LinearCode(ReducePair(G20,11,7)) eq C18;
assert [MinimumWeight(C20),MinimumWeight(C18)] eq [10,8];

minimum20 := MinimumWords(C20);
bestLoss := #minimum20+1;
bestPairs := [];
zeroLossPairs := 0;
for first in [1..20] do
    for second in [1..20] do
        if first ne second then
            loss := #[w : w in minimum20 |
                w[first] ne 0 and w[second] eq c*w[first]];
            if loss lt bestLoss then
                bestLoss := loss;
                bestPairs := [<first,second>];
            elif loss eq bestLoss then
                Append(~bestPairs,<first,second>);
            end if;
            if loss eq 0 then zeroLossPairs +:= 1; end if;
        end if;
    end for;
end for;
assert bestLoss eq 1896 and #bestPairs eq 10 and zeroLossPairs eq 0;

print "PASS GF13 best-known repeated lineage";
print "levels", [<20,10,10,#minimum20>, <18,9,8,1896>];
print "pair audit", 380, bestLoss, #bestPairs, zeroLossPairs;
print "selected pair", <11,7>;
print "W20", WeightDistribution(C20);
print "W18", WeightDistribution(C18);
