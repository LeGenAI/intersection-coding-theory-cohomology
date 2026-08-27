// Magma replay for the exact GF(13) lineage centered at length 20.

F := GF(13);
c := F!5;
sourceRow := [7,7,8,3,0,10,1,9,7,11,10];
A22 := Matrix(F,11,11,
    [F!sourceRow[((j-i) mod 11)+1] : i,j in [1..11]]);
G22 := HorizontalJoin(IdentityMatrix(F,11),A22);
G20 := Matrix(F,10,20,[
  0,0,0,0,0,0,0,0,0,7,4,11,3,3,4,12,6,6,3,7,
  1,0,0,0,0,0,0,0,0,1,4,2,10,8,1,6,8,7,4,5,
  0,1,0,0,0,0,0,0,0,7,8,1,2,7,10,11,7,0,1,4,
  0,0,1,0,0,0,0,0,0,11,6,8,4,7,6,11,12,1,7,8,
  0,0,0,1,0,0,0,0,0,11,8,4,5,10,5,3,2,4,3,0,
  0,0,0,0,1,0,0,0,0,12,7,1,4,11,6,11,1,5,3,3,
  0,0,0,0,0,1,0,0,0,8,1,0,7,7,5,1,11,5,5,4,
  0,0,0,0,0,0,1,0,0,11,12,7,8,9,9,5,6,11,1,2,
  0,0,0,0,0,0,0,1,0,3,11,11,6,1,10,12,5,1,11,3,
  0,0,0,0,0,0,0,0,1,9,6,10,1,10,5,10,9,5,6,5
]);
G18 := Matrix(F,9,18,[
  0,0,0,0,0,0,0,7,4,11,3,3,4,12,6,6,3,7,
  0,0,0,0,0,0,0,10,5,7,7,4,12,9,4,7,9,12,
  1,0,0,0,0,0,0,11,6,8,4,7,6,11,12,1,7,8,
  0,1,0,0,0,0,0,11,8,4,5,10,5,3,2,4,3,0,
  0,0,1,0,0,0,0,12,7,1,4,11,6,11,1,5,3,3,
  0,0,0,1,0,0,0,8,1,0,7,7,5,1,11,5,5,4,
  0,0,0,0,1,0,0,11,12,7,8,9,9,5,6,11,1,2,
  0,0,0,0,0,1,0,3,11,11,6,1,10,12,5,1,11,3,
  0,0,0,0,0,0,1,9,6,10,1,10,5,10,9,5,6,5
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

C22 := LinearCode(G22);
C20 := LinearCode(G20);
C18 := LinearCode(G18);
assert IsSelfDual(C22) and IsSelfDual(C20) and IsSelfDual(C18);
assert LinearCode(ReducePair(G22,1,16)) eq C20;
assert LinearCode(ReducePair(G20,1,2)) eq C18;
assert [MinimumWeight(C22),MinimumWeight(C20),MinimumWeight(C18)]
    eq [10,8,7];

minimum22 := MinimumWords(C22);
bestLoss := #minimum22+1;
bestPair := [0,0];
for first in [1..22] do
    for second in [1..22] do
        if first ne second then
            loss := #[w : w in minimum22 |
                w[first] ne 0 and w[second] eq c*w[first]];
            if loss lt bestLoss then
                bestLoss := loss;
                bestPair := [first,second];
            end if;
        end if;
    end for;
end for;
assert bestPair eq [1,16] and bestLoss eq 120;

minimum20 := MinimumWords(C20);
zeroLossPairs := 0;
bestDistance := 0;
for first in [1..20] do
    for second in [1..20] do
        if first ne second then
            loss := #[w : w in minimum20 |
                w[first] ne 0 and w[second] eq c*w[first]];
            if loss eq 0 then
                zeroLossPairs +:= 1;
                distance := MinimumWeight(LinearCode(ReducePair(G20,first,second)));
                if distance gt bestDistance then
                    bestDistance := distance;
                end if;
            end if;
        end if;
    end for;
end for;
assert zeroLossPairs eq 338 and bestDistance eq 7;

print "PASS GF13 repeated lineage";
print "levels", [<22,11,10,#minimum22>, <20,10,8,#minimum20>,
                 <18,9,7,72>];
print "first audit", 462, bestPair, bestLoss;
print "second audit", 380, zeroLossPairs, bestDistance;
print "W20", WeightDistribution(C20);
print "W18", WeightDistribution(C18);
