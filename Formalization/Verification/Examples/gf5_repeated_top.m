// Magma replay for the largest GF(5) repeated box in Section 4.

F := GF(5);
c := F!2;
A := Matrix(F,12,12,[
  4,1,1,1,1,1,1,1,4,0,1,4,
  1,4,1,1,1,1,1,4,1,1,4,0,
  1,1,4,1,1,1,4,1,1,4,0,1,
  4,4,4,4,1,1,1,0,4,4,4,1,
  4,4,4,1,4,1,0,4,1,4,1,4,
  4,4,4,1,1,4,4,1,0,1,4,4,
  4,4,1,4,0,1,4,1,1,1,1,1,
  4,1,4,0,1,4,1,4,1,1,1,1,
  1,4,4,1,4,0,1,1,4,1,1,1,
  0,4,1,1,1,4,4,4,4,4,1,1,
  4,1,0,1,4,1,4,4,4,1,4,1,
  1,0,4,4,1,1,4,4,4,1,1,4
]);
G24 := HorizontalJoin(2*IdentityMatrix(F,12),A);
G22 := Matrix(F,11,22,[
  0,0,0,0,0,0,0,0,0,1,0,1,1,4,3,4,3,3,1,3,3,2,
  2,0,0,0,0,0,0,0,0,2,0,0,1,2,0,2,0,3,0,2,3,1,
  0,2,0,0,0,0,0,0,0,3,0,2,4,0,2,0,0,2,2,3,1,0,
  0,0,2,0,0,0,0,0,0,2,0,3,4,0,0,2,0,4,3,0,3,2,
  0,0,0,2,0,0,0,0,0,2,0,3,4,2,3,2,4,3,0,0,0,0,
  0,0,0,0,2,0,0,0,0,2,0,3,4,2,0,0,3,0,4,2,3,0,
  0,0,0,0,0,2,0,0,0,2,0,3,1,0,4,2,3,0,0,2,0,2,
  0,0,0,0,0,0,2,0,0,3,0,0,4,4,2,3,2,0,2,0,2,0,
  0,0,0,0,0,0,0,2,0,2,0,0,4,2,3,1,0,0,3,2,0,2,
  0,0,0,0,0,0,0,0,2,2,0,4,1,2,0,0,3,3,3,0,0,2,
  0,0,0,0,0,0,0,0,0,0,2,1,4,4,1,1,4,4,4,1,1,4
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

C24 := LinearCode(G24);
C22 := LinearCode(G22);
assert IsSelfDual(C24) and IsSelfDual(C22);
assert [MinimumWeight(C24),MinimumWeight(C22)] eq [9,8];
assert LinearCode(ReducePair(G24,1,14)) eq C22;

words9 := MinimumWords(C24);
words10 := Words(C24,10);
lossFree := 0;
parentA8Counts := [];
for first in [1..24] do
    for second in [1..24] do
        if first ne second then
            loss := #[w : w in words9 |
                w[first] ne 0 and w[second] eq c*w[first]];
            if loss eq 0 then
                lossFree +:= 1;
                Append(~parentA8Counts, #[w : w in words10 |
                    w[first] ne 0 and w[second] eq c*w[first]]);
            end if;
        end if;
    end for;
end for;
assert #words9 eq 1056 and lossFree eq 132;
assert Setseq(Seqset(parentA8Counts)) eq [660];

print "PASS GF5 largest repeated box";
print "levels", [<22,11,8,660>, <24,12,9,#words9>];
print "audit", 552, lossFree, [1,14], "parent A8", 660;
print "W22", WeightDistribution(C22);
