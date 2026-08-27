// Exact A_6 audit for every two-coordinate reduction of the GF(13) MDS code.

F := GF(13);
c := F!5;
firstRow := [F | 2,9,10,9,2,1,1];
A := Matrix(F,7,7,
    [firstRow[((j-i) mod 7)+1] : i,j in [1..7]]);
C14 := LinearCode(HorizontalJoin(IdentityMatrix(F,7),A));
minimumWords := MinimumWords(C14);
assert MinimumWeight(C14) eq 8 and #minimumWords eq 36036;

parentA6 := [];
for first in [1..14] do
    for second in [1..14] do
        if first ne second then
            count := #[w : w in minimumWords |
                w[first] ne 0 and w[second] eq c*w[first]];
            Append(~parentA6,count);
        end if;
    end for;
end for;

assert #parentA6 eq 182;
assert Setseq(Seqset(parentA6)) eq [960];
print "PASS GF13 MDS parent A6 audit";
print "ordered pairs", #parentA6, "parent A6", 960;
