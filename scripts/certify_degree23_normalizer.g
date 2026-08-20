# Exact normalizer input used by the GT/boundary transport comparison.

SizeScreen([100000,100000]);;

gA := (1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22);;
gB := (1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)
      (13,20)(15,17);;
G := Group(gA,gB);;
ambient := SymmetricGroup(23);;
ambientCentralizer := Centralizer(ambient,G);;
ambientNormalizer := Normalizer(ambient,G);;

if Size(G)<>10200960
        or Size(ambientCentralizer)<>1
        or ambientNormalizer<>G then
    Error("the natural degree-23 M23 action is not self-normalizing");
fi;

rows := [
    "schema=m23.fixed-point.degree23-normalizer.v1",
    Concatenation("group_order=",String(Size(G))),
    Concatenation(
        "ambient_centralizer_order=",String(Size(ambientCentralizer))
    ),
    Concatenation(
        "ambient_normalizer_order=",String(Size(ambientNormalizer))
    ),
    "ambient_normalizer_equals_M23=true"
];;

output := OutputTextFile("results/degree23_normalizer_summary.txt",false);;
SetPrintFormattingStatus(output,false);;
for row in rows do
    AppendTo(output,row,"\n");
od;
CloseStream(output);;

for row in rows do
    Print(row,"\n");
od;
Print("PASS_DEGREE23_NORMALIZER\n");
