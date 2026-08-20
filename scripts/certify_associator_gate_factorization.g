# Certify the associator gate factorization.  The Galois action on the
# seven classes is [x',y'] -> [x',(y'^lambda)^(f_sigma(x',y'))] for
# lambda a square mod 23, composed with the branch swap for nonsquare
# lambda.  Fixing the published class is therefore an exact condition on
# the single evaluation f_sigma(x,y) in M23:
#
#   f_sigma(x,y) in <y> h_lambda C(x),
#
# a union of eleven disjoint (<y>,C(x)) double cosets, one per square,
# whose union is the known 1/15 inertia gate N(<y>)C(x).  The frame
# return of sigma is the canonical C(x)-component of the factorization,
# recovered choice-freely as the unique w in C(x) with y^w=(y^lambda)^f;
# returns compose multiplicatively, and the nonsquare coset returns are
# r times a square-part return, with complex conjugation returning r.

SizeScreen([100000,100000]);;

gA := (1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22);;
gB := (1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)(13,20)(15,17);;
G := Group(gA,gB);;
y := (1,2,11,10,16,9,6,3,23,19,20,14,21,17,4,8,22,5,18,15,13,7,12);;
x := (3,21)(4,16)(9,22)(10,15)(11,20)(12,19)(13,18)(14,17);;
r := (3,18)(4,16)(5,6)(7,23)(10,14)(12,19)(13,21)(15,17);;

C := Centralizer(G,x);;
N := Normalizer(G,Group(y));;
squares := Filtered([1..22],s -> Jacobi(s,23)=1);;
publishedOrbit := Orbit(C,y,OnPoints);;
publishedOrbitSet := Set(publishedOrbit);;

if Size(G)<>10200960
        or Size(C)<>2688
        or Size(N)<>253
        or Size(Intersection(N,C))<>1
        or Size(Centralizer(G,y))<>23
        or Size(Intersection(C,Group(y)))<>1
        or Length(squares)<>11
        or Length(publishedOrbit)<>2688
        or Length(publishedOrbitSet)<>2688
        or Intersection(Filtered([1..23],p -> p^x=p),
            Filtered([1..23],p -> p^r=p))<>[1,2,8] then
    Error("gate base data changed");
fi;

Ret := function(partner)
    local w;
    w := RepresentativeAction(C,y,partner,OnPoints);
    if w=fail or y^w<>partner then
        Error("return element does not exist");
    fi;
    return w;
end;;

# ---- the eleven square gates ----

gateReps := [];;
for lambda in squares do
    transporter := RepresentativeAction(G,y^lambda,y);
    if transporter=fail
            or (y^lambda)^transporter<>y
            or not transporter in N
            or Size(Intersection(Group(y),C^(transporter^-1)))<>1 then
        Error("gate transporter data changed");
    fi;
    Add(gateReps,transporter);
od;

# disjointness of the eleven double cosets
for i in [1..11] do
    for j in [i+1..11] do
        for shift in [0..22] do
            if gateReps[i]^-1*y^(-shift)*gateReps[j] in C then
                Error("gates are not disjoint");
            fi;
        od;
    od;
od;

# the eleven <y>-cosets of the gate transporters tile N(<y>)
tiling := Set(Concatenation(List([1..11],i ->
    List([0..22],shift -> y^shift*gateReps[i]))));;
if tiling<>Set(Elements(N))
        or 11*23*Size(C)<>Size(N)*Size(C)
        or Size(N)*Size(C)<>Size(G)/15 then
    Error("gate union is not the inertia gate");
fi;

# containment and component recovery on a structured sample
sampleComponents := Concatenation([(),x,r],GeneratorsOfGroup(C),
    [GeneratorsOfGroup(C)[1]*r]);;
for i in [1..11] do
    for shift in [0,7] do
        for component in sampleComponents do
            gateElement := y^shift*gateReps[i]*component;
            partner := (y^squares[i])^gateElement;
            if not partner in publishedOrbitSet
                    or Ret(partner)<>component then
                Error("gate containment or component recovery failed");
            fi;
        od;
    od;
od;

# negative membership sample
if (y^2)^gB in publishedOrbitSet then
    Error("negative gate sample failed");
fi;

# ---- composition of returns ----

sampleGate := [];;
for sampleData in [[0,1,1],[7,1,3],[0,2,4],[7,2,5]] do
    Add(sampleGate,[squares[sampleData[2]],
        y^sampleData[1]*gateReps[sampleData[2]]
        *sampleComponents[sampleData[3]]]);
od;
for firstSample in sampleGate do
    for secondSample in sampleGate do
        firstReturn := Ret((y^firstSample[1])^firstSample[2]);
        secondReturn := Ret((y^secondSample[1])^secondSample[2]);
        compositePartner := ((y^firstReturn)^secondSample[1])
            ^(secondSample[2]^firstReturn);
        if Ret(compositePartner)<>secondReturn*firstReturn then
            Error("square-square return composition failed");
        fi;
    od;
od;

# nonsquare normalization: y -> x*(y^-lambda)^f, return = r * square part
for lambda in [5,22] do
    for component in [(),GeneratorsOfGroup(C)[1],r] do
        gateElement := gateReps[Position(squares,(23-lambda) mod 23)]
            *component;
        squarePart := Ret((y^((23-lambda) mod 23))^gateElement);
        if Ret(x*((y^((23-lambda) mod 23))^gateElement))
                <>r*squarePart then
            Error("nonsquare return factorization failed");
        fi;
    od;
od;

# complex conjugation: lambda=-1, trivial associator value, return r
if Ret(x*y)<>r then
    Error("real instance does not return the branch reflection");
fi;

# nonsquare-nonsquare composition stays multiplicative
for mixData in [[22,(),5,()],[22,r,7,GeneratorsOfGroup(C)[1]]] do
    firstElement := gateReps[Position(squares,(23-mixData[1]) mod 23)]
        *mixData[2];
    secondElement := gateReps[Position(squares,(23-mixData[3]) mod 23)]
        *mixData[4];
    firstReturn := Ret(x*((y^((23-mixData[1]) mod 23))^firstElement));
    secondReturn := Ret(x*((y^((23-mixData[3]) mod 23))^secondElement));
    compositePartner := x*(((y^firstReturn)^((23-mixData[3]) mod 23))
        ^(secondElement^firstReturn));
    if Ret(compositePartner)<>secondReturn*firstReturn then
        Error("nonsquare-nonsquare composition failed");
    fi;
od;

# ---- outputs ----

output := OutputTextFile(
    "results/associator_gate_factorization_summary.txt",false);;
SetPrintFormattingStatus(output,false);;
AppendTo(output,
    "schema=m23.miraculous-fixed-point.associator-gate-factorization.v1\n",
    "published_x_frame_orbit=2688\n",
    "square_gate_count=11\n",
    "gate_double_coset_size=",23*Size(C),"\n",
    "gates_pairwise_disjoint=true\n",
    "gate_transporter_cosets_tile_inertia_normalizer=true\n",
    "gate_union_size=",Size(N)*Size(C),"\n",
    "gate_union_is_one_fifteenth_of_M23=true\n",
    "unique_factorization=f=a*h_lambda*b\n",
    "return_is_canonical_C_component=true\n",
    "return_component_recovery_verified=true\n",
    "return_composition_multiplicative=true\n",
    "nonsquare_return=r_times_square_part\n",
    "complex_conjugation_return=branch_reflection\n",
    "miracle_equivalent_to=f_sigma(x,y)_in_gate_for_all_sigma\n",
    "return_conjecture_on_stabilizer=return_mod_kernel_equals_boundary_representation\n",
    "return_conjecture_does_not_imply_gate_membership=true\n",
    "remaining_input=arithmetic_of_the_associator_evaluation\n"
);;
CloseStream(output);;

Print("eleven disjoint square gates, union = N(<y>)C(x) = |M23|/15\n");
Print("unique factorization f=a*h_lambda*b with canonical return b\n");
Print("returns compose multiplicatively; nonsquare coset = r*square\n");
Print("complex conjugation returns the branch reflection\n");

QUIT_GAP(0);
