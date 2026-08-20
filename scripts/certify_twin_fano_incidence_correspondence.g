# Exact finite certificate for the choice-free twin-point/original-line
# correspondence.
#
# The canonical tripod switch c_T identifies the point set of the original
# Fano plane with the point set of a twin Mathieu frame.  Transporting the
# Fano incidence relation across that identification gives a canonical
# bidegree-(3,3) correspondence from twin points to original lines.  Its
# 7-by-7 incidence matrix has determinant 24 and is therefore an isomorphism
# of rational permutation modules.  It is not itself the graph of a
# point-line bijection: point and line stabilizers in PSL(3,2) are
# nonconjugate.  Later in this certificate the incidence-selected ordering
# of the marked cut does select a unique outer-twisted correlation.
# Some internal identifiers below retain the historical word "polarity";
# there it means an involutive correlation only after the marked twin and
# original planes have been identified.  It does not assert an intrinsic
# self-correlation of one plane.

SizeScreen([100000,100000]);;

gA := (1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22);;
gB := (1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)
      (13,20)(15,17);;
G := Group(gA,gB);;
sheetRelabelGenerators := [
    (1,2),
    (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23)
];;
y := (1,2,11,10,16,9,6,3,23,19,20,14,21,17,4,8,22,5,18,15,
      13,7,12);;
x := (3,21)(4,16)(9,22)(10,15)(11,20)(12,19)(13,18)(14,17);;
r := (3,18)(4,16)(5,6)(7,23)(10,14)(12,19)(13,21)(15,17);;

# The pointed Hilbert--90 switch a |-> -a+7 in the y-cycle coordinate.
cyclePoints := [1];;
for index in [2..23] do
    Add(cyclePoints,cyclePoints[index-1]^y);
od;
CycleCoordinate := point -> Position(cyclePoints,point)-1;;
cT := PermList(List([1..23],point ->
    cyclePoints[((-CycleCoordinate(point)+7) mod 23)+1]
));;

C := Centralizer(G,x);;
H := Set(Filtered([1..23],point -> point^x=point));;
pointHom := ActionHomomorphism(C,H,OnPoints);;
F := Image(pointHom);;
fanoLines := Set(List(
    Filtered(AsList(F),element -> Order(element)=2),
    element -> Set(Filtered([1..7],point -> point^element=point))
));;
lineSheets := List(fanoLines,line -> Set(List(line,i -> H[i])));;

twinC := C^cT;;
twinX := x^cT;;
twinH := Set(Filtered([1..23],point -> point^twinX=point));;
twinPointHom := ActionHomomorphism(twinC,twinH,OnPoints);;
twinF := Image(twinPointHom);;
twinFanoLines := Set(List(
    Filtered(AsList(twinF),element -> Order(element)=2),
    element -> Set(Filtered([1..7],point -> point^element=point))
));;
twinLineSheets := List(twinFanoLines,line ->
    Set(List(line,index -> twinH[index]))
);;

# Pull a twin point back through c_T, then use ordinary Fano incidence.
incidenceMatrix := List(twinH,q -> List([1..7],function(lineIndex)
    if Position(H,q^cT) in fanoLines[lineIndex] then
        return 1;
    fi;
    return 0;
end));;
antiIncidenceMatrix := List(incidenceMatrix,row ->
    List(row,value -> 1-value));;
identity7 := IdentityMat(7);;
ones7 := List([1..7],i -> List([1..7],j -> 1));;
gramExpected := 2*identity7+ones7;;
gram := incidenceMatrix*TransposedMat(incidenceMatrix);;
determinant := DeterminantMat(incidenceMatrix);;
inverseFormula := (1/2)*TransposedMat(incidenceMatrix)-(1/6)*ones7;;

RelationPairs := Set(Concatenation(List([1..7],i -> List(
    Filtered([1..7],j -> incidenceMatrix[i][j]=1),
    j -> [twinH[i],lineSheets[j]]
))));;
LineImage := function(line,g)
    return Set(List(line,point -> point^g));
end;;

# The switch carries the forward packet (twin points, original lines) to
# the backward packet (original points, twin lines) without exchanging the
# point and line sides.  With transported orders, the two incidence matrices
# are literally equal, and a second application is the identity.
backwardPointOrder := List(twinH,point -> point^cT);;
backwardLineOrder := List(lineSheets,line -> LineImage(line,cT));;
backwardIncidenceMatrix := List(backwardPointOrder,point -> List(
    backwardLineOrder,function(line)
        if point^cT in line then return 1; fi;
        return 0;
    end
));;
BackwardRelationPairs := Set(Concatenation(List(
    backwardPointOrder,point -> List(
        Filtered(backwardLineOrder,line -> point^cT in line),
        line -> [point,line]
    )
)));;
switchTransportedRelation := Set(List(RelationPairs,pair -> [
    pair[1]^cT,LineImage(pair[2],cT)
]));;
switchReturnedRelation := Set(List(switchTransportedRelation,pair -> [
    pair[1]^cT,LineImage(pair[2],cT)
]));;

relationEquivariance := ForAll(GeneratorsOfGroup(C),g ->
    Set(List(RelationPairs,pair -> [
        pair[1]^(g^cT),LineImage(pair[2],g)
    ]))=RelationPairs
);;
frameKernel := Kernel(pointHom);;
frameKernelTrivialOnPacket := ForAll(
    GeneratorsOfGroup(frameKernel),g ->
        ForAll(twinH,point -> point^(g^cT)=point)
        and ForAll(lineSheets,line -> LineImage(line,g)=line)
);;
branchReflectionPacketPreserved := r in C and Set(List(
    RelationPairs,pair -> [
        pair[1]^(r^cT),LineImage(pair[2],r)
    ]
))=RelationPairs;;

# Rebuild the entire relation after a simultaneous relabelling.  This checks
# label independence, not merely equivariance inside the fixed x-frame.
BuildRelation := function(ambientGroup,frame,switch)
    local centralizer,points,hom,plane,lines,linesOnSheets,twinPoints;
    centralizer := Centralizer(ambientGroup,frame);
    points := Set(Filtered([1..23],point -> point^frame=point));
    hom := ActionHomomorphism(centralizer,points,OnPoints);
    plane := Image(hom);
    lines := Set(List(
        Filtered(AsList(plane),element -> Order(element)=2),
        element -> Set(Filtered([1..7],point -> point^element=point))
    ));
    linesOnSheets := List(lines,line -> Set(List(line,i -> points[i])));
    twinPoints := Set(Filtered([1..23],point -> point^(frame^switch)=point));
    return Set(Concatenation(List(twinPoints,q -> List(
        Filtered([1..7],j -> Position(points,q^switch) in lines[j]),
        j -> [q,linesOnSheets[j]]
    ))));
end;;
labelEquivariance := ForAll(sheetRelabelGenerators,g ->
    BuildRelation(G^g,x^g,cT^g)=Set(List(RelationPairs,pair -> [
        pair[1]^g,LineImage(pair[2],g)
    ]))
);;

# The two orbitals in point x line are incidence and anti-incidence.  They
# span every rational F-equivariant linear correspondence.
pointStabilizer := Stabilizer(F,1);;
lineStabilizer := Stabilizer(F,fanoLines[1],OnSets);;
pointCharacter := PermutationCharacter(F,pointStabilizer);;
lineCharacter := PermutationCharacter(F,lineStabilizer);;
pointLinePairs := Cartesian([1..7],[1..7]);;
pairAction := function(pair,g)
    return [pair[1]^g,Position(fanoLines,OnSets(fanoLines[pair[2]],g))];
end;;
pairOrbits := OrbitsDomain(F,pointLinePairs,pairAction);;

# The marked cut does pick one incidence arrow, but not a two-point phase
# bijection.  This is the exact reason the linear correspondence does not
# by itself supply the missing S_2-torsor section.
deltaSheets := Intersection(H,Filtered([1..23],point -> point^r=point));;
Psheet := 8;;
P := Position(H,Psheet);;
delta := Set(List(deltaSheets,sheet -> Position(H,sheet)));;
deltaIndex := Position(fanoLines,delta);;
tripodCut := Intersection(H,twinH);;
linePhaseIndices := Difference(
    Filtered([1..7],j -> P in fanoLines[j]),[deltaIndex]
);;
cutCompanions := Difference(tripodCut,[Psheet]);;
cutPhaseDegrees := List(cutCompanions,q -> Number(linePhaseIndices,j ->
    incidenceMatrix[Position(twinH,q)][j]=1
));;
selectedCutPoint := cutCompanions[Position(cutPhaseDegrees,1)];;
selectedLineIndex := Filtered(linePhaseIndices,j ->
    incidenceMatrix[Position(twinH,selectedCutPoint)][j]=1
)[1];;

# The integral defect of N is itself canonical.  Its 2-primary part is the
# binary simplex code on each side.  The seven nonzero words on the twin
# side are complements of original lines; dually, the seven nonzero words
# on the line side are complements of twin-point pencils.
smithNormalForm := SmithNormalFormIntegerMat(incidenceMatrix);;
smithDiagonal := DiagonalOfMat(smithNormalForm);;
F2 := GF(2);;
zero7F2 := List([1..7],i -> Zero(F2));;
N2 := incidenceMatrix*One(F2);;
allF2Vectors7 := AsList(F2^7);;
leftKernelVectors := Difference(Filtered(allF2Vectors7,vector ->
    vector*N2=zero7F2
),[zero7F2]);;
rightKernelVectors := Difference(Filtered(allF2Vectors7,vector ->
    vector*TransposedMat(N2)=zero7F2
),[zero7F2]);;
lineComplementVectors := List([1..7],lineIndex -> List(
    [1..7],pointIndex -> antiIncidenceMatrix[pointIndex][lineIndex]*One(F2)
));;
pointOffPencilVectors := List([1..7],pointIndex ->
    antiIncidenceMatrix[pointIndex]*One(F2)
);;

BlockEntry := function(i,j)
    if i<=7 and j>7 then return incidenceMatrix[i][j-7]; fi;
    if i>7 and j<=7 then return incidenceMatrix[j][i-7]; fi;
    return 0;
end;;
blockMatrix := List([1..14],i -> List([1..14],j -> BlockEntry(i,j)));;
blockSmithDiagonal := DiagonalOfMat(
    SmithNormalFormIntegerMat(blockMatrix)
);;
blockRadicalBasis2 := NullspaceMat(blockMatrix*One(F2));;

# The discriminant linking pairing on coker(B), B=[0 N;N^T 0], pulls back
# along ker(B mod 2) -> coker(B)[2], v |-> Bv/2.  On the two side-pure
# seven-sets it is zero precisely on incidence and 1/2 on anti-incidence.
linkingValues := List(lineComplementVectors,leftVector -> List(
    pointOffPencilVectors,rightVector ->
        ScalarProduct(
            List(leftVector,Int)*incidenceMatrix,List(rightVector,Int)
        )/4
));;
linkingBits := List(linkingValues,row -> List(row,value ->
    (2*value) mod 2
));;
lineByPointIncidence := TransposedMat(incidenceMatrix);;
lineByPointAntiIncidence := List(lineByPointIncidence,row ->
    List(row,value -> 1-value)
);;

# Recover the complete order-336 point-line symmetry from N.  The marked
# flag stabilizer is D16.  Its four phase vertices embed canonically as four
# distinguished nonzero vectors in the mod-2 radical.
rowToOriginalPoint := List(twinH,q -> Position(H,q^cT));;
LiftCollineation := function(g)
    return PermList(Concatenation(
        List([1..7],row -> Position(
            rowToOriginalPoint,rowToOriginalPoint[row]^g
        )),
        List([1..7],lineIndex -> 7+Position(
            fanoLines,OnSets(fanoLines[lineIndex],g)
        ))
    ));
end;;
dualities := [];;
for pointToLine in AsList(SymmetricGroup(7)) do
    lineToPointList := [];
    good := true;
    for lineIndex in [1..7] do
        candidates := Filtered([1..7],pointIndex -> ForAll([1..7],i ->
            incidenceMatrix[i][lineIndex]
                = incidenceMatrix[pointIndex][i^pointToLine]
        ));
        if Length(candidates)<>1 then
            good := false;
            break;
        fi;
        Add(lineToPointList,candidates[1]);
    od;
    if good and Set(lineToPointList)=[1..7] then
        Add(dualities,[pointToLine,PermList(lineToPointList)]);
    fi;
od;
LiftCorrelation := function(duality)
    return PermList(Concatenation(
        List([1..7],pointIndex -> 7+pointIndex^duality[1]),
        List([1..7],lineIndex -> lineIndex^duality[2])
    ));
end;;
incidenceCollineationGroup := Group(List(
    GeneratorsOfGroup(F),LiftCollineation
));;
incidenceAutomorphismGroup := Group(Concatenation(
    GeneratorsOfGroup(incidenceCollineationGroup),
    [LiftCorrelation(dualities[1])]
));;
rowP := Position(rowToOriginalPoint,P);;
flagEdge := Set([rowP,7+deltaIndex]);;
extendedFlagStabilizer := Stabilizer(
    incidenceAutomorphismGroup,flagEdge,OnSets
);;
pointPhaseRows := List(Difference(delta,[P]),point ->
    Position(rowToOriginalPoint,point)
);;
phaseSquare := Concatenation(
    pointPhaseRows,List(linePhaseIndices,lineIndex -> 7+lineIndex)
);;
phaseSquareHom := ActionHomomorphism(
    extendedFlagStabilizer,phaseSquare,OnPoints
);;
zero14Half := zero7F2;
distinguishedRadicalVectors := Concatenation(
    List([1..7],pointIndex -> Concatenation(
        zero14Half,pointOffPencilVectors[pointIndex]
    )),
    List([1..7],lineIndex -> Concatenation(
        lineComplementVectors[lineIndex],zero14Half
    ))
);;
ActVector := function(vector,g)
    return List([1..Length(vector)],i -> vector[i^(g^-1)]);
end;;
RadicalCarrierPermutation := function(g)
    return PermList(List(distinguishedRadicalVectors,vector ->
        Position(distinguishedRadicalVectors,ActVector(vector,g))
    ));
end;;
radicalCarrierImage := Group(List(
    GeneratorsOfGroup(incidenceAutomorphismGroup),
    RadicalCarrierPermutation
));;
phaseRadicalVectors := List(
    phaseSquare,vertex -> distinguishedRadicalVectors[vertex]
);;
PhaseRadicalPermutation := function(g)
    return PermList(List(phaseRadicalVectors,vector ->
        Position(phaseRadicalVectors,ActVector(vector,g))
    ));
end;;
phaseRadicalEquivariance := ForAll(
    GeneratorsOfGroup(extendedFlagStabilizer),g ->
        PhaseRadicalPermutation(g)=Image(phaseSquareHom,g)
);;

# The superficially attractive characteristic-3 explanation is false.  The
# block radical is two-dimensional, hence has four projective points, but
# D16 acts on them only through C2 rather than through the phase-square D8.
F3 := GF(3);;
blockRadicalBasis3 := NullspaceMat(blockMatrix*One(F3));;
blockRadicalSpace3 := VectorSpace(F3,blockRadicalBasis3);;
blockRadicalLinearBasis3 := Basis(
    blockRadicalSpace3,blockRadicalBasis3
);;
NormalizeProjective := function(vector)
    local first;
    first := First([1..Length(vector)],i -> not IsZero(vector[i]));
    return vector/vector[first];
end;;
projectiveRadicalLines3 := Set(List(
    Difference(AsList(F3^2),[[Zero(F3),Zero(F3)]]),
    NormalizeProjective
));;
RadicalMatrix3 := function(g)
    return List(blockRadicalBasis3,vector -> Coefficients(
        blockRadicalLinearBasis3,ActVector(vector,g)
    ));
end;;
ProjectiveRadicalPermutation3 := function(g)
    local matrix;
    matrix := RadicalMatrix3(g);
    return PermList(List(projectiveRadicalLines3,vector -> Position(
        projectiveRadicalLines3,NormalizeProjective(vector*matrix)
    )));
end;;
projectiveRadicalImage3 := Group(List(
    GeneratorsOfGroup(extendedFlagStabilizer),
    ProjectiveRadicalPermutation3
));;

# The marked tripod also defines an unordered packet of the two involutive
# flag correlations compatible with its selected point/line phase arrow.
# Summing their graphs gives a weighted bidegree-(2,2) correspondence without
# choosing between them.
flagDualities := Filtered(dualities,duality ->
    rowP^duality[1]=deltaIndex and deltaIndex^duality[2]=rowP
);;
selectedOriginalPoint := Position(H,2);;
selectedPhaseRow := Position(rowToOriginalPoint,selectedOriginalPoint);;
otherPhaseRow := Difference(pointPhaseRows,[selectedPhaseRow])[1];;
otherPhaseLine := Difference(linePhaseIndices,[selectedLineIndex])[1];;
compatiblePolarities := Filtered(flagDualities,duality ->
    selectedPhaseRow^duality[1]=selectedLineIndex
    and otherPhaseRow^duality[1]=otherPhaseLine
    and Order(LiftCorrelation(duality))=2
);;
polarityPacketMatrix := List([1..7],pointIndex -> List(
    [1..7],lineIndex -> Number(compatiblePolarities,duality ->
        pointIndex^duality[1]=lineIndex
    )
));;
polarityPacketSupport := List(polarityPacketMatrix,row -> List(
    row,function(value)
        if value>0 then return 1; fi;
        return 0;
    end
));;
polarityAgreementRows := Filtered([1..7],pointIndex ->
    polarityPacketMatrix[pointIndex]
        [pointIndex^compatiblePolarities[1][1]]=2
);;
polarityAgreementSheets := Set(List(
    polarityAgreementRows,row -> H[rowToOriginalPoint[row]]
));;
polarityAgreementTwinSheets := Set(List(
    polarityAgreementRows,row -> twinH[row]
));;
polarityPacketRank := RankMat(polarityPacketMatrix);;
polarityPacketSmithDiagonal := DiagonalOfMat(
    SmithNormalFormIntegerMat(polarityPacketMatrix)
);;
rFano := Image(pointHom,r);;
rowReflection := PermList(List([1..7],row -> Position(
    rowToOriginalPoint,rowToOriginalPoint[row]^rFano
)));;
lineReflection := PermList(List([1..7],lineIndex -> Position(
    fanoLines,OnSets(fanoLines[lineIndex],rFano)
)));;
polarityRelativePoint := compatiblePolarities[1][1]
    * compatiblePolarities[2][1]^-1;;
polarityRelativeLine := compatiblePolarities[1][2]
    * compatiblePolarities[2][2]^-1;;
relativePointIsReflection := polarityRelativePoint=rowReflection
    or polarityRelativePoint=rowReflection^-1;;
relativeLineIsReflection := polarityRelativeLine=lineReflection
    or polarityRelativeLine=lineReflection^-1;;

# A noncollinear triangle is a projective basis.  The common cut therefore
# gives a canonical point-plane identification (fix its three shared sheets)
# and a canonical basis polarity (send each vertex to the opposite side).
# Their composite is a single outer-twisted twin-point/original-line map.
originalCutPositions := Set(List(
    tripodCut,sheet -> Position(H,sheet)
));;
twinCutPositions := Set(List(
    tripodCut,sheet -> Position(twinH,sheet)
));;
twinToOriginalPlaneIsomorphisms := Filtered(
    AsList(SymmetricGroup(7)),isomorphism ->
        Set(List(twinFanoLines,line -> OnSets(line,isomorphism)))
            = Set(fanoLines)
);;
identityCutPlaneIsomorphisms := Filtered(
    twinToOriginalPlaneIsomorphisms,isomorphism ->
        ForAll(tripodCut,sheet ->
            Position(twinH,sheet)^isomorphism=Position(H,sheet)
        )
);;
OppositeCutLine := function(sheet)
    local otherSheets;
    otherSheets := Difference(tripodCut,[sheet]);
    return Filtered([1..7],lineIndex ->
        IsSubset(lineSheets[lineIndex],otherSheets)
    )[1];
end;;
triangleCorrelationCandidates := Filtered(dualities,duality ->
    ForAll(tripodCut,sheet ->
        Position(twinH,sheet)^duality[1]=OppositeCutLine(sheet)
    )
);;
triangleCorrelation := triangleCorrelationCandidates[1];;
triangleCorrelationMap := List([1..7],row -> [
    twinH[row],lineSheets[row^triangleCorrelation[1]]
]);;
triangleSelectedArrow := Position(twinH,2)^triangleCorrelation[1]
    = Position(lineSheets,[5,6,8]);;
triangleFlagPreserving := rowP^triangleCorrelation[1]=deltaIndex
    and deltaIndex^triangleCorrelation[2]=rowP;;
triangleCorrelationOrder := Order(LiftCorrelation(triangleCorrelation));;
triangleInCompatibleFlagPacket := triangleCorrelation in compatiblePolarities;;
compatiblePolarityMaps := List(compatiblePolarities,duality -> List(
    [1..7],row -> [twinH[row],lineSheets[row^duality[1]]]
));;
otherCutPoint := Difference(cutCompanions,[selectedCutPoint])[1];;
orientedCutCycle := [selectedCutPoint,otherCutPoint,Psheet];;
orientedCutPolarityCandidates := Filtered(
    compatiblePolarities,duality -> ForAll([1..3],index ->
        orientedCutCycle[index] in lineSheets[
            Position(twinH,orientedCutCycle[index])^duality[1]
        ]
        and orientedCutCycle[(index mod 3)+1] in lineSheets[
            Position(twinH,orientedCutCycle[index])^duality[1]
        ]
    )
);;
orientedCutPolarity := orientedCutPolarityCandidates[1];;
orientedCutPolarityMap := List([1..7],row -> [
    twinH[row],lineSheets[row^orientedCutPolarity[1]]
]);;
orientedCutSelectedPhaseArrow := Position(twinH,6)
    ^orientedCutPolarity[1]=selectedLineIndex;;
orientedCutFlagPreserving := rowP^orientedCutPolarity[1]=deltaIndex
    and deltaIndex^orientedCutPolarity[2]=rowP;;
orientedCutPolarityOrder := Order(LiftCorrelation(orientedCutPolarity));;

# Conceptual factorization.  A noncollinear triangle is a projective basis
# over F_2, so there is a unique twin-plane collineation rotating the ordered
# cut backwards.  Composing that rotation with the cut's opposite-side
# correlation is exactly the oriented-cut polarity.
backwardCutCycle := [Psheet,selectedCutPoint,otherCutPoint];;
cutRotationCandidates := Filtered(AsList(twinF),rotation ->
    List(orientedCutCycle,sheet ->
        twinH[Position(twinH,sheet)^rotation]
    )=backwardCutCycle
);;
cutRotation := cutRotationCandidates[1];;
cutRotationOrder := Order(cutRotation);;
orientedCutFactorization :=
    cutRotation*triangleCorrelation[1]=orientedCutPolarity[1];;

BuildOrientedCutPolarity := function(
    ambientGroup,frame,reflection,switch,markedPoint
)
    local centralizer,points,hom,plane,lines,linesOnSheets,twinPoints,
          matrix,cut,axisSheets,axis,axisIndex,pointIndex,sourcePointIndex,
          onAxisCut,offAxisCut,pointPhaseSheets,otherPhaseSheet,
          selectedSource,otherSource,linePhaseIndices,selectedLine,
          otherLine,cycle,correlations,pointToLine,lineToPointList,good,
          lineIndex,candidates,sourceIndex,duality,lifted,solutions;
    centralizer := Centralizer(ambientGroup,frame);
    points := Set(Filtered([1..23],point -> point^frame=point));
    hom := ActionHomomorphism(centralizer,points,OnPoints);
    plane := Image(hom);
    lines := Set(List(
        Filtered(AsList(plane),element -> Order(element)=2),
        element -> Set(Filtered([1..7],point -> point^element=point))
    ));
    linesOnSheets := List(lines,line -> Set(List(line,i -> points[i])));
    twinPoints := Set(Filtered(
        [1..23],point -> point^(frame^switch)=point
    ));
    matrix := List(twinPoints,sourcePoint -> List(
        linesOnSheets,function(line)
            if sourcePoint^switch in line then return 1; fi;
            return 0;
        end
    ));
    cut := Intersection(points,twinPoints);
    axisSheets := Intersection(points,Filtered(
        [1..23],point -> point^reflection=point
    ));
    axis := Set(List(axisSheets,sheet -> Position(points,sheet)));
    axisIndex := Position(lines,axis);
    pointIndex := Position(points,markedPoint);
    sourcePointIndex := Position(twinPoints,markedPoint^(switch^-1));
    onAxisCut := Difference(Intersection(cut,axisSheets),[markedPoint]);
    offAxisCut := Difference(cut,axisSheets);
    pointPhaseSheets := Difference(axisSheets,[markedPoint]);
    otherPhaseSheet := Difference(pointPhaseSheets,onAxisCut)[1];
    selectedSource := Position(twinPoints,onAxisCut[1]^(switch^-1));
    otherSource := Position(twinPoints,otherPhaseSheet^(switch^-1));
    linePhaseIndices := Difference(
        Filtered([1..7],j -> pointIndex in lines[j]),[axisIndex]
    );
    selectedLine := Filtered(linePhaseIndices,j ->
        offAxisCut[1] in linesOnSheets[j]
    )[1];
    otherLine := Difference(linePhaseIndices,[selectedLine])[1];
    cycle := [
        offAxisCut[1]^(switch^-1),
        onAxisCut[1]^(switch^-1),
        markedPoint^(switch^-1)
    ];
    correlations := [];
    for pointToLine in AsList(SymmetricGroup(7)) do
        lineToPointList := [];
        good := true;
        for lineIndex in [1..7] do
            candidates := Filtered([1..7],sourceIndex ->
                ForAll([1..7],i ->
                    matrix[i][lineIndex]
                        = matrix[sourceIndex][i^pointToLine]
                )
            );
            if Length(candidates)<>1 then
                good := false;
                break;
            fi;
            Add(lineToPointList,candidates[1]);
        od;
        if good and Set(lineToPointList)=[1..7] then
            Add(correlations,[pointToLine,PermList(lineToPointList)]);
        fi;
    od;
    solutions := [];
    for duality in correlations do
        lifted := PermList(Concatenation(
            List([1..7],i -> 7+i^duality[1]),
            List([1..7],j -> j^duality[2])
        ));
        if sourcePointIndex^duality[1]=axisIndex
                and axisIndex^duality[2]=sourcePointIndex
                and selectedSource^duality[1]=selectedLine
                and otherSource^duality[1]=otherLine
                and Order(lifted)=2
                and ForAll([1..3],index ->
                    cycle[index] in linesOnSheets[
                        Position(twinPoints,cycle[index])^duality[1]
                    ]
                    and cycle[(index mod 3)+1] in linesOnSheets[
                        Position(twinPoints,cycle[index])^duality[1]
                    ]
                ) then
            Add(solutions,duality);
        fi;
    od;
    if Length(solutions)<>1 then
        Error("oriented-cut polarity is not unique");
    fi;
    return Set(List([1..7],i -> [
        twinPoints[i],linesOnSheets[i^solutions[1][1]]
    ]));
end;;

orientedCutPolarityPairs := Set(orientedCutPolarityMap);;
orientedCutLabelEquivariance := ForAll(sheetRelabelGenerators,g ->
    BuildOrientedCutPolarity(G^g,x^g,r^g,cT^g,Psheet^g)
        = Set(List(orientedCutPolarityPairs,pair -> [
            pair[1]^g,LineImage(pair[2],g)
        ]))
);;
backwardOrientedCutPolarityPairs := BuildOrientedCutPolarity(
    G^cT,x^cT,r^cT,cT,Psheet^cT
);;
orientedCutSwitchCocycle := Set(List(
    orientedCutPolarityPairs,pair -> [
        pair[1]^cT,LineImage(pair[2],cT)
    ]
))=backwardOrientedCutPolarityPairs
and Set(List(backwardOrientedCutPolarityPairs,pair -> [
    pair[1]^cT,LineImage(pair[2],cT)
]))=orientedCutPolarityPairs;;

if Size(G)<>10200960
        or Size(C)<>2688
        or Size(frameKernel)<>16
        or Size(F)<>168
        or StructureDescription(F)<>"PSL(3,2)"
        or Order(cT)<>2
        or H<>[1,2,5,6,7,8,23]
        or twinH<>[2,3,6,8,12,17,19]
        or Set(twinLineSheets)<>Set(backwardLineOrder)
        or backwardIncidenceMatrix<>incidenceMatrix
        or switchTransportedRelation<>BackwardRelationPairs
        or switchReturnedRelation<>RelationPairs
        or not frameKernelTrivialOnPacket
        or not branchReflectionPacketPreserved
        or List(incidenceMatrix,Sum)<>[3,3,3,3,3,3,3]
        or List(TransposedMat(incidenceMatrix),Sum)<>[3,3,3,3,3,3,3]
        or List(antiIncidenceMatrix,Sum)<>[4,4,4,4,4,4,4]
        or gram<>gramExpected
        or AbsInt(determinant)<>24
        or determinant mod 23<>1
        or incidenceMatrix*inverseFormula<>identity7
        or inverseFormula*incidenceMatrix<>identity7
        or Length(RelationPairs)<>21
        or not relationEquivariance
        or not labelEquivariance
        or IsConjugate(F,pointStabilizer,lineStabilizer)
        or pointCharacter<>lineCharacter
        or ScalarProduct(pointCharacter,lineCharacter)<>2
        or SortedList(List(pairOrbits,Length))<>[21,28]
        or tripodCut<>[2,6,8]
        or cutCompanions<>[2,6]
        or cutPhaseDegrees<>[1,0]
        or selectedCutPoint<>2
        or lineSheets[selectedLineIndex]<>[5,6,8]
        or smithDiagonal<>[1,1,1,1,2,2,6]
        or blockSmithDiagonal<>[1,1,1,1,1,1,1,1,2,2,2,2,6,6]
        or Length(leftKernelVectors)<>7
        or Length(rightKernelVectors)<>7
        or Set(leftKernelVectors)<>Set(lineComplementVectors)
        or Set(rightKernelVectors)<>Set(pointOffPencilVectors)
        or Length(blockRadicalBasis2)<>6
        or Set(Flat(linkingValues))<>[3/2,2]
        or linkingBits<>lineByPointAntiIncidence
        or Length(dualities)<>168
        or Size(incidenceAutomorphismGroup)<>336
        or StructureDescription(incidenceAutomorphismGroup)
            <>"PSL(3,2) : C2"
        or Size(extendedFlagStabilizer)<>16
        or StructureDescription(extendedFlagStabilizer)<>"D16"
        or StructureDescription(radicalCarrierImage)<>"PSL(3,2) : C2"
        or not phaseRadicalEquivariance
        or StructureDescription(Image(phaseSquareHom))<>"D8"
        or Length(blockRadicalBasis3)<>2
        or Length(projectiveRadicalLines3)<>4
        or StructureDescription(projectiveRadicalImage3)<>"C2"
        or Length(flagDualities)<>8
        or Length(compatiblePolarities)<>2
        or List(polarityPacketMatrix,Sum)<>[2,2,2,2,2,2,2]
        or List(TransposedMat(polarityPacketMatrix),Sum)
            <>[2,2,2,2,2,2,2]
        or Sum(List(polarityPacketSupport,Sum))<>11
        or polarityAgreementSheets<>[1,2,8]
        or polarityAgreementTwinSheets<>LineImage(deltaSheets,cT)
        or polarityPacketRank<>5
        or polarityPacketSmithDiagonal<>[1,1,2,2,2,0,0]
        or not relativePointIsReflection
        or not relativeLineIsReflection
        or originalCutPositions in Set(fanoLines)
        or twinCutPositions in Set(twinFanoLines)
        or Length(identityCutPlaneIsomorphisms)<>1
        or Length(triangleCorrelationCandidates)<>1
        or not triangleSelectedArrow
        or triangleCorrelationOrder<>2
        or triangleFlagPreserving
        or triangleInCompatibleFlagPacket
        or Length(orientedCutPolarityCandidates)<>1
        or Length(orientedCutPolarityPairs)<>7
        or orientedCutPolarityOrder<>2
        or Length(cutRotationCandidates)<>1
        or cutRotationOrder<>3
        or not orientedCutFactorization
        or not orientedCutFlagPreserving
        or not orientedCutSelectedPhaseArrow
        or not orientedCutLabelEquivariance
        or not orientedCutSwitchCocycle then
    Error("twin/Fano incidence correspondence certificate changed");
fi;

Print("object\tinvariant\tvalue\tstatus\n");
Print("twin_incidence\tleft_degree\t3\texact\n");
Print("twin_incidence\tright_degree\t3\texact\n");
Print("twin_incidence\tedge_count\t21\texact\n");
Print("twin_incidence\tdeterminant\t",determinant,"\tinvertible_over_Q_and_Z[1/6]\n");
Print("twin_incidence\tdeterminant_mod_23\t1\tinvertible_on_the_p23_carrier\n");
Print("twin_incidence\tgram_identity\tNN^T=2I+J\texact\n");
Print("twin_incidence\tinverse\t(1/2)N^T-(1/6)J\texact\n");
Print("twin_incidence\tframe_equivariant\ttrue\tC_to_C^cT\n");
Print("twin_incidence\tlabel_independent\ttrue\tchecked_on_S23_generators\n");
Print("twin_packet_descent\tforward_to_backward_switch\ttrue\tcT_preserves_point_line_sides\n");
Print("twin_packet_descent\ttwo_step_return\tidentity\tcT_squared\n");
Print("twin_packet_descent\tcT_closed_on_one_ordered_packet\tfalse\tmaps_forward_packet_to_backward_packet\n");
Print("frame_return_action\tkernel_2^4\ttrivial\ton_point_line_packet\n");
Print("frame_return_action\tquotient\tPSL(3,2)\tside_preserving_collineations\n");
Print("frame_return_action\touter_character\ttrivial\tall_closed_returns_side_preserving\n");
Print("branch_reflection_return\tpacket_action\ttransvection\tside_preserving\n");
Print("point_line_modules\tpermutation_characters_equal\ttrue\tGassmann_equivalence\n");
Print("point_line_modules\thom_dimension\t2\tincidence_and_anti_incidence\n");
Print("point_line_sets\tequivariant_bijection\tfalse\tnonconjugate_stabilizers\n");
Print("integral_defect\tsmith_normal_form\t[1,1,1,1,2,2,6]\tcoker_N=(C2)^3xC3\n");
Print("integral_defect\tblock_smith_normal_form\t[1^8,2^4,6^2]\tcoker_B_2=(C2)^6\n");
Print("mod2_radical\tdimension\t6\ttwo_simplex_code_halves\n");
Print("mod2_radical\tside_weight_enumerator\t1+7z^4\t[7,3,4]_simplex_code\n");
Print("mod2_radical\tnonzero_side_words\t7+7\tline_complements_and_off_pencils\n");
Print("mod2_discriminant_linking\tzero_pairs\t21\texactly_incidence\n");
Print("mod2_discriminant_linking\thalf_pairs\t28\texactly_anti_incidence\n");
Print("mod2_radical_carrier\tfull_image\tPSL(3,2):2\tpoint_line_envelope_recovered\n");
Print("mod2_linking_geometry\tautomorphism_group_order\t336\t168_collineations_plus_168_correlations\n");
Print("marked_phase_square\tmod2_radical_realization\ttrue\tD8_action_equivariant\n");
Print("mod3_projective_radical\tsize\t4\tnumerical_match_only\n");
Print("mod3_projective_radical\tmarked_image\tC2\tnot_the_phase_square_D8\n");
Print("tripod_correlation_packet\tcompatible_correlations\t",Length(compatiblePolarities),"\tinvolutive_after_marked_identification\n");
Print("tripod_correlation_packet\tweighted_row_sums\t",List(polarityPacketMatrix,Sum),"\tbidegree_two\n");
Print("tripod_correlation_packet\tweighted_matrix\t",polarityPacketMatrix,"\texact\n");
Print("tripod_correlation_packet\treduced_support_edges\t",Sum(List(polarityPacketSupport,Sum)),"\texact\n");
Print("tripod_correlation_packet\tagreement_sheets\t",polarityAgreementSheets,"\texact\n");
Print("tripod_correlation_packet\tagreement_twin_sheets\t",polarityAgreementTwinSheets,"\tDelta^cT\n");
Print("tripod_correlation_packet\trank\t",polarityPacketRank,"\tover_Q\n");
Print("tripod_correlation_packet\tsmith_diagonal\t",polarityPacketSmithDiagonal,"\texact\n");
Print("tripod_correlation_packet\trelative_collineation\tbranch_reflection_r\tfixed_flag_(P,Delta)\n");
Print("tripod_correlation_packet\trational_kernel\tminus_one_eigenspace_of_r\tdimension_two\n");
Print("cut_triangle_correlation\toriginal_cut_collinear\t",originalCutPositions in Set(fanoLines),"\tfalse_required\n");
Print("cut_triangle_correlation\ttwin_cut_collinear\t",twinCutPositions in Set(twinFanoLines),"\tfalse_required\n");
Print("cut_triangle_correlation\tpoint_plane_isomorphisms_fixing_cut\t",Length(identityCutPlaneIsomorphisms),"\tunique\n");
Print("cut_triangle_correlation\tcorrelation_count\t",Length(triangleCorrelationCandidates),"\tunique_opposite_side_rule\n");
Print("cut_triangle_correlation\tmap\t",triangleCorrelationMap,"\texact\n");
Print("cut_triangle_correlation\tselected_arrow\t",triangleSelectedArrow,"\t2_to_{5,6,8}\n");
Print("cut_triangle_correlation\torder_after_marked_identification\t",triangleCorrelationOrder,"\tinvolutive\n");
Print("cut_triangle_correlation\tflag_preserving\t",triangleFlagPreserving,"\texact\n");
Print("cut_triangle_correlation\tin_compatible_flag_packet\t",triangleInCompatibleFlagPacket,"\texact\n");
Print("tripod_correlation_packet\tindividual_maps\t",compatiblePolarityMaps,"\texact\n");
Print("oriented_cut_correlation\tcut_cycle\t",orientedCutCycle,"\tselected_other_P\n");
Print("oriented_cut_correlation\tcandidate_count\t",Length(orientedCutPolarityCandidates),"\tunique\n");
Print("oriented_cut_correlation\tmap\t",orientedCutPolarityMap,"\texact\n");
Print("oriented_cut_correlation\tbidegree\t[1,1]\texact\n");
Print("oriented_cut_correlation\tlinearization\tpermutation_matrix\tintegral_isomorphism\n");
Print("oriented_cut_correlation\torder_after_marked_identification\t",orientedCutPolarityOrder,"\tinvolutive\n");
Print("oriented_cut_correlation\tcut_rotation_count\t",Length(cutRotationCandidates),"\tunique_projective_basis_rotation\n");
Print("oriented_cut_correlation\tcut_rotation_order\t",cutRotationOrder,"\tbackward_3_cycle\n");
Print("oriented_cut_correlation\tfactorization\tbackward_cut_rotation_then_opposite_side_correlation\texact\n");
Print("oriented_cut_correlation\tflag_preserving\t",orientedCutFlagPreserving,"\tP_to_Delta\n");
Print("oriented_cut_correlation\tselected_phase_arrow\t",orientedCutSelectedPhaseArrow,"\t6_to_{5,6,8}\n");
Print("oriented_cut_correlation\tlabel_independent\t",orientedCutLabelEquivariance,"\tchecked_on_S23_generators\n");
Print("oriented_cut_correlation\treversal_compatibility\t",orientedCutSwitchCocycle,"\tforward_backward_inverse\n");
Print("marked_tripod_outer_map\tdegree_one_exists\ttrue\toriented_cut_correlation\n");
Print("marked_cut\tline_phase_row_degrees\t[1,0]\tnot_an_S2_phase_isomorphism\n");
Print("marked_cut\tselected_incidence_arrow\t2->{5,6,8}\texact\n");
Print("incidence_certificate_scope\tglobal_descent\tfalse\trequires_transport_theorem\n");
Print("PASS_TWIN_FANO_INCIDENCE_CORRESPONDENCE\n");

QUIT_GAP(0);
