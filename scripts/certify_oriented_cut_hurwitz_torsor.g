# Exact 168-state audit for the oriented-cut correlation torsor.
#
# This certificate separates three questions which can otherwise be
# conflated:
#
#   (1) Does the set of point--line correlations carry two commuting
#       regular PSL(3,2)-torsor actions?
#   (2) Can an untwisted point/line action fix a degree-one correlation?
#   (3) Once an OUTER transport is independently supplied, is its
#       coboundary equation soluble and is the solution unique?
#
# The answer is yes, no, yes.  The last answer is deliberately conditional:
# manufacturing the target action by conjugating through a chosen correlation
# is circular.  The only extra arithmetic edge tested here is the independently
# certified real branch-exchange lift r.

SizeScreen([100000,100000]);;

gA := (1,2)(3,4)(7,8)(9,10)(13,14)(15,16)(19,20)(21,22);;
gB := (1,16,11,3)(2,9,21,12)(4,5,8,23)(6,22,14,18)
      (13,20)(15,17);;
G := Group(gA,gB);;
y := (1,2,11,10,16,9,6,3,23,19,20,14,21,17,4,8,22,5,18,15,
      13,7,12);;
x := (3,21)(4,16)(9,22)(10,15)(11,20)(12,19)(13,18)(14,17);;
r := (3,18)(4,16)(5,6)(7,23)(10,14)(12,19)(13,21)(15,17);;

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

incidenceMatrix := List(twinH,q -> List([1..7],function(lineIndex)
    if Position(H,q^cT) in fanoLines[lineIndex] then return 1; fi;
    return 0;
end));;

# Enumerate all 168 correlations from the incidence matrix.  A state is the
# permutation p with source point i sent to target line i^p.
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
correlations := Set(List(dualities,duality -> duality[1]));;

# The previously certified oriented-cut correlation, reconstructed from its
# exact sheet graph.  Membership in correlations is checked below.
orientedCutSheetMap := [
    [2,[2,6,23]], [3,[7,8,23]], [6,[5,6,8]], [8,[1,2,8]],
    [12,[1,6,7]], [17,[2,5,7]], [19,[1,5,23]]
];;
phi := PermList(List(twinH,point -> Position(
    lineSheets,orientedCutSheetMap[
        Position(List(orientedCutSheetMap,pair -> pair[1]),point)
    ][2]
)));;
phiPosition := Position(correlations,phi);;

# The original collineation g acts on the twin rows through g^cT, which is
# most transparently recorded by pulling every row back through cT.
rowToOriginalPoint := List(twinH,q -> Position(H,q^cT));;
PointRowPermutation := function(g)
    return PermList(List([1..7],row -> Position(
        rowToOriginalPoint,rowToOriginalPoint[row]^g
    )));
end;;
LinePermutation := function(g)
    return PermList(List([1..7],lineIndex -> Position(
        fanoLines,OnSets(fanoLines[lineIndex],g)
    )));
end;;

pointRowGroup := Group(List(GeneratorsOfGroup(F),PointRowPermutation));;
lineGroup := Group(List(GeneratorsOfGroup(F),LinePermutation));;
pointElements := AsList(pointRowGroup);;
lineElements := AsList(lineGroup);;

# Left and right multiplication each act freely and transitively on the 168
# correlations.  These are the two commuting regular torsor actions.
leftOrbit := Set(List(pointElements,a -> a*phi));;
rightOrbit := Set(List(lineElements,b -> phi*b));;
leftStabilizer := Filtered(pointElements,a -> a*phi=phi);;
rightStabilizer := Filtered(lineElements,b -> phi*b=phi);;
actionsCommute := ForAll(
    GeneratorsOfGroup(pointRowGroup),a -> ForAll(
        GeneratorsOfGroup(lineGroup),b ->
            a*(phi*b)=(a*phi)*b
    )
);;

# Matched side-preserving transport is the untwisted diagonal action.
# A fixed state would be an F-equivariant point--line bijection.
DiagonalStatePermutation := function(g)
    local a,b;
    a := PointRowPermutation(g);
    b := LinePermutation(g);
    return PermList(List(correlations,p -> Position(
        correlations,a^-1*p*b
    )));
end;;
diagonalStateGroup := Group(List(
    GeneratorsOfGroup(F),DiagonalStatePermutation
));;
diagonalOrbitSizes := SortedList(List(
    Orbits(diagonalStateGroup,[1..Length(correlations)]),Length
));;
untwistedFixedStates := Filtered(correlations,p -> ForAll(
    GeneratorsOfGroup(F),g ->
        PointRowPermutation(g)*p=p*LinePermutation(g)
));;
phiDiagonalStabilizer := Stabilizer(
    diagonalStateGroup,phiPosition,OnPoints
);;

# Every correlation p supplies an outer isomorphism theta_p by conjugation.
# The corresponding coboundary equation a p = p theta_p(a) then has the
# unique solution p.  Checking all 168 states exposes the circularity: the
# torsor verifies a supplied outer cocycle but does not define one.
pointGenerators := GeneratorsOfGroup(pointRowGroup);;
OuterGeneratorImages := p -> List(pointGenerators,a -> p^-1*a*p);;
outerGeneratorImageKeys := Set(List(correlations,OuterGeneratorImages));;
allOuterImagesLandInLineGroup := ForAll(correlations,p -> ForAll(
    pointElements,a -> p^-1*a*p in lineGroup
));;
allOuterImagesAreOnto := ForAll(correlations,p ->
    Group(OuterGeneratorImages(p))=lineGroup
);;
CoboundarySolutions := function(images)
    return Filtered(correlations,p -> ForAll(
        [1..Length(pointGenerators)],i ->
            pointGenerators[i]*p=p*images[i]
    ));
end;;
allCircularCoboundariesUnique := ForAll(correlations,p ->
    CoboundarySolutions(OuterGeneratorImages(p))=[p]
);;
selectedOuterSolutions := CoboundarySolutions(OuterGeneratorImages(phi));;
Defect := function(a,p,b)
    # In right-action notation, compatibility is a*p=p*b.  This source-side
    # defect is the identity exactly when that square commutes.
    return a*p*b^-1*p^-1;
end;;
selectedOuterDefects := List([1..Length(pointGenerators)],i -> Defect(
    pointGenerators[i],phi,OuterGeneratorImages(phi)[i]
));;
fGenerators := GeneratorsOfGroup(F);;
selectedUntwistedDefects := List(fGenerators,g -> Defect(
    PointRowPermutation(g),phi,LinePermutation(g)
));;
selectedUntwistedDefectGroup := Group(selectedUntwistedDefects);;
selectedUntwistedDefectOrders := List(selectedUntwistedDefects,Order);;

# The independently defined real edge.  The base involution exchanging the
# two order-23 branches has the unique lift r at ID 6.  Its sheet transport
# conjugates every input of the oriented-cut construction.  Rebuild from
# the conjugated data, rather than declaring the answer by transport.
LineImage := function(line,g)
    return Set(List(line,point -> point^g));
end;;
BuildOrientedCutCorrelation := function(
    ambientGroup,frame,reflection,switch,markedPoint
)
    local centralizer,points,hom,plane,lines,linesOnSheets,twinPoints,
          matrix,cut,axisSheets,axis,axisIndex,pointIndex,sourcePointIndex,
          onAxisCut,offAxisCut,pointPhaseSheets,otherPhaseSheet,
          selectedSource,otherSource,linePhaseIndices,selectedLine,
          otherLine,cycle,correlationsLocal,pointToLine,lineToPointList,
          goodLocal,lineIndex,candidatesLocal,sourceIndex,duality,lifted,
          solutions;
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
    correlationsLocal := [];
    for pointToLine in AsList(SymmetricGroup(7)) do
        lineToPointList := [];
        goodLocal := true;
        for lineIndex in [1..7] do
            candidatesLocal := Filtered([1..7],sourceIndex ->
                ForAll([1..7],i ->
                    matrix[i][lineIndex]
                        = matrix[sourceIndex][i^pointToLine]
                )
            );
            if Length(candidatesLocal)<>1 then
                goodLocal := false;
                break;
            fi;
            Add(lineToPointList,candidatesLocal[1]);
        od;
        if goodLocal and Set(lineToPointList)=[1..7] then
            Add(correlationsLocal,[
                pointToLine,PermList(lineToPointList)
            ]);
        fi;
    od;
    solutions := [];
    for duality in correlationsLocal do
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
        Error("oriented-cut correlation is not unique in rebuilt chart");
    fi;
    return Set(List([1..7],i -> [
        twinPoints[i],linesOnSheets[i^solutions[1][1]]
    ]));
end;;

phiSheetPairs := Set(List(orientedCutSheetMap,pair -> [pair[1],pair[2]]));;
realTransportedPairs := Set(List(phiSheetPairs,pair -> [
    pair[1]^r,LineImage(pair[2],r)
]));;
realRebuiltPairs := BuildOrientedCutCorrelation(
    G^r,x^r,r^r,cT^r,8^r
);;
realTransportDefectZero := realTransportedPairs=realRebuiltPairs;;
realTwoStep := Set(List(realTransportedPairs,pair -> [
    pair[1]^r,LineImage(pair[2],r)
]))=phiSheetPairs;;
realChangesMarkedTwinChart := cT^r<>cT;;
realBareGraphFixed := realTransportedPairs=phiSheetPairs;;

if Size(G)<>10200960
        or Size(C)<>2688
        or Size(F)<>168
        or StructureDescription(F)<>"PSL(3,2)"
        or Length(correlations)<>168
        or phiPosition=fail
        or Size(pointRowGroup)<>168
        or Size(lineGroup)<>168
        or leftOrbit<>correlations
        or rightOrbit<>correlations
        or Length(leftStabilizer)<>1
        or Length(rightStabilizer)<>1
        or not actionsCommute
        or Length(untwistedFixedStates)<>0
        or Length(outerGeneratorImageKeys)<>168
        or not allOuterImagesLandInLineGroup
        or not allOuterImagesAreOnto
        or not allCircularCoboundariesUnique
        or selectedOuterSolutions<>[phi]
        or not ForAll(selectedOuterDefects,IsOne)
        or not ForAll(selectedUntwistedDefects,d -> d in pointRowGroup)
        or not realTransportDefectZero
        or not realTwoStep
        or not realChangesMarkedTwinChart
        or realBareGraphFixed then
    Error("oriented-cut Hurwitz torsor certificate changed");
fi;

Print("object\tinvariant\tvalue\tstatus\n");
Print("correlation_torsor\tstate_count\t",Length(correlations),"\texact\n");
Print("correlation_torsor\tleft_action\tfree_transitive\tPSL3(2)\n");
Print("correlation_torsor\tright_action\tfree_transitive\tPSL3(2)\n");
Print("correlation_torsor\tactions_commute\t",actionsCommute,"\ttwo_regular_actions\n");
Print("untwisted_descent\tfixed_correlation_count\t",Length(untwistedFixedStates),"\timpossible\n");
Print("untwisted_descent\torbit_sizes\t",diagonalOrbitSizes,"\texact\n");
Print("oriented_cut_state\tposition\t",phiPosition,"\tin_168_state_torsor\n");
Print("oriented_cut_state\tuntwisted_stabilizer_order\t",Size(phiDiagonalStabilizer),"\texact\n");
Print("outer_transport\tdistinct_candidate_cocycles\t",Length(outerGeneratorImageKeys),"\tone_per_correlation\n");
Print("outer_transport\tall_land_in_target_PSL3(2)\t",allOuterImagesLandInLineGroup,"\texact\n");
Print("outer_transport\tcoboundary_solution_count_for_Phi_T\t",Length(selectedOuterSolutions),"\tunique\n");
Print("outer_transport\tall_168_circular_solvers_unique\t",allCircularCoboundariesUnique,"\tnonselection_theorem\n");
Print("outer_transport\tPhi_T_generator_defects\tidentity\texact\n");
Print("untwisted_descent\tPhi_T_generator_defect_orders\t",selectedUntwistedDefectOrders,"\texact\n");
Print("untwisted_descent\tPhi_T_defect_group_order\t",Size(selectedUntwistedDefectGroup),"\texact\n");
Print("real_hurwitz_edge\tlift\tbranch_reflection_r\tindependent_input\n");
Print("real_hurwitz_edge\tconjugate_rebuild_equals_transport\t",realTransportDefectZero,"\tzero_defect\n");
Print("real_hurwitz_edge\tinvolutive_return\t",realTwoStep,"\tr_squared\n");
Print("real_hurwitz_edge\tchanges_marked_twin_chart\t",realChangesMarkedTwinChart,"\tcT_to_cT^r\n");
Print("real_hurwitz_edge\tbare_graph_fixed\t",realBareGraphFixed,"\torientation_data_required\n");
Print("finite_audit_scope\tglobal_hurwitz_descent\tfalse\trequires_arithmetic_specialization\n");
Print("PASS_ORIENTED_CUT_HURWITZ_TORSOR\n");

QUIT_GAP(0);
