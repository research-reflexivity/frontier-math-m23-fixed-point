# Exact identification of the independently defined boundary-octic affine
# frame torsor with the 168-state point--line correlation torsor.
#
# The eight ramified double points form a torsor under K/<x> = C2^3.  An
# affine frame is an origin together with an ordered basis of differences.
# Quotienting the 8*168 affine frames by translations leaves 168 frames.
# The canonical KernelLine labelling identifies their seven nonzero
# differences with the seven Fano lines, without choosing a correlation.

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
K := Kernel(pointHom);;
fanoLines := Set(List(
    Filtered(AsList(F),element -> Order(element)=2),
    element -> Set(Filtered([1..7],point -> point^element=point))
));;
lineSheets := List(fanoLines,line -> Set(List(line,i -> H[i])));;

doublePoints := List(Orbits(Group(x),Difference([1..23],H)),Set);;
pairHom := ActionHomomorphism(C,doublePoints,OnSets);;
affineGroup := Image(pairHom);;
translations := Image(pairHom,K);;

KernelLine := function(k)
    local image;
    image := Image(pointHom,Centralizer(C,k));
    return Filtered([1..7],lineIndex -> ForAll(
        GeneratorsOfGroup(image),g ->
            OnSets(fanoLines[lineIndex],g)=fanoLines[lineIndex]
    ));
end;;

# Label each nonidentity translation by its canonical Fano line.  The two
# lifts to K differ by x and have the same label.
translationElements := AsList(translations);;
nonzeroTranslations := Difference(translationElements,[()]);;
TranslationLine := function(t)
    local lifts,labels;
    lifts := Filtered(Elements(K),k -> Image(pairHom,k)=t);
    labels := Set(List(lifts,KernelLine));
    if Length(lifts)<>2 or Length(labels)<>1 or Length(labels[1])<>1 then
        Error("translation does not have a unique line label");
    fi;
    return labels[1][1];
end;;
translationLineLabels := List(nonzeroTranslations,TranslationLine);;
CachedTranslationLine := t -> translationLineLabels[
    Position(nonzeroTranslations,t)
];;

DifferenceTranslation := function(origin,target)
    local found;
    found := Filtered(translationElements,t -> origin^t=target);
    if Length(found)<>1 then
        Error("translation action is not regular");
    fi;
    return found[1];
end;;

# One normalized representative, with origin 1, for every translation orbit
# of affine frames.
normalizedFrames := [];;
for first in [2..8] do
    for second in [2..8] do
        for third in [2..8] do
            if Length(Set([first,second,third]))=3 then
                directions := List([first,second,third],target ->
                    DifferenceTranslation(1,target));
                if Group(directions)=translations then
                    Add(normalizedFrames,[1,first,second,third]);
                fi;
            fi;
        od;
    od;
od;

NormalizeFrame := function(frame)
    local shift;
    shift := DifferenceTranslation(frame[1],1);
    return List(frame,point -> point^shift);
end;;
TransportFrame := function(frame,g)
    return NormalizeFrame(List(frame,point -> point^g));
end;;
FrameActionPermutation := function(g)
    return PermList(List(normalizedFrames,frame -> Position(
        normalizedFrames,TransportFrame(frame,g)
    )));
end;;
affineGenerators := GeneratorsOfGroup(affineGroup);;
frameActionGenerators := List(affineGenerators,FrameActionPermutation);;
frameActionGroup := Group(frameActionGenerators);;
frameActionHom := GroupHomomorphismByImages(
    affineGroup,frameActionGroup,affineGenerators,frameActionGenerators
);;

# Reconstruct the 168 correlations directly from twin/original incidence.
twinX := x^cT;;
twinH := Set(Filtered([1..23],point -> point^twinX=point));;
incidenceMatrix := List(twinH,q -> List([1..7],function(lineIndex)
    if Position(H,q^cT) in fanoLines[lineIndex] then return 1; fi;
    return 0;
end));;
correlations := [];;
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
        Add(correlations,pointToLine);
    fi;
od;
correlations := Set(correlations);;

# The oriented cut supplies a source basis, but no target correlation.  Derive
# its cyclic order directly from (x,r,cT,P), exactly as in the oriented-cut
# theorem: off-axis, on-axis, marked point, pulled back through cT.
Psheet := 8;;
axisSheets := Intersection(H,Filtered(
    [1..23],point -> point^r=point
));
tripodCut := Intersection(H,twinH);;
onAxisCut := Difference(Intersection(tripodCut,axisSheets),[Psheet]);;
offAxisCut := Difference(tripodCut,axisSheets);;
orientedCutCycle := [
    offAxisCut[1]^(cT^-1),
    onAxisCut[1]^(cT^-1),
    Psheet^(cT^-1)
];;
sourceBasisSheets := orientedCutCycle;;
sourceBasisRows := List(sourceBasisSheets,q -> Position(twinH,q));;
FrameLineBasis := function(frame)
    return List([2..4],index -> CachedTranslationLine(
        DifferenceTranslation(frame[1],frame[index])
    ));
end;;
FrameCorrelation := function(frame)
    local lineBasis,solutions;
    lineBasis := FrameLineBasis(frame);
    solutions := Filtered(correlations,p -> ForAll([1..3],index ->
        sourceBasisRows[index]^p=lineBasis[index]
    ));
    if Length(solutions)<>1 then
        Error("affine frame does not define a unique correlation");
    fi;
    return solutions[1];
end;;
frameCorrelations := List(normalizedFrames,FrameCorrelation);;

# Construct the target affine frame directly from the same cycle.  For each
# vertex take the Fano line through it and its successor.  The KernelLine
# bijection then turns those three lines into three octic translations.  This
# is the desired cut-to-frame arrow and is defined before phi is mentioned.
SuccessorLineBasis := function(cycle)
    return List([1..3],index -> First([1..7],lineIndex ->
        cycle[index] in lineSheets[lineIndex]
        and cycle[(index mod 3)+1] in lineSheets[lineIndex]
    ));
end;;
FrameFromLineBasis := function(lineBasis)
    local directions;
    directions := List(lineBasis,lineIndex -> First(
        nonzeroTranslations,t -> CachedTranslationLine(t)=lineIndex
    ));
    return [1,1^directions[1],1^directions[2],1^directions[3]];
end;;
FrameFromCutCycle := cycle -> FrameFromLineBasis(
    SuccessorLineBasis(cycle)
);;
successorLineBasis := SuccessorLineBasis(orientedCutCycle);;
cutDefinedFrame := FrameFromCutCycle(orientedCutCycle);;
cutDefinedCorrelation := FrameCorrelation(cutDefinedFrame);;

LinePermutation := function(g)
    return PermList(List([1..7],lineIndex -> Position(
        fanoLines,OnSets(fanoLines[lineIndex],g)
    )));
end;;

# Pair and line actions arise from the same centralizer element.  After
# quotienting origins, the affine-octic action becomes the free transitive
# target-line action on correlations.
ComparisonEquivariantFor := function(c)
    local pairImage,lineImage;
    pairImage := Image(pairHom,c);
    lineImage := LinePermutation(Image(pointHom,c));
    return ForAll([1..Length(normalizedFrames)],frameIndex ->
        frameCorrelations[Position(normalizedFrames,TransportFrame(
            normalizedFrames[frameIndex],pairImage
        ))] = frameCorrelations[frameIndex]*lineImage
    );
end;;
equivariantForCentralizer := ForAll(Elements(C),ComparisonEquivariantFor);;
cutToFrameEquivariant := ForAll(Elements(C),c ->
    FrameFromCutCycle(List(orientedCutCycle,point -> point^c))
        = TransportFrame(cutDefinedFrame,Image(pairHom,c))
);;

# Locate the previously certified oriented-cut correlation only after the
# independent torsor and its comparison map have been constructed.
orientedCutSheetMap := [
    [2,[2,6,23]], [3,[7,8,23]], [6,[5,6,8]], [8,[1,2,8]],
    [12,[1,6,7]], [17,[2,5,7]], [19,[1,5,23]]
];;
phi := PermList(List(twinH,point -> Position(
    lineSheets,orientedCutSheetMap[
        Position(List(orientedCutSheetMap,pair -> pair[1]),point)
    ][2]
)));;
phiFramePosition := Position(frameCorrelations,phi);;
phiFrame := normalizedFrames[phiFramePosition];;
phiLineBasis := FrameLineBasis(phiFrame);;

if Size(G)<>10200960
        or Size(C)<>2688
        or Size(F)<>168
        or Size(affineGroup)<>1344
        or StructureDescription(affineGroup)<>"(C2 x C2 x C2) : PSL(3,2)"
        or Size(translations)<>8
        or not IsElementaryAbelian(translations)
        or not IsRegular(translations,[1..8])
        or Set(translationLineLabels)<>[1..7]
        or Length(normalizedFrames)<>168
        or Length(correlations)<>168
        or Set(frameCorrelations)<>correlations
        or Size(frameActionGroup)<>168
        or Kernel(frameActionHom)<>translations
        or not IsTransitive(frameActionGroup,[1..168])
        or Size(Stabilizer(frameActionGroup,1))<>1
        or not equivariantForCentralizer
        or orientedCutCycle<>[2,6,8]
        or successorLineBasis<>[5,6,1]
        or not cutToFrameEquivariant
        or phiFramePosition=fail
        or cutDefinedFrame<>phiFrame
        or cutDefinedCorrelation<>phi then
    Error("affine-frame/correlation torsor certificate changed");
fi;

Print("object\tinvariant\tvalue\tstatus\n");
Print("boundary_octic\tdouble_point_count\t",Length(doublePoints),"\texact\n");
Print("boundary_octic\taffine_monodromy_order\t",Size(affineGroup),"\texact\n");
Print("boundary_octic\ttranslation_group\tC2^3\tregular\n");
Print("boundary_octic\tnonzero_difference_labels\t7_Fano_lines\tbijection\n");
Print("affine_frames\tfull_frame_count\t",8*Length(normalizedFrames),"\texact\n");
Print("affine_frames\ttranslation_quotient_count\t",Length(normalizedFrames),"\texact\n");
Print("affine_frames\tquotient_action_order\t",Size(frameActionGroup),"\tPSL3(2)\n");
Print("affine_frames\tquotient_action\tfree_transitive\texact\n");
Print("affine_frames\taction_kernel\ttranslation_C2^3\texact\n");
Print("comparison\tcorrelation_count\t",Length(correlations),"\texact\n");
Print("comparison\tframe_to_correlation\tbijection\texact\n");
Print("comparison\tcentralizer_equivariant\t",equivariantForCentralizer,"\tall_2688_elements\n");
Print("cut_to_frame\toriented_cycle\t",orientedCutCycle,"\tderived_from_x_r_cT_P\n");
Print("cut_to_frame\tsuccessor_line_basis\t",successorLineBasis,"\tindependent_of_Phi_T\n");
Print("cut_to_frame\tframe_class\t",cutDefinedFrame,"\tindependent_of_Phi_T\n");
Print("cut_to_frame\tcentralizer_equivariant\t",cutToFrameEquivariant,"\tall_2688_elements\n");
Print("cut_to_frame\treconstructed_correlation_equals_Phi_T\t",cutDefinedCorrelation=phi,"\tverified_after_construction\n");
Print("oriented_cut_state\taffine_frame_position\t",phiFramePosition,"\tlocated_after_comparison\n");
Print("oriented_cut_state\tnormalized_affine_frame\t",phiFrame,"\texact\n");
Print("oriented_cut_state\tdouble_point_frame\t",List(
    phiFrame,index -> doublePoints[index]
),"\texact\n");
Print("oriented_cut_state\tline_basis\t",phiLineBasis,"\texact\n");
Print("descent_scope\tindependent_168_state_target\ttrue\tboundary_arithmetic\n");
Print("descent_scope\tcanonical_global_section\tfalse\tframe_torsor_not_trivialized\n");
Print("descent_scope\tmarked_cut_to_frame_arrow\ttrue\tfinite_Hurwitz_atlas\n");
Print("descent_scope\tdecided_by_affine_certificate\tfalse\trequires_specialization_theorem\n");
Print("PASS_AFFINE_FRAME_CORRELATION_TORSOR\n");

QUIT_GAP(0);
