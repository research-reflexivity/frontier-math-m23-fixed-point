# Certificate targets named as in the paper's certificate table.
GAP ?= gap
GP ?= gp

.PHONY: verify paper-check \
	branch-cycle-description special-fibre-fano fano-flag-descent \
	local-flag-places special-fibre-field-tower \
	octic-splitting-field special-fibre-frobenius-scan \
	vanishing-cycle-class special-fibre-ramification \
	real-frame-cocycle associator-gate-factorization \
	degree23-normalizer twin-fano-incidence \
	oriented-cut-hurwitz-torsor affine-frame-correlation-torsor \
	gt-boundary-transport

results:
	mkdir -p results

branch-cycle-description: results
	$(GAP) -A -q scripts/certify_branch_cycle_description.g
	$(GP) -q -f scripts/certify_branch_cycle_description.gp

special-fibre-fano: results
	$(GP) -q -f scripts/certify_special_fibre_fano_arithmetic.gp
	$(GAP) -A -q scripts/certify_special_fibre_fano_geometry.g

fano-flag-descent: results
	$(GAP) -A -q scripts/certify_fano_flag_descent.g

local-flag-places: results
	$(GAP) -A -q scripts/certify_local_flag_places.g
	$(GP) -q -f scripts/certify_local_flag_places.gp

special-fibre-field-tower: results
	$(GAP) -A -q scripts/certify_special_fibre_field_tower.g
	$(GP) -q -f scripts/certify_special_fibre_field_tower.gp

octic-splitting-field: results
	$(GP) -q -f scripts/verify_octic_splitting_degree.gp

special-fibre-frobenius-scan: special-fibre-field-tower
	$(GP) -q -f scripts/certify_cyclotomic_special_fibre_independence.gp

vanishing-cycle-class: results
	$(GAP) -A -q scripts/certify_vanishing_cycle_class.g
	$(GP) -q -f scripts/certify_vanishing_cycle_class.gp

special-fibre-ramification: results
	$(GAP) -A -q scripts/certify_special_fibre_ramification.g
	$(GP) -q -f scripts/certify_special_fibre_ramification.gp
	$(GP) -q -f scripts/certify_central_quadratic_ramification.gp

real-frame-cocycle: results
	$(GAP) -A -q scripts/certify_real_frame_cocycle.g
	$(GP) -q -f scripts/certify_real_frame_cocycle.gp

associator-gate-factorization: results
	$(GAP) -A -q scripts/certify_associator_gate_factorization.g

degree23-normalizer: results
	$(GAP) -A -q scripts/certify_degree23_normalizer.g

twin-fano-incidence:
	$(GAP) -A -q scripts/certify_twin_fano_incidence_correspondence.g | \
	  tee results/twin_fano_incidence.tsv

oriented-cut-hurwitz-torsor:
	$(GAP) -A -q scripts/certify_oriented_cut_hurwitz_torsor.g | \
	  tee results/oriented_cut_hurwitz_torsor.tsv

affine-frame-correlation-torsor:
	$(GAP) -A -q scripts/certify_affine_frame_correlation_torsor.g | \
	  tee results/affine_frame_correlation_torsor.tsv

gt-boundary-transport: branch-cycle-description \
	special-fibre-field-tower associator-gate-factorization \
	degree23-normalizer twin-fano-incidence \
	oriented-cut-hurwitz-torsor affine-frame-correlation-torsor
	python3 scripts/verify_gt_boundary_transport.py

verify paper-check: branch-cycle-description special-fibre-fano \
	fano-flag-descent local-flag-places special-fibre-field-tower \
	octic-splitting-field special-fibre-frobenius-scan \
	vanishing-cycle-class special-fibre-ramification real-frame-cocycle \
	gt-boundary-transport
