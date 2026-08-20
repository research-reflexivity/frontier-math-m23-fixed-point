#!/usr/bin/env python3
"""Audit the exact inputs and logical scope of the transport theorem."""

from __future__ import annotations

import csv
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"


def key_values(name: str) -> dict[str, str]:
    path = RESULTS / name
    return dict(
        line.split("=", 1)
        for line in path.read_text(encoding="utf-8").splitlines()
        if "=" in line
    )


def four_column_rows(name: str) -> set[tuple[str, str, str, str]]:
    path = RESULTS / name
    rows: set[tuple[str, str, str, str]] = set()
    for row in csv.reader(path.read_text(encoding="utf-8").splitlines(),
                          delimiter="\t"):
        if len(row) == 4 and row[0] not in {"object", "step"}:
            rows.add(tuple(row))
    return rows


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def main() -> None:
    branch = key_values("branch_cycle_description_summary.txt")
    branch_group = key_values("branch_cycle_group_summary.txt")
    gate = key_values("associator_gate_factorization_summary.txt")
    normalizer = key_values("degree23_normalizer_summary.txt")
    affine_group = key_values("special_fibre_field_tower_group_summary.txt")
    affine_arithmetic = key_values(
        "special_fibre_field_tower_arithmetic_summary.txt"
    )

    require(
        branch.get("special_fibre_is_smooth") == "true"
        and branch.get("special_fibre_type") == "1^7_2^8"
        and branch.get("special_fibre_inertia_class") == "2A"
        and branch.get("branch_points") == "3"
        and branch.get("nielsen_class") == "(2A,23A,23B)",
        "tame special-fibre geometry changed",
    )
    require(
        branch_group.get("special_fibre_matches_2A") == "true"
        and branch_group.get("triple_generates_M23") == "true"
        and branch_group.get(
            "branch_swap_is_the_nonsquare_cyclotomic_action"
        ) == "true",
        "branch-cycle group data changed",
    )
    require(
        gate.get("unique_factorization") == "f=a*h_lambda*b"
        and gate.get("return_is_canonical_C_component") == "true"
        and gate.get("return_component_recovery_verified") == "true"
        and gate.get("return_composition_multiplicative") == "true"
        and gate.get("nonsquare_return") == "r_times_square_part",
        "normalized return certificate changed",
    )
    require(
        normalizer.get("ambient_normalizer_equals_M23") == "true",
        "degree-23 normalizer certificate changed",
    )
    require(
        affine_group.get("pair_action_order") == "1344"
        and affine_group.get("pair_action_kernel") == "inertia"
        and affine_group.get("line_module_regular_normal") == "true",
        "boundary affine group changed",
    )
    require(
        affine_arithmetic.get("witness_prime") == "599"
        and affine_arithmetic.get(
            "octic_splitting_field_strictly_contains_septic_closure"
        ) == "true",
        "boundary affine arithmetic changed",
    )

    affine = four_column_rows("affine_frame_correlation_torsor.tsv")
    require(
        {
            ("comparison", "centralizer_equivariant", "true",
             "all_2688_elements"),
            ("cut_to_frame", "centralizer_equivariant", "true",
             "all_2688_elements"),
            ("cut_to_frame", "reconstructed_correlation_equals_Phi_T",
             "true", "verified_after_construction"),
        } <= affine,
        "affine-frame comparison changed",
    )

    incidence = four_column_rows("twin_fano_incidence.tsv")
    require(
        {
            ("oriented_cut_correlation", "label_independent", "true",
             "checked_on_S23_generators"),
            ("oriented_cut_correlation", "reversal_compatibility", "true",
             "forward_backward_inverse"),
        } <= incidence,
        "oriented-cut naturality changed",
    )

    torsor = four_column_rows("oriented_cut_hurwitz_torsor.tsv")
    require(
        {
            ("correlation_torsor", "state_count", "168", "exact"),
            ("untwisted_descent", "fixed_correlation_count", "0",
             "impossible"),
            ("outer_transport", "coboundary_solution_count_for_Phi_T",
             "1", "unique"),
        } <= torsor,
        "correlation-torsor audit changed",
    )

    obligations = four_column_rows(
        "gt_boundary_transport_proof_obligations.tsv"
    )
    require(
        {
            ("octic_transport",
             "rho_R8(sigma)=pair(w_(sigma^-1))", "proved",
             "Galois-equivariant specialization restricted to the eight 2-orbits"),
            ("bare_fixed_graph", "untwisted rational correlation", "false",
             "the theorem is twisted descent and does not trivialize the torsor"),
            ("abstract_GT", "all elements of the abstract profinite GT group",
             "not_claimed",
             "the arithmetic boundary field carries the actual G_Q action"),
        } <= obligations,
        "transport theorem scope changed",
    )

    print("PASS_GT_BOUNDARY_TRANSPORT_COMPATIBILITY")


if __name__ == "__main__":
    main()
