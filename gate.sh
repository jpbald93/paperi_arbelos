#!/bin/bash
# Gate for the ErdosMordell Lean formalisation. Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Arbelos"
LIB="Arbelos"
REQUIRED="Arbelos.vline Arbelos.ptA Arbelos.ptC Arbelos.ptB Arbelos.bigS Arbelos.leftS Arbelos.rightS Arbelos.perpC Arbelos.dist_sq_re_im Arbelos.isExtTangent_iff Arbelos.isIntTangent_iff Arbelos.mem_vline_iff Arbelos.isTangent_vline_iff Arbelos.invSphere Arbelos.inversion_re Arbelos.inversion_im Arbelos.norm_sq_re_im Arbelos.mem_sphere_iff_sq Arbelos.inversion_mem_invSphere_iff Arbelos.image_inversion_sphere Arbelos.twin_left Arbelos.twin_right Arbelos.twin_left_exists Arbelos.twin_right_exists Arbelos.arbelosRegion Arbelos.upperHalf Arbelos.measurableSet_upperHalf Arbelos.volume_realAxis Arbelos.two_mul_volume_inter_upperHalf Arbelos.ofReal_disc_area Arbelos.volume_half_of_two_mul Arbelos.conj_mem_ball_iff Arbelos.conj_mem_closedBall_iff Arbelos.volume_closedHalfDisc Arbelos.volume_openHalfDisc Arbelos.dist_ofReal_ofReal Arbelos.arbelosRegion_eq Arbelos.arbelos_area Arbelos.famDen Arbelos.famCircle Arbelos.pappusCircle Arbelos.incircleChain Arbelos.invRadius Arbelos.famDen_pos Arbelos.famCircle_radius_pos Arbelos.famCircle_tangent_big Arbelos.famCircle_tangent_left Arbelos.famCircle_dist_sq Arbelos.famCircle_tangent_famCircle Arbelos.famCircle_height Arbelos.invRadius_sq Arbelos.invRadius_ne_zero Arbelos.invSphere_famCircle Arbelos.famCircle_center_ne Arbelos.famCircle_param_of_tangent Arbelos.eq_of_sq_eq_one Arbelos.pappusCircle_zero Arbelos.pappus_radius_pos Arbelos.pappus_tangent_big Arbelos.pappus_tangent_left Arbelos.pappus_tangent_succ Arbelos.pappus_chain Arbelos.incircleChain_spec Arbelos.inversion_bigS Arbelos.inversion_leftS Arbelos.inversion_pappusCircle Arbelos.eq_famCircle Arbelos.pappus_unique Arbelos.extTangentAt_eq Arbelos.incircle_eq Arbelos.bankoff Arbelos.IsSteinerChain Arbelos.rotSphere Arbelos.dist_rot_rot Arbelos.dist_center_rot Arbelos.concentric_tangent Arbelos.steiner_concentric Arbelos.powC Arbelos.exists_inversion_concentric Arbelos.dist_sq_sub Arbelos.powC_eq Arbelos.invSphere_center_sub Arbelos.invSphere_radius Arbelos.invSphere_sub_re Arbelos.invSphere_sub_im Arbelos.powC_invSphere Arbelos.invSphere_invSphere Arbelos.ext_alg Arbelos.int_alg Arbelos.invSphere_isExtTangent Arbelos.invSphere_isIntTangent Arbelos.powC_pos_of_isIntTangent Arbelos.steiner_porism Arbelos.l14_twin_left Arbelos.l14_twin_right Arbelos.l14_arbelos_area Arbelos.l14_pappus_chain Arbelos.l14_pappus_unique Arbelos.l14_inversion_bigS Arbelos.l14_inversion_leftS Arbelos.l14_inversion_pappusCircle Arbelos.l14_bankoff Arbelos.l14_steiner_porism Arbelos.l14h_mem_sphere Arbelos.l14h_wbtw Arbelos.l14h_sqrt_two_sq Arbelos.l14w_twin Arbelos.l14w_arbelos_area Arbelos.l14w_pappus_chain Arbelos.l14w_pappus_unique Arbelos.l14w_inversion_bigS Arbelos.l14w_bankoff Arbelos.l14h_zmod6 Arbelos.l14wChain Arbelos.l14w_steiner_porism"
REQUIRED="$REQUIRED Arbelos.bankoff_exists Arbelos.IsSimpleSteinerChain Arbelos.HasDisjointDiscs Arbelos.IsDisjointSteinerChain Arbelos.hasDisjointDiscs_iff Arbelos.rotSphere_injective Arbelos.invSphere_inj Arbelos.invSphere_sep Arbelos.steiner_concentric_strong Arbelos.steiner_porism_strong Arbelos.steiner_porism_simple Arbelos.steiner_porism_disjoint"
REQUIRED="$REQUIRED Arbelos.bridge_vline Arbelos.bridge_perpC Arbelos.bridge_arbelos_area Arbelos.bridge_twin_radius Arbelos.bridge_twin_left Arbelos.bridge_twin_right Arbelos.bankoff_center Arbelos.bridge_bankoff Arbelos.bridge_isSteinerChain_iff Arbelos.bridge_powC Arbelos.bridge_exists_inversion_concentric"
# Arbelos/Open.lean (open items, contains `sorry`) is deliberately NOT imported by the root and not gated.
SOURCES="$(ls Arbelos/*.lean | grep -v '^Arbelos/Open.lean$') Arbelos.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
