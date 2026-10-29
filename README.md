# Arbelos — the arbelos, Pappus chains and inversion in Lean 4 / Mathlib

The plane is `ℂ`, treated as a real inner product space. Circles are Mathlib's
`EuclideanGeometry.Sphere ℂ`, tangency uses Mathlib's `Sphere.IsExtTangent`, `IsIntTangent`,
`IsTangent` and `IsExtTangentAt`, inversion is Mathlib's `EuclideanGeometry.inversion`, and area
is `MeasureTheory.volume`.

**Setting** (`Arbelos/Basic.lean`): take a, b > 0 with A = 0, C = 2a, B = 2(a+b). The circles are
`bigS a b` (diameter AB), `leftS a b` (diameter AC) and `rightS a b` (diameter CB).
`perpC a b` is the perpendicular to AB at C, and "upper half" means `0 < im`.

## Main results (all proved, no `sorry`)

| Statement | Lean name | File |
|---|---|---|
| Archimedes' twin circles: each twin has radius ab/(a+b) (and both exist) | `Arbelos.twin_left`, `twin_right`, `twin_left_exists`, `twin_right_exists` | `Arbelos/Twin.lean:14,30,46,70` |
| Area of the arbelos = area of the circle on diameter CD | `Arbelos.arbelos_area` | `Arbelos/Area.lean:125` |
| **Pappus chain theorem**: the centre of the n-th circle lies n diameters above AB, for every n | `Arbelos.pappus_chain` | `Arbelos/Pappus.lean:173` |
| Chain tangencies (big circle, AC-circle, consecutive circles); circle 0 is the CB-circle | `pappus_tangent_big`, `pappus_tangent_left`, `pappus_tangent_succ`, `pappusCircle_zero` | `Arbelos/Pappus.lean:145–167` |
| The same chain indexed from the incircle (C_0 tangent to the CB-circle): height (n+1)·diameter | `Arbelos.incircleChain_spec` | `Arbelos/Pappus.lean:178` |
| Inversion at A sends the big circle and AC-circle to parallel lines and the chain to a column of equal circles | `inversion_bigS`, `inversion_leftS`, `inversion_pappusCircle` | `Arbelos/Pappus.lean:190,221,254` |
| Uniqueness of the Pappus chain | `Arbelos.pappus_unique` (with `eq_famCircle`) | `Arbelos/Pappus.lean:298` |
| Bankoff's circle has radius ab/(a+b) (with uniqueness of the incircle) | `Arbelos.bankoff`, `incircle_eq` | `Arbelos/Bankoff.lean:58,25` |
| **Steiner's porism**: if a closed chain of n circles exists, one exists starting from any tangent circle | `Arbelos.steiner_porism` | `Arbelos/Steiner.lean:305` |
| Steiner: concentric case; reduction by inversion; inversion preserves tangency | `steiner_concentric`, `exists_inversion_concentric`, `invSphere_isExtTangent`, `invSphere_isIntTangent` | `Arbelos/Steiner.lean:43,84,222,241` |
| Bridges: Mathlib tangency predicates and inversion images in coordinates | `isExtTangent_iff`, `isIntTangent_iff`, `isTangent_vline_iff`, `image_inversion_sphere` | `Arbelos/Basic.lean`, `Arbelos/Inversion.lean` |

Note on indexing: `pappusCircle a b 0` is the CB-circle, following Pappus, so `y_n = n · 2r_n`.
The chain that starts at the incircle is `incircleChain a b n = pappusCircle a b (n+1)`.

## Build and check

```
lake build                 # build the library
bash gate.sh               # forbidden-token scan + build + `#print axioms` for every declaration
SCAFFOLD=1 bash gate.sh    # same, but tolerates `sorry`
bash tests/tamper.sh       # plants 7 kinds of defect in scratch copies; each must be rejected
```
Expected: `PASS (93 declarations, standard axioms only)` and `ALL TAMPERING TESTS REJECTED`.
Mathlib is pinned at `v4.33.1` (see `lake-manifest.json`). Do not run `lake update`.
