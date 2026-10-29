# REPORT — Paper I, Group I2: the arbelos, Pappus chains and inversion

Library `Arbelos` (Lean 4 v4.33.1 + Mathlib v4.33.1). Repo `paperi_arbelos` on john.

## Summary

* **Everything requested is proved, no open items**: I2.1, I2.2, I2.3 (tangencies for all n, the height formula, the inversion picture, and uniqueness, which was marked a stretch), I2.4, and I2.5 (the full Steiner porism, plus the concentric case and the reduction lemma as separate theorems).
* No `sorry`/`admit`/`native_decide`/`axiom`/`set_option`/`#eval`/`macro`/`notation` in library files. `Arbelos/Open.lean` was not needed, so it does not exist.
* Gate: `PASS (93 declarations, standard axioms only)`
* Tamper: `ALL TAMPERING TESTS REJECTED` (sorry, ax2line, evalfake, macro, wrap → rejected at the stated stage; falsehyp — remove `hup` from `pappus_unique` → `FAIL: build`; falsehyp_ext — remove `h₂'` from `steiner_porism` → `FAIL: build`).
* Total: 1300 lines of Lean (Arbelos/*.lean + Arbelos.lean); 93 gated declarations (every theorem and definition in the library).

## Setting (what was chosen and why)

The plane is `ℂ`, a real inner product space, so Mathlib's Euclidean objects apply directly: `EuclideanGeometry.Sphere ℂ`, `Sphere.IsExtTangent`, `Sphere.IsIntTangent`, `Sphere.IsTangent` (affine subspace), `Sphere.IsExtTangentAt`, `EuclideanGeometry.inversion`, `MeasureTheory.volume` and `Metric.ball`. Coordinates: A = 0, C = 2a, B = 2(a+b); `bigS a b = ⟨a+b, a+b⟩`, `leftS a b = ⟨a, a⟩`, `rightS a b = ⟨2a+b, b⟩`; `perpC a b = vline (2a)`, built with `AffineSubspace.mk'`. "Upper half" means `0 < z.im`.
Tangency is to the full circles. This is the standard meaning, and for circles in the upper half plane it is equivalent to tangency to the semicircles. Theorem statements use only Mathlib predicates; the coordinate forms enter only through the proved bridge lemmas in `Basic.lean`.

Pappus indexing: `pappusCircle a b 0` is the CB-circle and `pappusCircle a b 1` is the incircle, which gives y_n = n·(2r_n) exactly as in Pappus. The task's indexing (C_0 = incircle, tangent to the CB-circle) is `incircleChain a b n = pappusCircle a b (n+1)`. In that indexing the height is (n+1)·(2r_n), proved in `incircleChain_spec`. The formula y_n = n·d_n in the task holds with Pappus' indexing, where C_0 is the CB-semicircle itself; this note records the off-by-one.

## Theorems

### `Arbelos.twin_left` — proved: **Y** — `Arbelos/Twin.lean:14`

I2.1 Archimedes twin (left): a circle left of the perpendicular at C, tangent to it, internally tangent to the big circle and externally tangent to the AC-circle, has radius ab/(a+b).

```lean
theorem twin_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : s.center.re < 2 * a) (hperp : s.IsTangent (perpC a b))
    (hbig : s.IsIntTangent (bigS a b)) (hsmall : (leftS a b).IsExtTangent s) :
    s.radius = a * b / (a + b)
```

'Arbelos.twin_left' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.twin_right` — proved: **Y** — `Arbelos/Twin.lean:30`

I2.1 Archimedes twin (right), same with the CB-circle.

```lean
theorem twin_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : 2 * a < s.center.re) (hperp : s.IsTangent (perpC a b))
    (hbig : s.IsIntTangent (bigS a b)) (hsmall : (rightS a b).IsExtTangent s) :
    s.radius = a * b / (a + b)
```

'Arbelos.twin_right' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.twin_left_exists` — proved: **Y** — `Arbelos/Twin.lean:46`

I2.1 existence of the left twin (upper half plane).

```lean
theorem twin_left_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 2 * a ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s
```

'Arbelos.twin_left_exists' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.twin_right_exists` — proved: **Y** — `Arbelos/Twin.lean:70`

I2.1 existence of the right twin.

```lean
theorem twin_right_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ 2 * a < s.center.re ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (rightS a b).IsExtTangent s
```

'Arbelos.twin_right_exists' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.arbelos_area` — proved: **Y** — `Arbelos/Area.lean:125`

I2.2 Lebesgue area of the arbelos = area of the disc with diameter CD.

```lean
theorem arbelos_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (D : ℂ) (hD : D ∈ bigS a b)
    (hDperp : D ∈ perpC a b) (hDup : 0 < D.im) :
    volume (arbelosRegion a b) = volume (Metric.ball (midpoint ℝ (ptC a b) D) (dist (ptC a b) D / 2))
```

'Arbelos.arbelos_area' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappus_chain` — proved: **Y** — `Arbelos/Pappus.lean:173`

I2.3 HEADLINE Pappus chain theorem: centre height of the n-th circle = n · diameter, all n : ℕ.

```lean
theorem pappus_chain {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).center.im = n * (2 * (pappusCircle a b n).radius)
```

'Arbelos.pappus_chain' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappus_tangent_big` — proved: **Y** — `Arbelos/Pappus.lean:159`

I2.3 each chain circle is internally tangent to the big circle.

```lean
theorem pappus_tangent_big {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).IsIntTangent (bigS a b)
```

'Arbelos.pappus_tangent_big' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappus_tangent_left` — proved: **Y** — `Arbelos/Pappus.lean:163`

I2.3 each chain circle is externally tangent to the AC-circle.

```lean
theorem pappus_tangent_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (leftS a b).IsExtTangent (pappusCircle a b n)
```

'Arbelos.pappus_tangent_left' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappus_tangent_succ` — proved: **Y** — `Arbelos/Pappus.lean:167`

I2.3 consecutive chain circles are externally tangent.

```lean
theorem pappus_tangent_succ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).IsExtTangent (pappusCircle a b (n + 1))
```

'Arbelos.pappus_tangent_succ' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappusCircle_zero` — proved: **Y** — `Arbelos/Pappus.lean:145`

I2.3 chain circle 0 is the CB-circle (Pappus indexing).

```lean
theorem pappusCircle_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pappusCircle a b 0 = rightS a b
```

'Arbelos.pappusCircle_zero' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.incircleChain_spec` — proved: **Y** — `Arbelos/Pappus.lean:178`

I2.3 the chain indexed from the incircle C_0 (task indexing): all tangencies and height (n+1)·diameter.

```lean
theorem incircleChain_spec {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (incircleChain a b n).IsIntTangent (bigS a b) ∧
      (leftS a b).IsExtTangent (incircleChain a b n) ∧
      (rightS a b).IsExtTangent (incircleChain a b 0) ∧
      (incircleChain a b n).IsExtTangent (incircleChain a b (n + 1)) ∧
      (incircleChain a b n).center.im = (n + 1) * (2 * (incircleChain a b n).radius)
```

'Arbelos.incircleChain_spec' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.inversion_bigS` — proved: **Y** — `Arbelos/Pappus.lean:190`

I2.3 inversion at A (radius 2√(a(a+b))) maps big circle \ {A} onto the line re = 2a.

```lean
theorem inversion_bigS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (ptA a b) (invRadius a b) '' ((bigS a b : Set ℂ) \ {ptA a b}) = vline (2 * a)
```

'Arbelos.inversion_bigS' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.inversion_leftS` — proved: **Y** — `Arbelos/Pappus.lean:221`

I2.3 the same inversion maps AC-circle \ {A} onto the line re = 2(a+b).

```lean
theorem inversion_leftS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (ptA a b) (invRadius a b) '' ((leftS a b : Set ℂ) \ {ptA a b}) =
      vline (2 * (a + b))
```

'Arbelos.inversion_leftS' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.inversion_pappusCircle` — proved: **Y** — `Arbelos/Pappus.lean:254`

I2.3 the same inversion maps chain circle n onto the circle of radius b centred at (2a+b) + 2nb·i.

```lean
theorem inversion_pappusCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    inversion (ptA a b) (invRadius a b) '' (pappusCircle a b n : Set ℂ) =
      Metric.sphere (⟨2 * a + b, 2 * n * b⟩ : ℂ) b
```

'Arbelos.inversion_pappusCircle' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.eq_famCircle` — proved: **Y** — `Arbelos/Pappus.lean:264`

I2.3 every circle tangent to big and AC circles lies in the explicit family.

```lean
theorem eq_famCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ) (hs : 0 < s.radius)
    (hbig : s.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s) :
    s = famCircle a b (s.center.im / (2 * s.radius))
```

'Arbelos.eq_famCircle' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.pappus_unique` — proved: **Y** — `Arbelos/Pappus.lean:298`

I2.3 (stretch) uniqueness: any chain with the tangencies, not doubling back, going upward, is the Pappus chain.

```lean
theorem pappus_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℕ → Sphere ℂ)
    (h0 : c 0 = rightS a b) (hpos : ∀ n, 0 < (c n).radius)
    (hbig : ∀ n, (c n).IsIntTangent (bigS a b)) (hleft : ∀ n, (leftS a b).IsExtTangent (c n))
    (hsucc : ∀ n, (c n).IsExtTangent (c (n + 1))) (hne : ∀ n, c (n + 2) ≠ c n)
    (hup : 0 < (c 1).center.im) (n : ℕ) :
    c n = pappusCircle a b n
```

'Arbelos.pappus_unique' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.incircle_eq` — proved: **Y** — `Arbelos/Bankoff.lean:25`

I2.4 uniqueness of the incircle of the arbelos (upper half plane).

```lean
theorem incircle_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hbig : s.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s)
    (hright : (rightS a b).IsExtTangent s) (hup : 0 < s.center.im) :
    s = pappusCircle a b 1
```

'Arbelos.incircle_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.bankoff` — proved: **Y** — `Arbelos/Bankoff.lean:58`

I2.4 Bankoff: the circle through C and the incircle touch points T1, T2 has radius ab/(a+b).

```lean
theorem bankoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s₀)
    (hright : (rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (leftS a b).IsExtTangentAt s₀ T₁) (hT₂ : (rightS a b).IsExtTangentAt s₀ T₂)
    (s : Sphere ℂ) (hC : ptC a b ∈ s) (h₁ : T₁ ∈ s) (h₂ : T₂ ∈ s) :
    s.radius = a * b / (a + b)
```

'Arbelos.bankoff' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.steiner_porism` — proved: **Y** — `Arbelos/Steiner.lean:305`

I2.5 FULL Steiner porism (S1 strictly inside S2, any n, chain indexed by ZMod n).

```lean
theorem steiner_porism (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (hs₀ : 0 < s₀.radius) (h₁' : S₁.IsExtTangent s₀) (h₂' : s₀.IsIntTangent S₂) :
    ∃ d : ZMod n → Sphere ℂ, IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀
```

'Arbelos.steiner_porism' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.steiner_concentric` — proved: **Y** — `Arbelos/Steiner.lean:43`

I2.5 concentric case.

```lean
theorem steiner_concentric (S₁ S₂ : Sphere ℂ) (hc : S₁.center = S₂.center)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (hs₀ : 0 < s₀.radius) (h₁ : S₁.IsExtTangent s₀) (h₂ : s₀.IsIntTangent S₂) :
    ∃ d : ZMod n → Sphere ℂ, IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀
```

'Arbelos.steiner_concentric' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.exists_inversion_concentric` — proved: **Y** — `Arbelos/Steiner.lean:84`

I2.5 reduction lemma: an inversion (centre outside both circles) makes S1, S2 concentric.

```lean
theorem exists_inversion_concentric (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hne : S₁.center ≠ S₂.center) (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius) :
    ∃ c : ℂ, 0 < powC c S₁ ∧ 0 < powC c S₂ ∧
      (invSphere c 1 S₁).center = (invSphere c 1 S₂).center
```

'Arbelos.exists_inversion_concentric' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.invSphere_isExtTangent` — proved: **Y** — `Arbelos/Steiner.lean:222`

I2.5 inversion preserves external tangency (positive powers).

```lean
theorem invSphere_isExtTangent {c : ℂ} {s t : Sphere ℂ} (hs : 0 < powC c s) (ht : 0 < powC c t)
    (h : s.IsExtTangent t) : (invSphere c 1 s).IsExtTangent (invSphere c 1 t)
```

'Arbelos.invSphere_isExtTangent' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.invSphere_isIntTangent` — proved: **Y** — `Arbelos/Steiner.lean:241`

I2.5 inversion preserves internal tangency (positive powers).

```lean
theorem invSphere_isIntTangent {c : ℂ} {s t : Sphere ℂ} (hs : 0 < powC c s) (ht : 0 < powC c t)
    (h : s.IsIntTangent t) : (invSphere c 1 s).IsIntTangent (invSphere c 1 t)
```

'Arbelos.invSphere_isIntTangent' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.image_inversion_sphere` — proved: **Y** — `Arbelos/Inversion.lean:86`

Bridge: Mathlib `inversion` maps a circle not through the centre onto `invSphere`.

```lean
theorem image_inversion_sphere {c : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) {s : Sphere ℂ}
    (hr : 0 ≤ s.radius) (hp : ‖s.center - c‖ ^ 2 ≠ s.radius ^ 2) :
    inversion c ρ '' (s : Set ℂ) = (invSphere c ρ s : Set ℂ)
```

'Arbelos.image_inversion_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.isExtTangent_iff` — proved: **Y** — `Arbelos/Basic.lean:46`

Bridge: Mathlib `Sphere.IsExtTangent` ↔ coordinates.

```lean
theorem isExtTangent_iff (s t : Sphere ℂ) : s.IsExtTangent t ↔
    (s.center.re - t.center.re) ^ 2 + (s.center.im - t.center.im) ^ 2 = (s.radius + t.radius) ^ 2
      ∧ 0 ≤ s.radius ∧ 0 ≤ t.radius
```

'Arbelos.isExtTangent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.isIntTangent_iff` — proved: **Y** — `Arbelos/Basic.lean:58`

Bridge: Mathlib `Sphere.IsIntTangent` ↔ coordinates.

```lean
theorem isIntTangent_iff (s t : Sphere ℂ) : s.IsIntTangent t ↔
    (s.center.re - t.center.re) ^ 2 + (s.center.im - t.center.im) ^ 2 = (t.radius - s.radius) ^ 2
      ∧ 0 ≤ s.radius ∧ s.radius ≤ t.radius
```

'Arbelos.isIntTangent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

### `Arbelos.isTangent_vline_iff` — proved: **Y** — `Arbelos/Basic.lean:82`

Bridge: Mathlib `Sphere.IsTangent` (to a vertical line) ↔ |x - x₀| = r.

```lean
theorem isTangent_vline_iff (s : Sphere ℂ) (x₀ : ℝ) :
    s.IsTangent (vline x₀) ↔ |s.center.re - x₀| = s.radius
```

'Arbelos.isTangent_vline_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

## Prior art (searched)

* Pinned Mathlib: no arbelos, Pappus chain, twin-circle, Bankoff or Steiner-porism results; grep for `arbelos|pappus chain|steiner chain|porism` returned nothing. What Mathlib does provide and this library uses: `EuclideanGeometry.inversion` (Inversion/Basic, ImageHyperplane), `Sphere.IsTangent/IsExtTangent/IsIntTangent` with `isExtTangent_iff_dist_center` and `isIntTangent_iff_dist_center` (Sphere/Tangent), and `Complex.volume_ball`/`volume_closedBall`.
* `gh search code` for "arbelos", "Pappus chain", "Steiner porism", "Archimedes twin circles" (language: Lean) returned no hits; "Bankoff" returned only unrelated identifiers.

## Method notes

* Every identity was checked first with mpmath (30 digits, 20 random (a,b), Pappus for n = 0..10) and sympy (exact certificates). The scripts are not part of the repo.
* Pappus: the explicit family `famCircle a b t` (centre (a(a+b)(2a+b), 2ab(a+b)t)/D, radius ab(a+b)/D, D = a(a+b)+t²b²) comes from inverting the strip picture. The key identity `famCircle_dist_sq` is: |c_t - c_u|² - (r_t + r_u)² = 4 r_t r_u ((t-u)² - 1). It gives tangency of consecutive circles, and conversely that the parameters of tangent family members differ by ±1, which drives uniqueness. The inversion picture (`inversion_*`) is proved against Mathlib's `inversion`.
* Area: conjugation is a measure-preserving linear isometry and the real axis is a null submodule, so an upper half disc has half the disc area; the arbelos is a closed half disc minus two disjoint open half discs (`measure_sdiff`).
* Steiner: concentric case by rotation about the common centre. Reduction: an inversion centre on the line of centres, a root of Dλ² - (D + r₁² - r₂²)λ + r₁² chosen so that it lies outside both circles. Inversion with positive powers preserves external and internal tangency (rational identities plus a sum-of-squares certificate for r_s/E_s ≤ r_t/E_t). Pulling the rotated chain back gives the porism.

## Build / check

From the repo root: `lake build`, `bash gate.sh` (or `SCAFFOLD=1 bash gate.sh`), `bash tests/tamper.sh`. On john use the wrapper `~/lean/jl build|gate|tamper`.
