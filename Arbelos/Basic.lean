import Mathlib

/-!
# The arbelos: setting and bridge lemmas

We work in the Euclidean plane `ℂ` (a real inner product space, so Mathlib's
`EuclideanGeometry.Sphere`, tangency predicates, `inversion` and `volume` all apply).

The arbelos has parameters `a b > 0`: `A = 0`, `C = 2a`, `B = 2(a+b)` on the real axis;
the three semicircles lie in the upper half plane `0 < z.im` and are halves of
* `bigS a b`   : centre `a + b`,  radius `a + b` (diameter `AB`),
* `leftS a b`  : centre `a`,      radius `a`     (diameter `AC`),
* `rightS a b` : centre `2a + b`, radius `b`     (diameter `CB`).
`perpC a b` is the perpendicular to `AB` at `C` (the vertical line `re z = 2a`).
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- The vertical line `{z | z.re = x₀}` as a real affine subspace of `ℂ`. -/
noncomputable def vline (x₀ : ℝ) : AffineSubspace ℝ ℂ :=
  AffineSubspace.mk' (x₀ : ℂ) (ℝ ∙ Complex.I)

/-- The point `A = 0`. -/
def ptA (_a _b : ℝ) : ℂ := 0
/-- The point `C = 2a`. -/
noncomputable def ptC (a _b : ℝ) : ℂ := ((2 * a : ℝ) : ℂ)
/-- The point `B = 2(a+b)`. -/
noncomputable def ptB (a b : ℝ) : ℂ := ((2 * (a + b) : ℝ) : ℂ)

/-- The circle on the diameter `AB`. -/
noncomputable def bigS (a b : ℝ) : Sphere ℂ := ⟨((a + b : ℝ) : ℂ), a + b⟩
/-- The circle on the diameter `AC`. -/
noncomputable def leftS (a _b : ℝ) : Sphere ℂ := ⟨((a : ℝ) : ℂ), a⟩
/-- The circle on the diameter `CB`. -/
noncomputable def rightS (a b : ℝ) : Sphere ℂ := ⟨((2 * a + b : ℝ) : ℂ), b⟩
/-- The perpendicular to `AB` at `C`. -/
noncomputable def perpC (a _b : ℝ) : AffineSubspace ℝ ℂ := vline (2 * a)

/-- Squared distance in coordinates. -/
theorem dist_sq_re_im (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- Bridge: external tangency of circles in coordinates. -/
theorem isExtTangent_iff (s t : Sphere ℂ) : s.IsExtTangent t ↔
    (s.center.re - t.center.re) ^ 2 + (s.center.im - t.center.im) ^ 2 = (s.radius + t.radius) ^ 2
      ∧ 0 ≤ s.radius ∧ 0 ≤ t.radius := by
  rw [Sphere.isExtTangent_iff_dist_center, ← dist_sq_re_im]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨by rw [h], h1, h2⟩
  · rintro ⟨h, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    have := (sq_eq_sq₀ dist_nonneg (add_nonneg h1 h2)).1 h
    exact this

/-- Bridge: internal tangency (`s` inside `t`) in coordinates. -/
theorem isIntTangent_iff (s t : Sphere ℂ) : s.IsIntTangent t ↔
    (s.center.re - t.center.re) ^ 2 + (s.center.im - t.center.im) ^ 2 = (t.radius - s.radius) ^ 2
      ∧ 0 ≤ s.radius ∧ s.radius ≤ t.radius := by
  rw [Sphere.isIntTangent_iff_dist_center, ← dist_sq_re_im]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨by rw [h], h1, ?_⟩
    have := dist_nonneg (x := s.center) (y := t.center)
    linarith
  · rintro ⟨h, h1, h2⟩
    refine ⟨(sq_eq_sq₀ dist_nonneg (by linarith)).1 h, h1, by linarith⟩

theorem mem_vline_iff {x₀ : ℝ} {z : ℂ} : z ∈ vline x₀ ↔ z.re = x₀ := by
  rw [vline, AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    have := congrArg Complex.re ht
    simp at this
    linarith
  · intro h
    refine ⟨z.im, ?_⟩
    apply Complex.ext <;> simp [h]

/-- Bridge: tangency of a circle to a vertical line in coordinates. -/
theorem isTangent_vline_iff (s : Sphere ℂ) (x₀ : ℝ) :
    s.IsTangent (vline x₀) ↔ |s.center.re - x₀| = s.radius := by
  constructor
  · rintro ⟨p, hs, hm, hle⟩
    rw [mem_vline_iff] at hm
    have hpI : p + Complex.I ∈ vline x₀ := by rw [mem_vline_iff]; simpa using hm
    have h0 := Sphere.mem_orthRadius_iff_inner_left.1 (hle hpI)
    rw [vsub_eq_sub, vsub_eq_sub, Complex.inner] at h0
    simp at h0
    have hd : dist p s.center = s.radius := hs
    rw [Complex.dist_eq_re_im, hm, show p.im - s.center.im = 0 by linarith, zero_pow two_ne_zero,
      add_zero, Real.sqrt_sq_eq_abs, abs_sub_comm] at hd
    exact hd
  · intro h
    refine ⟨⟨x₀, s.center.im⟩, ?_, ?_, ?_⟩
    · show dist _ _ = _
      rw [Complex.dist_eq_re_im]
      simp [Real.sqrt_sq_eq_abs]
      rw [abs_sub_comm]; exact h
    · rw [mem_vline_iff]
    · intro x hx
      rw [mem_vline_iff] at hx
      rw [Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub, Complex.inner]
      simp [hx]

end Arbelos
