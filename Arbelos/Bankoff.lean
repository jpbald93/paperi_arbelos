import Arbelos.Pappus

/-!
# I2.4 The Bankoff circle
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- The tangency point of two externally tangent circles of positive radii, in coordinates. -/
theorem extTangentAt_eq {s t : Sphere ℂ} {T : ℂ} (h : s.IsExtTangentAt t T)
    (hs : 0 < s.radius) (ht : 0 < t.radius) :
    T = s.center + ((s.radius / (s.radius + t.radius) : ℝ) : ℂ) * (t.center - s.center) := by
  have hd := h.isExtTangent.dist_center
  obtain ⟨m1, m2, w⟩ := h
  obtain ⟨μ, ⟨hμ0, hμ1⟩, rfl⟩ := w
  have h1 : dist (AffineMap.lineMap s.center t.center μ) s.center = s.radius := m1
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hμ0, hd] at h1
  have hμ : μ = s.radius / (s.radius + t.radius) := by
    rw [eq_div_iff (by positivity)]; exact h1
  rw [hμ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]; ring

/-- The incircle of the arbelos is unique: it is `pappusCircle a b 1`. -/
theorem incircle_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hbig : s.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s)
    (hright : (rightS a b).IsExtTangent s) (hup : 0 < s.center.im) :
    s = pappusCircle a b 1 := by
  have hr : 0 < s.radius := by
    rw [isExtTangent_iff] at hright
    rcases hright.2.2.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [isIntTangent_iff] at hbig
      rw [isExtTangent_iff] at hleft
      obtain ⟨h1, -, -⟩ := hbig; obtain ⟨h2, -, -⟩ := hleft; obtain ⟨h3, -, -⟩ := hright
      simp only [bigS, leftS, rightS, Complex.ofReal_re, Complex.ofReal_im, ← h] at h1 h2 h3
      have hX : s.center.re = 2 * a := by
        have : 2 * (a + b) * (s.center.re - 2 * a) = 0 := by linear_combination h2 - h3
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      rw [hX] at h2
      nlinarith
  rw [eq_famCircle ha hb s hr hbig hleft] at hright ⊢
  rw [← pappusCircle_zero ha hb, pappusCircle] at hright
  have h := famCircle_param_of_tangent ha hb hright
  have hpos : 0 < s.center.im / (2 * s.radius) := by positivity
  rw [pappusCircle]
  congr 1
  push_cast at h
  rcases eq_of_sq_eq_one h with h | h
  · linarith
  · linarith

/-- **Bankoff's circle.** The circle through `C` and the points where the incircle of the arbelos
touches the two small semicircles has radius `ab/(a+b)`. -/
theorem bankoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s₀)
    (hright : (rightS a b).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (leftS a b).IsExtTangentAt s₀ T₁) (hT₂ : (rightS a b).IsExtTangentAt s₀ T₂)
    (s : Sphere ℂ) (hC : ptC a b ∈ s) (h₁ : T₁ ∈ s) (h₂ : T₂ ∈ s) :
    s.radius = a * b / (a + b) := by
  have hR : 0 < a + b := by linarith
  have h0 := incircle_eq ha hb s₀ hbig hleft hright hup
  subst h0
  have hD := famDen_pos ha hb 1
  have hr := pappus_radius_pos ha hb 1
  have e1 := extTangentAt_eq hT₁ ha hr
  have e2 := extTangentAt_eq hT₂ hb hr
  have hD1 : 0 < a ^ 2 + 2 * a * b + 2 * b ^ 2 := by positivity
  have hD2 : 0 < 2 * a ^ 2 + 2 * a * b + b ^ 2 := by positivity
  have x1 : (a ^ 2 + 2 * a * b + 2 * b ^ 2) * T₁.re = 2 * a * (a + b) ^ 2 := by
    rw [e1]
    simp only [leftS, pappusCircle, famCircle, famDen, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero,
      Nat.cast_one]
    field_simp; ring
  have y1 : (a ^ 2 + 2 * a * b + 2 * b ^ 2) * T₁.im = 2 * a * b * (a + b) := by
    rw [e1]
    simp only [leftS, pappusCircle, famCircle, famDen, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, add_zero,
      sub_zero, zero_add, Nat.cast_one]
    field_simp; ring
  have x2 : (2 * a ^ 2 + 2 * a * b + b ^ 2) * T₂.re = 2 * a * (a + b) * (2 * a + b) := by
    rw [e2]
    simp only [rightS, pappusCircle, famCircle, famDen, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero,
      Nat.cast_one]
    field_simp; ring
  have y2 : (2 * a ^ 2 + 2 * a * b + b ^ 2) * T₂.im = 2 * a * b * (a + b) := by
    rw [e2]
    simp only [rightS, pappusCircle, famCircle, famDen, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, add_zero,
      sub_zero, zero_add, Nat.cast_one]
    field_simp; ring
  have hs0 : 0 ≤ s.radius := s.radius_nonneg_of_mem hC
  rw [mem_sphere_iff_sq hs0] at hC h₁ h₂
  simp only [ptC, Complex.ofReal_re, Complex.ofReal_im] at hC
  set u := s.center.re
  set v := s.center.im
  set D1 := a ^ 2 + 2 * a * b + 2 * b ^ 2
  set D2 := 2 * a ^ 2 + 2 * a * b + b ^ 2
  have L1 : 4 * a * b * D1 * (b * u - (a + b) * v - a * b) = 0 := by
    linear_combination D1 ^ 2 * (h₁ - hC) - (D1 * T₁.re + 2 * a * (a + b) ^ 2 - 2 * u * D1) * x1
      - (D1 * T₁.im + 2 * a * b * (a + b) - 2 * v * D1) * y1
  have L2 : 4 * a * b * D2 * (a * u + (a + b) * v - 2 * a ^ 2 - a * b) = 0 := by
    linear_combination -(D2 ^ 2 * (h₂ - hC) - (D2 * T₂.re + 2 * a * (a + b) * (2 * a + b) -
      2 * u * D2) * x2 - (D2 * T₂.im + 2 * a * b * (a + b) - 2 * v * D2) * y2)
  have k1 : b * u - (a + b) * v - a * b = 0 := by
    rcases mul_eq_zero.1 L1 with h | h
    · exact absurd h (by positivity)
    · exact h
  have k2 : a * u + (a + b) * v - 2 * a ^ 2 - a * b = 0 := by
    rcases mul_eq_zero.1 L2 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hu : u = 2 * a := by
    have : (a + b) * (u - 2 * a) = 0 := by linear_combination k1 + k2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hv : v * (a + b) = a * b := by rw [hu] at k1; linear_combination -k1
  have hρ : s.radius ^ 2 = (a * b / (a + b)) ^ 2 := by
    rw [← hC, hu, show v = a * b / (a + b) by rw [eq_div_iff hR.ne']; exact hv]; ring
  exact (sq_eq_sq₀ hs0 (by positivity)).1 hρ

end Arbelos
