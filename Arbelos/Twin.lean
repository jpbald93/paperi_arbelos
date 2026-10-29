import Arbelos.Basic

/-!
# I2.1 Archimedes' twin circles
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- **Archimedes' twin circles (left).** A circle on the `A`-side of the perpendicular at `C`,
tangent to that perpendicular, internally tangent to the big circle and externally tangent to the
circle on `AC`, has radius `ab/(a+b)`. -/
theorem twin_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : s.center.re < 2 * a) (hperp : s.IsTangent (perpC a b))
    (hbig : s.IsIntTangent (bigS a b)) (hsmall : (leftS a b).IsExtTangent s) :
    s.radius = a * b / (a + b) := by
  rw [perpC, isTangent_vline_iff, abs_of_neg (by linarith)] at hperp
  rw [isIntTangent_iff] at hbig
  rw [isExtTangent_iff] at hsmall
  obtain ⟨h1, -, -⟩ := hbig
  obtain ⟨h2, -, -⟩ := hsmall
  simp only [bigS, leftS, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have hx : s.center.re = 2 * a - s.radius := by linarith
  rw [hx] at h1 h2
  field_simp
  nlinarith [h1, h2]

/-- **Archimedes' twin circles (right).** -/
theorem twin_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : 2 * a < s.center.re) (hperp : s.IsTangent (perpC a b))
    (hbig : s.IsIntTangent (bigS a b)) (hsmall : (rightS a b).IsExtTangent s) :
    s.radius = a * b / (a + b) := by
  rw [perpC, isTangent_vline_iff, abs_of_pos (by linarith)] at hperp
  rw [isIntTangent_iff] at hbig
  rw [isExtTangent_iff] at hsmall
  obtain ⟨h1, -, -⟩ := hbig
  obtain ⟨h2, -, -⟩ := hsmall
  simp only [bigS, rightS, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have hx : s.center.re = 2 * a + s.radius := by linarith
  rw [hx] at h1 h2
  field_simp
  nlinarith [h1, h2]

/-- The left twin exists (in the upper half plane). -/
theorem twin_left_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ s.center.re < 2 * a ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (leftS a b).IsExtTangent s := by
  have hR : 0 < a + b := by linarith
  set r := a * b / (a + b) with hr
  have hr0 : 0 < r := by positivity
  have hrR : r * (a + b) = a * b := by rw [hr]; field_simp
  have hra : r < a := by
    rw [hr, div_lt_iff₀ hR]; nlinarith
  refine ⟨⟨⟨2 * a - r, 2 * Real.sqrt (a * r)⟩, r⟩, by simp; positivity, by simp; linarith,
    ?_, ?_, ?_⟩
  · rw [perpC, isTangent_vline_iff]; simp [abs_of_pos hr0]
  · rw [isIntTangent_iff]
    simp only [bigS, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, hr0.le, by nlinarith⟩
    have := Real.sq_sqrt (show 0 ≤ a * r by positivity)
    nlinarith
  · rw [isExtTangent_iff]
    simp only [leftS, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, ha.le, hr0.le⟩
    have := Real.sq_sqrt (show 0 ≤ a * r by positivity)
    nlinarith

/-- The right twin exists (in the upper half plane). -/
theorem twin_right_exists {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ s : Sphere ℂ, 0 < s.center.im ∧ 2 * a < s.center.re ∧ s.IsTangent (perpC a b) ∧
      s.IsIntTangent (bigS a b) ∧ (rightS a b).IsExtTangent s := by
  have hR : 0 < a + b := by linarith
  set r := a * b / (a + b) with hr
  have hr0 : 0 < r := by positivity
  have hrR : r * (a + b) = a * b := by rw [hr]; field_simp
  have hrb : r < b := by
    rw [hr, div_lt_iff₀ hR]; nlinarith
  refine ⟨⟨⟨2 * a + r, 2 * Real.sqrt (b * r)⟩, r⟩, by simp; positivity, by simp; linarith,
    ?_, ?_, ?_⟩
  · rw [perpC, isTangent_vline_iff]; simp [abs_of_pos hr0]
  · rw [isIntTangent_iff]
    simp only [bigS, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, hr0.le, by nlinarith⟩
    have := Real.sq_sqrt (show 0 ≤ b * r by positivity)
    nlinarith
  · rw [isExtTangent_iff]
    simp only [rightS, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, hb.le, hr0.le⟩
    have := Real.sq_sqrt (show 0 ≤ b * r by positivity)
    nlinarith

end Arbelos
