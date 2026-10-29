import Arbelos.Basic

/-!
# Inversion of circles in `ℂ`

`invSphere c ρ s` is the image of the circle `s` (not through `c`) under Mathlib's
`EuclideanGeometry.inversion c ρ`.
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- The image circle of `s` under inversion in the circle of centre `c` and radius `ρ`. -/
noncomputable def invSphere (c : ℂ) (ρ : ℝ) (s : Sphere ℂ) : Sphere ℂ :=
  ⟨c + ((ρ ^ 2 / (‖s.center - c‖ ^ 2 - s.radius ^ 2) : ℝ) : ℂ) * (s.center - c),
    ρ ^ 2 * s.radius / |‖s.center - c‖ ^ 2 - s.radius ^ 2|⟩

/-- Inversion in coordinates (real part). -/
theorem inversion_re (c : ℂ) (ρ : ℝ) (z : ℂ) : (inversion c ρ z).re =
    c.re + ρ ^ 2 / ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) * (z.re - c.re) := by
  rw [inversion, vsub_eq_sub, vadd_eq_add, Complex.add_re, Complex.smul_re, smul_eq_mul,
    div_pow, dist_sq_re_im, Complex.sub_re]
  ring

/-- Inversion in coordinates (imaginary part). -/
theorem inversion_im (c : ℂ) (ρ : ℝ) (z : ℂ) : (inversion c ρ z).im =
    c.im + ρ ^ 2 / ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) * (z.im - c.im) := by
  rw [inversion, vsub_eq_sub, vadd_eq_add, Complex.add_im, Complex.smul_im, smul_eq_mul,
    div_pow, dist_sq_re_im, Complex.sub_im]
  ring

theorem norm_sq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Membership in a circle via squared coordinates (for nonnegative radius). -/
theorem mem_sphere_iff_sq {z : ℂ} {s : Sphere ℂ} (hr : 0 ≤ s.radius) :
    z ∈ s ↔ (z.re - s.center.re) ^ 2 + (z.im - s.center.im) ^ 2 = s.radius ^ 2 := by
  rw [EuclideanGeometry.mem_sphere, ← dist_sq_re_im]
  exact ⟨fun h ↦ by rw [h], fun h ↦ (sq_eq_sq₀ dist_nonneg hr).1 h⟩

/-- Inversion maps a circle not through the centre onto `invSphere`. -/
theorem inversion_mem_invSphere_iff {c : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) {s : Sphere ℂ}
    (hr : 0 ≤ s.radius) (hp : ‖s.center - c‖ ^ 2 ≠ s.radius ^ 2) (z : ℂ) :
    inversion c ρ z ∈ invSphere c ρ s ↔ z ∈ s := by
  set E := ‖s.center - c‖ ^ 2 - s.radius ^ 2 with hE
  have hE0 : E ≠ 0 := sub_ne_zero.2 hp
  have hr' : 0 ≤ (invSphere c ρ s).radius := by simp only [invSphere]; positivity
  rw [mem_sphere_iff_sq hr', mem_sphere_iff_sq hr]
  have hEdef : ‖s.center - c‖ ^ 2 - s.radius ^ 2 = E := rfl
  simp only [invSphere, inversion_re, inversion_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, zero_mul, sub_zero, add_zero, div_pow, sq_abs, hEdef]
  set x := z.re - c.re
  set y := z.im - c.im
  set p := s.center.re - c.re
  set q := s.center.im - c.im
  have hzr : z.re - s.center.re = x - p := by simp [x, p]
  have hzi : z.im - s.center.im = y - q := by simp [y, q]
  rw [hzr, hzi]
  have hE' : E = p ^ 2 + q ^ 2 - s.radius ^ 2 := by
    rw [hE, norm_sq_re_im]; simp [p, q]
  have hk : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  rcases eq_or_ne (x ^ 2 + y ^ 2) 0 with hN | hN
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    rw [hN, div_zero, zero_mul, zero_mul, hx, hy]
    constructor
    · intro h
      exfalso; apply hE0
      have : (ρ ^ 2) ^ 2 * (p ^ 2 + q ^ 2 - s.radius ^ 2) = 0 := by
        field_simp at h; linear_combination h
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (pow_ne_zero 2 hk)
      · rw [hE']; linarith
    · intro h; exfalso; apply hE0; rw [hE']; linarith
  · have key : (c.re + ρ ^ 2 / (x ^ 2 + y ^ 2) * x - (c.re + ρ ^ 2 / E * p)) ^ 2 +
        (c.im + ρ ^ 2 / (x ^ 2 + y ^ 2) * y - (c.im + ρ ^ 2 / E * q)) ^ 2 -
        (ρ ^ 2 * s.radius) ^ 2 / E ^ 2 =
        (ρ ^ 2) ^ 2 / ((x ^ 2 + y ^ 2) * E) * ((x - p) ^ 2 + (y - q) ^ 2 - s.radius ^ 2) := by
      field_simp; rw [hE']; ring
    have hne : (ρ ^ 2) ^ 2 / ((x ^ 2 + y ^ 2) * E) ≠ 0 := by
      have := pow_ne_zero 2 hk; positivity
    rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right hne, sub_eq_zero]

theorem image_inversion_sphere {c : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) {s : Sphere ℂ}
    (hr : 0 ≤ s.radius) (hp : ‖s.center - c‖ ^ 2 ≠ s.radius ^ 2) :
    inversion c ρ '' (s : Set ℂ) = (invSphere c ρ s : Set ℂ) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (inversion_mem_invSphere_iff hρ hr hp w).2 hw
  · intro hz
    refine ⟨inversion c ρ z, ?_, inversion_inversion c hρ z⟩
    rw [← inversion_inversion c hρ z] at hz
    exact (inversion_mem_invSphere_iff hρ hr hp _).1 hz

end Arbelos
