import Arbelos.Inversion

/-!
# I2.3 The Pappus chain

Inverting in the circle of centre `A = 0` and radius `ρ = 2√(a(a+b))` sends the big circle and
the circle on `AC` to the vertical lines `re = 2a` and `re = 2(a+b)`; the chain becomes the
column of circles of radius `b` centred at `(2a+b) + 2nb·i`.  Pulling back gives the explicit
circles `famCircle a b t` (`t : ℝ`), and the chain is `pappusCircle a b n = famCircle a b n`.
With Pappus' own indexing, `pappusCircle a b 0` is the circle on `CB` itself and
`pappusCircle a b 1` is the incircle of the arbelos.
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- Denominator `a(a+b) + t²b²`. -/
noncomputable def famDen (a b t : ℝ) : ℝ := a * (a + b) + t ^ 2 * b ^ 2

/-- The one-parameter family of circles tangent internally to the big circle and externally
to the circle on `AC` (the inverse images of the circles in the strip). -/
noncomputable def famCircle (a b t : ℝ) : Sphere ℂ :=
  ⟨⟨a * (a + b) * (2 * a + b) / famDen a b t, 2 * a * b * (a + b) * t / famDen a b t⟩,
    a * b * (a + b) / famDen a b t⟩

/-- The `n`-th circle of the Pappus chain (Pappus' indexing: `n = 0` is the circle on `CB`). -/
noncomputable def pappusCircle (a b : ℝ) (n : ℕ) : Sphere ℂ := famCircle a b n

/-- The chain re-indexed from the incircle: `incircleChain a b 0` is the incircle of the
arbelos (tangent to the circle on `CB`). -/
noncomputable def incircleChain (a b : ℝ) (n : ℕ) : Sphere ℂ := pappusCircle a b (n + 1)

/-- The radius of the inversion used. -/
noncomputable def invRadius (a b : ℝ) : ℝ := 2 * Real.sqrt (a * (a + b))

theorem famDen_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) : 0 < famDen a b t := by
  unfold famDen; positivity

theorem famCircle_radius_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    0 < (famCircle a b t).radius := by
  have := famDen_pos ha hb t
  simp only [famCircle]; positivity

theorem famCircle_tangent_big {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (famCircle a b t).IsIntTangent (bigS a b) := by
  have hD := famDen_pos ha hb t
  rw [isIntTangent_iff]
  simp only [famCircle, bigS, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, by positivity, ?_⟩
  · field_simp; unfold famDen; ring
  · rw [div_le_iff₀ hD]; unfold famDen; nlinarith [mul_nonneg (add_pos ha hb).le (sq_nonneg (t * b)),
    mul_pos (mul_pos ha ha) (add_pos ha hb)]

theorem famCircle_tangent_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    (leftS a b).IsExtTangent (famCircle a b t) := by
  have hD := famDen_pos ha hb t
  rw [isExtTangent_iff]
  simp only [famCircle, leftS, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, ha.le, by positivity⟩
  field_simp; unfold famDen; ring

/-- Key identity: the tangency defect of two family members is `4 r r' ((t-u)² - 1)`. -/
theorem famCircle_dist_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t u : ℝ) :
    ((famCircle a b t).center.re - (famCircle a b u).center.re) ^ 2 +
      ((famCircle a b t).center.im - (famCircle a b u).center.im) ^ 2 -
      ((famCircle a b t).radius + (famCircle a b u).radius) ^ 2 =
      4 * (famCircle a b t).radius * (famCircle a b u).radius * ((t - u) ^ 2 - 1) := by
  have hD := (famDen_pos ha hb t).ne'
  have hE := (famDen_pos ha hb u).ne'
  simp only [famCircle]
  field_simp; unfold famDen; ring

theorem famCircle_tangent_famCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t u : ℝ}
    (h : (t - u) ^ 2 = 1) : (famCircle a b t).IsExtTangent (famCircle a b u) := by
  rw [isExtTangent_iff]
  have := famCircle_dist_sq ha hb t u
  rw [h, sub_self, mul_zero, sub_eq_zero] at this
  exact ⟨this, (famCircle_radius_pos ha hb t).le, (famCircle_radius_pos ha hb u).le⟩

theorem famCircle_height (a b t : ℝ) :
    (famCircle a b t).center.im = t * (2 * (famCircle a b t).radius) := by
  simp only [famCircle]; ring

theorem invRadius_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : invRadius a b ^ 2 = 4 * a * (a + b) := by
  rw [invRadius, mul_pow, Real.sq_sqrt (by positivity)]; ring

theorem invRadius_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : invRadius a b ≠ 0 := by
  rw [invRadius]; have : 0 < Real.sqrt (a * (a + b)) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- The image of `famCircle a b t` under the inversion: radius `b`, centre `(2a+b) + 2bt·i`. -/
theorem invSphere_famCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    invSphere (ptA a b) (invRadius a b) (famCircle a b t) = ⟨⟨2 * a + b, 2 * b * t⟩, b⟩ := by
  have hD := famDen_pos ha hb t
  have hE : ‖(famCircle a b t).center - ptA a b‖ ^ 2 - (famCircle a b t).radius ^ 2 =
      4 * a ^ 2 * (a + b) ^ 2 / famDen a b t := by
    rw [ptA, sub_zero, norm_sq_re_im]
    simp only [famCircle]
    field_simp; unfold famDen; ring
  have hEpos : 0 < 4 * a ^ 2 * (a + b) ^ 2 / famDen a b t := by positivity
  unfold invSphere
  rw [hE, invRadius_sq ha hb, abs_of_pos hEpos]
  simp only [ptA, zero_add, sub_zero]
  refine Sphere.ext ?_ ?_
  · apply Complex.ext
    · simp only [famCircle, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      field_simp
    · simp only [famCircle, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero]
      field_simp
  · simp only [famCircle]
    field_simp

theorem famCircle_center_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖(famCircle a b t).center - ptA a b‖ ^ 2 ≠ (famCircle a b t).radius ^ 2 := by
  have hD := famDen_pos ha hb t
  rw [ptA, sub_zero, norm_sq_re_im]
  simp only [famCircle]
  intro h
  field_simp at h
  nlinarith [mul_pos ha hb, sq_nonneg t, sq_nonneg (t * b), mul_pos (mul_pos ha ha) (add_pos ha hb)]

/-- From two family members being externally tangent, their parameters differ by `±1`. -/
theorem famCircle_param_of_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {t u : ℝ}
    (h : (famCircle a b t).IsExtTangent (famCircle a b u)) : (t - u) ^ 2 = 1 := by
  rw [isExtTangent_iff] at h
  have key := famCircle_dist_sq ha hb t u
  rw [h.1, sub_self] at key
  have h1 := famCircle_radius_pos ha hb t
  have h2 := famCircle_radius_pos ha hb u
  have : 4 * (famCircle a b t).radius * (famCircle a b u).radius ≠ 0 := by positivity
  have := mul_eq_zero.1 key.symm
  rcases this with h3 | h3
  · exact absurd h3 (by positivity)
  · linarith

theorem eq_of_sq_eq_one {x y : ℝ} (h : (x - y) ^ 2 = 1) : x = y + 1 ∨ x = y - 1 := by
  have : (x - y - 1) * (x - y + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

theorem pappusCircle_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pappusCircle a b 0 = rightS a b := by
  have hD : famDen a b 0 = a * (a + b) := by simp [famDen]
  have hR : a * (a + b) ≠ 0 := by positivity
  simp only [pappusCircle, famCircle, Nat.cast_zero, hD, rightS]
  congr 1
  · apply Complex.ext <;> simp
    field_simp
  · field_simp

theorem pappus_radius_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 < (pappusCircle a b n).radius := by
  exact famCircle_radius_pos ha hb n

theorem pappus_tangent_big {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).IsIntTangent (bigS a b) := by
  exact famCircle_tangent_big ha hb n

theorem pappus_tangent_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (leftS a b).IsExtTangent (pappusCircle a b n) := by
  exact famCircle_tangent_left ha hb n

theorem pappus_tangent_succ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).IsExtTangent (pappusCircle a b (n + 1)) := by
  exact famCircle_tangent_famCircle ha hb (by push_cast; ring)

/-- **Pappus chain theorem.** The centre of the `n`-th circle is at height `n` times its
diameter above the line `AB`. -/
theorem pappus_chain {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (pappusCircle a b n).center.im = n * (2 * (pappusCircle a b n).radius) := by
  exact famCircle_height a b n

/-- The chain indexed from the incircle: tangencies and height `(n+1)` diameters. -/
theorem incircleChain_spec {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (incircleChain a b n).IsIntTangent (bigS a b) ∧
      (leftS a b).IsExtTangent (incircleChain a b n) ∧
      (rightS a b).IsExtTangent (incircleChain a b 0) ∧
      (incircleChain a b n).IsExtTangent (incircleChain a b (n + 1)) ∧
      (incircleChain a b n).center.im = (n + 1) * (2 * (incircleChain a b n).radius) := by
  refine ⟨pappus_tangent_big ha hb _, pappus_tangent_left ha hb _, ?_, pappus_tangent_succ ha hb _,
    ?_⟩
  · rw [← pappusCircle_zero ha hb]; exact pappus_tangent_succ ha hb 0
  · rw [incircleChain, pappus_chain ha hb]; push_cast; ring

/-- The inversion picture: the big circle (minus `A`) goes to the line `re = 2a`. -/
theorem inversion_bigS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (ptA a b) (invRadius a b) '' ((bigS a b : Set ℂ) \ {ptA a b}) = vline (2 * a) := by
  have hρ := invRadius_ne_zero ha hb
  have hk := invRadius_sq ha hb
  have hR : 0 ≤ a + b := by linarith
  have key : ∀ z : ℂ, z ≠ 0 → (z ∈ bigS a b ↔ (inversion (ptA a b) (invRadius a b) z).re = 2 * a) := by
    intro z hz
    have hN : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
      rw [← norm_sq_re_im]; positivity
    rw [mem_sphere_iff_sq hR, inversion_re, hk]
    simp only [bigS, ptA, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      sub_zero, zero_add]
    rw [div_mul_eq_mul_div, div_eq_iff hN]
    constructor <;> intro h <;> nlinarith
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
    rw [SetLike.mem_coe, mem_vline_iff]
    exact (key z hz0).1 hz
  · intro hw
    rw [SetLike.mem_coe, mem_vline_iff] at hw
    have hw0 : w ≠ ptA a b := by
      intro h; rw [h, ptA] at hw; simp at hw; linarith
    refine ⟨inversion (ptA a b) (invRadius a b) w, ⟨?_, ?_⟩, inversion_inversion _ hρ w⟩
    · have hz0 : inversion (ptA a b) (invRadius a b) w ≠ 0 := fun h ↦
        hw0 ((inversion_eq_center hρ).1 h)
      show _ ∈ (_ : Sphere ℂ)
      rw [key _ hz0, inversion_inversion _ hρ]; exact hw
    · rw [Set.mem_singleton_iff, inversion_eq_center hρ]; exact hw0

/-- The inversion picture: the circle on `AC` (minus `A`) goes to the line `re = 2(a+b)`. -/
theorem inversion_leftS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (ptA a b) (invRadius a b) '' ((leftS a b : Set ℂ) \ {ptA a b}) =
      vline (2 * (a + b)) := by
  have hρ := invRadius_ne_zero ha hb
  have hk := invRadius_sq ha hb
  have hR : 0 ≤ a := ha.le
  have key : ∀ z : ℂ, z ≠ 0 → (z ∈ leftS a b ↔ (inversion (ptA a b) (invRadius a b) z).re = 2 * (a + b)) := by
    intro z hz
    have hN : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
      rw [← norm_sq_re_im]; positivity
    rw [mem_sphere_iff_sq hR, inversion_re, hk]
    simp only [leftS, ptA, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      sub_zero, zero_add]
    rw [div_mul_eq_mul_div, div_eq_iff hN]
    constructor <;> intro h <;> nlinarith
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
    rw [SetLike.mem_coe, mem_vline_iff]
    exact (key z hz0).1 hz
  · intro hw
    rw [SetLike.mem_coe, mem_vline_iff] at hw
    have hw0 : w ≠ ptA a b := by
      intro h; rw [h, ptA] at hw; simp at hw; nlinarith
    refine ⟨inversion (ptA a b) (invRadius a b) w, ⟨?_, ?_⟩, inversion_inversion _ hρ w⟩
    · have hz0 : inversion (ptA a b) (invRadius a b) w ≠ 0 := fun h ↦
        hw0 ((inversion_eq_center hρ).1 h)
      show _ ∈ (_ : Sphere ℂ)
      rw [key _ hz0, inversion_inversion _ hρ]; exact hw
    · rw [Set.mem_singleton_iff, inversion_eq_center hρ]; exact hw0

/-- The inversion picture: the `n`-th chain circle goes to the circle of radius `b` centred at
`(2a+b) + 2nb·i` in the strip. -/
theorem inversion_pappusCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    inversion (ptA a b) (invRadius a b) '' (pappusCircle a b n : Set ℂ) =
      Metric.sphere (⟨2 * a + b, 2 * n * b⟩ : ℂ) b := by
  rw [pappusCircle, image_inversion_sphere (invRadius_ne_zero ha hb)
    (famCircle_radius_pos ha hb _).le (famCircle_center_ne ha hb _), invSphere_famCircle ha hb,
    Sphere.coe_mk]
  congr 2; ring

/-- Every circle of positive radius tangent internally to the big circle and externally to the
circle on `AC` belongs to the family `famCircle`. -/
theorem eq_famCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ) (hs : 0 < s.radius)
    (hbig : s.IsIntTangent (bigS a b)) (hleft : (leftS a b).IsExtTangent s) :
    s = famCircle a b (s.center.im / (2 * s.radius)) := by
  rw [isIntTangent_iff] at hbig
  rw [isExtTangent_iff] at hleft
  obtain ⟨h1, -, -⟩ := hbig
  obtain ⟨h2, -, -⟩ := hleft
  simp only [bigS, leftS, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  set r := s.radius
  set X := s.center.re
  set Y := s.center.im
  set t := Y / (2 * r) with ht
  have hY : Y = 2 * r * t := by rw [ht]; field_simp
  have hX : X * b = r * (2 * a + b) := by linear_combination (h2 - h1) / 2
  have hq : 4 * r ^ 2 * a * (a + b) + Y ^ 2 * b ^ 2 = 4 * a * b * (a + b) * r := by
    linear_combination b ^ 2 * h2 + (-X * b + 2 * a * b - 2 * a * r - b * r) * hX
  have hrD : r * famDen a b t = a * b * (a + b) := by
    apply mul_left_cancel₀ (show (4 * r : ℝ) ≠ 0 by positivity)
    rw [hY] at hq; unfold famDen; linear_combination hq
  have hD := famDen_pos ha hb t
  refine Sphere.ext (Complex.ext ?_ ?_) ?_
  · show X = a * (a + b) * (2 * a + b) / famDen a b t
    rw [eq_div_iff hD.ne']
    apply mul_left_cancel₀ hb.ne'
    linear_combination famDen a b t * hX + (2 * a + b) * hrD
  · show Y = 2 * a * b * (a + b) * t / famDen a b t
    rw [eq_div_iff hD.ne', hY]
    linear_combination 2 * t * hrD
  · show r = a * b * (a + b) / famDen a b t
    rw [eq_div_iff hD.ne']; exact hrD

/-- **Uniqueness of the Pappus chain.** Any chain of circles starting from the circle on `CB`,
each tangent to the big circle and to the circle on `AC` and to the next one, with consecutive
circles not doubling back and the first new circle in the upper half plane, is the Pappus chain. -/
theorem pappus_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℕ → Sphere ℂ)
    (h0 : c 0 = rightS a b) (hpos : ∀ n, 0 < (c n).radius)
    (hbig : ∀ n, (c n).IsIntTangent (bigS a b)) (hleft : ∀ n, (leftS a b).IsExtTangent (c n))
    (hsucc : ∀ n, (c n).IsExtTangent (c (n + 1))) (hne : ∀ n, c (n + 2) ≠ c n)
    (hup : 0 < (c 1).center.im) (n : ℕ) :
    c n = pappusCircle a b n := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ n, c n = famCircle a b (t n) :=
    ⟨_, fun n ↦ eq_famCircle ha hb (c n) (hpos n) (hbig n) (hleft n)⟩
  have hstep : ∀ n, t (n + 1) = t n + 1 ∨ t (n + 1) = t n - 1 := fun n ↦ by
    have := hsucc n
    rw [ht n, ht (n + 1)] at this
    have h := famCircle_param_of_tangent ha hb this
    rcases eq_of_sq_eq_one h with h | h
    · right; linarith
    · left; linarith
  have h0' : t 0 = 0 := by
    have h := famCircle_height a b (t 0)
    rw [← ht 0, h0] at h
    simp only [rightS, Complex.ofReal_im] at h
    rcases mul_eq_zero.1 h.symm with h | h
    · exact h
    · linarith
  have h1' : t 1 = 1 := by
    have h := famCircle_height a b (t 1)
    rw [← ht 1] at h
    have hr := hpos 1
    have : 0 < t 1 := by
      by_contra hn; rw [not_lt] at hn; nlinarith
    rcases hstep 0 with h' | h' <;> rw [h0'] at h'
    · linarith
    · linarith
  have main : ∀ n : ℕ, t n = n ∧ t (n + 1) = n + 1 := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using h0', by simpa using h1'⟩
    | succ k ih =>
      refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
      rcases hstep (k + 1) with h | h
      · rw [h, ih.2]; push_cast; ring
      · exfalso
        apply hne k
        rw [ht (k + 2), ht k, show k + 1 + 1 = k + 2 from rfl] at *
        rw [show t (k + 2) = t k by rw [h, ih.2, ih.1]; ring]
  rw [ht n, (main n).1]; rfl

end Arbelos
