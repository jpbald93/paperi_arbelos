import Arbelos.Area
import Arbelos.Twin
import Arbelos.Bankoff
import Arbelos.Steiner

/-!
# Layer 14: Mathlib-only restatements and explicit witnesses

`l14_<name>` restates each main theorem with every local definition unfolded (`ptA`, `ptC`,
`bigS`, `leftS`, `rightS`, `vline`, `perpC`, `arbelosRegion`, `famDen`, `famCircle`,
`pappusCircle`, `invRadius`, `IsSteinerChain`): circles are written as Mathlib spheres
`(⟨centre, radius⟩ : Sphere ℂ)`, the perpendicular at `C` as `AffineSubspace.mk' (2a) (ℝ ∙ I)`,
and inversion is Mathlib's `EuclideanGeometry.inversion`. Each is proved from the library theorem.

`l14w_<name>` gives a concrete configuration (arbelos radii `a = 1`, `b = 2`, i.e. `A = 0`,
`C = 2`, `B = 6`) satisfying every hypothesis, with a non-degenerate conclusion.
-/

open EuclideanGeometry Complex MeasureTheory

namespace Arbelos

section Restatements

/-- **Archimedes' twin circles** (left twin). -/
theorem l14_twin_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : s.center.re < 2 * a)
    (hperp : s.IsTangent (AffineSubspace.mk' (((2 * a : ℝ)) : ℂ) (ℝ ∙ Complex.I)))
    (hbig : s.IsIntTangent (⟨((a + b : ℝ) : ℂ), a + b⟩ : Sphere ℂ))
    (hsmall : (⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ).IsExtTangent s) :
    s.radius = a * b / (a + b) :=
  twin_left ha hb s hside hperp hbig hsmall

/-- **Archimedes' twin circles** (right twin). -/
theorem l14_twin_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : Sphere ℂ)
    (hside : 2 * a < s.center.re)
    (hperp : s.IsTangent (AffineSubspace.mk' (((2 * a : ℝ)) : ℂ) (ℝ ∙ Complex.I)))
    (hbig : s.IsIntTangent (⟨((a + b : ℝ) : ℂ), a + b⟩ : Sphere ℂ))
    (hsmall : (⟨((2 * a + b : ℝ) : ℂ), b⟩ : Sphere ℂ).IsExtTangent s) :
    s.radius = a * b / (a + b) :=
  twin_right ha hb s hside hperp hbig hsmall

/-- **Area of the arbelos** (Archimedes). -/
theorem l14_arbelos_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (D : ℂ)
    (hD : D ∈ (⟨((a + b : ℝ) : ℂ), a + b⟩ : Sphere ℂ))
    (hDperp : D ∈ AffineSubspace.mk' (((2 * a : ℝ)) : ℂ) (ℝ ∙ Complex.I)) :
    volume {z : ℂ | 0 < z.im ∧ dist z ((a + b : ℝ) : ℂ) ≤ a + b ∧ a ≤ dist z ((a : ℝ) : ℂ) ∧
        b ≤ dist z ((2 * a + b : ℝ) : ℂ)} =
      volume (Metric.ball (midpoint ℝ ((2 * a : ℝ) : ℂ) D) (dist ((2 * a : ℝ) : ℂ) D / 2)) :=
  arbelos_area ha hb D hD hDperp

/-- **Pappus chain theorem**, with the chain written out: the `n`-th circle has centre
`(a(a+b)(2a+b) + 2ab(a+b)n·i) / (a(a+b) + n²b²)` and radius `ab(a+b) / (a(a+b) + n²b²)`; circle `0`
is the circle on `CB`, every circle touches the big circle internally and the circle on `AC`
externally, consecutive circles touch, and the centre of the `n`-th circle lies `n` diameters
above `AB`. -/
theorem l14_pappus_chain {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + ((0 : ℕ) : ℝ) ^ 2 * b ^ 2),
        2 * a * b * (a + b) * ((0 : ℕ) : ℝ) / (a * (a + b) + ((0 : ℕ) : ℝ) ^ 2 * b ^ 2)⟩,
        a * b * (a + b) / (a * (a + b) + ((0 : ℕ) : ℝ) ^ 2 * b ^ 2)⟩ : Sphere ℂ) =
      ⟨((2 * a + b : ℝ) : ℂ), b⟩ ∧
    ∀ n : ℕ,
      (⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩ : Sphere ℂ).IsIntTangent
        ⟨((a + b : ℝ) : ℂ), a + b⟩ ∧
      (⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ).IsExtTangent
        ⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩ ∧
      (⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩ : Sphere ℂ).IsExtTangent
        ⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + ((n + 1 : ℕ) : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * ((n + 1 : ℕ) : ℝ) / (a * (a + b) + ((n + 1 : ℕ) : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + ((n + 1 : ℕ) : ℝ) ^ 2 * b ^ 2)⟩ ∧
      2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2) =
        n * (2 * (a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2))) :=
  ⟨pappusCircle_zero ha hb, fun n =>
    ⟨pappus_tangent_big ha hb n, pappus_tangent_left ha hb n, pappus_tangent_succ ha hb n,
      pappus_chain n⟩⟩

/-- **Uniqueness of the Pappus chain**: any chain of positive circles starting at the circle on
`CB`, tangent to the big circle and the circle on `AC` and to its successor, not doubling back,
with the first new circle in the upper half plane, is the explicit chain above. -/
theorem l14_pappus_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℕ → Sphere ℂ)
    (h0 : c 0 = ⟨((2 * a + b : ℝ) : ℂ), b⟩) (hpos : ∀ n, 0 < (c n).radius)
    (hbig : ∀ n, (c n).IsIntTangent ⟨((a + b : ℝ) : ℂ), a + b⟩)
    (hleft : ∀ n, (⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ).IsExtTangent (c n))
    (hsucc : ∀ n, (c n).IsExtTangent (c (n + 1))) (hne : ∀ n, c (n + 2) ≠ c n)
    (hup : 0 < (c 1).center.im) (n : ℕ) :
    c n = ⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩ :=
  pappus_unique ha hb c h0 hpos hbig hleft hsucc hne hup n

/-- Inversion at `A` with radius `2√(a(a+b))` maps the big circle (minus `A`) onto the line
`re = 2a`. -/
theorem l14_inversion_bigS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (0 : ℂ) (2 * Real.sqrt (a * (a + b))) ''
        (((⟨((a + b : ℝ) : ℂ), a + b⟩ : Sphere ℂ) : Set ℂ) \ {0}) =
      (AffineSubspace.mk' (((2 * a : ℝ)) : ℂ) (ℝ ∙ Complex.I) : Set ℂ) :=
  inversion_bigS ha hb

/-- … and the circle on `AC` (minus `A`) onto the line `re = 2(a+b)`. -/
theorem l14_inversion_leftS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inversion (0 : ℂ) (2 * Real.sqrt (a * (a + b))) ''
        (((⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ) : Set ℂ) \ {0}) =
      (AffineSubspace.mk' (((2 * (a + b) : ℝ)) : ℂ) (ℝ ∙ Complex.I) : Set ℂ) :=
  inversion_leftS ha hb

/-- … and the `n`-th chain circle onto the circle of radius `b` about `(2a+b) + 2nb·i`. -/
theorem l14_inversion_pappusCircle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    inversion (0 : ℂ) (2 * Real.sqrt (a * (a + b))) ''
        ((⟨⟨a * (a + b) * (2 * a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2),
          2 * a * b * (a + b) * (n : ℝ) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩,
          a * b * (a + b) / (a * (a + b) + (n : ℝ) ^ 2 * b ^ 2)⟩ : Sphere ℂ) : Set ℂ) =
      Metric.sphere (⟨2 * a + b, 2 * n * b⟩ : ℂ) b :=
  inversion_pappusCircle ha hb n

/-- **Bankoff's circle.** -/
theorem l14_bankoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s₀ : Sphere ℂ)
    (hbig : s₀.IsIntTangent ⟨((a + b : ℝ) : ℂ), a + b⟩)
    (hleft : (⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ).IsExtTangent s₀)
    (hright : (⟨((2 * a + b : ℝ) : ℂ), b⟩ : Sphere ℂ).IsExtTangent s₀) (hup : 0 < s₀.center.im)
    (T₁ T₂ : ℂ) (hT₁ : (⟨((a : ℝ) : ℂ), a⟩ : Sphere ℂ).IsExtTangentAt s₀ T₁)
    (hT₂ : (⟨((2 * a + b : ℝ) : ℂ), b⟩ : Sphere ℂ).IsExtTangentAt s₀ T₂)
    (s : Sphere ℂ) (hC : ((2 * a : ℝ) : ℂ) ∈ s) (h₁ : T₁ ∈ s) (h₂ : T₂ ∈ s) :
    s.radius = a * b / (a + b) :=
  bankoff ha hb s₀ hbig hleft hright hup T₁ T₂ hT₁ hT₂ s hC h₁ h₂

/-- **Steiner's porism.** -/
theorem l14_steiner_porism (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (n : ℕ) (c : ZMod n → Sphere ℂ)
    (hchain : ∀ i, 0 < (c i).radius ∧ S₁.IsExtTangent (c i) ∧ (c i).IsIntTangent S₂ ∧
      (c i).IsExtTangent (c (i + 1)))
    (s₀ : Sphere ℂ) (hs₀ : 0 < s₀.radius) (h₁' : S₁.IsExtTangent s₀) (h₂' : s₀.IsIntTangent S₂) :
    ∃ d : ZMod n → Sphere ℂ, (∀ i, 0 < (d i).radius ∧ S₁.IsExtTangent (d i) ∧
      (d i).IsIntTangent S₂ ∧ (d i).IsExtTangent (d (i + 1))) ∧ d 0 = s₀ :=
  steiner_porism S₁ S₂ h₁ hin n c hchain s₀ hs₀ h₁' h₂'

end Restatements

/-! ### Witnesses (`a = 1`, `b = 2`) -/

section Witnesses

theorem l14h_mem_sphere {z c : ℂ} {r : ℝ} (hr : 0 ≤ r := by norm_num)
    (h : (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 = r ^ 2) : z ∈ (⟨c, r⟩ : Sphere ℂ) := by
  show dist z c = r
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hr]

theorem l14h_wbtw {x y z : ℂ} (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (h : y = x + (k : ℂ) * (z - x)) :
    Wbtw ℝ x y z := by
  refine ⟨k, ⟨hk0, hk1⟩, ?_⟩
  rw [h, AffineMap.lineMap_apply]; simp [Complex.real_smul]; ring

theorem l14h_sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- **Witness for the twin circles.** For `a = 1`, `b = 2` the left twin is the circle of radius
`2/3` about `4/3 + 2√(2/3)·i`, the right twin the circle of radius `2/3` about `8/3 + 2√(4/3)·i`;
all hypotheses hold and the radii are positive. -/
theorem l14w_twin :
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re < 2 * 1 ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspace.mk' (((2 * 1 : ℝ)) : ℂ) (ℝ ∙ Complex.I)) ∧
    (⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsIntTangent
      ⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ ∧
    (⟨((1 : ℝ) : ℂ), 1⟩ : Sphere ℂ).IsExtTangent ⟨⟨4 / 3, 2 * Real.sqrt (2 / 3)⟩, 2 / 3⟩ ∧
    2 * 1 < (⟨⟨8 / 3, 2 * Real.sqrt (4 / 3)⟩, 2 / 3⟩ : Sphere ℂ).center.re ∧
    (⟨⟨8 / 3, 2 * Real.sqrt (4 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsTangent
      (AffineSubspace.mk' (((2 * 1 : ℝ)) : ℂ) (ℝ ∙ Complex.I)) ∧
    (⟨⟨8 / 3, 2 * Real.sqrt (4 / 3)⟩, 2 / 3⟩ : Sphere ℂ).IsIntTangent
      ⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ ∧
    (⟨((2 * 1 + 2 : ℝ) : ℂ), 2⟩ : Sphere ℂ).IsExtTangent ⟨⟨8 / 3, 2 * Real.sqrt (4 / 3)⟩, 2 / 3⟩ ∧
    (0 : ℝ) < 2 / 3 := by
  have s1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have s2 := Real.sq_sqrt (show (0 : ℝ) ≤ 4 / 3 by norm_num)
  refine ⟨by norm_num, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · rw [← vline, isTangent_vline_iff]; norm_num [abs_of_pos]
  · rw [isIntTangent_iff]; refine ⟨?_, by norm_num, by norm_num⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im]; nlinarith
  · rw [isExtTangent_iff]; refine ⟨?_, by norm_num, by norm_num⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im]; nlinarith
  · rw [← vline, isTangent_vline_iff]; norm_num [abs_of_pos]
  · rw [isIntTangent_iff]; refine ⟨?_, by norm_num, by norm_num⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im]; nlinarith
  · rw [isExtTangent_iff]; refine ⟨?_, by norm_num, by norm_num⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im]; nlinarith

/-- **Witness for the arbelos area.** For `a = 1`, `b = 2` the point `D = 2 + 2√2·i` lies on the
big circle and on the perpendicular at `C`; the area is `2π ≠ 0` (the ball of radius `√2`). -/
theorem l14w_arbelos_area :
    (⟨2, 2 * Real.sqrt 2⟩ : ℂ) ∈ (⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ : Sphere ℂ) ∧
    (⟨2, 2 * Real.sqrt 2⟩ : ℂ) ∈ AffineSubspace.mk' (((2 * 1 : ℝ)) : ℂ) (ℝ ∙ Complex.I) ∧
    volume {z : ℂ | 0 < z.im ∧ dist z ((1 + 2 : ℝ) : ℂ) ≤ 1 + 2 ∧ 1 ≤ dist z ((1 : ℝ) : ℂ) ∧
        2 ≤ dist z ((2 * 1 + 2 : ℝ) : ℂ)} = ENNReal.ofReal 2 * NNReal.pi ∧
    ENNReal.ofReal 2 * NNReal.pi ≠ 0 := by
  have hD : (⟨2, 2 * Real.sqrt 2⟩ : ℂ) ∈ (⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ : Sphere ℂ) :=
    l14h_mem_sphere (by norm_num) (by simp; nlinarith [l14h_sqrt_two_sq])
  have hP : (⟨2, 2 * Real.sqrt 2⟩ : ℂ) ∈ AffineSubspace.mk' (((2 * 1 : ℝ)) : ℂ) (ℝ ∙ Complex.I) := by
    rw [← vline, mem_vline_iff]; norm_num
  refine ⟨hD, hP, ?_, by simp [NNReal.pi_ne_zero]⟩
  rw [l14_arbelos_area one_pos two_pos _ hD hP, Complex.volume_ball]
  congr 2
  have hd : dist (((2 * 1 : ℝ)) : ℂ) ⟨2, 2 * Real.sqrt 2⟩ = 2 * Real.sqrt 2 := by
    rw [Complex.dist_eq_re_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [show ((2 * 1 : ℝ) - 2) ^ 2 + (0 - 2 * Real.sqrt 2) ^ 2 = (2 * Real.sqrt 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hd, show 2 * Real.sqrt 2 / 2 = Real.sqrt 2 by ring, ← ENNReal.ofReal_pow (by positivity),
    l14h_sqrt_two_sq]

/-- **Witness for the Pappus chain.** For `a = 1`, `b = 2` the explicit circles `1` and `2` of
the chain are `(12/7 + 12/7·i, 6/7)` and `(12/19 + 24/19·i, 6/19)`; their centres lie `1` and `2`
diameters above `AB` (heights `12/7 ≠ 0`, `24/19 ≠ 0`). -/
theorem l14w_pappus_chain :
    (⟨⟨1 * (1 + 2) * (2 * 1 + 2) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2),
        2 * 1 * 2 * (1 + 2) * ((1 : ℕ) : ℝ) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩,
        1 * 2 * (1 + 2) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩ : Sphere ℂ) =
      ⟨⟨12 / 7, 12 / 7⟩, 6 / 7⟩ ∧
    (⟨⟨1 * (1 + 2) * (2 * 1 + 2) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2),
        2 * 1 * 2 * (1 + 2) * ((2 : ℕ) : ℝ) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩,
        1 * 2 * (1 + 2) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩ : Sphere ℂ) =
      ⟨⟨12 / 19, 24 / 19⟩, 6 / 19⟩ ∧
    (12 / 7 : ℝ) = 1 * (2 * (6 / 7)) ∧ (24 / 19 : ℝ) = 2 * (2 * (6 / 19)) ∧
    (⟨⟨12 / 7, 12 / 7⟩, 6 / 7⟩ : Sphere ℂ).IsExtTangent ⟨⟨12 / 19, 24 / 19⟩, 6 / 19⟩ := by
  have e1 : (⟨⟨1 * (1 + 2) * (2 * 1 + 2) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2),
        2 * 1 * 2 * (1 + 2) * ((1 : ℕ) : ℝ) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩,
        1 * 2 * (1 + 2) / (1 * (1 + 2) + ((1 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩ : Sphere ℂ) =
      ⟨⟨12 / 7, 12 / 7⟩, 6 / 7⟩ := by norm_num
  have e2 : (⟨⟨1 * (1 + 2) * (2 * 1 + 2) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2),
        2 * 1 * 2 * (1 + 2) * ((2 : ℕ) : ℝ) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩,
        1 * 2 * (1 + 2) / (1 * (1 + 2) + ((2 : ℕ) : ℝ) ^ 2 * 2 ^ 2)⟩ : Sphere ℂ) =
      ⟨⟨12 / 19, 24 / 19⟩, 6 / 19⟩ := by norm_num
  refine ⟨e1, e2, by norm_num, by norm_num, ?_⟩
  have := ((l14_pappus_chain (a := 1) (b := 2) one_pos two_pos).2 1).2.2.1
  rw [e1] at this
  norm_num at this ⊢
  convert this using 2

/-- **Witness for the uniqueness of the Pappus chain.** For `a = 1`, `b = 2` the explicit chain
satisfies every hypothesis (including `c (n + 2) ≠ c n`, checked by the radii, and the first circle
`(12/7 + 12/7·i, 6/7)` in the upper half plane). -/
theorem l14w_pappus_unique :
    ∃ c : ℕ → Sphere ℂ, c 0 = ⟨((2 * 1 + 2 : ℝ) : ℂ), 2⟩ ∧ (∀ n, 0 < (c n).radius) ∧
      (∀ n, (c n).IsIntTangent ⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩) ∧
      (∀ n, (⟨((1 : ℝ) : ℂ), 1⟩ : Sphere ℂ).IsExtTangent (c n)) ∧
      (∀ n, (c n).IsExtTangent (c (n + 1))) ∧ (∀ n, c (n + 2) ≠ c n) ∧ 0 < (c 1).center.im ∧
      c 1 = ⟨⟨12 / 7, 12 / 7⟩, 6 / 7⟩ := by
  refine ⟨pappusCircle 1 2, pappusCircle_zero one_pos two_pos, pappus_radius_pos one_pos two_pos,
    pappus_tangent_big one_pos two_pos, pappus_tangent_left one_pos two_pos,
    pappus_tangent_succ one_pos two_pos, fun n h => ?_, ?_, ?_⟩
  · have := congrArg Sphere.radius h
    simp only [pappusCircle, famCircle, famDen] at this
    have hd1 : (0 : ℝ) < 1 * (1 + 2) + ((n + 2 : ℕ) : ℝ) ^ 2 * 2 ^ 2 := by positivity
    have hd2 : (0 : ℝ) < 1 * (1 + 2) + ((n : ℕ) : ℝ) ^ 2 * 2 ^ 2 := by positivity
    rw [div_eq_div_iff hd1.ne' hd2.ne'] at this
    push_cast at this
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · simp [pappusCircle, famCircle, famDen]; norm_num
  · simp [pappusCircle, famCircle, famDen]; norm_num

/-- **Witness for the inversion picture.** For `a = 1`, `b = 2` (inversion radius `2√3`) the
point `B = 6` of the big circle is mapped to `2` on the line `re = 2`. -/
theorem l14w_inversion_bigS :
    (6 : ℂ) ∈ ((⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ : Sphere ℂ) : Set ℂ) \ {0} ∧
    inversion (0 : ℂ) (2 * Real.sqrt (1 * (1 + 2))) 6 = 2 := by
  have h6 : (6 : ℂ) ∈ (⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ : Sphere ℂ) :=
    l14h_mem_sphere (by norm_num) (by simp; norm_num)
  refine ⟨⟨h6, by norm_num⟩, ?_⟩
  have h3 : Real.sqrt (1 * (1 + 2)) ^ 2 = 3 := by
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 1 * (1 + 2) by norm_num)]; norm_num
  apply Complex.ext
  · rw [inversion_re]; simp only [Complex.zero_re, Complex.zero_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_pow, h3]; norm_num
  · rw [inversion_im]; simp

/-- **Witness for Bankoff.** For `a = 1`, `b = 2`: the incircle `s₀ = (12/7 + 12/7·i, 6/7)`
touches the circle on `AC` at `T₁ = 18/13 + 12/13·i` and the circle on `CB` at
`T₂ = 12/5 + 6/5·i`; the circle `s = (2 + 2/3·i, 2/3)` passes through `C = 2`, `T₁`, `T₂` (three
distinct points) and its radius `2/3 = ab/(a+b)` is positive. -/
theorem l14w_bankoff :
    let s₀ : Sphere ℂ := ⟨⟨12 / 7, 12 / 7⟩, 6 / 7⟩
    let s : Sphere ℂ := ⟨⟨2, 2 / 3⟩, 2 / 3⟩
    let T₁ : ℂ := ⟨18 / 13, 12 / 13⟩
    let T₂ : ℂ := ⟨12 / 5, 6 / 5⟩
    s₀.IsIntTangent ⟨((1 + 2 : ℝ) : ℂ), 1 + 2⟩ ∧
    (⟨((1 : ℝ) : ℂ), 1⟩ : Sphere ℂ).IsExtTangent s₀ ∧
    (⟨((2 * 1 + 2 : ℝ) : ℂ), 2⟩ : Sphere ℂ).IsExtTangent s₀ ∧ 0 < s₀.center.im ∧
    (⟨((1 : ℝ) : ℂ), 1⟩ : Sphere ℂ).IsExtTangentAt s₀ T₁ ∧
    (⟨((2 * 1 + 2 : ℝ) : ℂ), 2⟩ : Sphere ℂ).IsExtTangentAt s₀ T₂ ∧
    ((2 * 1 : ℝ) : ℂ) ∈ s ∧ T₁ ∈ s ∧ T₂ ∈ s ∧ T₁ ≠ T₂ ∧ T₁ ≠ 2 ∧ T₂ ≠ 2 ∧
    s.radius = 1 * 2 / (1 + 2) ∧ 0 < s.radius := by
  intro s₀ s T₁ T₂
  have t1 : (⟨((1 : ℝ) : ℂ), 1⟩ : Sphere ℂ).IsExtTangentAt s₀ T₁ :=
    ⟨l14h_mem_sphere (by norm_num) (by norm_num [T₁]),
      l14h_mem_sphere (by norm_num) (by norm_num [T₁, s₀]),
      l14h_wbtw (7 / 13) (by norm_num) (by norm_num)
        (by apply Complex.ext <;> norm_num [T₁, s₀])⟩
  have t2 : (⟨((2 * 1 + 2 : ℝ) : ℂ), 2⟩ : Sphere ℂ).IsExtTangentAt s₀ T₂ :=
    ⟨l14h_mem_sphere (by norm_num) (by norm_num [T₂]),
      l14h_mem_sphere (by norm_num) (by norm_num [T₂, s₀]),
      l14h_wbtw (7 / 10) (by norm_num) (by norm_num)
        (by apply Complex.ext <;> norm_num [T₂, s₀])⟩
  refine ⟨?_, t1.isExtTangent, t2.isExtTangent, by norm_num [s₀], t1, t2,
    l14h_mem_sphere (by norm_num) (by norm_num [s]),
    l14h_mem_sphere (by norm_num) (by norm_num [s, T₁]),
    l14h_mem_sphere (by norm_num) (by norm_num [s, T₂]), ?_, ?_, ?_, by norm_num [s],
    by norm_num [s]⟩
  · rw [isIntTangent_iff]; norm_num [s₀]
  · intro h; have := congrArg Complex.re h; norm_num [T₁, T₂] at this
  · intro h; have := congrArg Complex.im h; norm_num [T₁] at this
  · intro h; have := congrArg Complex.im h; norm_num [T₂] at this

/-- The six chain circles of radius `1` about `2·e^{ikπ/3}` (concentric Steiner chain between
the circles `(0, 1)` and `(0, 3)`). -/
theorem l14h_zmod6 (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  revert i; decide

/-- The six chain circles of radius `1` about `2·e^{ikπ/3}` (concentric Steiner chain between
the circles `(0, 1)` and `(0, 3)`). -/
noncomputable def l14wChain (i : ZMod 6) : Sphere ℂ :=
  ⟨if i = 0 then ⟨2, 0⟩ else if i = 1 then ⟨1, Real.sqrt 3⟩ else if i = 2 then ⟨-1, Real.sqrt 3⟩
    else if i = 3 then ⟨-2, 0⟩ else if i = 4 then ⟨-1, -Real.sqrt 3⟩ else ⟨1, -Real.sqrt 3⟩, 1⟩

/-- **Witness for Steiner's porism.** `S₁ = (0, 1)` inside `S₂ = (0, 3)` carries the closed chain
of six unit circles `l14wChain`; the circle `s₀ = (√3 + i, 1)`, tangent to both and different
from every chain circle, satisfies the remaining hypotheses. (Honest note: the witness is the
concentric configuration; the hypotheses of the porism do not force non-concentric circles.) -/
theorem l14w_steiner_porism :
    let S₁ : Sphere ℂ := ⟨0, 1⟩
    let S₂ : Sphere ℂ := ⟨0, 3⟩
    let s₀ : Sphere ℂ := ⟨⟨Real.sqrt 3, 1⟩, 1⟩
    0 < S₁.radius ∧ dist S₁.center S₂.center < S₂.radius - S₁.radius ∧
    (∀ i, 0 < (l14wChain i).radius ∧ S₁.IsExtTangent (l14wChain i) ∧
      (l14wChain i).IsIntTangent S₂ ∧ (l14wChain i).IsExtTangent (l14wChain (i + 1))) ∧
    0 < s₀.radius ∧ S₁.IsExtTangent s₀ ∧ s₀.IsIntTangent S₂ ∧ ∀ i, l14wChain i ≠ s₀ := by
  intro S₁ S₂ s₀
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  refine ⟨by norm_num [S₁], by norm_num [S₁, S₂], ?_, by norm_num [s₀], ?_, ?_, ?_⟩
  · intro i
    refine ⟨by simp [l14wChain], ?_, ?_, ?_⟩
    · rw [isExtTangent_iff]
      refine ⟨?_, by norm_num [S₁], by simp [l14wChain]⟩
      rcases l14h_zmod6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [l14wChain, S₁] <;> nlinarith
    · rw [isIntTangent_iff]
      refine ⟨?_, by simp [l14wChain], by norm_num [l14wChain, S₂]⟩
      rcases l14h_zmod6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [l14wChain, S₂] <;> nlinarith
    · rw [isExtTangent_iff]
      refine ⟨?_, by simp [l14wChain], by simp [l14wChain]⟩
      rcases l14h_zmod6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [l14wChain] <;> nlinarith
  · rw [isExtTangent_iff]; refine ⟨?_, by norm_num [S₁], by norm_num [s₀]⟩
    simp [S₁, s₀]; nlinarith
  · rw [isIntTangent_iff]; refine ⟨?_, by norm_num [s₀], by norm_num [s₀, S₂]⟩
    simp [S₂, s₀]; nlinarith
  · intro i h
    have hc := congrArg (fun s : Sphere ℂ => s.center) h
    rcases l14h_zmod6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [l14wChain, s₀, Complex.ext_iff] at hc <;> nlinarith

end Witnesses

end Arbelos
