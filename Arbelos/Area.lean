import Arbelos.Inversion

/-!
# I2.2 The area of the arbelos
-/

open EuclideanGeometry Complex MeasureTheory

namespace Arbelos

/-- The (closed-boundary) arbelos: points of the upper half plane inside the big semicircle and
outside both small ones. -/
def arbelosRegion (a b : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ dist z (bigS a b).center ≤ (bigS a b).radius ∧
    (leftS a b).radius ≤ dist z (leftS a b).center ∧
    (rightS a b).radius ≤ dist z (rightS a b).center}

/-- The open upper half plane. -/
def upperHalf : Set ℂ := {z | 0 < z.im}

theorem measurableSet_upperHalf : MeasurableSet upperHalf :=
  measurableSet_lt measurable_const Complex.measurable_im

/-- The real axis is a null set. -/
theorem volume_realAxis : volume {z : ℂ | z.im = 0} = 0 := by
  have h : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imLm : Set ℂ) := by
    ext z; simp
  rw [h]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  have : Complex.I ∈ LinearMap.ker Complex.imLm := htop ▸ Submodule.mem_top
  simp at this

/-- A measurable set symmetric under conjugation has half its area in the upper half plane. -/
theorem two_mul_volume_inter_upperHalf {S : Set ℂ} (hS : MeasurableSet S)
    (hsym : ∀ z, z ∈ S ↔ (starRingEnd ℂ) z ∈ S) :
    2 * volume (S ∩ upperHalf) = volume S := by
  have hL : volume (S ∩ {z : ℂ | z.im < 0}) = volume (S ∩ upperHalf) := by
    have hpre : Complex.conjLIE ⁻¹' (S ∩ upperHalf) = S ∩ {z : ℂ | z.im < 0} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, Complex.conjLIE_apply, upperHalf,
        Set.mem_setOf_eq, Complex.conj_im, neg_pos]
      rw [← hsym]
    rw [← hpre]
    exact (LinearIsometryEquiv.measurePreserving Complex.conjLIE).measure_preimage
      (hS.inter measurableSet_upperHalf).nullMeasurableSet
  apply le_antisymm
  · rw [two_mul]
    nth_rewrite 2 [← hL]
    rw [← measure_union _ ((hS.inter (measurableSet_lt Complex.measurable_im measurable_const)))]
    · exact measure_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
    · rw [Set.disjoint_left]
      rintro z ⟨-, h1⟩ ⟨-, h2⟩
      simp only [upperHalf, Set.mem_setOf_eq] at h1 h2
      linarith
  · calc volume S ≤ volume ((S ∩ upperHalf) ∪ (S ∩ {z : ℂ | z.im < 0}) ∪ {z : ℂ | z.im = 0}) := by
          apply measure_mono
          intro z hz
          rcases lt_trichotomy z.im 0 with h | h | h
          · exact Or.inl (Or.inr ⟨hz, h⟩)
          · exact Or.inr h
          · exact Or.inl (Or.inl ⟨hz, h⟩)
      _ ≤ volume (S ∩ upperHalf) + volume (S ∩ {z : ℂ | z.im < 0}) + volume {z : ℂ | z.im = 0} :=
          (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ = 2 * volume (S ∩ upperHalf) := by rw [volume_realAxis, add_zero, hL, two_mul]

theorem ofReal_disc_area (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal r ^ 2 * NNReal.pi = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), mul_comm]

theorem volume_half_of_two_mul {x : ENNReal} {A : ℝ} (h : 2 * x = ENNReal.ofReal A) :
    x = ENNReal.ofReal (A / 2) := by
  have h2 : (2 : ENNReal) * ENNReal.ofReal (A / 2) = ENNReal.ofReal A := by
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [← h2] at h
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h

theorem conj_mem_ball_iff (c : ℝ) (r : ℝ) (z : ℂ) :
    z ∈ Metric.ball (c : ℂ) r ↔ (starRingEnd ℂ) z ∈ Metric.ball (c : ℂ) r := by
  simp only [Metric.mem_ball]
  rw [← Complex.conj_ofReal c, Complex.dist_conj_conj, Complex.conj_ofReal]

theorem conj_mem_closedBall_iff (c : ℝ) (r : ℝ) (z : ℂ) :
    z ∈ Metric.closedBall (c : ℂ) r ↔ (starRingEnd ℂ) z ∈ Metric.closedBall (c : ℂ) r := by
  simp only [Metric.mem_closedBall]
  rw [← Complex.conj_ofReal c, Complex.dist_conj_conj, Complex.conj_ofReal]

/-- Area of a closed upper half disc centred on the real axis. -/
theorem volume_closedHalfDisc (c r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (c : ℂ) r ∩ upperHalf) = ENNReal.ofReal (Real.pi * r ^ 2 / 2) := by
  apply volume_half_of_two_mul
  rw [two_mul_volume_inter_upperHalf Metric.isClosed_closedBall.measurableSet
    (conj_mem_closedBall_iff c r), Complex.volume_closedBall, ofReal_disc_area r hr]

/-- Area of an open upper half disc centred on the real axis. -/
theorem volume_openHalfDisc (c r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball (c : ℂ) r ∩ upperHalf) = ENNReal.ofReal (Real.pi * r ^ 2 / 2) := by
  apply volume_half_of_two_mul
  rw [two_mul_volume_inter_upperHalf Metric.isOpen_ball.measurableSet
    (conj_mem_ball_iff c r), Complex.volume_ball, ofReal_disc_area r hr]

theorem dist_ofReal_ofReal (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The arbelos as a difference of half discs. -/
theorem arbelosRegion_eq (a b : ℝ) : arbelosRegion a b =
    (Metric.closedBall ((a + b : ℝ) : ℂ) (a + b) ∩ upperHalf) \
      ((Metric.ball ((a : ℝ) : ℂ) a ∩ upperHalf) ∪ (Metric.ball ((2 * a + b : ℝ) : ℂ) b ∩ upperHalf)) := by
  ext z
  simp only [arbelosRegion, bigS, leftS, rightS, upperHalf, Set.mem_setOf_eq, Set.mem_diff,
    Set.mem_inter_iff, Set.mem_union, Metric.mem_closedBall, Metric.mem_ball, not_or, not_and,
    not_lt]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨h1, h0⟩, fun h ↦ absurd h2 (not_le.2 h), fun h ↦ absurd h3 (not_le.2 h)⟩
  · rintro ⟨⟨h1, h0⟩, h2, h3⟩
    refine ⟨h0, h1, ?_, ?_⟩
    · by_contra h; exact absurd (h2 (not_le.1 h)) (not_le.2 h0)
    · by_contra h; exact absurd (h3 (not_le.1 h)) (not_le.2 h0)

/-- **Archimedes.** The area of the arbelos equals the area of the circle on the diameter `CD`,
where `D` is the point where the perpendicular at `C` meets the big semicircle. -/
theorem arbelos_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (D : ℂ) (hD : D ∈ bigS a b)
    (hDperp : D ∈ perpC a b) :
    volume (arbelosRegion a b) = volume (Metric.ball (midpoint ℝ (ptC a b) D) (dist (ptC a b) D / 2)) := by
  have hR : 0 < a + b := by linarith
  -- the area of the arbelos
  have hsub : (Metric.ball ((a : ℝ) : ℂ) a ∩ upperHalf) ∪
      (Metric.ball ((2 * a + b : ℝ) : ℂ) b ∩ upperHalf) ⊆
      Metric.closedBall ((a + b : ℝ) : ℂ) (a + b) ∩ upperHalf := by
    rintro z (⟨hz, hu⟩ | ⟨hz, hu⟩) <;> refine ⟨?_, hu⟩ <;> rw [Metric.mem_closedBall] <;>
      rw [Metric.mem_ball] at hz
    · have := dist_triangle z ((a : ℝ) : ℂ) ((a + b : ℝ) : ℂ)
      rw [dist_ofReal_ofReal, show a - (a + b) = -b by ring, abs_neg, abs_of_pos hb] at this
      linarith
    · have := dist_triangle z ((2 * a + b : ℝ) : ℂ) ((a + b : ℝ) : ℂ)
      rw [dist_ofReal_ofReal, show 2 * a + b - (a + b) = a by ring, abs_of_pos ha] at this
      linarith
  have hdisj : Disjoint (Metric.ball ((a : ℝ) : ℂ) a ∩ upperHalf)
      (Metric.ball ((2 * a + b : ℝ) : ℂ) b ∩ upperHalf) := by
    rw [Set.disjoint_left]
    rintro z ⟨h1, -⟩ ⟨h2, -⟩
    rw [Metric.mem_ball] at h1 h2
    have := dist_triangle_left ((a : ℝ) : ℂ) ((2 * a + b : ℝ) : ℂ) z
    rw [dist_ofReal_ofReal, show a - (2 * a + b) = -(a + b) by ring, abs_neg,
      abs_of_pos hR] at this
    linarith
  have hm2 : MeasurableSet (Metric.ball ((2 * a + b : ℝ) : ℂ) b ∩ upperHalf) :=
    Metric.isOpen_ball.measurableSet.inter measurableSet_upperHalf
  have hm : MeasurableSet ((Metric.ball ((a : ℝ) : ℂ) a ∩ upperHalf) ∪
      (Metric.ball ((2 * a + b : ℝ) : ℂ) b ∩ upperHalf)) :=
    (Metric.isOpen_ball.measurableSet.inter measurableSet_upperHalf).union hm2
  have hA : volume (arbelosRegion a b) = ENNReal.ofReal (Real.pi * (a * b)) := by
    rw [arbelosRegion_eq, measure_sdiff hsub hm.nullMeasurableSet, measure_union hdisj hm2,
      volume_closedHalfDisc _ _ hR.le, volume_openHalfDisc _ _ ha.le, volume_openHalfDisc _ _ hb.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_sub _ (by positivity)]
    · congr 1; ring
    · rw [measure_union hdisj hm2, volume_openHalfDisc _ _ ha.le, volume_openHalfDisc _ _ hb.le]
      simp
  -- the circle on `CD`
  rw [perpC, mem_vline_iff] at hDperp
  have hD' : (D.re - (a + b)) ^ 2 + D.im ^ 2 = (a + b) ^ 2 := by
    have := (mem_sphere_iff_sq hR.le).1 hD
    simpa [bigS] using this
  have hCD : dist (ptC a b) D / 2 = Real.sqrt (a * b) := by
    rw [ptC, Complex.dist_eq_re_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, hDperp, sub_self, zero_sub, neg_sq]
    rw [hDperp] at hD'
    have : D.im ^ 2 = 4 * (a * b) := by linarith
    rw [zero_pow two_ne_zero, zero_add, this, show 4 * (a * b) = 2 ^ 2 * (a * b) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  rw [hA, hCD, Complex.volume_ball, ofReal_disc_area _ (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

end Arbelos
