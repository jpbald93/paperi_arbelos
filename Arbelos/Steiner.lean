import Arbelos.Inversion

/-!
# I2.5 Steiner's porism
-/

open EuclideanGeometry Complex

namespace Arbelos

/-- A closed Steiner chain of `n` circles between the inner circle `S₁` and the outer circle `S₂`
(indices in `ZMod n`, so the chain closes up). -/
def IsSteinerChain (S₁ S₂ : Sphere ℂ) (n : ℕ) (c : ZMod n → Sphere ℂ) : Prop :=
  ∀ i, 0 < (c i).radius ∧ S₁.IsExtTangent (c i) ∧ (c i).IsIntTangent S₂ ∧
    (c i).IsExtTangent (c (i + 1))

/-- Rotation of a circle about `O` by the complex factor `w` (with `‖w‖ = 1`). -/
noncomputable def rotSphere (O w : ℂ) (s : Sphere ℂ) : Sphere ℂ :=
  ⟨O + w * (s.center - O), s.radius⟩

theorem dist_rot_rot {O w : ℂ} (hw : ‖w‖ = 1) (x y : ℂ) :
    dist (O + w * (x - O)) (O + w * (y - O)) = dist x y := by
  rw [Complex.dist_eq, Complex.dist_eq, show O + w * (x - O) - (O + w * (y - O)) = w * (x - y) by
    ring, norm_mul, hw, one_mul]

theorem dist_center_rot {O w : ℂ} (hw : ‖w‖ = 1) (x : ℂ) :
    dist O (O + w * (x - O)) = dist O x := by
  rw [Complex.dist_eq, Complex.dist_eq, show O - (O + w * (x - O)) = w * (O - x) by ring,
    norm_mul, hw, one_mul]

/-- For concentric `S₁`, `S₂`, a circle tangent to both has radius `(r₂ - r₁)/2` and its centre is
at distance `(r₁ + r₂)/2` from the common centre. -/
theorem concentric_tangent {S₁ S₂ s : Sphere ℂ} (hc : S₁.center = S₂.center)
    (h₁ : S₁.IsExtTangent s) (h₂ : s.IsIntTangent S₂) :
    s.radius = (S₂.radius - S₁.radius) / 2 ∧
      dist S₁.center s.center = (S₁.radius + S₂.radius) / 2 := by
  have e1 := h₁.dist_center
  have e2 := h₂.dist_center
  rw [dist_comm, ← hc] at e2
  constructor <;> linarith

/-- **Steiner's porism, concentric case.** -/
theorem steiner_concentric (S₁ S₂ : Sphere ℂ) (hc : S₁.center = S₂.center)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (h₁ : S₁.IsExtTangent s₀) (h₂ : s₀.IsIntTangent S₂) :
    ∃ d : ZMod n → Sphere ℂ, IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  obtain ⟨hr0, hd0⟩ := concentric_tangent hc h₁ h₂
  obtain ⟨hr, h1, h2, -⟩ := hchain 0
  obtain ⟨hrc, hdc⟩ := concentric_tangent hc h1 h2
  have hS₁ : 0 ≤ S₁.radius := ((Sphere.isExtTangent_iff_dist_center).1 h₁).2.1
  have hm : 0 < (S₁.radius + S₂.radius) / 2 := by linarith
  set O := S₁.center
  have hne : (c 0).center - O ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hdc; linarith
  set w := (s₀.center - O) / ((c 0).center - O) with hwdef
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_div, ← Complex.dist_eq, ← Complex.dist_eq, dist_comm, hd0, dist_comm, hdc,
      div_self hm.ne']
  have rot_ext : ∀ s : Sphere ℂ, S₁.IsExtTangent s → S₁.IsExtTangent (rotSphere O w s) := by
    intro s hs
    rw [Sphere.isExtTangent_iff_dist_center] at hs ⊢
    simp only [rotSphere]
    rw [dist_center_rot hw]; exact hs
  have rot_int : ∀ s : Sphere ℂ, s.IsIntTangent S₂ → (rotSphere O w s).IsIntTangent S₂ := by
    intro s hs
    rw [Sphere.isIntTangent_iff_dist_center] at hs ⊢
    simp only [rotSphere]
    rw [← hc, dist_comm, dist_center_rot hw, dist_comm, hc]; exact hs
  refine ⟨fun i ↦ rotSphere O w (c i), fun i ↦ ?_, ?_⟩
  · obtain ⟨hp, ha, hb, hn⟩ := hchain i
    refine ⟨hp, rot_ext _ ha, rot_int _ hb, ?_⟩
    rw [Sphere.isExtTangent_iff_dist_center] at hn ⊢
    simp only [rotSphere]
    rw [dist_rot_rot hw]; exact hn
  · simp only [rotSphere]
    refine Sphere.ext ?_ (by rw [hrc, hr0])
    rw [hwdef, div_mul_cancel₀ _ hne]; ring

/-- The power `‖centre - c‖² - radius²` of the point `c` with respect to the circle `s`. -/
noncomputable def powC (c : ℂ) (s : Sphere ℂ) : ℝ := ‖s.center - c‖ ^ 2 - s.radius ^ 2

/-- **Reduction lemma.** Two non-concentric circles, one strictly inside the other, are sent by an
inversion (of radius `1`, centred at a point outside both circles) to two concentric circles. -/
theorem exists_inversion_concentric (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hne : S₁.center ≠ S₂.center) (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius) :
    ∃ c : ℂ, 0 < powC c S₁ ∧ 0 < powC c S₂ ∧
      (invSphere c 1 S₁).center = (invSphere c 1 S₂).center := by
  set O₁ := S₁.center
  set O₂ := S₂.center
  set r₁ := S₁.radius
  set r₂ := S₂.radius
  set p := (O₂ - O₁).re
  set q := (O₂ - O₁).im
  set D := p ^ 2 + q ^ 2 with hDdef
  have hd : dist O₁ O₂ ^ 2 = D := by
    rw [dist_comm, Complex.dist_eq, norm_sq_re_im]
  have hd0 : 0 < dist O₁ O₂ := dist_pos.2 hne
  have hDpos : 0 < D := by rw [← hd]; positivity
  set d₀ := dist O₁ O₂
  -- the centre of inversion is `O₁ + λ (O₂ - O₁)`, `λ` a root of `Dλ² - (D + r₁² - r₂²)λ + r₁²`
  have hr₂ : r₁ + d₀ < r₂ := by linarith
  have hB : D + r₁ ^ 2 - r₂ ^ 2 < 0 := by rw [← hd]; nlinarith
  have hdisc : 0 < discrim D (-(D + r₁ ^ 2 - r₂ ^ 2)) (r₁ ^ 2) := by
    rw [discrim]
    have h1 : 2 * d₀ * r₁ < r₂ ^ 2 - r₁ ^ 2 - D := by rw [← hd]; nlinarith
    have h2 := pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    rw [mul_pow, mul_pow, hd] at h2
    nlinarith
  set sq := Real.sqrt (discrim D (-(D + r₁ ^ 2 - r₂ ^ 2)) (r₁ ^ 2))
  have hsq : discrim D (-(D + r₁ ^ 2 - r₂ ^ 2)) (r₁ ^ 2) = sq * sq :=
    (Real.mul_self_sqrt hdisc.le).symm
  have hsqpos : 0 < sq := Real.sqrt_pos.2 hdisc
  set lam := (-(-(D + r₁ ^ 2 - r₂ ^ 2)) - sq) / (2 * D)
  have hq : D * (lam * lam) + -(D + r₁ ^ 2 - r₂ ^ 2) * lam + r₁ ^ 2 = 0 :=
    (quadratic_eq_zero_iff hDpos.ne' hsq lam).2 (Or.inr rfl)
  have hl : 2 * D * lam = (D + r₁ ^ 2 - r₂ ^ 2) - sq := by
    simp only [lam]; field_simp
  rw [discrim] at hsq
  clear_value lam sq
  have hlam : lam < 0 := by nlinarith
  set c := O₁ + (lam : ℂ) * (O₂ - O₁)
  have n1 : ‖O₁ - c‖ ^ 2 = lam ^ 2 * D := by
    rw [norm_sq_re_im]; simp [c, p, q, D]; ring
  have n2 : ‖O₂ - c‖ ^ 2 = (1 - lam) ^ 2 * D := by
    rw [norm_sq_re_im]; simp [c, p, q, D]; ring
  set E₁ := lam ^ 2 * D - r₁ ^ 2
  set E₂ := (1 - lam) ^ 2 * D - r₂ ^ 2
  have key : -lam * E₂ = (1 - lam) * E₁ := by linear_combination hq
  have hE₁v : 2 * D * (E₁ + lam * sq) = 0 := by
    linear_combination 2 * D * hq + ((D + r₁ ^ 2 - r₂ ^ 2) + sq) * hl + hsq
  have hE₁ : 0 < E₁ := by
    have : E₁ + lam * sq = 0 := (mul_eq_zero.1 hE₁v).resolve_left (by positivity)
    nlinarith
  have hE₂ : 0 < E₂ := by
    have h : 0 < -lam * E₂ := by rw [key]; exact mul_pos (by linarith) hE₁
    exact (pos_iff_pos_of_mul_pos h).1 (by linarith)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [powC, n1]; exact hE₁
  · rw [powC, n2]; exact hE₂
  · simp only [invSphere]
    rw [n1, n2]
    have hc1 : O₁ - c = -(lam : ℂ) * (O₂ - O₁) := by simp [c]
    have hc2 : O₂ - c = ((1 - lam : ℝ) : ℂ) * (O₂ - O₁) := by simp [c]; ring
    rw [hc1, hc2, ← mul_assoc, ← mul_assoc]
    congr 2
    rw [show -(lam : ℂ) = ((-lam : ℝ) : ℂ) by simp, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    show 1 ^ 2 / E₁ * -lam = 1 ^ 2 / E₂ * (1 - lam)
    field_simp
    linear_combination key

/-! ### Inversion and tangency -/

theorem dist_sq_sub (z w c : ℂ) :
    dist z w ^ 2 = ((z - c).re - (w - c).re) ^ 2 + ((z - c).im - (w - c).im) ^ 2 := by
  rw [dist_sq_re_im]; simp only [Complex.sub_re, Complex.sub_im]; ring

theorem powC_eq (c : ℂ) (s : Sphere ℂ) :
    powC c s = (s.center - c).re ^ 2 + (s.center - c).im ^ 2 - s.radius ^ 2 := by
  rw [powC, norm_sq_re_im]

theorem invSphere_center_sub (c : ℂ) (s : Sphere ℂ) :
    (invSphere c 1 s).center - c = ((1 / powC c s : ℝ) : ℂ) * (s.center - c) := by
  simp [invSphere, powC]

theorem invSphere_radius {c : ℂ} {s : Sphere ℂ} (hs : 0 < powC c s) :
    (invSphere c 1 s).radius = s.radius / powC c s := by
  have : |‖s.center - c‖ ^ 2 - s.radius ^ 2| = powC c s := abs_of_pos hs
  simp only [invSphere, this, one_pow, one_mul]

theorem invSphere_sub_re (c : ℂ) (s : Sphere ℂ) :
    ((invSphere c 1 s).center - c).re = (s.center - c).re / powC c s := by
  rw [invSphere_center_sub]; simp; ring

theorem invSphere_sub_im (c : ℂ) (s : Sphere ℂ) :
    ((invSphere c 1 s).center - c).im = (s.center - c).im / powC c s := by
  rw [invSphere_center_sub]; simp; ring

theorem powC_invSphere {c : ℂ} {s : Sphere ℂ} (hs : 0 < powC c s) :
    powC c (invSphere c 1 s) = 1 / powC c s := by
  rw [powC_eq, invSphere_sub_re, invSphere_sub_im, invSphere_radius hs]
  have h := powC_eq c s
  have hs' := hs.ne'
  rw [h] at hs' ⊢
  field_simp

theorem invSphere_invSphere {c : ℂ} {s : Sphere ℂ} (hs : 0 < powC c s) :
    invSphere c 1 (invSphere c 1 s) = s := by
  have hE := powC_invSphere hs
  have hE' : 0 < powC c (invSphere c 1 s) := by rw [hE]; positivity
  refine Sphere.ext ?_ ?_
  · have h1 := invSphere_center_sub c (invSphere c 1 s)
    rw [hE, invSphere_center_sub c s, sub_eq_iff_eq_add] at h1
    rw [h1]
    have : (powC c s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    ring
  · rw [invSphere_radius hE', invSphere_radius hs, hE]
    field_simp

theorem ext_alg (x1 x2 y1 y2 rs rt : ℝ) (hs : x1 ^ 2 + x2 ^ 2 - rs ^ 2 ≠ 0)
    (ht : y1 ^ 2 + y2 ^ 2 - rt ^ 2 ≠ 0) :
    (x1 / (x1 ^ 2 + x2 ^ 2 - rs ^ 2) - y1 / (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) ^ 2 +
      (x2 / (x1 ^ 2 + x2 ^ 2 - rs ^ 2) - y2 / (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) ^ 2 -
      (rs / (x1 ^ 2 + x2 ^ 2 - rs ^ 2) + rt / (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) ^ 2 =
      ((x1 - y1) ^ 2 + (x2 - y2) ^ 2 - (rs + rt) ^ 2) /
        ((x1 ^ 2 + x2 ^ 2 - rs ^ 2) * (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) := by
  field_simp; ring

theorem int_alg (x1 x2 y1 y2 rs rt : ℝ) (hs : x1 ^ 2 + x2 ^ 2 - rs ^ 2 ≠ 0)
    (ht : y1 ^ 2 + y2 ^ 2 - rt ^ 2 ≠ 0) :
    (x1 / (x1 ^ 2 + x2 ^ 2 - rs ^ 2) - y1 / (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) ^ 2 +
      (x2 / (x1 ^ 2 + x2 ^ 2 - rs ^ 2) - y2 / (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) ^ 2 -
      (rt / (y1 ^ 2 + y2 ^ 2 - rt ^ 2) - rs / (x1 ^ 2 + x2 ^ 2 - rs ^ 2)) ^ 2 =
      ((x1 - y1) ^ 2 + (x2 - y2) ^ 2 - (rt - rs) ^ 2) /
        ((x1 ^ 2 + x2 ^ 2 - rs ^ 2) * (y1 ^ 2 + y2 ^ 2 - rt ^ 2)) := by
  field_simp; ring

/-- Inversion in a circle of positive power with respect to both circles preserves external
tangency. -/
theorem invSphere_isExtTangent {c : ℂ} {s t : Sphere ℂ} (hs : 0 < powC c s) (ht : 0 < powC c t)
    (h : s.IsExtTangent t) : (invSphere c 1 s).IsExtTangent (invSphere c 1 t) := by
  rw [Sphere.isExtTangent_iff_dist_center] at h ⊢
  obtain ⟨hd, h1, h2⟩ := h
  have hsq : dist s.center t.center ^ 2 = (s.radius + t.radius) ^ 2 := by rw [hd]
  rw [invSphere_radius hs, invSphere_radius ht]
  refine ⟨(sq_eq_sq₀ dist_nonneg (by positivity)).1 ?_, div_nonneg h1 hs.le,
    div_nonneg h2 ht.le⟩
  rw [dist_sq_sub _ _ c] at hsq ⊢
  rw [invSphere_sub_re, invSphere_sub_re, invSphere_sub_im, invSphere_sub_im]
  have hs' := hs.ne'; have ht' := ht.ne'
  rw [powC_eq] at hs' ht' ⊢
  rw [powC_eq c t]
  have := ext_alg _ _ _ _ _ _ hs' ht'
  linear_combination this + (1 / (((s.center - c).re ^ 2 + (s.center - c).im ^ 2 - s.radius ^ 2) *
    ((t.center - c).re ^ 2 + (t.center - c).im ^ 2 - t.radius ^ 2))) * hsq

/-- Inversion in a circle of positive power with respect to both circles preserves internal
tangency. -/
theorem invSphere_isIntTangent {c : ℂ} {s t : Sphere ℂ} (hs : 0 < powC c s) (ht : 0 < powC c t)
    (h : s.IsIntTangent t) : (invSphere c 1 s).IsIntTangent (invSphere c 1 t) := by
  rw [Sphere.isIntTangent_iff_dist_center] at h ⊢
  obtain ⟨hd, h1, h2⟩ := h
  have hrle : s.radius ≤ t.radius := by linarith [dist_nonneg (x := s.center) (y := t.center)]
  have hsq : dist s.center t.center ^ 2 = (t.radius - s.radius) ^ 2 := by rw [hd]
  rw [dist_sq_sub _ _ c] at hsq
  have hle : s.radius / powC c s ≤ t.radius / powC c t := by
    rw [div_le_div_iff₀ hs ht, powC_eq, powC_eq]
    rcases (sub_nonneg.2 hrle).lt_or_eq with hpos | heq
    · have key : (t.radius - s.radius) * (t.radius * ((s.center - c).re ^ 2 +
          (s.center - c).im ^ 2 - s.radius ^ 2) - s.radius * ((t.center - c).re ^ 2 +
          (t.center - c).im ^ 2 - t.radius ^ 2)) =
          ((t.radius - s.radius) * (t.center - c).re + t.radius * ((s.center - c).re -
            (t.center - c).re)) ^ 2 +
          ((t.radius - s.radius) * (t.center - c).im + t.radius * ((s.center - c).im -
            (t.center - c).im)) ^ 2 := by
        linear_combination (-(s.radius * t.radius)) * hsq
      nlinarith [sq_nonneg ((t.radius - s.radius) * (t.center - c).re + t.radius *
        ((s.center - c).re - (t.center - c).re)), sq_nonneg ((t.radius - s.radius) *
        (t.center - c).im + t.radius * ((s.center - c).im - (t.center - c).im))]
    · rw [← heq, zero_pow two_ne_zero] at hsq
      have e1 : (s.center - c).re = (t.center - c).re := by
        nlinarith [sq_nonneg ((s.center - c).re - (t.center - c).re),
          sq_nonneg ((s.center - c).im - (t.center - c).im)]
      have e2 : (s.center - c).im = (t.center - c).im := by
        nlinarith [sq_nonneg ((s.center - c).re - (t.center - c).re),
          sq_nonneg ((s.center - c).im - (t.center - c).im)]
      have e3 : s.radius = t.radius := by linarith
      rw [e1, e2, e3]
  rw [invSphere_radius hs, invSphere_radius ht]
  refine ⟨(sq_eq_sq₀ dist_nonneg (by linarith)).1 ?_, div_nonneg h1 hs.le,
    div_nonneg h2 ht.le⟩
  rw [dist_sq_sub _ _ c]
  rw [invSphere_sub_re, invSphere_sub_re, invSphere_sub_im, invSphere_sub_im]
  have hs' := hs.ne'; have ht' := ht.ne'
  rw [powC_eq] at hs' ht' ⊢
  rw [powC_eq c t]
  have := int_alg _ _ _ _ _ _ hs' ht'
  linear_combination this + (1 / (((s.center - c).re ^ 2 + (s.center - c).im ^ 2 - s.radius ^ 2) *
    ((t.center - c).re ^ 2 + (t.center - c).im ^ 2 - t.radius ^ 2))) * hsq

/-- A circle inside a circle `t` of positive power has positive power. -/
theorem powC_pos_of_isIntTangent {c : ℂ} {s t : Sphere ℂ} (ht : 0 < powC c t)
    (h : s.IsIntTangent t) : 0 < powC c s := by
  rw [Sphere.isIntTangent_iff_dist_center] at h
  obtain ⟨hd, h1, h2⟩ := h
  rw [powC] at ht ⊢
  have hN : t.radius < ‖t.center - c‖ := by
    by_contra hle
    rw [not_lt] at hle
    have := pow_le_pow_left₀ (norm_nonneg _) hle 2
    linarith
  have htri : ‖t.center - c‖ ≤ dist t.center s.center + ‖s.center - c‖ := by
    rw [Complex.dist_eq]
    have := norm_add_le (t.center - s.center) (s.center - c)
    rwa [sub_add_sub_cancel] at this
  rw [dist_comm, hd] at htri
  have hlt : s.radius < ‖s.center - c‖ := by linarith
  nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖s.center - c‖ + s.radius)]

/-- **Steiner's porism.** If a closed Steiner chain of `n` circles exists between a circle `S₁` and
a circle `S₂` containing it, then a closed Steiner chain of `n` circles exists starting from any
circle `s₀` tangent to both. -/
theorem steiner_porism (S₁ S₂ : Sphere ℂ) (h₁ : 0 < S₁.radius)
    (hin : dist S₁.center S₂.center < S₂.radius - S₁.radius)
    (n : ℕ) (c : ZMod n → Sphere ℂ) (hchain : IsSteinerChain S₁ S₂ n c)
    (s₀ : Sphere ℂ) (hs₀ : 0 < s₀.radius) (h₁' : S₁.IsExtTangent s₀) (h₂' : s₀.IsIntTangent S₂) :
    ∃ d : ZMod n → Sphere ℂ, IsSteinerChain S₁ S₂ n d ∧ d 0 = s₀ := by
  by_cases hc : S₁.center = S₂.center
  · exact steiner_concentric S₁ S₂ hc n c hchain s₀ h₁' h₂'
  obtain ⟨o, hE₁, hE₂, hcen⟩ := exists_inversion_concentric S₁ S₂ h₁ hc hin
  have hEc : ∀ s : Sphere ℂ, s.IsIntTangent S₂ → 0 < powC o s :=
    fun s hs ↦ powC_pos_of_isIntTangent hE₂ hs
  have hT₁ : 0 < powC o (invSphere o 1 S₁) := by rw [powC_invSphere hE₁]; positivity
  have hT₂ : 0 < powC o (invSphere o 1 S₂) := by rw [powC_invSphere hE₂]; positivity
  have hchain' : IsSteinerChain (invSphere o 1 S₁) (invSphere o 1 S₂) n
      (fun i ↦ invSphere o 1 (c i)) := by
    intro i
    obtain ⟨hp, ha, hb, hn⟩ := hchain i
    have e := hEc _ hb
    have e' := hEc _ (hchain (i + 1)).2.2.1
    refine ⟨?_, invSphere_isExtTangent hE₁ e ha, invSphere_isIntTangent e hE₂ hb,
      invSphere_isExtTangent e e' hn⟩
    show 0 < (invSphere o 1 (c i)).radius
    rw [invSphere_radius e]; positivity
  have hs₀E := hEc _ h₂'
  obtain ⟨d, hd, hd0⟩ := steiner_concentric _ _ hcen n _ hchain' (invSphere o 1 s₀)
    (invSphere_isExtTangent hE₁ hs₀E h₁')
    (invSphere_isIntTangent hs₀E hE₂ h₂')
  have hdE : ∀ i, 0 < powC o (d i) := fun i ↦ powC_pos_of_isIntTangent hT₂ (hd i).2.2.1
  refine ⟨fun i ↦ invSphere o 1 (d i), fun i ↦ ?_, ?_⟩
  · obtain ⟨hp, ha, hb, hn⟩ := hd i
    have e := hdE i
    refine ⟨?_, ?_, ?_, invSphere_isExtTangent e (hdE (i + 1)) hn⟩
    · show 0 < (invSphere o 1 (d i)).radius
      rw [invSphere_radius e]; positivity
    · have := invSphere_isExtTangent hT₁ e ha
      rwa [invSphere_invSphere hE₁] at this
    · have := invSphere_isIntTangent e hT₂ hb
      rwa [invSphere_invSphere hE₂] at this
  · show invSphere o 1 (d 0) = s₀
    rw [hd0]; exact invSphere_invSphere hs₀E

end Arbelos
