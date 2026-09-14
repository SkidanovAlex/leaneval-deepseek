import Mathlib
import Submission.Commons.Analysis.Integral.planar_circle_average_parabolic_neg

set_option maxHeartbeats 1600000

namespace Commons.Analysis.Integral

open MeasureTheory Set Real

/-! ## Data -/

/-- Critical time at which the parabolic radius `c * t ^ (2/3)` equals `rho`. -/
private noncomputable def tcrit (c rho : ℝ) : ℝ := (rho / c) ^ (3 / 2 : ℝ)

/-- The θ-integrand of the Euclidean circle average (l2 norm). -/
private noncomputable def circL2 (c rho : ℝ) (t theta : ℝ) : ℝ :=
  (Real.sqrt ((c * t ^ (2 / 3 : ℝ) - rho * Real.cos theta) ^ 2
      + (rho * Real.sin theta) ^ 2))⁻¹ - (c * t ^ (2 / 3 : ℝ))⁻¹

/-- The θ-integrand of the sup-norm circle average. -/
private noncomputable def circSup (c rho : ℝ) (t theta : ℝ) : ℝ :=
  (max |c * t ^ (2 / 3 : ℝ) - rho * Real.cos theta| |rho * Real.sin theta|)⁻¹
    - (c * t ^ (2 / 3 : ℝ))⁻¹

/-- The sup-norm averaged integrand (exactly the expression appearing in
`planar_circle_average_parabolic_neg`). -/
private noncomputable def Fsup (c rho : ℝ) (t : ℝ) : ℝ :=
  ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
      (‖(c * t ^ (2 / 3 : ℝ)) • ((1, 0) : ℝ × ℝ)
        - rho • (Real.cos theta, Real.sin theta)‖)⁻¹
    - (c * t ^ (2 / 3 : ℝ))⁻¹)

/-- The Euclidean averaged integrand, in explicit `sqrt` form. -/
private noncomputable def Fl2 (c rho : ℝ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi), circL2 c rho t theta

/-- Pointwise lower-bound term. -/
private noncomputable def hbnd (c rho : ℝ) (t : ℝ) : ℝ :=
  rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho))

/-! ## The isometry identity -/

private lemma norm_smul_orthonormal_cos_sin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (a rho theta : ℝ) :
    ‖a • e - rho • (Real.cos theta • e + Real.sin theta • f)‖
      = Real.sqrt ((a - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2) := by
  have hdecomp : a • e - rho • (Real.cos theta • e + Real.sin theta • f)
      = (a - rho * Real.cos theta) • e + (-(rho * Real.sin theta)) • f := by
    rw [smul_add, smul_smul, smul_smul]
    module
  rw [hdecomp]
  have hsq : ‖(a - rho * Real.cos theta) • e + (-(rho * Real.sin theta)) • f‖ ^ 2
      = (a - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, he, hf]
    simp only [Real.norm_eq_abs, abs_neg, mul_one, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hef, mul_zero]
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]

/-! ## Elementary norm algebra -/

private lemma norm_pair (x y : ℝ) : ‖((x, y) : ℝ × ℝ)‖ = max |x| |y| := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]

private lemma norm_sub_smul_pair (a rho theta : ℝ) :
    ‖((a, 0) : ℝ × ℝ) - rho • (Real.cos theta, Real.sin theta)‖
      = max |a - rho * Real.cos theta| |rho * Real.sin theta| := by
  have h : ((a, 0) : ℝ × ℝ) - rho • (Real.cos theta, Real.sin theta)
      = (a - rho * Real.cos theta, -(rho * Real.sin theta)) := by
    ext <;> simp
  rw [h, norm_pair, abs_neg]

private lemma smul_pair (a : ℝ) : a • ((1, 0) : ℝ × ℝ) = (a, 0) := by
  ext <;> simp

/-- `1/√(x²+y²) ≤ 1/max(|x|,|y|)`. -/
private lemma inv_sqrt_le_inv_max (x y : ℝ) :
    (Real.sqrt (x ^ 2 + y ^ 2))⁻¹ ≤ (max |x| |y|)⁻¹ := by
  have hM : 0 ≤ max |x| |y| := le_trans (abs_nonneg y) (le_max_right _ _)
  have hle : max |x| |y| ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
    refine max_le ?_ ?_
    · rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
    · rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  rcases eq_or_lt_of_le hM with h0 | hpos
  · have hx : x = 0 := abs_eq_zero.mp (le_antisymm (h0 ▸ le_max_left |x| |y|) (abs_nonneg x))
    have hy : y = 0 := abs_eq_zero.mp (le_antisymm (h0 ▸ le_max_right |x| |y|) (abs_nonneg y))
    rw [hx, hy]; norm_num
  · have hspos : 0 < Real.sqrt (x ^ 2 + y ^ 2) := lt_of_lt_of_le hpos hle
    exact (inv_le_inv₀ hspos hpos).2 hle

/-- Pointwise comparison of the two θ-integrands. -/
private lemma circL2_le_circSup (c rho t theta : ℝ) :
    circL2 c rho t theta ≤ circSup c rho t theta := by
  rw [circL2, circSup]
  have h := inv_sqrt_le_inv_max (c * t ^ (2 / 3 : ℝ) - rho * Real.cos theta)
    (rho * Real.sin theta)
  linarith [h]

/-- `Fsup` rewritten using `circSup`. -/
private lemma Fsup_eq (c rho t : ℝ) :
    Fsup c rho t
      = (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi), circSup c rho t theta := by
  simp only [Fsup, circSup]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  simp only [smul_pair, norm_sub_smul_pair]

/-! ## Positivity of the denominators -/

private lemma tcrit_rpow (c rho : ℝ) (hc : 0 < c) (hrho : 0 < rho) :
    (tcrit c rho) ^ (2 / 3 : ℝ) = rho / c := by
  rw [tcrit, ← Real.rpow_mul (le_of_lt (div_pos hrho hc))]
  norm_num

private lemma tcrit_pos (c rho : ℝ) (hc : 0 < c) (hrho : 0 < rho) : 0 < tcrit c rho :=
  Real.rpow_pos_of_pos (div_pos hrho hc) _

private lemma mul_rpow_ne_rho {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t)
    (hne : t ≠ tcrit c rho) : c * t ^ (2 / 3 : ℝ) ≠ rho := by
  intro hcon
  have h1 : t ^ (2 / 3 : ℝ) = rho / c := by
    rw [eq_div_iff (ne_of_gt hc)]
    linarith
  have h2 : t ^ (2 / 3 : ℝ) = (tcrit c rho) ^ (2 / 3 : ℝ) := by
    rw [h1, tcrit_rpow c rho hc hrho]
  have h3 : t = tcrit c rho := by
    have hthis := congrArg (fun x : ℝ => x ^ (3 / 2 : ℝ)) h2
    rwa [← Real.rpow_mul (le_of_lt ht), ← Real.rpow_mul (le_of_lt (tcrit_pos c rho hc hrho)),
      show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hthis
  exact hne h3

private lemma sin_eq_zero_cos (theta : ℝ) (h : Real.sin theta = 0) :
    Real.cos theta = 1 ∨ Real.cos theta = -1 := by
  have h1 : Real.cos theta ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq theta
    rw [h] at this
    nlinarith
  exact sq_eq_one_iff.mp h1

private lemma mul_sin_eq_zero {rho : ℝ} (hrho : 0 < rho) {theta : ℝ}
    (h : rho * Real.sin theta = 0) : Real.sin theta = 0 := by
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (ne_of_gt hrho)
  · exact h1

private lemma drift_ne_gen {A rho : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hne : A ≠ rho) (theta : ℝ) :
    A - rho * Real.cos theta ≠ 0 ∨ rho * Real.sin theta ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h1, h2⟩ := h
  have hs : Real.sin theta = 0 := mul_sin_eq_zero hrho h2
  rcases sin_eq_zero_cos theta hs with hc1 | hc1
  · rw [hc1, mul_one] at h1
    exact hne (by linarith)
  · rw [hc1, mul_neg_one] at h1
    nlinarith

private lemma sqsum_pos_gen {A rho : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hne : A ≠ rho) (theta : ℝ) :
    0 < (A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2 := by
  have hne0 : (A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2 ≠ 0 := by
    rcases drift_ne_gen hrho hA hne theta with h | h
    · intro hz
      refine h ?_
      have : (A - rho * Real.cos theta) ^ 2 = 0 := by
        nlinarith [sq_nonneg (A - rho * Real.cos theta), sq_nonneg (rho * Real.sin theta)]
      exact sq_eq_zero_iff.mp this
    · intro hz
      refine h ?_
      have : (rho * Real.sin theta) ^ 2 = 0 := by
        nlinarith [sq_nonneg (A - rho * Real.cos theta), sq_nonneg (rho * Real.sin theta)]
      exact sq_eq_zero_iff.mp this
  exact lt_of_le_of_ne (by positivity) (Ne.symm hne0)

private lemma max_pos_gen {A rho : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hne : A ≠ rho) (theta : ℝ) :
    0 < max |A - rho * Real.cos theta| |rho * Real.sin theta| := by
  have hne0 : max |A - rho * Real.cos theta| |rho * Real.sin theta| ≠ 0 := by
    intro hz
    have h1 : |rho * Real.sin theta| = 0 :=
      le_antisymm (hz ▸ le_max_right _ _) (abs_nonneg _)
    have h2 : |A - rho * Real.cos theta| = 0 :=
      le_antisymm (hz ▸ le_max_left _ _) (abs_nonneg _)
    rcases drift_ne_gen hrho hA hne theta with h | h
    · exact h (abs_eq_zero.mp h2)
    · exact h (abs_eq_zero.mp h1)
  exact lt_of_le_of_ne (le_trans (abs_nonneg _) (le_max_right _ _)) (Ne.symm hne0)

/-! ## Continuity of the θ-integrands away from the critical time -/

private lemma continuous_circL2 {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t)
    (hne : t ≠ tcrit c rho) :
    Continuous fun theta : ℝ => circL2 c rho t theta := by
  have hne' : c * t ^ (2 / 3 : ℝ) ≠ rho := mul_rpow_ne_rho hc hrho ht hne
  have hpos : ∀ theta : ℝ, 0 < Real.sqrt ((c * t ^ (2 / 3 : ℝ) - rho * Real.cos theta) ^ 2
      + (rho * Real.sin theta) ^ 2) := fun theta =>
    Real.sqrt_pos.mpr (sqsum_pos_gen hrho (by positivity) hne' theta)
  simp only [circL2]
  exact (Continuous.inv₀ (by fun_prop) (fun theta => ne_of_gt (hpos theta))).sub
    continuous_const

private lemma continuous_circSup {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t)
    (hne : t ≠ tcrit c rho) :
    Continuous fun theta : ℝ => circSup c rho t theta := by
  have hne' : c * t ^ (2 / 3 : ℝ) ≠ rho := mul_rpow_ne_rho hc hrho ht hne
  have hpos : ∀ theta : ℝ, 0 < max |c * t ^ (2 / 3 : ℝ) - rho * Real.cos theta|
      |rho * Real.sin theta| := fun theta => max_pos_gen hrho (by positivity) hne' theta
  simp only [circSup]
  exact (Continuous.inv₀ (by fun_prop) (fun theta => ne_of_gt (hpos theta))).sub
    continuous_const

/-! ## Pointwise comparisons of the averaged integrands -/

private lemma Fl2_le_Fsup {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t)
    (hne : t ≠ tcrit c rho) : Fl2 c rho t ≤ Fsup c rho t := by
  have h1 : IntervalIntegrable (fun θ : ℝ => circL2 c rho t θ) volume 0 (2 * Real.pi) :=
    (continuous_circL2 hc hrho ht hne).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => circSup c rho t θ) volume 0 (2 * Real.pi) :=
    (continuous_circSup hc hrho ht hne).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := (0 : ℝ))
    (b := 2 * Real.pi) (by positivity) h1 h2 (fun x _ => circL2_le_circSup c rho t x)
  have := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  rw [Fsup_eq, Fl2]
  exact this

/-- Pointwise lower bound for the Euclidean θ-integrand. -/
private lemma neg_hbnd_le_circL2 {A rho theta : ℝ} (hrho : 0 < rho) (hA : 0 < A) (hne : A ≠ rho) :
    -(rho / (A * (A + rho)))
      ≤ (Real.sqrt ((A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2))⁻¹ - A⁻¹ := by
  have hApos : 0 < A + rho := by linarith
  have hsq_le : Real.sqrt ((A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2) ≤ A + rho := by
    have hkey : (A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2
        = (A + rho) ^ 2 - 2 * A * rho * (1 + Real.cos theta) := by
      have h1 : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by
        have := Real.sin_sq_add_cos_sq theta
        linarith
      rw [show (rho * Real.sin theta) ^ 2 = rho ^ 2 * Real.sin theta ^ 2 by ring, h1]
      ring
    have hnn : 0 ≤ 2 * A * rho * (1 + Real.cos theta) := by
      have h1 : 0 ≤ 1 + Real.cos theta := by linarith [Real.neg_one_le_cos theta]
      positivity
    rw [← Real.sqrt_sq hApos.le]
    apply Real.sqrt_le_sqrt
    rw [hkey]
    linarith
  have hspos : 0 < Real.sqrt ((A - rho * Real.cos theta) ^ 2 + (rho * Real.sin theta) ^ 2) :=
    Real.sqrt_pos.mpr (sqsum_pos_gen hrho hA hne theta)
  have hinv : (A + rho)⁻¹ ≤ (Real.sqrt ((A - rho * Real.cos theta) ^ 2
      + (rho * Real.sin theta) ^ 2))⁻¹ := (inv_le_inv₀ hApos hspos).2 hsq_le
  have heq : (A + rho)⁻¹ - A⁻¹ = -(rho / (A * (A + rho))) := by
    field_simp
    ring
  linarith [hinv, heq]

private lemma neg_hbnd_le_Fl2 {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t)
    (hne : t ≠ tcrit c rho) : -hbnd c rho t ≤ Fl2 c rho t := by
  have hne' : c * t ^ (2 / 3 : ℝ) ≠ rho := mul_rpow_ne_rho hc hrho ht hne
  have hA : (0 : ℝ) < c * t ^ (2 / 3 : ℝ) := by positivity
  have hcont : IntervalIntegrable (fun θ : ℝ => circL2 c rho t θ) volume 0 (2 * Real.pi) :=
    (continuous_circL2 hc hrho ht hne).intervalIntegrable _ _
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      -(rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho))) ≤ circL2 c rho t θ := by
    intro θ _
    simp only [circL2]
    exact neg_hbnd_le_circL2 hrho hA hne'
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := (0 : ℝ))
    (b := 2 * Real.pi) (by positivity) intervalIntegrable_const hcont hpt
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have hstep := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have hone : (1 / (2 * Real.pi)) * ((2 * Real.pi) *
      (-(rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho)))))
      = -(rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho))) := by
    field_simp
  rw [hone] at hstep
  rw [Fl2, hbnd]
  exact hstep

/-! ## Almost everywhere statements -/

private lemma ae_ne_tcrit (c rho : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ tcrit c rho := by
  rw [ae_iff]
  simp

private lemma Fl2_le_Fsup_ae {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    Fl2 c rho ≤ᵐ[volume.restrict (Set.Ioi 0)] Fsup c rho := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (ae_ne_tcrit c rho)] with t ht hne
  exact Fl2_le_Fsup hc hrho ht hne

private lemma nonneg_Fl2_add_hbnd_ae {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun t => Fl2 c rho t + hbnd c rho t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (ae_ne_tcrit c rho)] with t ht hne
  have := neg_hbnd_le_Fl2 hc hrho ht hne
  show 0 ≤ Fl2 c rho t + hbnd c rho t
  linarith

private lemma Fl2_add_hbnd_le_Fsup_add_hbnd_ae {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    (fun t => Fl2 c rho t + hbnd c rho t) ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun t => Fsup c rho t + hbnd c rho t := by
  filter_upwards [Fl2_le_Fsup_ae hc hrho] with t ht
  linarith

/-! ## Integrability -/

private lemma stronglyMeasurable_Fl2 (c rho : ℝ) : StronglyMeasurable (Fl2 c rho) := by
  have hgm : Measurable (fun p : ℝ × ℝ => circL2 c rho p.1 p.2) := by
    unfold circL2
    fun_prop
  have hg : StronglyMeasurable (fun p : ℝ × ℝ => circL2 c rho p.1 p.2) := hgm.stronglyMeasurable
  have hind : StronglyMeasurable (fun p : ℝ × ℝ =>
      (Set.univ ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)).indicator
        (fun q : ℝ × ℝ => circL2 c rho q.1 q.2) p) :=
    hg.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
  have hint := hind.integral_prod_right' (ν := volume)
  have hfin : Fl2 c rho = fun t : ℝ => (1 / (2 * Real.pi)) *
      ∫ θ, (Set.univ ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)).indicator
        (fun q : ℝ × ℝ => circL2 c rho q.1 q.2) (t, θ) ∂volume := by
    funext t
    rw [Fl2]
    congr 1
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    by_cases hθ : θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (by simpa using hθ)]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem (by simpa using hθ)]
  rw [hfin]
  exact hint.const_mul _

private lemma integrableOn_Fsup {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    IntegrableOn (Fsup c rho) (Set.Ioi 0) := by
  by_contra hni
  have h0 : ∫ t in Set.Ioi (0 : ℝ), Fsup c rho t = 0 := integral_undef hni
  have hneg : (∫ t in Set.Ioi (0 : ℝ), Fsup c rho t) < 0 := by
    simpa only [Fsup] using planar_circle_average_parabolic_neg (c := c) (rho := rho) hc hrho
  rw [h0] at hneg
  exact lt_irrefl 0 hneg

private lemma hbnd_nonneg {c rho t : ℝ} (hc : 0 < c) (hrho : 0 < rho) (ht : 0 < t) :
    0 ≤ hbnd c rho t := by
  have h1 : 0 < c * t ^ (2 / 3 : ℝ) := by positivity
  have h2 : 0 < (c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho) := by positivity
  rw [hbnd]
  positivity

private lemma integrableOn_hbnd {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    IntegrableOn (hbnd c rho) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  refine IntegrableOn.union ?_ ?_
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 / 3) : ℝ)) (Set.Ioc (0 : ℝ) 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine Integrable.mono' (hbase.const_mul c⁻¹) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      have hcA : ContinuousOn (fun t : ℝ => c * t ^ (2 / 3 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
        continuousOn_const.mul (continuousOn_id.rpow_const (fun _ _ => Or.inr (by norm_num)))
      show ContinuousOn (fun t : ℝ => rho / ((c * t ^ (2 / 3 : ℝ))
        * (c * t ^ (2 / 3 : ℝ) + rho))) (Set.Ioc (0 : ℝ) 1)
      exact ContinuousOn.div continuousOn_const (hcA.mul (hcA.add continuousOn_const))
        (fun t ht => by
          have h1 : 0 < t := ht.1
          exact ne_of_gt (by positivity))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have h1 : 0 < t := ht.1
      have hA : 0 < c * t ^ (2 / 3 : ℝ) := by positivity
      have key1 : rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho))
          ≤ rho / ((c * t ^ (2 / 3 : ℝ)) * rho) :=
        div_le_div_of_nonneg_left hrho.le (by positivity) (by nlinarith)
      have key2 : rho / ((c * t ^ (2 / 3 : ℝ)) * rho) = c⁻¹ * t ^ (-(2 / 3) : ℝ) := by
        rw [show rho / ((c * t ^ (2 / 3 : ℝ)) * rho) = (c * t ^ (2 / 3 : ℝ))⁻¹ by field_simp]
        rw [mul_inv, ← Real.rpow_neg (le_of_lt h1)]
      rw [hbnd, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ rho / _)]
      rw [← key2]
      exact key1
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-(4 / 3) : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine Integrable.mono' (hbase.const_mul (rho * c⁻¹ * c⁻¹)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      have hcA : ContinuousOn (fun t : ℝ => c * t ^ (2 / 3 : ℝ)) (Set.Ioi (1 : ℝ)) :=
        continuousOn_const.mul (continuousOn_id.rpow_const (fun _ _ => Or.inr (by norm_num)))
      show ContinuousOn (fun t : ℝ => rho / ((c * t ^ (2 / 3 : ℝ))
        * (c * t ^ (2 / 3 : ℝ) + rho))) (Set.Ioi (1 : ℝ))
      exact ContinuousOn.div continuousOn_const (hcA.mul (hcA.add continuousOn_const))
        (fun t ht => by
          have h1 : 0 < t := lt_trans zero_lt_one ht
          exact ne_of_gt (by positivity))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have h1 : 0 < t := lt_trans zero_lt_one ht
      have hA : 0 < c * t ^ (2 / 3 : ℝ) := by positivity
      have key1 : rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ) + rho))
          ≤ rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ))) :=
        div_le_div_of_nonneg_left hrho.le (by positivity) (by nlinarith)
      have key2 : rho / ((c * t ^ (2 / 3 : ℝ)) * (c * t ^ (2 / 3 : ℝ)))
          = rho * c⁻¹ * c⁻¹ * t ^ (-(4 / 3) : ℝ) := by
        have hrpow : t ^ (-(4 / 3) : ℝ) = ((t ^ (2 / 3 : ℝ)) * (t ^ (2 / 3 : ℝ)))⁻¹ := by
          rw [← Real.rpow_add h1, show (2 / 3 : ℝ) + 2 / 3 = 4 / 3 by norm_num,
            Real.rpow_neg (le_of_lt h1)]
        rw [hrpow]
        field_simp
      rw [hbnd, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ rho / _)]
      rw [← key2]
      exact key1

private lemma integrableOn_Fl2 {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho) :
    IntegrableOn (Fl2 c rho) (Set.Ioi 0) := by
  have hFsup := integrableOn_Fsup hc hrho
  have hh := integrableOn_hbnd hc hrho
  refine Integrable.mono' (hFsup.abs.add hh) ?_ ?_
  · exact (stronglyMeasurable_Fl2 c rho).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (ae_ne_tcrit c rho)] with t ht hne
    have h1 := Fl2_le_Fsup hc hrho ht hne
    have h2 := neg_hbnd_le_Fl2 hc hrho ht hne
    have h3 := hbnd_nonneg hc hrho ht
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;> linarith [h1, h2, h3, le_abs_self (Fsup c rho t), abs_nonneg (Fsup c rho t)]

/-! ## The main statement -/

theorem average_inv_parabolic_circle_neg {d : ℕ} (hd : 2 ≤ d)
    {c rho : ℝ} (hc : 0 < c) (hrho : 0 < rho)
    (e f : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    ∫ t in Set.Ioi (0 : ℝ),
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
            (‖(c * t ^ (2 / 3 : ℝ)) • e
              - rho • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
          - (c * t ^ (2 / 3 : ℝ))⁻¹)
      < 0 := by
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
        ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
            (‖(c * t ^ (2 / 3 : ℝ)) • e
              - rho • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
          - (c * t ^ (2 / 3 : ℝ))⁻¹))
      = ∫ t in Set.Ioi (0 : ℝ), Fl2 c rho t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (‖(c * t ^ (2 / 3 : ℝ)) • e
          - rho • (Real.cos theta • e + Real.sin theta • f)‖)⁻¹
      - (c * t ^ (2 / 3 : ℝ))⁻¹)
      = (1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi), circL2 c rho t theta
    congr 1
    apply intervalIntegral.integral_congr
    intro theta _
    beta_reduce
    rw [norm_smul_orthonormal_cos_sin e f he hf hef]
    simp only [circL2]
  rw [hcongr]
  have hIntFl2 : IntegrableOn (Fl2 c rho) (Set.Ioi 0) := integrableOn_Fl2 hc hrho
  have hIntFsup : IntegrableOn (Fsup c rho) (Set.Ioi 0) := integrableOn_Fsup hc hrho
  have hmono := setIntegral_mono_on_ae hIntFl2 hIntFsup measurableSet_Ioi (by
    filter_upwards [ae_ne_tcrit c rho] with t hne ht
    exact Fl2_le_Fsup hc hrho ht hne)
  have hneg : (∫ t in Set.Ioi (0 : ℝ), Fsup c rho t) < 0 := by
    simpa only [Fsup] using planar_circle_average_parabolic_neg (c := c) (rho := rho) hc hrho
  linarith

end Commons.Analysis.Integral
