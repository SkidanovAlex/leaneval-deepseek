import Mathlib
import Submission.Work.FIArea7.SepBump

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology

noncomputable section

/-! ## 3. The smooth trapezoid `sepK` -/

/-- The smooth trapezoid: `Ψ((x+λ)/ε) - Ψ((x-λ)/ε)`. -/
noncomputable def sepK (lam eps : ℝ) (x : ℝ) : ℝ :=
  sepPsi ((x + lam)/eps) - sepPsi ((x - lam)/eps)

/-- The derivative of `sepK`. -/
noncomputable def sepK1 (lam eps : ℝ) (x : ℝ) : ℝ :=
  (sepRho ((x + lam)/eps) - sepRho ((x - lam)/eps))/eps

/-- The second derivative of `sepK`. -/
noncomputable def sepK2 (lam eps : ℝ) (x : ℝ) : ℝ :=
  (deriv sepRho ((x + lam)/eps) - deriv sepRho ((x - lam)/eps))/(eps*eps)

lemma integral_sepPsi_neg_one_one : ∫ u in (-1:ℝ)..1, sepPsi u = 0 := by
  have h2 : (∫ u in (0:ℝ)..1, sepPsi (-u)) = -(∫ u in (0:ℝ)..1, sepPsi u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y _
    exact sepPsi_neg y
  have hsym : (∫ u in (-1:ℝ)..0, sepPsi u) = -(∫ u in (0:ℝ)..1, sepPsi u) := by
    have h := intervalIntegral.integral_comp_neg (f := sepPsi) (a := (0:ℝ)) (b := (1:ℝ))
    simp only [neg_zero] at h
    rw [← h, h2]
  have hadd : (∫ u in (-1:ℝ)..0, sepPsi u) + (∫ u in (0:ℝ)..1, sepPsi u)
      = ∫ u in (-1:ℝ)..1, sepPsi u :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (sepPsi_continuous.intervalIntegrable (-1) 0) (sepPsi_continuous.intervalIntegrable 0 1)
  linarith

lemma integral_comp_div_add (f : ℝ → ℝ) (c eps : ℝ) (hε : 0 < eps) :
    ∫ x : ℝ, f ((x + c)/eps) = eps * ∫ u : ℝ, f u := by
  have h1 : ∫ x : ℝ, f ((x+c)/eps)
      = ∫ x : ℝ, (fun y : ℝ => f (y + c/eps)) ((1/eps) * x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    show f ((x+c)/eps) = f ((1/eps)*x + c/eps)
    congr 1
    field_simp
  rw [h1, Measure.integral_comp_mul_left (fun y : ℝ => f (y + c/eps)) (1/eps)]
  rw [integral_add_right_eq_self f (c/eps)]
  rw [show |(1/eps)⁻¹| = eps by simp only [one_div, inv_inv, abs_of_pos hε]]
  simp [smul_eq_mul]

lemma integral_abs_comp_div_add (f : ℝ → ℝ) (c eps : ℝ) (hε : 0 < eps) :
    ∫ x : ℝ, |f ((x + c)/eps)| = eps * ∫ u : ℝ, |f u| := by
  have h1 : ∫ x : ℝ, |f ((x+c)/eps)|
      = ∫ x : ℝ, (fun y : ℝ => |f (y + c/eps)|) ((1/eps) * x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    show |f ((x+c)/eps)| = |f ((1/eps)*x + c/eps)|
    congr 2
    field_simp
  rw [h1, Measure.integral_comp_mul_left (fun y : ℝ => |f (y + c/eps)|) (1/eps)]
  rw [integral_add_right_eq_self (fun y : ℝ => |f y|) (c/eps)]
  rw [show |(1/eps)⁻¹| = eps by simp only [one_div, inv_inv, abs_of_pos hε]]
  simp [smul_eq_mul]

lemma sepK_continuous (lam eps : ℝ) (hε : eps ≠ 0) : Continuous (sepK lam eps) := by
  unfold sepK
  have h1 : Continuous fun x : ℝ => (x + lam)/eps := by fun_prop
  have h2 : Continuous fun x : ℝ => (x - lam)/eps := by fun_prop
  exact (sepPsi_continuous.comp h1).sub (sepPsi_continuous.comp h2)

lemma sepK_nonneg {lam eps x : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps) :
    0 ≤ sepK lam eps x := by
  unfold sepK
  apply sub_nonneg.mpr
  apply sepPsi_monotone
  rw [div_le_div_iff_of_pos_right hε]
  linarith

lemma sepK_le_one (lam eps x : ℝ) : sepK lam eps x ≤ 1 := by
  unfold sepK
  have h1 := sepPsi_le_half ((x + lam)/eps)
  have h2 := neg_half_le_sepPsi ((x - lam)/eps)
  linarith

lemma sepK_eq_one {lam eps x : ℝ} (hε : 0 < eps) (hlam : eps ≤ lam) (h : |x| ≤ lam - eps) :
    sepK lam eps x = 1 := by
  unfold sepK
  have h1 : 1 ≤ (x + lam)/eps := by
    rw [le_div_iff₀ hε]; linarith [(abs_le.mp h).1]
  have h2 : (x - lam)/eps ≤ -1 := by
    rw [div_le_iff₀ hε]; linarith [(abs_le.mp h).2]
  rw [sepPsi_eq_half h1, sepPsi_eq_neg_half h2]
  norm_num

lemma sepK_eq_zero_of_le {lam eps x : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps)
    (h : x ≤ -(lam + eps)) : sepK lam eps x = 0 := by
  unfold sepK
  have h1 : (x + lam)/eps ≤ -1 := by
    rw [div_le_iff₀ hε]; linarith
  have h2 : (x - lam)/eps ≤ -1 := by
    rw [div_le_iff₀ hε]; linarith
  rw [sepPsi_eq_neg_half h1, sepPsi_eq_neg_half h2]
  ring

lemma sepK_eq_zero_of_ge {lam eps x : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps)
    (h : lam + eps ≤ x) : sepK lam eps x = 0 := by
  unfold sepK
  have h1 : 1 ≤ (x + lam)/eps := by
    rw [le_div_iff₀ hε]; linarith
  have h2 : 1 ≤ (x - lam)/eps := by
    rw [le_div_iff₀ hε]; linarith
  rw [sepPsi_eq_half h1, sepPsi_eq_half h2]
  ring

lemma sepK_even (lam eps : ℝ) (x : ℝ) : sepK lam eps (-x) = sepK lam eps x := by
  unfold sepK
  rw [show (-x + lam)/eps = -((x - lam)/eps) by ring_nf,
    show (-x - lam)/eps = -((x + lam)/eps) by ring_nf]
  rw [sepPsi_neg, sepPsi_neg]
  ring

lemma sepRho_diff : Differentiable ℝ sepRho := fun x => (sepRho_hasDerivAt x).differentiableAt

lemma sepPsi_diff : Differentiable ℝ sepPsi := fun x => (sepPsi_hasDerivAt x).differentiableAt

lemma deriv_comp_affine (c eps : ℝ) :
    deriv (fun x : ℝ => sepRho ((x + c)/eps))
      = fun x => deriv sepRho ((x + c)/eps) * (1/eps) := by
  funext x
  rw [show (fun x : ℝ => sepRho ((x + c)/eps)) = sepRho ∘ (fun x : ℝ => (x + c)/eps) from rfl]
  rw [deriv_comp]
  · rw [show deriv (fun x : ℝ => (x + c)/eps) x = 1/eps by
      rw [deriv_div_const, deriv_add_const, deriv_id'', one_div]]
  · exact sepRho_diff.differentiableAt
  · fun_prop

lemma deriv_comp_affine_sub (c eps : ℝ) :
    deriv (fun x : ℝ => sepRho ((x - c)/eps))
      = fun x => deriv sepRho ((x - c)/eps) * (1/eps) := by
  funext x
  rw [show (fun x : ℝ => sepRho ((x - c)/eps)) = sepRho ∘ (fun x : ℝ => (x - c)/eps) from rfl]
  rw [deriv_comp]
  · rw [show deriv (fun x : ℝ => (x - c)/eps) x = 1/eps by
      rw [deriv_div_const, deriv_sub_const, deriv_id'', one_div]]
  · exact sepRho_diff.differentiableAt
  · fun_prop

lemma sepK_hasDerivAt (lam eps : ℝ) (hε : eps ≠ 0) (x : ℝ) :
    HasDerivAt (sepK lam eps) (sepK1 lam eps x) x := by
  have hg1 : HasDerivAt (fun x : ℝ => (x + lam)/eps) (1/eps) x := by
    have h := ((hasDerivAt_id x : HasDerivAt (fun x : ℝ => x) 1 x)).add_const lam
    simpa using h.div_const eps
  have hg2 : HasDerivAt (fun x : ℝ => (x - lam)/eps) (1/eps) x := by
    have h := ((hasDerivAt_id x : HasDerivAt (fun x : ℝ => x) 1 x)).sub_const lam
    simpa using h.div_const eps
  have hA : HasDerivAt (fun x : ℝ => sepPsi ((x + lam)/eps))
      (sepRho ((x + lam)/eps) * (1/eps)) x := by
    exact (sepPsi_hasDerivAt ((x + lam)/eps)).comp x hg1
  have hB : HasDerivAt (fun x : ℝ => sepPsi ((x - lam)/eps))
      (sepRho ((x - lam)/eps) * (1/eps)) x := by
    exact (sepPsi_hasDerivAt ((x - lam)/eps)).comp x hg2
  have h := hA.sub hB
  rw [show sepK lam eps = (fun x : ℝ => sepPsi ((x + lam)/eps))
      - (fun x : ℝ => sepPsi ((x - lam)/eps)) from rfl]
  refine h.congr_deriv ?_
  rw [sepK1]
  ring

lemma deriv_sepK (lam eps : ℝ) (hε : eps ≠ 0) : deriv (sepK lam eps) = sepK1 lam eps :=
  funext fun x => (sepK_hasDerivAt lam eps hε x).deriv

lemma deriv_sepK1 (lam eps : ℝ) (hε : eps ≠ 0) : deriv (sepK1 lam eps) = sepK2 lam eps := by
  funext x
  rw [show sepK1 lam eps = fun y : ℝ => ((fun x : ℝ => sepRho ((x + lam)/eps))
      - (fun x : ℝ => sepRho ((x - lam)/eps))) y / eps from rfl]
  rw [deriv_div_const, deriv_sub]
  · rw [deriv_comp_affine lam eps, deriv_comp_affine_sub lam eps]
    unfold sepK2
    ring
  · exact (sepRho_diff.comp (by fun_prop)).differentiableAt
  · exact (sepRho_diff.comp (by fun_prop)).differentiableAt

/-! ## 4. Integrals of `sepK` and its derivatives -/

lemma sepRho_eq_zero_of_lt_neg_one' {y : ℝ} (h : y ≤ -1) : sepRho y = 0 := sepRho_eq_zero_of_le h

lemma deriv_sepRho_eq_zero_of_le {y : ℝ} (h : y ≤ -1) : deriv sepRho y = 0 := by
  rw [deriv_sepRho_eq]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 8*(y+1) ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*(1-y)),
    deriv_smoothTransition_eq_zero_of_nonpos (by linarith : 8*(y+1) ≤ 0),
    deriv_smoothTransition_eq_zero_of_one_lt (by linarith : 1 < 8*(1-y))]
  ring

lemma deriv_sepRho_eq_zero_of_one_le {y : ℝ} (h : 1 ≤ y) : deriv sepRho y = 0 := by
  rw [deriv_sepRho_eq]
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 8*(y+1)),
    Real.smoothTransition.zero_of_nonpos (by linarith : 8*(1-y) ≤ 0),
    deriv_smoothTransition_eq_zero_of_one_lt (by linarith : 1 < 8*(y+1)),
    deriv_smoothTransition_eq_zero_of_nonpos (by linarith : 8*(1-y) ≤ 0)]
  ring

lemma integrable_sepK (lam eps : ℝ) (hlam : 0 ≤ lam) (hε : 0 < eps) :
    Integrable (sepK lam eps) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact sepK_continuous lam eps hε.ne'
  · refine HasCompactSupport.intro (K := Set.Icc (-(lam+eps)) (lam+eps)) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact sepK_eq_zero_of_le hlam hε (le_of_lt h)
    · exact sepK_eq_zero_of_ge hlam hε (le_of_lt h)

lemma integrable_sepK1 (lam eps : ℝ) (hlam : 0 ≤ lam) (hε : 0 < eps) :
    Integrable (sepK1 lam eps) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold sepK1
    have h1 : Continuous fun x : ℝ => (x + lam)/eps := by fun_prop
    have h2 : Continuous fun x : ℝ => (x - lam)/eps := by fun_prop
    exact ((sepRho_continuous.comp h1).sub (sepRho_continuous.comp h2)).div_const eps
  · refine HasCompactSupport.intro (K := Set.Icc (-(lam+eps)) (lam+eps)) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    unfold sepK1
    rcases hx with h | h
    · rw [sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith),
        sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith)]
      ring
    · rw [sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith),
        sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith)]
      ring

lemma continuous_deriv_sepRho : Continuous (deriv sepRho) := by
  rw [show deriv sepRho = fun y => (8/15) * ((deriv Real.smoothTransition (8*(y+1)) * 8)
      * Real.smoothTransition (8*(1-y)))
      + (8/15) * (Real.smoothTransition (8*(y+1))
        * (deriv Real.smoothTransition (8*(1-y)) * (-8))) from funext deriv_sepRho_eq]
  fun_prop

lemma integrable_sepK2 (lam eps : ℝ) (hlam : 0 ≤ lam) (hε : 0 < eps) :
    Integrable (sepK2 lam eps) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold sepK2
    have h1 : Continuous fun x : ℝ => (x + lam)/eps := by fun_prop
    have h2 : Continuous fun x : ℝ => (x - lam)/eps := by fun_prop
    exact ((continuous_deriv_sepRho.comp h1).sub (continuous_deriv_sepRho.comp h2)).div_const (eps*eps)
  · refine HasCompactSupport.intro (K := Set.Icc (-(lam+eps)) (lam+eps)) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    unfold sepK2
    rcases hx with h | h
    · rw [deriv_sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith),
        deriv_sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith)]
      ring
    · rw [deriv_sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith),
        deriv_sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith)]
      ring

lemma integral_sepK_middle (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) :
    (∫ x in (-(lam-eps))..(lam-eps), sepK lam eps x) = 2*(lam-eps) := by
  rw [show (∫ x in (-(lam-eps))..(lam-eps), sepK lam eps x)
      = ∫ x in (-(lam-eps))..(lam-eps), (1:ℝ) from by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    refine sepK_eq_one hε hle ?_
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  rw [intervalIntegral.integral_const]
  simp
  ring

lemma integral_sepK_trans_left (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) :
    (∫ x in (-(lam+eps))..(-(lam-eps)), sepK lam eps x) = eps := by
  have hpt : ∀ x ∈ Set.uIcc (-(lam+eps)) (-(lam-eps)),
      sepK lam eps x = sepPsi ((x+lam)/eps) + 1/2 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    unfold sepK
    have h2 : (x - lam)/eps ≤ -1 := by
      rw [div_le_iff₀ hε]; linarith [hx.2]
    rw [sepPsi_eq_neg_half h2]
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [show (∫ x in (-(lam+eps))..(-(lam-eps)), (sepPsi ((x+lam)/eps) + 1/2))
      = ∫ x in (-(lam+eps))..(-(lam-eps)),
          (fun u : ℝ => sepPsi u + 1/2) ((1/eps)*x + lam/eps) from by
    apply intervalIntegral.integral_congr
    intro x _
    show sepPsi ((x+lam)/eps) + 1/2 = sepPsi ((1/eps)*x + lam/eps) + 1/2
    congr 1
    field_simp]
  rw [intervalIntegral.integral_comp_mul_add (f := fun u : ℝ => sepPsi u + 1/2)
    (by positivity) (lam/eps)]
  simp only [smul_eq_mul]
  rw [show (1/eps)⁻¹ = eps by simp only [one_div, inv_inv]]
  rw [show (1/eps) * (-(lam+eps)) + lam/eps = -1 by field_simp; ring]
  rw [show (1/eps) * (-(lam-eps)) + lam/eps = 1 by field_simp; ring]
  have hone : (∫ u in (-1:ℝ)..1, (sepPsi u + 1/2)) = 1 := by
    rw [intervalIntegral.integral_add (sepPsi_continuous.intervalIntegrable (-1) 1)
      intervalIntegrable_const]
    rw [integral_sepPsi_neg_one_one, zero_add, intervalIntegral.integral_const]
    norm_num
  rw [hone]
  ring

lemma integral_sepK_trans_right (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) :
    (∫ x in (lam-eps)..(lam+eps), sepK lam eps x) = eps := by
  have hpt : ∀ x ∈ Set.uIcc (lam-eps) (lam+eps),
      sepK lam eps x = (1/2) - sepPsi ((x-lam)/eps) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    unfold sepK
    have h2 : 1 ≤ (x + lam)/eps := by
      rw [le_div_iff₀ hε]; linarith [hx.1]
    rw [sepPsi_eq_half h2]
  rw [intervalIntegral.integral_congr hpt]
  rw [show (∫ x in (lam-eps)..(lam+eps), ((1/2) - sepPsi ((x-lam)/eps)))
      = ∫ x in (lam-eps)..(lam+eps),
          (fun u : ℝ => (1/2) - sepPsi u) ((1/eps)*x + (-(lam/eps))) from by
    apply intervalIntegral.integral_congr
    intro x _
    show (1/2) - sepPsi ((x-lam)/eps) = (1/2) - sepPsi ((1/eps)*x + -(lam/eps))
    congr 1
    field_simp
    ring_nf]
  rw [intervalIntegral.integral_comp_mul_add (f := fun u : ℝ => (1/2) - sepPsi u)
    (by positivity) (-(lam/eps))]
  simp only [smul_eq_mul]
  rw [show (1/eps)⁻¹ = eps by simp only [one_div, inv_inv]]
  rw [show (1/eps) * (lam-eps) + -(lam/eps) = -1 by field_simp; ring]
  rw [show (1/eps) * (lam+eps) + -(lam/eps) = 1 by field_simp; ring]
  have hone : (∫ u in (-1:ℝ)..1, ((1/2) - sepPsi u)) = 1 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (sepPsi_continuous.intervalIntegrable (-1) 1)]
    rw [integral_sepPsi_neg_one_one, sub_zero, intervalIntegral.integral_const]
    norm_num
  rw [hone]
  ring

lemma integral_abs_sepK {lam eps : ℝ} (hlam : 0 ≤ lam) (hε : 0 < eps) (hle : eps ≤ lam) :
    ∫ x : ℝ, |sepK lam eps x| = 2*lam := by
  have hzero : ∀ x ∉ Set.Ioc (-(lam+eps)) (lam+eps), sepK lam eps x = 0 := by
    intro x hx
    rw [Set.mem_Ioc, not_and_or] at hx
    rcases hx with h | h
    · exact sepK_eq_zero_of_le hlam hε (not_lt.mp h)
    · exact sepK_eq_zero_of_ge hlam hε (le_of_lt (not_le.mp h))
  have habs : ∀ x, |sepK lam eps x| = sepK lam eps x :=
    fun x => abs_of_nonneg (sepK_nonneg hlam hε)
  rw [show (∫ x : ℝ, |sepK lam eps x|) = ∫ x : ℝ, sepK lam eps x from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact habs x]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [← intervalIntegral.integral_of_le (by linarith : -(lam+eps) ≤ lam+eps)]
  have hint := (integrable_sepK lam eps hlam hε)
  have hsplit1 : (∫ x in (-(lam+eps))..(-(lam-eps)), sepK lam eps x)
      + (∫ x in (-(lam-eps))..(lam-eps), sepK lam eps x)
      = ∫ x in (-(lam+eps))..(lam-eps), sepK lam eps x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((sepK_continuous lam eps hε.ne').intervalIntegrable (-(lam+eps)) (-(lam-eps)))
      ((sepK_continuous lam eps hε.ne').intervalIntegrable (-(lam-eps)) (lam-eps))
  have hsplit2 : (∫ x in (-(lam+eps))..(lam-eps), sepK lam eps x)
      + (∫ x in (lam-eps)..(lam+eps), sepK lam eps x)
      = ∫ x in (-(lam+eps))..(lam+eps), sepK lam eps x :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((sepK_continuous lam eps hε.ne').intervalIntegrable (-(lam+eps)) (lam-eps))
      ((sepK_continuous lam eps hε.ne').intervalIntegrable (lam-eps) (lam+eps))
  rw [← hsplit2, ← hsplit1, integral_sepK_trans_left lam eps hε hle,
    integral_sepK_middle lam eps hε hle, integral_sepK_trans_right lam eps hε hle]
  ring

lemma integral_sepRho_univ : ∫ u : ℝ, sepRho u = 1 := by
  have hzero : ∀ y ∉ Set.Ioc (-1:ℝ) 1, sepRho y = 0 := by
    intro y hy
    rw [Set.mem_Ioc, not_and_or] at hy
    rcases hy with h | h
    · exact sepRho_eq_zero_of_le (not_lt.mp h)
    · exact sepRho_eq_zero_of_one_le (le_of_lt (not_le.mp h))
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  exact integral_sepRho

lemma integrable_sepRho_comp (c eps : ℝ) (hε : 0 < eps) :
    Integrable (fun x : ℝ => sepRho ((x + c)/eps)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact sepRho_continuous.comp (by fun_prop)
  · refine HasCompactSupport.intro (K := Set.Icc (-c-eps) (-c+eps)) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith)]
    · rw [sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith)]

lemma integrable_deriv_sepRho_comp (c eps : ℝ) (hε : 0 < eps) :
    Integrable (fun x : ℝ => deriv sepRho ((x + c)/eps)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_deriv_sepRho.comp (by fun_prop)
  · refine HasCompactSupport.intro (K := Set.Icc (-c-eps) (-c+eps)) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [deriv_sepRho_eq_zero_of_le (by rw [div_le_iff₀ hε]; linarith)]
    · rw [deriv_sepRho_eq_zero_of_one_le (by rw [le_div_iff₀ hε]; linarith)]

lemma integral_abs_sepK1_le {lam eps : ℝ} (hε : 0 < eps) :
    ∫ x : ℝ, |sepK1 lam eps x| ≤ 2 := by
  have hbd : ∀ x, |sepK1 lam eps x|
      ≤ (sepRho ((x + lam)/eps) + sepRho ((x - lam)/eps))/eps := by
    intro x
    have h1 : 0 ≤ sepRho ((x + lam)/eps) := sepRho_nonneg _
    have h2 : 0 ≤ sepRho ((x - lam)/eps) := sepRho_nonneg _
    have h : |sepRho ((x + lam)/eps) - sepRho ((x - lam)/eps)|
        ≤ sepRho ((x + lam)/eps) + sepRho ((x - lam)/eps) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    unfold sepK1
    rw [abs_div, abs_of_pos hε]
    exact div_le_div_of_nonneg_right h hε.le
  have hint : Integrable (fun x : ℝ => (sepRho ((x + lam)/eps)
      + sepRho ((x - lam)/eps))/eps) :=
    ((integrable_sepRho_comp lam eps hε).add (integrable_sepRho_comp (-lam) eps hε)).div_const eps
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun x : ℝ => |sepK1 lam eps x|)
    (g := fun x : ℝ => (sepRho ((x + lam)/eps) + sepRho ((x - lam)/eps))/eps)
    (by filter_upwards with x; exact abs_nonneg _) hint
    (by filter_upwards with x; exact hbd x)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_div]
  rw [show (fun a : ℝ => sepRho ((a + lam)/eps) + sepRho ((a - lam)/eps))
      = (fun a : ℝ => sepRho ((a + lam)/eps)) + (fun a : ℝ => sepRho ((a + (-lam))/eps)) from rfl]
  rw [show ((fun a : ℝ => sepRho ((a + lam)/eps))
      + (fun a : ℝ => sepRho ((a + (-lam))/eps)))
      = fun a : ℝ => sepRho ((a + lam)/eps) + sepRho ((a + (-lam))/eps) from rfl]
  rw [MeasureTheory.integral_add (integrable_sepRho_comp lam eps hε)
    (integrable_sepRho_comp (-lam) eps hε)]
  rw [integral_comp_div_add sepRho lam eps hε, integral_comp_div_add sepRho (-lam) eps hε,
    integral_sepRho_univ]
  rw [div_eq_iff (ne_of_gt hε)]
  ring

lemma integral_abs_sepK2_le {lam eps : ℝ} (hε : 0 < eps) :
    ∫ x : ℝ, |sepK2 lam eps x| ≤ 32/(15*eps) := by
  have hbd : ∀ x, |sepK2 lam eps x|
      ≤ (|deriv sepRho ((x + lam)/eps)| + |deriv sepRho ((x - lam)/eps)|)/(eps*eps) := by
    intro x
    have ha := le_abs_self (deriv sepRho ((x + lam)/eps))
    have hb := neg_abs_le (deriv sepRho ((x + lam)/eps))
    have hc := le_abs_self (deriv sepRho ((x - lam)/eps))
    have hd := neg_abs_le (deriv sepRho ((x - lam)/eps))
    have h : |deriv sepRho ((x + lam)/eps) - deriv sepRho ((x - lam)/eps)|
        ≤ |deriv sepRho ((x + lam)/eps)| + |deriv sepRho ((x - lam)/eps)| := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    unfold sepK2
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < eps*eps)]
    exact div_le_div_of_nonneg_right h (by positivity)
  have hint : Integrable (fun x : ℝ => (|deriv sepRho ((x + lam)/eps)|
      + |deriv sepRho ((x - lam)/eps)|)/(eps*eps)) :=
    (((integrable_deriv_sepRho_comp lam eps hε).abs).add
      ((integrable_deriv_sepRho_comp (-lam) eps hε).abs)).div_const (eps*eps)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun x : ℝ => |sepK2 lam eps x|)
    (g := fun x : ℝ => (|deriv sepRho ((x + lam)/eps)|
      + |deriv sepRho ((x - lam)/eps)|)/(eps*eps))
    (by filter_upwards with x; exact abs_nonneg _) hint
    (by filter_upwards with x; exact hbd x)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_div]
  rw [show (fun a : ℝ => |deriv sepRho ((a + lam)/eps)| + |deriv sepRho ((a - lam)/eps)|)
      = (fun a : ℝ => |deriv sepRho ((a + lam)/eps)|)
        + (fun a : ℝ => |deriv sepRho ((a + (-lam))/eps)|) from rfl]
  rw [show ((fun a : ℝ => |deriv sepRho ((a + lam)/eps)|)
      + (fun a : ℝ => |deriv sepRho ((a + (-lam))/eps)|))
      = fun a : ℝ => |deriv sepRho ((a + lam)/eps)| + |deriv sepRho ((a + (-lam))/eps)| from rfl]
  rw [MeasureTheory.integral_add (integrable_deriv_sepRho_comp lam eps hε).abs
    (integrable_deriv_sepRho_comp (-lam) eps hε).abs]
  rw [integral_abs_comp_div_add (deriv sepRho) lam eps hε,
    integral_abs_comp_div_add (deriv sepRho) (-lam) eps hε]
  have h2 := integral_abs_deriv_sepRho_le
  rw [div_le_iff₀ (by positivity : (0:ℝ) < eps*eps)]
  rw [show 32/(15*eps) * (eps*eps) = 32*eps/15 by field_simp]
  nlinarith [h2, hε]

/-! ## 5. The parameters `λ, ε` attached to `M = ⌊x⌋` -/

/-- `λ = (log M + log (M+1)) / (4π)`. -/
noncomputable def sepLam (M : ℕ) : ℝ := (Real.log M + Real.log (M+1))/(4*Real.pi)

/-- `ε = (log (M+1) - log M) / (4π)`. -/
noncomputable def sepEps (M : ℕ) : ℝ := (Real.log (M+1) - Real.log M)/(4*Real.pi)

lemma sepEps_pos {M : ℕ} (hM : 1 ≤ M) : 0 < sepEps M := by
  unfold sepEps
  have h1 : (0:ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have h2 : Real.log M < Real.log (M+1) := by
    apply Real.log_lt_log
    · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (by exact_mod_cast hM)
    · exact_mod_cast Nat.lt_succ_self M
  exact div_pos (by linarith) (by positivity)

lemma sepEps_le_sepLam {M : ℕ} (hM : 1 ≤ M) : sepEps M ≤ sepLam M := by
  unfold sepEps sepLam
  have h1 : (0:ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 4*Real.pi)]
  linarith

lemma sepLam_nonneg {M : ℕ} (hM : 1 ≤ M) : 0 ≤ sepLam M := by
  unfold sepLam
  have h1 : (0:ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have h2 : (0:ℝ) ≤ Real.log (M+1) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero M))
  exact div_nonneg (by linarith) (by positivity)

lemma sepLam_sub_sepEps (M : ℕ) : sepLam M - sepEps M = Real.log M/(2*Real.pi) := by
  unfold sepLam sepEps
  field_simp
  ring

lemma sepLam_add_sepEps (M : ℕ) : sepLam M + sepEps M = Real.log (M+1)/(2*Real.pi) := by
  unfold sepLam sepEps
  field_simp
  ring

lemma sepK_sepLam_sepEps_of_le {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) (hkM : k ≤ M) :
    sepK (sepLam M) (sepEps M) (Real.log k/(2*Real.pi)) = 1 := by
  have hε := sepEps_pos hM
  have hle := sepEps_le_sepLam hM
  refine sepK_eq_one hε hle ?_
  rw [abs_le]
  constructor
  · have hk0 : (0:ℝ) ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hkM' : Real.log k ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkM)
    rw [sepLam_sub_sepEps, ← neg_div,
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2*Real.pi)]
    linarith
  · rw [sepLam_sub_sepEps,
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2*Real.pi)]
    exact Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkM)

lemma sepK_sepLam_sepEps_of_lt {M k : ℕ} (hM : 1 ≤ M) (hk : M+1 ≤ k) :
    sepK (sepLam M) (sepEps M) (Real.log k/(2*Real.pi)) = 0 := by
  have hε := sepEps_pos hM
  have hlam := sepLam_nonneg hM
  refine sepK_eq_zero_of_ge hlam hε ?_
  rw [sepLam_add_sepEps M, div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2*Real.pi)]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hk)


end

end Work.FIArea7
