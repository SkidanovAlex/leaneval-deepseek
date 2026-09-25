import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.integral_mul_dbarCoord_eq_neg
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.bmDbarKernel_shell_eq_zero

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-! ## The Wirtinger derivative `∂̄_j` of the Bochner–Martinelli kernel -/

theorem dbarCoord_bmKernel {n : ℕ} {j k : Fin n} {x : Fin n → ℂ} (hx : x ≠ 0) :
    Work.CR.Flat.dbarCoord j (Work.CR.Flat.Cauchy.bmKernel k) x
      = Work.CR.Flat.Cauchy.bmDbarKernel j k x := by
  have hsm : sm x ≠ 0 := ne_of_gt (sm_pos hx)
  have hsmC : ((sm x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsm
  have hdiff1 : DifferentiableAt ℝ (fun y : Fin n → ℂ => starRingEnd ℂ (y k)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp x
      ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ)) x := by
    have h : (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ)) = (fun y => ((nrmSq y : ℝ) : ℂ)) := by
      funext y; simp [sm_apply, nrmSq, Complex.normSq_eq_norm_sq]
    rw [h]
    exact BmEpsAux.differentiableAt_nrmSq_complex x
  have hdiff2 : DifferentiableAt ℝ (fun y : Fin n → ℂ => (((sm y : ℝ) : ℂ)) ^ (-(n:ℤ))) x :=
    BmEpsAux.differentiableAt_zpow_comp x (-(n:ℤ)) hGdiff hsmC
  have hbmeq : Work.CR.Flat.Cauchy.bmKernel k
      = (fun y => starRingEnd ℂ (y k) * (((sm y : ℝ) : ℂ) ^ (-(n:ℤ)))) :=
    funext fun y => Work.CR.Flat.Cauchy.bmCz.bmKernel_eq k y
  rw [hbmeq, Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ x hdiff1 hdiff2]
  simp only [starRingEnd_apply]
  rw [Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord j k x]
  have hzp := BmEpsAux.dbarCoord_zpow j (-(n:ℤ)) x hGdiff hsmC
  rw [hzp]
  rw [show Work.CR.Flat.dbarCoord j (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ)) x = x j from by
    rw [show (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ)) = (fun y => ((nrmSq y : ℝ) : ℂ)) from by
      funext y; simp [sm_apply, nrmSq, Complex.normSq_eq_norm_sq]]
    exact BmEpsAux.dbarCoord_nrmSq j x]
  rw [Work.CR.Flat.Cauchy.bmDbarKernel, div_eq_mul_inv, div_eq_mul_inv]
  rw [Work.CR.Flat.Cauchy.bmCz.eucNorm_pow_inv_eq x, ← Work.CR.Flat.Cauchy.bmCz.sm_zpow_eq x]
  simp only [starRingEnd_apply]
  push_cast
  ring

/-! ## The regularised kernel `bmKerEps` -/

lemma dbarCoord_bmKerEps_gen {n : ℕ} {ε : ℝ} (hε : 0 < ε) (j k : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (bmKerEps k ε) z
      = (if j = k then 1 else 0) / (((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ n
        - (n : ℂ) * star (z k) * z j / (((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1) := by
  have hfun : bmKerEps k ε = fun x : Fin n → ℂ =>
      star (x k) * ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ))) := by
    funext x
    rw [bmKerEps_apply, div_eq_mul_inv]
    congr 1
    rw [show (-(n:ℤ)) = -((n:ℤ)) from rfl, zpow_neg, zpow_natCast]
  have hu : DifferentiableAt ℝ (fun x : Fin n → ℂ => star (x k)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z
      ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt
  have hGdiff : DifferentiableAt ℝ (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z := by
    have hsum : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ)))
        = fun x => ((nrmSq x : ℝ) : ℂ) + ((ε ^ 2 : ℝ) : ℂ) := by
      funext x; simp [Complex.ofReal_add]
    rw [hsum]
    exact (BmEpsAux.differentiableAt_nrmSq_complex z).add (differentiableAt_const ((ε ^ 2 : ℝ) : ℂ))
  have hGz : (fun x : Fin n → ℂ => ((((nrmSq x + ε ^ 2 : ℝ)) : ℂ))) z ≠ 0 := by
    show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ≠ 0
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg z; positivity)
  have hv := BmEpsAux.differentiableAt_zpow_comp z (-(n:ℤ)) hGdiff hGz
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ z hu hv]
  rw [show Work.CR.Flat.dbarCoord j (fun x : Fin n → ℂ => star (x k)) z = if j = k then 1 else 0 from
    Work.CR.Flat.Polydisc.dbarCoord_apply_conj_coord j k z]
  rw [BmEpsAux.dbarCoord_radial hε j z]
  rw [show ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ) ^ (-(n:ℤ)))
      = 1 / ((((nrmSq z + ε ^ 2 : ℝ)) : ℂ)) ^ n from by
    rw [show (-(n:ℤ)) = -((n:ℤ)) from rfl, zpow_neg, zpow_natCast, one_div]]
  ring

lemma contDiff_one_bmKerEps' {n : ℕ} (k : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (bmKerEps k ε) := by
  have hnum : ContDiff ℝ 1 (fun x : Fin n → ℂ => starRingEnd ℂ (x k)) := by
    have h : (fun x : Fin n → ℂ => starRingEnd ℂ (x k))
        = ⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) ∘
            ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := by
      funext x; simp
    rw [h]
    exact (Complex.conjCLE.contDiff).comp
      (((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))
  have hnrm : ContDiff ℝ 1 (fun x : Fin n → ℂ => nrmSq x) := by
    have h : (fun x : Fin n → ℂ => nrmSq x) = fun x => ∑ i : Fin n, ‖x i‖ ^ 2 := rfl
    rw [h]
    refine ContDiff.sum (s := Finset.univ) (fun i _ => ?_)
    have h2 : (fun x : Fin n → ℂ => ‖x i‖ ^ 2)
        = (fun y : ℂ => ‖y‖ ^ 2) ∘
            ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := rfl
    rw [h2]
    exact (contDiff_norm_sq ℂ (E := ℂ) (n := 1)).comp
      (((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))
  have hden : ContDiff ℝ 1 (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n) :=
    (Complex.ofRealCLM.contDiff.comp (hnrm.add contDiff_const)).pow n
  have hne : ∀ x : Fin n → ℂ, (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n ≠ 0 := by
    intro x
    apply pow_ne_zero
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := nrmSq_nonneg x; positivity)
  have hfun : bmKerEps k ε = (fun x : Fin n → ℂ => starRingEnd ℂ (x k))
      * (fun x : Fin n → ℂ => (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)⁻¹ := by
    funext x; rw [Pi.mul_apply, Pi.inv_apply, bmKerEps_apply, div_eq_mul_inv]
  rw [hfun]
  exact ContDiff.mul hnum (ContDiff.inv hden hne)

lemma norm_apply_le_eucNorm'' {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : ‖x i‖ ≤ eucNorm x :=
  (pi_norm_le_iff_of_nonneg (eucNorm_nonneg x)).mp (pi_norm_le_eucNorm x) i

lemma norm_dbarCoord_bmKerEps_le {n : ℕ} {ε : ℝ} (hε : 0 < ε) (j k : Fin n) {x : Fin n → ℂ}
    (hx : x ≠ 0) :
    ‖Work.CR.Flat.dbarCoord j (bmKerEps k ε) x‖ ≤ ((n : ℝ) + 1) / (eucNorm x) ^ (2 * n) := by
  rw [dbarCoord_bmKerEps_gen hε j k x]
  have hDpos : 0 < nrmSq x := nrmSq_pos hx
  have hDε : 0 < nrmSq x + ε ^ 2 := by positivity
  have hpow : (nrmSq x) = eucNorm x ^ 2 := nrmSq_eq_eucNorm_sq x
  have h1 : ‖(if j = k then (1:ℂ) else 0) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n‖
      ≤ 1 / (nrmSq x) ^ n := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDε]
    have hnum : ‖(if j = k then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    calc ‖(if j = k then (1:ℂ) else 0)‖ / (nrmSq x + ε ^ 2) ^ n
        ≤ 1 / (nrmSq x + ε ^ 2) ^ n := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 1 / (nrmSq x) ^ n := by
          refine div_le_div_of_nonneg_left (by norm_num) (pow_pos hDpos n) ?_
          exact pow_le_pow_left₀ (le_of_lt hDpos) (le_add_of_nonneg_right (sq_nonneg ε)) n
  have h2 : ‖(n : ℂ) * star (x k) * x j / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)‖
      ≤ (n : ℝ) / (nrmSq x) ^ n := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hDε]
    have hnk : ‖star (x k)‖ ≤ eucNorm x := by rw [norm_star]; exact norm_apply_le_eucNorm'' x k
    have hnj : ‖x j‖ ≤ eucNorm x := norm_apply_le_eucNorm'' x j
    have hnc : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [hnc]
    have hnum : (n:ℝ) * ‖star (x k)‖ * ‖x j‖ ≤ (n:ℝ) * eucNorm x * eucNorm x := by
      calc (n:ℝ) * ‖star (x k)‖ * ‖x j‖ ≤ (n:ℝ) * eucNorm x * ‖x j‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnk (Nat.cast_nonneg n))
              (norm_nonneg _)
        _ ≤ (n:ℝ) * eucNorm x * eucNorm x :=
            mul_le_mul_of_nonneg_left hnj (mul_nonneg (Nat.cast_nonneg n) (eucNorm_nonneg x))
    calc (n:ℝ) * ‖star (x k)‖ * ‖x j‖ / (nrmSq x + ε ^ 2) ^ (n + 1)
        ≤ (n:ℝ) * eucNorm x * eucNorm x / (nrmSq x + ε ^ 2) ^ (n + 1) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (n:ℝ) * eucNorm x * eucNorm x / (nrmSq x) ^ (n + 1) := by
          refine div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (eucNorm_nonneg x)) (eucNorm_nonneg x))
            (pow_pos hDpos _)
            (pow_le_pow_left₀ (le_of_lt hDpos) (le_add_of_nonneg_right (sq_nonneg ε)) (n + 1))
      _ = (n:ℝ) / (nrmSq x) ^ n := by
          have hex' : (n:ℝ) * eucNorm x * eucNorm x = (n:ℝ) * nrmSq x := by
            rw [hpow]; ring
          rw [hex', pow_succ]
          field_simp
  have htri := norm_sub_le ((if j = k then (1:ℂ) else 0) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n)
      ((n : ℂ) * star (x k) * x j / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
  have hsum : 1 / (nrmSq x) ^ n + (n:ℝ) / (nrmSq x) ^ n
      = ((n : ℝ) + 1) / (eucNorm x) ^ (2 * n) := by
    rw [hpow, show (eucNorm x ^ 2) ^ n = eucNorm x ^ (2 * n) by rw [pow_mul]]
    field_simp
    ring
  linarith [htri, h1, h2, hsum.le, hsum.ge]

lemma tendsto_dbarCoord_bmKerEps {n : ℕ} (j k : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Work.CR.Flat.dbarCoord j (bmKerEps k ε) x)
      (𝓝[>] (0:ℝ)) (𝓝 (bmDbarKernel j k x)) := by
  have hpos : (0:ℝ) < nrmSq x := nrmSq_pos hx
  have hcont : ContinuousAt (fun ε : ℝ =>
      (if j = k then (1:ℂ) else 0) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n
        - (n : ℂ) * star (x k) * x j / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) 0 := by
    have hne1 : (((nrmSq x + (0:ℝ) ^ 2 : ℝ)) : ℂ) ^ n ≠ 0 := by
      apply pow_ne_zero
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (by positivity)
    have hne2 : (((nrmSq x + (0:ℝ) ^ 2 : ℝ)) : ℂ) ^ (n + 1) ≠ 0 := by
      apply pow_ne_zero
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (by positivity)
    fun_prop (disch := assumption)
  have hF0 : (if j = k then (1:ℂ) else 0) / (((nrmSq x + (0:ℝ) ^ 2 : ℝ)) : ℂ) ^ n
        - (n : ℂ) * star (x k) * x j / (((nrmSq x + (0:ℝ) ^ 2 : ℝ)) : ℂ) ^ (n + 1)
      = bmDbarKernel j k x := by
    have hsq : (((nrmSq x : ℝ)) : ℂ) = ((eucNorm x : ℂ)) ^ 2 := by
      rw [nrmSq_eq_eucNorm_sq, Complex.ofReal_pow]
    have hp1 : ((((nrmSq x : ℝ)) : ℂ)) ^ n = ((eucNorm x : ℂ)) ^ (2 * n) := by
      rw [hsq, ← pow_mul]
    have hp2 : ((((nrmSq x : ℝ)) : ℂ)) ^ (n + 1) = ((eucNorm x : ℂ)) ^ (2 * n + 2) := by
      rw [hsq, ← pow_mul, show 2 * (n + 1) = 2 * n + 2 from by ring]
    simp only [pow_two, mul_zero, add_zero]
    rw [bmDbarKernel, hp1, hp2]
    simp only [starRingEnd_apply]
  have h1 : Tendsto (fun ε : ℝ =>
      (if j = k then (1:ℂ) else 0) / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ n
        - (n : ℂ) * star (x k) * x j / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
      (𝓝[>] (0:ℝ)) (𝓝 (bmDbarKernel j k x)) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0:ℝ)] (0:ℝ) ≤ 𝓝 (0:ℝ))
    rwa [hF0] at this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dbarCoord_bmKerEps_gen hε j k x).symm



open Work.CR.Flat.Cauchy

lemma exists_norm_le_eucNorm_of_contDiff {n : ℕ} {h : (Fin n → ℂ) → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hh : ContDiff ℝ 1 h) (hsupp : ∀ x, ρ ≤ ‖x‖ → h x = 0) (h0 : h 0 = 0) :
    ∃ M, 0 ≤ M ∧ ∀ x, ‖h x‖ ≤ M * eucNorm x := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0:Fin n → ℂ) ρ)
      (hh.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ ρ
  · have hmem : x ∈ Metric.closedBall (0:Fin n → ℂ) ρ := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmem0 : (0:Fin n → ℂ) ∈ Metric.closedBall (0:Fin n → ℂ) ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hρ
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
        (s := Metric.closedBall (0:Fin n → ℂ) ρ)
        (fun y _ => (hh.differentiable (by norm_num)).differentiableAt)
        (fun y hy => le_trans (hC y hy) (le_max_left C 0))
        (convex_closedBall (0:Fin n → ℂ) ρ) hmem0 hmem
    rw [h0, sub_zero, sub_zero] at hmvt
    calc ‖h x‖ ≤ max C 0 * ‖x‖ := hmvt
      _ ≤ max C 0 * eucNorm x := mul_le_mul_of_nonneg_left (pi_norm_le_eucNorm x) (le_max_right _ _)
  · push Not at hx
    rw [hsupp x (le_of_lt hx), norm_zero]
    exact mul_nonneg (le_max_right _ _) (eucNorm_nonneg x)

lemma measurable_bmDbarKernel {n : ℕ} (j k : Fin n) : Measurable (bmDbarKernel j k) := by
  have h1 : Measurable (fun x : Fin n → ℂ => ((eucNorm x : ℂ)) ^ (2 * n)) :=
    ((Complex.continuous_ofReal.comp continuous_eucNorm).pow _).measurable
  have h2 : Measurable (fun x : Fin n → ℂ => ((eucNorm x : ℂ)) ^ (2 * n + 2)) :=
    ((Complex.continuous_ofReal.comp continuous_eucNorm).pow _).measurable
  have hnum2 : Measurable (fun x : Fin n → ℂ => (n:ℂ) * star (x k) * x j) := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact measurable_const
      · exact continuous_star.measurable.comp (measurable_pi_apply k)
    · exact measurable_pi_apply j
  have h3 : Measurable (fun x : Fin n → ℂ =>
      (if j = k then (1:ℂ) else 0) / ((eucNorm x : ℂ)) ^ (2*n)) := measurable_const.div h1
  have h4 : Measurable (fun x : Fin n → ℂ =>
      (n:ℂ) * star (x k) * x j / ((eucNorm x : ℂ)) ^ (2*n+2)) := hnum2.div h2
  have hfun : (fun x : Fin n → ℂ => bmDbarKernel j k x)
      = fun x => (if j = k then (1:ℂ) else 0) / ((eucNorm x : ℂ)) ^ (2*n)
          - (n:ℂ) * star (x k) * x j / ((eucNorm x : ℂ)) ^ (2*n+2) := by
    funext x; rw [bmDbarKernel, starRingEnd_apply]
  change Measurable (fun x : Fin n → ℂ => bmDbarKernel j k x)
  rw [hfun]
  exact h3.sub h4

lemma norm_bmDbarKernel_le {n : ℕ} (j k : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    ‖bmDbarKernel j k x‖ ≤ ((n:ℝ)+1) / (eucNorm x) ^ (2*n) := by
  have hE : 0 < eucNorm x := eucNorm_pos hx
  rw [bmDbarKernel, div_eq_mul_inv, div_eq_mul_inv]
  have h1 : ‖(if j = k then (1:ℂ) else 0) * ((eucNorm x : ℂ) ^ (2*n))⁻¹‖
      ≤ 1 / (eucNorm x) ^ (2*n) := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
    have hc : ‖(if j = k then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
    calc ‖(if j = k then (1:ℂ) else 0)‖ * (eucNorm x ^ (2*n))⁻¹
        ≤ 1 * (eucNorm x ^ (2*n))⁻¹ :=
          mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (by positivity))
      _ = 1 / (eucNorm x) ^ (2*n) := by rw [one_mul, inv_eq_one_div]
  have h2 : ‖(n:ℂ) * star (x k) * x j * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹‖
      ≤ (n:ℝ) / (eucNorm x) ^ (2*n) := by
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hE]
    have hnk : ‖star (x k)‖ ≤ eucNorm x := by rw [norm_star]; exact norm_apply_le_eucNorm'' x k
    have hnj : ‖x j‖ ≤ eucNorm x := norm_apply_le_eucNorm'' x j
    have hnc : ‖(n:ℂ)‖ = (n:ℝ) := by simp
    rw [hnc]
    have hkey : (eucNorm x) ^ (2*n+2) = (eucNorm x) ^ (2*n) * (eucNorm x * eucNorm x) := by
      rw [pow_add]; ring
    rw [hkey, mul_inv]
    have hstep : (n:ℝ) * ‖star (x k)‖ * ‖x j‖ * (((eucNorm x) ^ (2*n))⁻¹ * (eucNorm x * eucNorm x)⁻¹)
        ≤ (n:ℝ) * (eucNorm x * eucNorm x) * (((eucNorm x) ^ (2*n))⁻¹ * (eucNorm x * eucNorm x)⁻¹) :=
      mul_le_mul_of_nonneg_right
        (by
          calc (n:ℝ) * ‖star (x k)‖ * ‖x j‖ ≤ (n:ℝ) * eucNorm x * eucNorm x :=
                mul_le_mul (mul_le_mul_of_nonneg_left hnk (Nat.cast_nonneg n)) hnj
                  (norm_nonneg _) (by positivity)
            _ = (n:ℝ) * (eucNorm x * eucNorm x) := by ring)
        (by positivity)
    refine hstep.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    field_simp
  calc ‖(if j = k then (1:ℂ) else 0) * ((eucNorm x : ℂ) ^ (2*n))⁻¹
        - (n:ℂ) * star (x k) * x j * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹‖
      ≤ ‖(if j = k then (1:ℂ) else 0) * ((eucNorm x : ℂ) ^ (2*n))⁻¹‖
        + ‖(n:ℂ) * star (x k) * x j * ((eucNorm x : ℂ) ^ (2*n+2))⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / (eucNorm x) ^ (2*n) + (n:ℝ) / (eucNorm x) ^ (2*n) := add_le_add h1 h2
    _ = ((n:ℝ)+1) / (eucNorm x) ^ (2*n) := by ring

lemma integrable_of_eucNorm_bound {n : ℕ} (hn : 0 < n) {f : (Fin n → ℂ) → ℂ} {M ρ : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ x, ‖f x‖ ≤ M / (eucNorm x) ^ (2*n - 1))
    (hsupp : ∀ x, ρ ≤ ‖x‖ → f x = 0) : Integrable f volume := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const]
    ring
  have hd : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := by rw [hfr]; omega
  have hα : 2 * (n : ℝ) - 1 < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    rw [hfr]; push_cast; linarith
  have hIntOn : IntegrableOn f (Metric.ball (0:Fin n → ℂ) (ρ + 1)) volume := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := |M|) (α := 2 * (n : ℝ) - 1)
      hd hα ?_ hf
    filter_upwards with x
    by_cases hx : x = (0 : Fin n → ℂ)
    · subst hx
      have h0 : ‖f 0‖ = 0 := by
        have h := hbound 0
        rw [eucNorm_zero, zero_pow (by omega : 2*n - 1 ≠ 0), div_zero] at h
        have : f 0 = 0 := norm_le_zero_iff.mp h
        rw [this, norm_zero]
      have hzr : (0:ℝ) ^ (-(2*(n:ℝ)-1)) = 0 := by
        apply Real.zero_rpow
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        intro hc; linarith
      rw [h0, norm_zero, hzr, mul_zero]
    have hEnn : 0 < eucNorm x := eucNorm_pos hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hexp : (-(2 * (n : ℝ) - 1)) = -(((2*n - 1 : ℕ)) : ℝ) := by
      have h2 : ((2*n - 1 : ℕ) : ℝ) = 2*(n:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*n)]; push_cast; ring
      rw [h2]
    calc ‖f x‖ ≤ M / (eucNorm x) ^ (2*n - 1) := hbound x
      _ ≤ |M| / (eucNorm x) ^ (2*n - 1) :=
          div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| / ‖x‖ ^ (2*n - 1) := by
          refine div_le_div_of_nonneg_left (abs_nonneg M) (by positivity) ?_
          exact pow_le_pow_left₀ (norm_nonneg x) (pi_norm_le_eucNorm x) _
      _ = |M| * ‖x‖ ^ (-(2 * (n : ℝ) - 1)) := by
          rw [hexp, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast, div_eq_mul_inv]
  refine hIntOn.integrable_of_forall_notMem_eq_zero (fun x hx => hsupp x ?_)
  have : ¬ (‖x‖ < ρ + 1) := fun h => hx (by rwa [Metric.mem_ball, dist_zero_right])
  linarith

lemma integrable_bmDbarKernel_mul {n : ℕ} (hn : 0 < n) (j k : Fin n) {h : (Fin n → ℂ) → ℂ}
    {M ρ : ℝ} (hh : ContDiff ℝ 1 h) (hM : ∀ x, ‖h x‖ ≤ M * eucNorm x)
    (hsupp : ∀ x, ρ ≤ ‖x‖ → h x = 0) :
    Integrable (fun x => bmDbarKernel j k x * h x) volume := by
  have haesm : AEStronglyMeasurable (fun x => bmDbarKernel j k x * h x) volume :=
    ((measurable_bmDbarKernel j k).mul hh.continuous.measurable).aestronglyMeasurable
  refine integrable_of_eucNorm_bound hn haesm (M := ((n:ℝ)+1) * |M|) (ρ := ρ) ?_ ?_
  · intro x
    by_cases hx : x = 0
    · subst hx
      have hh0 : h 0 = 0 := by
        have hh := hM 0
        rw [eucNorm_zero, mul_zero] at hh
        exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg (h 0)))
      rw [hh0, mul_zero, norm_zero]
      rw [eucNorm_zero, zero_pow (by omega : 2*n - 1 ≠ 0), div_zero]
    · have hE : 0 < eucNorm x := eucNorm_pos hx
      have hbd := norm_bmDbarKernel_le j k hx
      have hMx : ‖h x‖ ≤ |M| * eucNorm x :=
        (hM x).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (eucNorm_nonneg x))
      have hstep : ‖bmDbarKernel j k x‖ * ‖h x‖
          ≤ (((n:ℝ)+1) / (eucNorm x) ^ (2*n)) * (|M| * eucNorm x) :=
        mul_le_mul hbd hMx (norm_nonneg _) (by positivity)
      calc ‖bmDbarKernel j k x * h x‖ = ‖bmDbarKernel j k x‖ * ‖h x‖ := norm_mul _ _
        _ ≤ (((n:ℝ)+1) / (eucNorm x) ^ (2*n)) * (|M| * eucNorm x) := hstep
        _ = ((n:ℝ)+1) * |M| / (eucNorm x) ^ (2*n - 1) := by
              have hp : (eucNorm x) ^ (2*n) = (eucNorm x) ^ (2*n - 1) * eucNorm x := by
                conv_lhs => rw [show (2*n : ℕ) = 2*n - 1 + 1 by omega]
                rw [pow_succ]
              rw [div_eq_mul_inv, div_eq_mul_inv, hp, mul_inv]
              field_simp
  · intro x hx
    rw [hsupp x hx, mul_zero]



lemma hasCompactSupport_of_norm_le' {n : ℕ} {f : (Fin n → ℂ) → ℂ} {R : ℝ}
    (h : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  push Not at hcon
  exact hx (h x hcon.le)

lemma integrable_mul_of_hasCompactSupport' {n : ℕ} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x => a x * b x) volume :=
  (ha.mul hb).integrable_of_hasCompactSupport (hbc.mul_left (f := a))

/-- A continuous function times a continuous compactly supported one is integrable
(the support may be carried by either factor). -/
lemma integrable_mul_of_hasCompactSupport_left {n : ℕ} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hac : HasCompactSupport a) :
    Integrable (fun x => a x * b x) volume := by
  have h1 : Integrable (fun x => b x * a x) volume :=
    integrable_mul_of_hasCompactSupport' hb ha hac
  simpa only [mul_comm] using h1

lemma hasCompactSupport_fderiv_apply' {n : ℕ} {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0) (v : Fin n → ℂ) :
    HasCompactSupport (fun x => fderiv ℝ g x v) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin n → ℂ) R) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  rw [Function.mem_support] at hx
  apply hx
  have hopen : {y : Fin n → ℂ | R < ‖y‖} ∈ 𝓝 x :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) hcon
  have heq : g =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
    filter_upwards [hopen] with y hy
    exact hsupp y hy.le
  rw [heq.fderiv_eq]
  simp

lemma integrable_of_eucNorm_bound' {n : ℕ} {F : Type*} [NormedAddCommGroup F] (hn : 0 < n)
    {f : (Fin n → ℂ) → F} {M ρ : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ x, ‖f x‖ ≤ M / (eucNorm x) ^ (2*n - 1))
    (hsupp : ∀ x, ρ ≤ ‖x‖ → f x = 0) : Integrable f volume := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Finset.sum_const]
    ring
  have hd : 1 ≤ Module.finrank ℝ (Fin n → ℂ) := by rw [hfr]; omega
  have hα : 2 * (n : ℝ) - 1 < (Module.finrank ℝ (Fin n → ℂ) : ℝ) := by
    rw [hfr]; push_cast; linarith
  have hIntOn : IntegrableOn f (Metric.ball (0:Fin n → ℂ) (ρ + 1)) volume := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := |M|) (α := 2 * (n : ℝ) - 1)
      hd hα ?_ hf
    filter_upwards with x
    by_cases hx : x = (0 : Fin n → ℂ)
    · subst hx
      have h0 : ‖f 0‖ = 0 := by
        have h := hbound 0
        rw [eucNorm_zero, zero_pow (by omega : 2*n - 1 ≠ 0), div_zero] at h
        have : f 0 = 0 := norm_le_zero_iff.mp h
        rw [this, norm_zero]
      have hzr : (0:ℝ) ^ (-(2*(n:ℝ)-1)) = 0 := by
        apply Real.zero_rpow
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        intro hc; linarith
      rw [h0, norm_zero, hzr, mul_zero]
    · have hEnn : 0 < eucNorm x := eucNorm_pos hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hexp : (-(2 * (n : ℝ) - 1)) = -(((2*n - 1 : ℕ)) : ℝ) := by
        have h2 : ((2*n - 1 : ℕ) : ℝ) = 2*(n:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2*n)]; push_cast; ring
        rw [h2]
      calc ‖f x‖ ≤ M / (eucNorm x) ^ (2*n - 1) := hbound x
        _ ≤ |M| / (eucNorm x) ^ (2*n - 1) :=
            div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
        _ ≤ |M| / ‖x‖ ^ (2*n - 1) := by
            refine div_le_div_of_nonneg_left (abs_nonneg M) (by positivity) ?_
            exact pow_le_pow_left₀ (norm_nonneg x) (pi_norm_le_eucNorm x) _
        _ = |M| * ‖x‖ ^ (-(2 * (n : ℝ) - 1)) := by
            rw [hexp, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast, div_eq_mul_inv]
  refine hIntOn.integrable_of_forall_notMem_eq_zero (fun x hx => hsupp x ?_)
  have : ¬ (‖x‖ < ρ + 1) := fun h => hx (by rwa [Metric.mem_ball, dist_zero_right])
  linarith

/-- The majorant `((n+1)‖h‖ / ‖·‖^{2n})` used to dominate the regularised `∂̄`-kernel is
integrable when `h` vanishes at the origin and has compact support. -/
lemma integrable_eucNorm_majorant {n : ℕ} (hn : 0 < n) {h : (Fin n → ℂ) → ℂ} {M ρ : ℝ}
    (hh : ContDiff ℝ 1 h) (hM : ∀ x, ‖h x‖ ≤ M * eucNorm x)
    (hsupp : ∀ x, ρ ≤ ‖x‖ → h x = 0) :
    Integrable (fun x : Fin n → ℂ => ((n:ℝ)+1) * ‖h x‖ / (eucNorm x) ^ (2*n)) volume := by
  have haesm : AEStronglyMeasurable
      (fun x : Fin n → ℂ => ((n:ℝ)+1) * ‖h x‖ / (eucNorm x) ^ (2*n)) volume :=
    ((measurable_const.mul hh.continuous.measurable.norm).div
      (continuous_eucNorm.pow (2*n)).measurable).aestronglyMeasurable
  refine integrable_of_eucNorm_bound' hn haesm (M := ((n:ℝ)+1) * |M|) (ρ := ρ) ?_ ?_
  · intro x
    by_cases hx : x = 0
    · subst hx
      have hh0 : h 0 = 0 := by
        have hh' := hM 0
        rw [eucNorm_zero, mul_zero] at hh'
        exact norm_le_zero_iff.mp hh'
      rw [hh0, norm_zero, mul_zero, zero_div, norm_zero]
      rw [eucNorm_zero, zero_pow (by omega : 2*n - 1 ≠ 0), div_zero]
    · have hE : 0 < eucNorm x := eucNorm_pos hx
      have hMx : ‖h x‖ ≤ |M| * eucNorm x :=
        (hM x).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (eucNorm_nonneg x))
      have h1 : ((n:ℝ)+1) * ‖h x‖ / (eucNorm x)^(2*n)
          ≤ ((n:ℝ)+1) * (|M| * eucNorm x) / (eucNorm x)^(2*n) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMx (by positivity)) (by positivity)
      have h2 : ((n:ℝ)+1) * (|M| * eucNorm x) / (eucNorm x)^(2*n)
          = ((n:ℝ)+1) * |M| / (eucNorm x)^(2*n-1) := by
        have hp : (eucNorm x)^(2*n) = (eucNorm x)^(2*n-1) * eucNorm x := by
          conv_lhs => rw [show (2*n : ℕ) = 2*n-1+1 by omega]
          rw [pow_succ]
        rw [hp]
        field_simp
      rw [Real.norm_of_nonneg (by positivity)]
      exact h1.trans (le_of_eq h2)
  · intro x hx
    rw [hsupp x hx, norm_zero, mul_zero, zero_div]

lemma integrable_bmDbarKernel_mul' {n : ℕ} (hn : 0 < n) (j k : Fin n) {h : (Fin n → ℂ) → ℂ}
    {M ρ : ℝ} (hh : ContDiff ℝ 1 h) (hM : ∀ x, ‖h x‖ ≤ M * eucNorm x)
    (hsupp : ∀ x, ρ ≤ ‖x‖ → h x = 0) :
    Integrable (fun x => bmDbarKernel j k x * h x) volume := by
  have haesm : AEStronglyMeasurable (fun x => bmDbarKernel j k x * h x) volume :=
    ((measurable_bmDbarKernel j k).mul hh.continuous.measurable).aestronglyMeasurable
  refine integrable_of_eucNorm_bound' hn haesm (M := ((n:ℝ)+1) * |M|) (ρ := ρ) ?_ ?_
  · intro x
    by_cases hx : x = 0
    · subst hx
      have hh0 : h 0 = 0 := by
        have hh' := hM 0
        rw [eucNorm_zero, mul_zero] at hh'
        exact norm_le_zero_iff.mp hh'
      rw [hh0, mul_zero, norm_zero]
      rw [eucNorm_zero, zero_pow (by omega : 2*n - 1 ≠ 0), div_zero]
    · have hE : 0 < eucNorm x := eucNorm_pos hx
      have hbd := norm_bmDbarKernel_le j k hx
      have hMx : ‖h x‖ ≤ |M| * eucNorm x :=
        (hM x).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (eucNorm_nonneg x))
      have hstep : ‖bmDbarKernel j k x‖ * ‖h x‖
          ≤ (((n:ℝ)+1) / (eucNorm x) ^ (2*n)) * (|M| * eucNorm x) :=
        mul_le_mul hbd hMx (norm_nonneg _) (by positivity)
      calc ‖bmDbarKernel j k x * h x‖ = ‖bmDbarKernel j k x‖ * ‖h x‖ := norm_mul _ _
        _ ≤ (((n:ℝ)+1) / (eucNorm x) ^ (2*n)) * (|M| * eucNorm x) := hstep
        _ = ((n:ℝ)+1) * |M| / (eucNorm x) ^ (2*n - 1) := by
              have hp : (eucNorm x) ^ (2*n) = (eucNorm x) ^ (2*n - 1) * eucNorm x := by
                conv_lhs => rw [show (2*n : ℕ) = 2*n - 1 + 1 by omega]
                rw [pow_succ]
              rw [div_eq_mul_inv, div_eq_mul_inv, hp, mul_inv]
              field_simp
  · intro x hx
    rw [hsupp x hx, mul_zero]


lemma integrable_bmKernel_mul_dbarCoord_gen {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous (Work.CR.Flat.dbarCoord j f))
    (hfs : HasCompactSupport (Work.CR.Flat.dbarCoord j f)) :
    Integrable (fun x => bmKernel k x * Work.CR.Flat.dbarCoord j f x) := by
  have h1 : Integrable (fun x => Work.CR.Flat.dbarCoord j f x • bmKernel k x) :=
    (locallyIntegrable_bmKernel hn k).integrable_smul_left_of_hasCompactSupport hf hfs
  simpa only [smul_eq_mul, mul_comm] using h1

lemma tendsto_integral_bmKerEps_mul_dbarCoord {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {f : (Fin n → ℂ) → ℂ} {R : ℝ} (hf : ContDiff ℝ 1 f) (hfs : ∀ x, R ≤ ‖x‖ → f x = 0) :
    Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j f x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j f x)) := by
  have hfdc : Continuous (Work.CR.Flat.dbarCoord j f) := continuous_dbarCoord hf j
  have hfsd : HasCompactSupport (Work.CR.Flat.dbarCoord j f) := hasCompactSupport_dbarCoord hfs j
  have hint : Integrable (fun x => bmKernel k x * Work.CR.Flat.dbarCoord j f x) :=
    integrable_bmKernel_mul_dbarCoord_gen hn j k hfdc hfsd
  have hbdd : Integrable (fun x => ‖bmKernel k x * Work.CR.Flat.dbarCoord j f x‖) := hint.norm
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖bmKernel k x * Work.CR.Flat.dbarCoord j f x‖) ?_ ?_ hbdd ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_bmKerEps k (ne_of_gt hε)).mul hfdc).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with x
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_bmKerEps_le k ε x) (norm_nonneg _)
  · filter_upwards with x
    exact (bmKerEps_tendsto k x).mul_const (Work.CR.Flat.dbarCoord j f x)

/-- Integration by parts for the regularised kernel. -/
lemma integral_bmKerEps_mul_dbarCoord_eq_neg {n : ℕ} (j k : Fin n) {ε : ℝ} (hε : 0 < ε)
    {g : (Fin n → ℂ) → ℂ} {R : ℝ} (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x, R ≤ ‖x‖ → g x = 0) :
    ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j g x
      = -∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * g x := by
  have hker : ContDiff ℝ 1 (bmKerEps k ε) := contDiff_one_bmKerEps' k hε
  have hkerd : Continuous (fun x => fderiv ℝ (bmKerEps k ε) x (Pi.single j (1:ℂ))) :=
    (hker.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hkerdI : Continuous (fun x => fderiv ℝ (bmKerEps k ε) x (Pi.single j (Complex.I))) :=
    (hker.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgc : HasCompactSupport g := hasCompactSupport_of_norm_le' hsupp
  have hgdc : Continuous (fun x => fderiv ℝ g x (Pi.single j (1:ℂ))) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgdIc : Continuous (fun x => fderiv ℝ g x (Pi.single j (Complex.I))) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  refine Work.CR.Flat.integral_mul_dbarCoord_eq_neg j hker hg ?_ ?_ ?_ ?_ ?_
  · exact integrable_mul_of_hasCompactSupport' hkerd hg.continuous hgc
  · exact integrable_mul_of_hasCompactSupport' hkerdI hg.continuous hgc
  · exact integrable_mul_of_hasCompactSupport' hker.continuous hgdc
      (hasCompactSupport_fderiv_apply' hsupp _)
  · exact integrable_mul_of_hasCompactSupport' hker.continuous hgdIc
      (hasCompactSupport_fderiv_apply' hsupp _)
  · exact integrable_mul_of_hasCompactSupport' hker.continuous hg.continuous hgc

/-- `∫ ∂̄_j F = 0` for a `C¹` function with compact support. -/
lemma integral_dbarCoord_eq_zero {n : ℕ} (j : Fin n) {F : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hF : ContDiff ℝ 1 F) (hFs : ∀ x, R ≤ ‖x‖ → F x = 0) :
    ∫ x, Work.CR.Flat.dbarCoord j F x = 0 := by
  have hFc : HasCompactSupport F := hasCompactSupport_of_norm_le' hFs
  have hFd : Continuous (fun x => fderiv ℝ F x (Pi.single j (1:ℂ))) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hFdI : Continuous (fun x => fderiv ℝ F x (Pi.single j (Complex.I))) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1u : Integrable (fun x => fderiv ℝ F x (Pi.single j (1:ℂ)) * (fun _ : Fin n → ℂ => (1:ℂ)) x) := by
    simpa only [Pi.one_apply, mul_one] using
      hFd.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_apply' hFs _)
  have hIu : Integrable (fun x => fderiv ℝ F x (Pi.single j (Complex.I)) * (fun _ : Fin n → ℂ => (1:ℂ)) x) := by
    simpa only [Pi.one_apply, mul_one] using
      hFdI.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_apply' hFs _)
  have h1v : Integrable (fun x => F x * fderiv ℝ (fun _ : Fin n → ℂ => (1:ℂ)) x (Pi.single j (1:ℂ))) := by
    have hz : (fun x => F x * fderiv ℝ (fun _ : Fin n → ℂ => (1:ℂ)) x (Pi.single j (1:ℂ))) = 0 := by
      funext x; simp
    rw [hz]; exact integrable_zero _ _ _
  have hIv : Integrable (fun x => F x * fderiv ℝ (fun _ : Fin n → ℂ => (1:ℂ)) x (Pi.single j (Complex.I))) := by
    have hz : (fun x => F x * fderiv ℝ (fun _ : Fin n → ℂ => (1:ℂ)) x (Pi.single j (Complex.I))) = 0 := by
      funext x; simp
    rw [hz]; exact integrable_zero _ _ _
  have huv : Integrable (fun x => F x * (fun _ : Fin n → ℂ => (1:ℂ)) x) := by
    simpa only [Pi.one_apply, mul_one] using hF.continuous.integrable_of_hasCompactSupport hFc
  have h := Work.CR.Flat.integral_mul_dbarCoord_eq_neg (n := n) (k := j) (u := F)
    (v := fun _ : Fin n → ℂ => (1:ℂ)) hF contDiff_const h1u hIu h1v hIv huv
  have hlhs : ∫ x, F x * Work.CR.Flat.dbarCoord j (fun _ : Fin n → ℂ => (1:ℂ)) x = 0 := by
    rw [show (fun x => F x * Work.CR.Flat.dbarCoord j (fun _ : Fin n → ℂ => (1:ℂ)) x)
          = (fun _ => (0:ℂ)) from by
      funext x; rw [BmEpsAux.dbarCoord_const]; simp]
    exact integral_zero _ _
  have hrhs : ∫ x, Work.CR.Flat.dbarCoord j F x * (fun _ : Fin n → ℂ => (1:ℂ)) x
      = ∫ x, Work.CR.Flat.dbarCoord j F x := by simp
  rw [hlhs, hrhs] at h
  exact neg_eq_zero.mp h.symm





open Work.CR.Flat.Cauchy

lemma contDiff_nrmSq' {n : ℕ} : ContDiff ℝ 1 (fun x : Fin n → ℂ => nrmSq x) := by
  have h : (fun x : Fin n → ℂ => nrmSq x) = fun x => ∑ i : Fin n, ‖x i‖ ^ 2 := rfl
  rw [h]
  refine ContDiff.sum (s := Finset.univ) (fun i _ => ?_)
  have h2 : (fun x : Fin n → ℂ => ‖x i‖ ^ 2)
      = (fun y : ℂ => ‖y‖ ^ 2) ∘
          ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := rfl
  rw [h2]
  exact (contDiff_norm_sq ℂ (E := ℂ) (n := 1)).comp
    (((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ).contDiff (𝕜 := ℝ))

noncomputable def cutPsi {n : ℕ} (R : ℝ) : (Fin n → ℂ) → ℂ :=
  fun x => ((cutProfile (nrmSq x / (4 * R ^ 2)) : ℝ) : ℂ)

lemma contDiff_cutPsi {n : ℕ} {R : ℝ} (_hR : 0 < R) : ContDiff ℝ 1 (cutPsi (n := n) R) := by
  have hden : ContDiff ℝ 1 (fun x : Fin n → ℂ => nrmSq x / (4 * R ^ 2)) :=
    contDiff_nrmSq'.div_const _
  exact Complex.ofRealCLM.contDiff.comp (contDiff_cutProfile.comp hden)

lemma cutPsi_eq_one {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin n → ℂ} (hx : eucNorm x ≤ R) :
    cutPsi (n := n) R x = 1 := by
  have h1 : nrmSq x ≤ R ^ 2 := by
    rw [nrmSq_eq_eucNorm_sq]; nlinarith [eucNorm_nonneg x, hx]
  have h2 : 2 * (nrmSq x / (4 * R ^ 2)) ≤ 1 := by
    rw [show 2 * (nrmSq x / (4 * R ^ 2)) = nrmSq x / (2 * R ^ 2) from by ring,
      div_le_one (by positivity)]
    linarith [sq_nonneg R]
  rw [cutPsi, cutProfile_of_two_mul_le_one h2]
  simp

lemma cutPsi_eq_zero {n : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin n → ℂ} (hx : 2*R ≤ eucNorm x) :
    cutPsi (n := n) R x = 0 := by
  have h1 : 1 ≤ nrmSq x / (4 * R ^ 2) := by
    rw [one_le_div (by positivity : (0:ℝ) < 4 * R ^ 2), nrmSq_eq_eucNorm_sq]
    nlinarith [eucNorm_nonneg x, hx]
  rw [cutPsi, cutProfile_of_one_le h1]
  simp





open Work.CR.Flat.Cauchy

lemma tendsto_integral_dbarCoord_bmKerEps_mul {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {h : (Fin n → ℂ) → ℂ} {R : ℝ} (hh : ContDiff ℝ 1 h) (h0 : h 0 = 0)
    (hsupp : ∀ x, R ≤ ‖x‖ → h x = 0) :
    Tendsto (fun ε : ℝ => ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * h x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x, bmDbarKernel j k x * h x)) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_eucNorm_of_contDiff (ρ := max R 0)
    (le_max_right _ _) hh (fun x hx => hsupp x (le_trans (le_max_left R 0) hx)) h0
  set Φ : (Fin n → ℂ) → ℝ := fun x => ((n:ℝ)+1) * ‖h x‖ / (eucNorm x) ^ (2*n) with hΦ
  have hsupp' : ∀ x, max R 0 ≤ ‖x‖ → h x = 0 :=
    fun x hx => hsupp x (le_trans (le_max_left R 0) hx)
  have hΦint : Integrable Φ volume := integrable_eucNorm_majorant hn hh hM hsupp'
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence Φ ?_ ?_ hΦint ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_dbarCoord (contDiff_one_bmKerEps' k hε) j).mul hh.continuous).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with x
    by_cases hx : x = 0
    · subst hx
      rw [h0, mul_zero, norm_zero]
      simp only [hΦ, h0, norm_zero, mul_zero, zero_div]
      exact le_refl 0
    · rw [hΦ, norm_mul]
      calc ‖Work.CR.Flat.dbarCoord j (bmKerEps k ε) x‖ * ‖h x‖
          ≤ (((n:ℝ)+1) / (eucNorm x)^(2*n)) * ‖h x‖ :=
            mul_le_mul_of_nonneg_right (norm_dbarCoord_bmKerEps_le hε j k hx) (norm_nonneg _)
        _ = ((n:ℝ)+1) * ‖h x‖ / (eucNorm x)^(2*n) := by ring
  · filter_upwards with x
    by_cases hx : x = 0
    · subst hx
      rw [h0]
      simp only [mul_zero]
      exact tendsto_const_nhds
    · exact (tendsto_dbarCoord_bmKerEps j k hx).mul_const (h x)





open Work.CR.Flat.Cauchy

lemma integral_bmKernel_mul_dbarCoord_aux {n : ℕ} (hn : 0 < n) (j k : Fin n)
    {g : (Fin n → ℂ) → ℂ} {R : ℝ} (hR : 0 < R) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) :
    (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j g x)
      = (-∫ x in eucBall (4 * R), bmDbarKernel j k x * (g x - g 0))
        - ((∫ x in eucBall (4 * R), bmDbarKernel j k x * (1 - cutPsi (n := n) R x))
            - (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j (cutPsi (n := n) R) x)) * g 0 := by
  set Ψ : (Fin n → ℂ) → ℂ := cutPsi (n := n) R with hΨdef
  set ĥ : (Fin n → ℂ) → ℂ := fun x => g x - g 0 * Ψ x with hĥdef
  have h2R : (0:ℝ) < 2*R := by linarith
  have hΨc : ContDiff ℝ 1 Ψ := by rw [hΨdef]; exact contDiff_cutPsi hR
  have hΨ1 : ∀ x, eucNorm x ≤ R → Ψ x = 1 := by intro x hx; rw [hΨdef]; exact cutPsi_eq_one hR hx
  have hΨ0 : ∀ x, 2*R ≤ eucNorm x → Ψ x = 0 := by intro x hx; rw [hΨdef]; exact cutPsi_eq_zero hR hx
  have hĥc : ContDiff ℝ 1 ĥ := by rw [hĥdef]; exact hg.sub (contDiff_const.mul hΨc)
  have hĥ0 : ĥ 0 = 0 := by
    show g 0 - g 0 * Ψ 0 = 0
    rw [hΨ1 0 (by rw [eucNorm_zero]; linarith)]; ring
  have hĥsupp : ∀ x, 2*R ≤ eucNorm x → ĥ x = 0 := by
    intro x hx
    show g x - g 0 * Ψ x = 0
    rw [hsupp x (by linarith), hΨ0 x hx]; ring
  have hΨ0n : ∀ x, 2*R ≤ ‖x‖ → Ψ x = 0 :=
    fun x hx => hΨ0 x (le_trans hx (pi_norm_le_eucNorm x))
  have hĥsuppn : ∀ x, 2*R ≤ ‖x‖ → ĥ x = 0 :=
    fun x hx => hĥsupp x (le_trans hx (pi_norm_le_eucNorm x))
  have hΨcpt : HasCompactSupport Ψ := hasCompactSupport_of_norm_le' hΨ0n
  set A : ℂ := ∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j Ψ x with hAdef
  set B : ℂ := ∫ x, bmDbarKernel j k x * ĥ x with hBdef
  set D : ℂ := ∫ x in eucBall (4*R), bmDbarKernel j k x * (1 - Ψ x) with hDdef
  -- limit statements
  have hsuppn : ∀ x, R ≤ ‖x‖ → g x = 0 :=
    fun x hx => hsupp x (le_trans hx (pi_norm_le_eucNorm x))
  have hL : Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j g x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j g x)) :=
    tendsto_integral_bmKerEps_mul_dbarCoord hn j k hg hsuppn
  have hAt : Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j Ψ x)
      (𝓝[>] (0:ℝ)) (𝓝 A) := by
    rw [hAdef]; exact tendsto_integral_bmKerEps_mul_dbarCoord hn j k hΨc hΨ0n
  have hBt : Tendsto (fun ε : ℝ => ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x)
      (𝓝[>] (0:ℝ)) (𝓝 B) := by
    rw [hBdef]; exact tendsto_integral_dbarCoord_bmKerEps_mul hn j k hĥc hĥ0 hĥsuppn
  -- the pointwise identity
  have hkey : ∀ ε : ℝ, 0 < ε → ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j g x
      = (-(g 0)) * (-∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j Ψ x)
        - ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x := by
    intro ε hε
    have hker : ContDiff ℝ 1 (bmKerEps k ε) := contDiff_one_bmKerEps' k hε
    have hkerd : Continuous (fun x => Work.CR.Flat.dbarCoord j (bmKerEps k ε) x) :=
      continuous_dbarCoord hker j
    have hkerdΨ : Continuous (fun x => Work.CR.Flat.dbarCoord j Ψ x) := continuous_dbarCoord hΨc j
    have hint1 : Integrable (fun x => Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x) :=
      integrable_mul_of_hasCompactSupport_left hkerdΨ hker.continuous
        (hasCompactSupport_dbarCoord hΨ0n j)
    have hint2 : Integrable (fun x => Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x) :=
      integrable_mul_of_hasCompactSupport_left hΨc.continuous hkerd hΨcpt
    have hprod : ∫ x, Work.CR.Flat.dbarCoord j (fun y => Ψ y * bmKerEps k ε y) x = 0 := by
      refine integral_dbarCoord_eq_zero j (R := 2*R) (hΨc.mul hker) ?_
      intro x hx; rw [hΨ0n x hx, zero_mul]
    have hexp : (fun x => Work.CR.Flat.dbarCoord j (fun y => Ψ y * bmKerEps k ε y) x)
        = (fun x => Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x
            + Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x) := by
      funext x
      rw [Work.CR.Flat.Polydisc.dbarCoord_mul j Ψ (bmKerEps k ε) x
        (hΨc.differentiable (by norm_num)).differentiableAt
        (hker.differentiable (by norm_num)).differentiableAt]
    have hpsi : ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x
        = -∫ x, Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x := by
      have hsum : (∫ x, Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x)
          + (∫ x, Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x) = 0 := by
        calc (∫ x, Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x)
              + (∫ x, Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x)
            = ∫ x, (Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x
                + Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x) :=
              (integral_add hint1 hint2).symm
          _ = ∫ x, Work.CR.Flat.dbarCoord j (fun y => Ψ y * bmKerEps k ε y) x := by
              refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
              exact (congrFun hexp x).symm
          _ = 0 := hprod
      have hswap : ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x
          = ∫ x, Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x
            = Ψ x * Work.CR.Flat.dbarCoord j (bmKerEps k ε) x
        rw [mul_comm]
      rw [hswap]
      exact eq_neg_of_add_eq_zero_right hsum
    have hcomm : ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j Ψ x
        = ∫ x, Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      show bmKerEps k ε x * Work.CR.Flat.dbarCoord j Ψ x
          = Work.CR.Flat.dbarCoord j Ψ x * bmKerEps k ε x
      rw [mul_comm]
    have hint3 : Integrable (fun x => Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x) :=
      integrable_mul_of_hasCompactSupport' hkerd hΨc.continuous hΨcpt
    have hint4 : Integrable (fun x => Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x) :=
      integrable_mul_of_hasCompactSupport' hkerd hĥc.continuous
        (hasCompactSupport_of_norm_le' hĥsuppn)
    have hsplit : (∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * g x)
        = g 0 * (∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x)
          + (∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x) := by
      have hcongr : ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * g x
          = ∫ x, (g 0 * (Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * Ψ x)
              + Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [hĥdef]; ring
      rw [hcongr, integral_add (hint3.const_mul _) hint4, integral_const_mul]
    rw [integral_bmKerEps_mul_dbarCoord_eq_neg j k hε hg hsuppn, hsplit, hpsi, hcomm]
    ring
  -- limits
  have hRHS : Tendsto (fun ε : ℝ => (-(g 0)) * (-∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j Ψ x)
        - ∫ x, Work.CR.Flat.dbarCoord j (bmKerEps k ε) x * ĥ x) (𝓝[>] (0:ℝ)) (𝓝 (g 0 * A - B)) := by
    have h2 := (hAt.neg.const_mul (-(g 0))).sub hBt
    have h3 : (-(g 0)) * (-A) - B = g 0 * A - B := by ring
    rwa [h3] at h2
  have hL' : Tendsto (fun ε : ℝ => ∫ x, bmKerEps k ε x * Work.CR.Flat.dbarCoord j g x)
      (𝓝[>] (0:ℝ)) (𝓝 (g 0 * A - B)) := by
    refine hRHS.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hkey ε hε).symm
  have hmain : (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j g x) = g 0 * A - B :=
    tendsto_nhds_unique hL hL'
  -- B = ∫_{eucBall 4R} bmDbarKernel jk ĥ
  have hBeq : ∫ x in eucBall (4*R), bmDbarKernel j k x * ĥ x = B := by
    rw [hBdef, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [mem_eucBall] at hx
    push Not at hx
    rw [hĥsupp x (by linarith), mul_zero]
  -- ∫_{eucBall 4R} bmDbarKernel jk (g - g0) = B - g0 * D
  obtain ⟨Mb, hMb, hMbb⟩ := exists_norm_le_eucNorm_of_contDiff (ρ := max (2*R) 0)
    (le_max_right _ _) hĥc (fun x hx => hĥsuppn x (le_trans (le_max_left _ _) hx)) hĥ0
  have hintB : Integrable (fun x => bmDbarKernel j k x * ĥ x) :=
    integrable_bmDbarKernel_mul' hn j k hĥc hMbb hĥsuppn
  have hintD : IntegrableOn (fun x => bmDbarKernel j k x * (1 - Ψ x)) (eucBall (4*R)) := by
    refine IntegrableOn.of_bound ?_ ?_ (2*(((n:ℝ)+1)/R^(2*n))) ?_
    · exact lt_of_le_of_lt (measure_mono (eucBall_subset_ball (n := n) (R := 4*R)))
        (measure_ball_lt_top (μ := volume) (x := (0:Fin n → ℂ)) (r := 4*R))
    · exact ((measurable_bmDbarKernel j k).mul
        (measurable_const.sub hΨc.continuous.measurable)).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' (measurableSet_eucBall (4*R))]
      refine Filter.Eventually.of_forall (fun x _ => ?_)
      by_cases hxR : eucNorm x ≤ R
      · rw [hΨ1 x hxR]
        simp only [sub_self, mul_zero, norm_zero]
        exact mul_nonneg (by norm_num)
          (le_of_lt (div_pos (by positivity : (0:ℝ) < (n:ℝ)+1) (pow_pos hR _)))
      · push Not at hxR
        have hx0 : x ≠ 0 := fun h => by rw [h, eucNorm_zero] at hxR; linarith
        have h1 : ‖bmDbarKernel j k x‖ ≤ ((n:ℝ)+1)/R^(2*n) := by
          refine (norm_bmDbarKernel_le j k hx0).trans ?_
          refine div_le_div_of_nonneg_left (by positivity) (pow_pos hR _) ?_
          exact pow_le_pow_left₀ hR.le hxR.le _
        have hPsi_le : ‖Ψ x‖ ≤ 1 := by
          rw [hΨdef, cutPsi, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (cutProfile_nonneg _)]
          exact cutProfile_le_one _
        have h2 : ‖1 - Ψ x‖ ≤ 2 := by
          calc ‖(1:ℂ) - Ψ x‖ ≤ ‖(1:ℂ)‖ + ‖Ψ x‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by rw [norm_one]; linarith
            _ = 2 := by norm_num
        calc ‖bmDbarKernel j k x * (1 - Ψ x)‖ = ‖bmDbarKernel j k x‖ * ‖1 - Ψ x‖ := norm_mul _ _
          _ ≤ (((n:ℝ)+1)/R^(2*n)) * 2 :=
              mul_le_mul h1 h2 (norm_nonneg _)
                (le_of_lt (div_pos (by positivity : (0:ℝ) < (n:ℝ)+1) (pow_pos hR _)))
          _ = 2*(((n:ℝ)+1)/R^(2*n)) := by ring
  have hkey2 : ∫ x in eucBall (4*R), bmDbarKernel j k x * (g x - g 0) = B - g 0 * D := by
    have hcongr : ∫ x in eucBall (4*R), bmDbarKernel j k x * (g x - g 0)
        = ∫ x in eucBall (4*R), (bmDbarKernel j k x * ĥ x
            - g 0 * (bmDbarKernel j k x * (1 - Ψ x))) := by
      refine setIntegral_congr_fun (measurableSet_eucBall (4*R)) (fun x _ => ?_)
      simp only [hĥdef]; ring
    rw [hcongr, integral_sub hintB.integrableOn (hintD.const_mul _), integral_const_mul, hBeq,
      ← hDdef]
  rw [hmain, hkey2]
  ring





open Work.CR.Flat.Cauchy

/-- The constant produced by the integration-by-parts computation at radius `R`. -/
noncomputable def cR {n : ℕ} (j k : Fin n) (R : ℝ) : ℂ :=
  (∫ x in eucBall (4*R), bmDbarKernel j k x * (1 - cutPsi (n:=n) R x))
    - (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j (cutPsi (n:=n) R) x)

lemma integrableOn_bmDbarKernel_mul_cutPsi {n : ℕ} (hn : 0 < n) (j k : Fin n) {ρ M : ℝ}
    (hρ : 0 < ρ) :
    IntegrableOn (fun x => bmDbarKernel j k x * (cutPsi (n:=n) (ρ/2) x - 1))
      (eucBall (n:=n) M) volume := by
  have hρ2 : 0 < ρ/2 := by linarith
  refine IntegrableOn.of_bound ?_ ?_ (2*(((n:ℝ)+1)/(ρ/2)^(2*n))) ?_
  · exact lt_of_le_of_lt (measure_mono (eucBall_subset_ball (n := n) (R := M)))
      (measure_ball_lt_top (μ := volume) (x := (0:Fin n → ℂ)) (r := M))
  · exact ((measurable_bmDbarKernel j k).mul
      (((contDiff_cutPsi (n := n) hρ2).continuous.measurable).sub measurable_const)
      ).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' (measurableSet_eucBall M)]
    refine Filter.Eventually.of_forall (fun x _ => ?_)
    by_cases hx : eucNorm x ≤ ρ/2
    · rw [cutPsi_eq_one hρ2 hx]
      simp only [sub_self, mul_zero, norm_zero]
      exact mul_nonneg (by norm_num)
        (le_of_lt (div_pos (by positivity : (0:ℝ) < (n:ℝ)+1) (pow_pos hρ2 _)))
    · push Not at hx
      have hx0 : x ≠ 0 := fun h => by rw [h, eucNorm_zero] at hx; linarith
      have h1 : ‖bmDbarKernel j k x‖ ≤ ((n:ℝ)+1)/(ρ/2)^(2*n) := by
        refine (norm_bmDbarKernel_le j k hx0).trans ?_
        refine div_le_div_of_nonneg_left (by positivity) (pow_pos hρ2 _) ?_
        exact pow_le_pow_left₀ hρ2.le hx.le _
      have hPsi : ‖cutPsi (n:=n) (ρ/2) x‖ ≤ 1 := by
        rw [cutPsi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutProfile_nonneg _)]
        exact cutProfile_le_one _
      have h2 : ‖cutPsi (n:=n) (ρ/2) x - 1‖ ≤ 2 := by
        calc ‖cutPsi (n:=n) (ρ/2) x - (1:ℂ)‖ ≤ ‖cutPsi (n:=n) (ρ/2) x‖ + ‖(1:ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [norm_one]; linarith
          _ = 2 := by norm_num
      calc ‖bmDbarKernel j k x * (cutPsi (n:=n) (ρ/2) x - 1)‖
          = ‖bmDbarKernel j k x‖ * ‖cutPsi (n:=n) (ρ/2) x - 1‖ := norm_mul _ _
        _ ≤ (((n:ℝ)+1)/(ρ/2)^(2*n)) * 2 :=
            mul_le_mul h1 h2 (norm_nonneg _)
              (le_of_lt (div_pos (by positivity : (0:ℝ) < (n:ℝ)+1) (pow_pos hρ2 _)))
        _ = 2*(((n:ℝ)+1)/(ρ/2)^(2*n)) := by ring

lemma cR_indep {n : ℕ} (hn : 0 < n) (j k : Fin n) {R R' : ℝ} (hR : 0 < R) (hR' : 0 < R') :
    cR j k R = cR j k R' := by
  set ρ := min R R' with hρdef
  have hρ0 : 0 < ρ := lt_min hR hR'
  have hρ2 : 0 < ρ/2 := by linarith
  set g : (Fin n → ℂ) → ℂ := cutPsi (n:=n) (ρ/2) with hgdef
  have hgc : ContDiff ℝ 1 g := by rw [hgdef]; exact contDiff_cutPsi hρ2
  have hg0 : g 0 = 1 := by
    rw [hgdef]; exact cutPsi_eq_one hρ2 (by rw [eucNorm_zero]; linarith)
  have hgsR : ∀ x, R ≤ eucNorm x → g x = 0 := by
    intro x hx
    rw [hgdef]
    refine cutPsi_eq_zero hρ2 ?_
    have h2 : ρ ≤ eucNorm x := le_trans (min_le_left _ _) hx
    linarith
  have hgsR' : ∀ x, R' ≤ eucNorm x → g x = 0 := by
    intro x hx
    rw [hgdef]
    refine cutPsi_eq_zero hρ2 ?_
    have h2 : ρ ≤ eucNorm x := le_trans (min_le_right _ _) hx
    linarith
  have haux1 := integral_bmKernel_mul_dbarCoord_aux hn j k hR hgc hgsR
  have haux2 := integral_bmKernel_mul_dbarCoord_aux hn j k hR' hgc hgsR'
  have hmain : cR j k R - cR j k R' =
      (∫ x in eucBall (4*R'), bmDbarKernel j k x * (g x - g 0))
        - (∫ x in eucBall (4*R), bmDbarKernel j k x * (g x - g 0)) := by
    have h := haux1.symm.trans haux2
    rw [hg0] at h ⊢
    unfold cR
    linear_combination -h
  have hInt1 : IntegrableOn (fun x => bmDbarKernel j k x * (g x - g 0)) (eucBall (4*R)) volume := by
    have h := integrableOn_bmDbarKernel_mul_cutPsi hn j k hρ0 (M := 4*R)
    rw [show (fun x => bmDbarKernel j k x * (cutPsi (n:=n) (ρ/2) x - 1))
        = (fun x => bmDbarKernel j k x * (g x - g 0)) from by funext x; rw [hg0, hgdef]] at h
    exact h
  have hInt2 : IntegrableOn (fun x => bmDbarKernel j k x * (g x - g 0)) (eucBall (4*R')) volume := by
    have h := integrableOn_bmDbarKernel_mul_cutPsi hn j k hρ0 (M := 4*R')
    rw [show (fun x => bmDbarKernel j k x * (cutPsi (n:=n) (ρ/2) x - 1))
        = (fun x => bmDbarKernel j k x * (g x - g 0)) from by funext x; rw [hg0, hgdef]] at h
    exact h
  have hgsmin : ∀ x, ρ ≤ eucNorm x → g x = 0 := by
    intro x hx
    rw [hgdef]
    exact cutPsi_eq_zero hρ2 (by linarith)
  have hshell : ∀ a b : ℝ, ρ ≤ 4*a →
      ∫ x in eucShell (4*a) (4*b), bmDbarKernel j k x * (g x - g 0) = 0 := by
    intro a b ha
    have hcongr : ∫ x in eucShell (4*a) (4*b), bmDbarKernel j k x * (g x - g 0)
        = ∫ x in eucShell (4*a) (4*b), -bmDbarKernel j k x := by
      refine setIntegral_congr_fun (measurableSet_eucShell (4*a) (4*b)) (fun x hx => ?_)
      have hxg : g x = 0 := by
        rw [mem_eucShell] at hx
        exact hgsmin x (by linarith [hx.1, ha])
      rw [hxg, hg0]
      ring
    rw [hcongr, integral_neg]
    rw [bmDbarKernel_shell_eq_zero hn (j := j) (k := k) (by linarith : (0:ℝ) < 4*a)]
    ring
  rcases le_total R R' with hle | hle
  · have hset : eucBall (n:=n) (4*R') = eucBall (n:=n) (4*R) ∪ eucShell (n:=n) (4*R) (4*R') := by
      ext x
      simp only [mem_eucBall, mem_eucShell, Set.mem_union]
      constructor
      · intro hx
        by_cases h : eucNorm x < 4*R
        · exact Or.inl h
        · exact Or.inr ⟨le_of_not_gt h, hx⟩
      · rintro (h | ⟨h1, h2⟩)
        · linarith [h, hR]
        · exact h2
    have hdisj : Disjoint (eucBall (n:=n) (4*R)) (eucShell (n:=n) (4*R) (4*R')) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      rw [mem_eucBall] at hx1
      rw [mem_eucShell] at hx2
      linarith [hx1, hx2.1]
    have hInts : IntegrableOn (fun x => bmDbarKernel j k x * (g x - g 0))
        (eucShell (n:=n) (4*R) (4*R')) volume :=
      hInt2.mono_set (by
        intro x hx
        rw [mem_eucShell] at hx
        rw [mem_eucBall]
        linarith [hx.2])
    have hunion := setIntegral_union hdisj (measurableSet_eucShell (n:=n) (4*R) (4*R')) hInt1 hInts
    have hB : (∫ x in eucBall (4*R'), bmDbarKernel j k x * (g x - g 0))
        = ∫ x in eucBall (4*R), bmDbarKernel j k x * (g x - g 0) := by
      rw [hset, hunion, hshell R R' (by linarith [min_le_left R R']), add_zero]
    exact sub_eq_zero.mp (by rw [hmain, hB, sub_self])
  · have hset : eucBall (n:=n) (4*R) = eucBall (n:=n) (4*R') ∪ eucShell (n:=n) (4*R') (4*R) := by
      ext x
      simp only [mem_eucBall, mem_eucShell, Set.mem_union]
      constructor
      · intro hx
        by_cases h : eucNorm x < 4*R'
        · exact Or.inl h
        · exact Or.inr ⟨le_of_not_gt h, hx⟩
      · rintro (h | ⟨h1, h2⟩)
        · linarith [h, hR']
        · exact h2
    have hdisj : Disjoint (eucBall (n:=n) (4*R')) (eucShell (n:=n) (4*R') (4*R)) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      rw [mem_eucBall] at hx1
      rw [mem_eucShell] at hx2
      linarith [hx1, hx2.1]
    have hInts : IntegrableOn (fun x => bmDbarKernel j k x * (g x - g 0))
        (eucShell (n:=n) (4*R') (4*R)) volume :=
      hInt1.mono_set (by
        intro x hx
        rw [mem_eucShell] at hx
        rw [mem_eucBall]
        linarith [hx.2])
    have hunion := setIntegral_union hdisj (measurableSet_eucShell (n:=n) (4*R') (4*R)) hInt2 hInts
    have hA : (∫ x in eucBall (4*R), bmDbarKernel j k x * (g x - g 0))
        = ∫ x in eucBall (4*R'), bmDbarKernel j k x * (g x - g 0) := by
      rw [hset, hunion, hshell R' R (by linarith [min_le_right R R']), add_zero]
    exact sub_eq_zero.mp (by rw [hmain, hA, sub_self])


/-- **The Bochner–Martinelli integration-by-parts identity.**  There is a kernel-dependent
constant `c j k` (independent of `g` and of the support radius `R`) such that for every `C¹`
function `g` vanishing for `eucNorm x ≥ R`,
`∫ x, bmKernel k x * ∂̄_j g x = -∫_{eucBall (4R)} bmDbarKernel j k x * (g x - g 0) - c j k * g 0`. -/
theorem integral_bmKernel_mul_dbarCoord {n : ℕ} (hn : 0 < n) :
    ∃ c : Fin n → Fin n → ℂ, ∀ (j k : Fin n) (g : (Fin n → ℂ) → ℂ) (R : ℝ), 0 < R →
      ContDiff ℝ 1 g → (∀ x : Fin n → ℂ, R ≤ eucNorm x → g x = 0) →
      (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j g x)
        = (-∫ x in eucBall (4 * R), bmDbarKernel j k x * (g x - g 0)) - c j k * g 0 := by
  refine ⟨fun j k => cR j k 1, ?_⟩
  intro j k g R hR hg hsupp
  have haux := integral_bmKernel_mul_dbarCoord_aux hn j k hR hg hsupp
  rw [show ((∫ x in eucBall (4*R), bmDbarKernel j k x * (1 - cutPsi (n:=n) R x))
      - (∫ x, bmKernel k x * Work.CR.Flat.dbarCoord j (cutPsi (n:=n) R) x)) = cR j k R from rfl]
    at haux
  rw [haux, cR_indep hn j k hR one_pos]

end Work.CR.Flat.Cauchy.bmCz
