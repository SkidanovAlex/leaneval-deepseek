import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EComparison.continuousOn_integral_left
import Submission.Work.FTS.StrongEps.EComparison.locallyIntegrableOn_mul_id
import Submission.Work.FTS.StrongEps.EComparison.contDiffOn_one_integral_left

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem EulerWeakClassical {α L b : ℝ} (hα : 0 < α) (hb : 0 < b) {W : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) {c₁ c₂ : ℝ}
    (haff : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 b)),
      -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z) + L * (∫ z in t..b, (z - t) * W z)
        = c₁ + c₂ * t) :
    ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Set.Ioo 0 b) ∧
      (∀ t ∈ Set.Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 b)] W := by
  have hαne : α ≠ 0 := ne_of_gt hα
  set I : Set ℝ := Set.Ioo 0 b with hI
  have hIopen : IsOpen I := by rw [hI]; exact isOpen_Ioo
  have hImeas : MeasurableSet I := hIopen.measurableSet
  have hIIoi : I ⊆ Set.Ioi (0 : ℝ) := by rw [hI]; exact Set.Ioo_subset_Ioi_self
  have hWz : MeasureTheory.LocallyIntegrableOn (fun z => W z * z) (Set.Ioi 0) := by
    have hfun : (fun z : ℝ => W z * z) = fun z => z * W z := by funext z; ring
    rw [hfun]
    exact locallyIntegrableOn_mul_id hW
  let GW : ℝ → ℝ := fun t => ∫ z in t..b, W z * z
  let HW : ℝ → ℝ := fun t => ∫ z in t..b, W z
  let FW : ℝ → ℝ := fun t => -(c₁ + c₂ * t) - α * (5 + α) * GW t + L * (GW t - t * HW t)
  let V : ℝ → ℝ := fun t => FW t / (α ^ 2 * t ^ 2)
  have hsplit : ∀ t ∈ Set.Ioi (0 : ℝ), (∫ z in t..b, (z - t) * W z) = GW t - t * HW t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hsub : Set.uIcc t b ⊆ Set.Ioi (0 : ℝ) := by
      rcases le_total t b with h | h
      · rw [Set.uIcc_of_le h]; intro x hx; exact lt_of_lt_of_le ht0 hx.1
      · rw [Set.uIcc_of_ge h]; intro x hx; exact lt_of_lt_of_le hb hx.1
    have hWint : MeasureTheory.IntegrableOn W (Set.uIcc t b) :=
      hW.integrableOn_compact_subset hsub isCompact_uIcc
    have hWzint : MeasureTheory.IntegrableOn (fun z => W z * z) (Set.uIcc t b) :=
      hWz.integrableOn_compact_subset hsub isCompact_uIcc
    have h1 : IntervalIntegrable W MeasureTheory.volume t b := hWint.intervalIntegrable
    have h2 : IntervalIntegrable (fun z => W z * z) MeasureTheory.volume t b :=
      hWzint.intervalIntegrable
    have h3 : IntervalIntegrable (fun z => t * W z) MeasureTheory.volume t b := h1.const_mul t
    calc ∫ z in t..b, (z - t) * W z
        = ∫ z in t..b, (W z * z - t * W z) :=
            intervalIntegral.integral_congr fun z _ => by ring
      _ = (∫ z in t..b, W z * z) - (∫ z in t..b, t * W z) :=
            intervalIntegral.integral_sub h2 h3
      _ = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z) := by
            rw [intervalIntegral.integral_const_mul]
      _ = GW t - t * HW t := by simp only [GW, HW]
  have hFWeq : FW =ᵐ[MeasureTheory.volume.restrict I] (fun t => α ^ 2 * t ^ 2 * W t) := by
    filter_upwards [haff, MeasureTheory.ae_restrict_mem hImeas] with t ht hmem
    have hsp := hsplit t hmem.1
    rw [hsp] at ht
    simp only [GW, HW, FW] at ht ⊢
    linarith
  have hVeq : V =ᵐ[MeasureTheory.volume.restrict I] W := by
    filter_upwards [hFWeq, MeasureTheory.ae_restrict_mem hImeas] with t ht hmem
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt hmem.1))
    simp only [V]
    rw [ht]
    exact mul_div_cancel_left₀ (W t) hne
  have hHWcont : ContinuousOn HW (Set.Ioi (0 : ℝ)) := by
    simp only [HW]; exact continuousOn_integral_left hb hW
  have hGWcont : ContinuousOn GW (Set.Ioi (0 : ℝ)) := by
    simp only [GW]; exact continuousOn_integral_left hb hWz
  have hFWcont : ContinuousOn FW (Set.Ioi (0 : ℝ)) := by
    simp only [FW]
    fun_prop
  have hVcont : ContinuousOn V (Set.Ioi (0 : ℝ)) := by
    simp only [V]
    have hden : ContinuousOn (fun t : ℝ => α ^ 2 * t ^ 2) (Set.Ioi 0) := by fun_prop
    exact hFWcont.div hden fun t ht =>
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht))
  let H : ℝ → ℝ := fun t => ∫ z in t..b, V z
  let G : ℝ → ℝ := fun t => ∫ z in t..b, V z * z
  let F : ℝ → ℝ := fun t => -(c₁ + c₂ * t) - α * (5 + α) * G t + L * (G t - t * H t)
  have hVGcont : ContinuousOn (fun z : ℝ => V z * z) (Set.Ioi (0 : ℝ)) :=
    hVcont.mul continuousOn_id
  have hHc1 : ContDiffOn ℝ 1 H I := (contDiffOn_one_integral_left hb hVcont).1.mono hIIoi
  have hGc1 : ContDiffOn ℝ 1 G I := (contDiffOn_one_integral_left hb hVGcont).1.mono hIIoi
  have hHderiv : ∀ t ∈ I, deriv H t = -V t :=
    fun t ht => (contDiffOn_one_integral_left hb hVcont).2 t (hIIoi ht)
  have hGderiv : ∀ t ∈ I, deriv G t = -(V t * t) :=
    fun t ht => (contDiffOn_one_integral_left hb hVGcont).2 t (hIIoi ht)
  have hFc1 : ContDiffOn ℝ 1 F I := by
    simp only [F]
    have hA : ContDiffOn ℝ 1 (fun t : ℝ => -(c₁ + c₂ * t)) I := by fun_prop
    have hB : ContDiffOn ℝ 1 (fun t : ℝ => α * (5 + α) * G t) I :=
      (contDiffOn_const (c := α * (5 + α))).mul hGc1
    have hC : ContDiffOn ℝ 1 (fun t : ℝ => L * (G t - t * H t)) I :=
      (contDiffOn_const (c := L)).mul (hGc1.sub (contDiffOn_id.mul hHc1))
    exact (hA.sub hB).add hC
  have hGH : ∀ t ∈ I, G t = GW t ∧ H t = HW t := by
    intro t ht
    have ha : (0 : ℝ) < t := ht.1
    have hab : t < b := ht.2
    have hae : ∀ᵐ x ∂(MeasureTheory.volume), x ∈ Set.uIoc t b → V x = W x := by
      have h1 : ∀ᵐ x ∂(MeasureTheory.volume), x ∈ Set.Ioo (0 : ℝ) b → V x = W x :=
        MeasureTheory.ae_imp_of_ae_restrict hVeq
      have h2 : ∀ᵐ x ∂(MeasureTheory.volume), x ≠ b := MeasureTheory.Measure.ae_ne volume b
      filter_upwards [h1, h2] with x hx1 hxb hxu
      rw [Set.uIoc_of_le hab.le] at hxu
      exact hx1 ⟨lt_trans ha hxu.1, lt_of_le_of_ne hxu.2 hxb⟩
    constructor
    · simp only [G, GW]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with x hx hxu
      rw [hx hxu]
    · simp only [H, HW]
      exact intervalIntegral.integral_congr_ae hae
  have hVF : ∀ t ∈ I, V t = F t / (α ^ 2 * t ^ 2) := by
    intro t ht
    obtain ⟨hGt, hHt⟩ := hGH t ht
    have hFeq : FW t = F t := by simp only [FW, F, hGt, hHt]
    simp only [V]
    rw [hFeq]
  have hE1 : ∀ t ∈ I, F t = α ^ 2 * t ^ 2 * V t := by
    intro t ht
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    rw [hVF t ht, mul_div_cancel₀ (F t) hne]
  have hVc1 : ContDiffOn ℝ 1 V I := by
    have hden : ContDiffOn ℝ 1 (fun t : ℝ => α ^ 2 * t ^ 2) I := by fun_prop
    have hdiv : ContDiffOn ℝ 1 (fun t : ℝ => F t / (α ^ 2 * t ^ 2)) I :=
      hFc1.div hden fun t ht =>
        mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    exact hdiv.congr fun t ht => hVF t ht
  -- Step 10: first derivative of `F`
  let DF : ℝ → ℝ := fun t => -c₂ + α * (5 + α) * (V t * t) - L * H t
  have hFderiv : ∀ t ∈ I, deriv F t = DF t := by
    intro t ht
    have hGA : HasDerivAt G (-(V t * t)) t := by
      have hd : DifferentiableAt ℝ G t :=
        (hGc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hGderiv t ht] at h
    have hHA : HasDerivAt H (-(V t)) t := by
      have hd : DifferentiableAt ℝ H t :=
        (hHc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hHderiv t ht] at h
    have hA : HasDerivAt (fun s : ℝ => -(c₁ + c₂ * s)) (-c₂) t := by
      have h1 : HasDerivAt (fun s : ℝ => c₂ * s) c₂ t := by
        have hh : HasDerivAt (fun s : ℝ => c₂ * s) (c₂ * 1) t :=
          (hasDerivAt_id t).const_mul c₂
        rw [mul_one] at hh
        exact hh
      exact (h1.const_add c₁).neg
    have hB : HasDerivAt (fun s : ℝ => α * (5 + α) * G s) (α * (5 + α) * (-(V t * t))) t :=
      hGA.const_mul (α * (5 + α))
    have hC : HasDerivAt (fun s : ℝ => L * (G s - s * H s))
        (L * (-(V t * t) - (1 * H t + t * (-(V t))))) t :=
      (hGA.sub ((hasDerivAt_id t).mul hHA)).const_mul L
    have hmain : HasDerivAt F
        (-c₂ - α * (5 + α) * (-(V t * t)) + L * (-(V t * t) - (1 * H t + t * (-(V t))))) t :=
      (hA.sub hB).add hC
    rw [hmain.deriv]
    simp only [DF]
    ring
  -- quadratic auxiliary
  have hsqderiv : ∀ t : ℝ, deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
    intro t
    have h1 : deriv (fun s : ℝ => s) t = 1 := (hasDerivAt_id t).deriv
    have h := deriv_pow (f := fun s : ℝ => s) (x := t)
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s) t) 2
    rw [h1] at h
    simpa [Nat.reduceSub, pow_one, mul_one] using h
  have hsqHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    intro t
    have hd : DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t := by fun_prop
    have h := hd.hasDerivAt
    rwa [hsqderiv t] at h
  have hquad : ∀ t : ℝ, deriv (fun s : ℝ => α ^ 2 * s ^ 2) t = 2 * α ^ 2 * t := by
    intro t
    rw [deriv_const_mul (α ^ 2) (hsqHas t).differentiableAt, hsqderiv t]
    ring
  have hquadHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => α ^ 2 * s ^ 2) (2 * α ^ 2 * t) t := by
    intro t
    have hd : DifferentiableAt ℝ (fun s : ℝ => α ^ 2 * s ^ 2) t := by fun_prop
    have h := hd.hasDerivAt
    rwa [hquad t] at h
  have hlinHas : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s) (2 * α ^ 2) t := by
    intro t
    have hh : HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s) ((2 * α ^ 2) * 1) t :=
      (hasDerivAt_id t).const_mul (2 * α ^ 2)
    rw [mul_one] at hh
    exact hh
  -- Step 11: derivative of `V` (explicitly) and `C¹` of `V`
  let DVe : ℝ → ℝ := fun t => (DF t * (α ^ 2 * t ^ 2) - F t * (2 * α ^ 2 * t)) / (α ^ 2 * t ^ 2) ^ 2
  have hDV : ∀ t ∈ I, deriv V t = DVe t := by
    intro t ht
    have hEq : V =ᶠ[𝓝 t] (fun s : ℝ => F s / (α ^ 2 * s ^ 2)) := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hVF s hs
    rw [hEq.deriv_eq]
    change deriv (F / fun s : ℝ => α ^ 2 * s ^ 2) t = DVe t
    have hFd : DifferentiableAt ℝ F t :=
      (hFc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
    have hne : α ^ 2 * t ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1))
    rw [deriv_div hFd (hquadHas t).differentiableAt hne, hFderiv t ht, hquad t]
  -- Step 12: `DF` and its derivative
  let D2F : ℝ → ℝ := fun t => α * (5 + α) * (deriv V t * t + V t) + L * V t
  have hVd : ∀ t ∈ I, HasDerivAt V (deriv V t) t :=
    fun t ht =>
      ((hVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)).hasDerivAt
  have hDFderiv : ∀ t ∈ I, deriv DF t = D2F t := by
    intro t ht
    have hHA : HasDerivAt H (-(V t)) t := by
      have hd : DifferentiableAt ℝ H t :=
        (hHc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)
      have h := hd.hasDerivAt
      rwa [hHderiv t ht] at h
    have hprod : HasDerivAt (fun s : ℝ => V s * s) (deriv V t * t + V t * 1) t :=
      (hVd t ht).mul (hasDerivAt_id t)
    have hG' : HasDerivAt (fun s : ℝ => α * (5 + α) * (V s * s))
        (α * (5 + α) * (deriv V t * t + V t * 1)) t :=
      hprod.const_mul (α * (5 + α))
    have hH' : HasDerivAt (fun s : ℝ => L * H s) (L * (-(V t))) t := hHA.const_mul L
    have hmain : HasDerivAt DF
        (0 + α * (5 + α) * (deriv V t * t + V t * 1) - L * (-(V t))) t :=
      ((hasDerivAt_const t (-c₂)).add hG').sub hH'
    rw [hmain.deriv, zero_add]
    simp only [D2F]
    ring
  have hIddF : ∀ t ∈ I, deriv (deriv F) t = D2F t := by
    intro t ht
    have hFE : deriv F =ᶠ[𝓝 t] DF := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hFderiv s hs
    rw [hFE.deriv_eq, hDFderiv t ht]
  -- Step 13: `C¹` of `DF` and of `DVe`
  have hDFc1 : ContDiffOn ℝ 1 DF I := by
    simp only [DF]
    fun_prop
  have hDVeC1 : ContDiffOn ℝ 1 DVe I := by
    have hN : ContDiffOn ℝ 1
        (fun t : ℝ => DF t * (α ^ 2 * t ^ 2) - F t * (2 * α ^ 2 * t)) I := by
      fun_prop
    have hD : ContDiffOn ℝ 1 (fun t : ℝ => (α ^ 2 * t ^ 2) ^ 2) I := by fun_prop
    simp only [DVe]
    exact hN.div hD fun t ht =>
      pow_ne_zero 2 (mul_ne_zero (pow_ne_zero 2 hαne) (pow_ne_zero 2 (ne_of_gt ht.1)))
  -- Step 14: `V` is `C²` on `I`
  have hVc2 : ContDiffOn ℝ 2 V I := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen hIopen]
    refine ⟨hVc1.differentiableOn (by norm_num), by simp, ?_⟩
    exact hDVeC1.congr fun t ht => hDV t ht
  -- Step 15: the second expression for `deriv (deriv F) t`
  let Psi : ℝ → ℝ := fun s => α ^ 2 * s ^ 2 * V s
  let Psi' : ℝ → ℝ := fun s => 2 * α ^ 2 * s * V s + α ^ 2 * s ^ 2 * deriv V s
  have hPsiHas : ∀ s ∈ I, HasDerivAt Psi ((2 * α ^ 2 * s) * V s + (α ^ 2 * s ^ 2) * deriv V s) s := by
    intro s hs
    have hVs : DifferentiableAt ℝ V s :=
      (hVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds hs)
    exact (hquadHas s).mul hVs.hasDerivAt
  have hPsideriv : ∀ s ∈ I, deriv Psi s = Psi' s := by
    intro s hs
    exact (hPsiHas s hs).deriv
  have hIIddF : ∀ t ∈ I,
      deriv (deriv F) t = 2 * α ^ 2 * V t + 4 * α ^ 2 * t * deriv V t
        + α ^ 2 * t ^ 2 * deriv (deriv V) t := by
    intro t ht
    have hFE : deriv F =ᶠ[𝓝 t] deriv Psi := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      have hEq : F =ᶠ[𝓝 s] Psi := by
        filter_upwards [hIopen.mem_nhds hs] with u hu
        simp only [Psi]
        exact hE1 u hu
      exact hEq.deriv_eq
    rw [hFE.deriv_eq]
    have hPsiEq : deriv Psi =ᶠ[𝓝 t] Psi' := by
      filter_upwards [hIopen.mem_nhds ht] with s hs
      exact hPsideriv s hs
    rw [hPsiEq.deriv_eq]
    have hdVc1 : ContDiffOn ℝ 1 (deriv V) I := hVc2.deriv_of_isOpen hIopen (by norm_num)
    have hVd' : HasDerivAt (deriv V) (deriv (deriv V) t) t :=
      ((hdVc1.differentiableOn (by norm_num)).differentiableAt (hIopen.mem_nhds ht)).hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 2 * α ^ 2 * s * V s)
        (2 * α ^ 2 * V t + 2 * α ^ 2 * t * deriv V t) t :=
      (hlinHas t).mul (hVd t ht)
    have h2 : HasDerivAt (fun s : ℝ => α ^ 2 * s ^ 2 * deriv V s)
        (2 * α ^ 2 * t * deriv V t + α ^ 2 * t ^ 2 * deriv (deriv V) t) t :=
      (hquadHas t).mul hVd'
    have hmain : HasDerivAt Psi'
        (2 * α ^ 2 * V t + 2 * α ^ 2 * t * deriv V t
          + (2 * α ^ 2 * t * deriv V t + α ^ 2 * t ^ 2 * deriv (deriv V) t)) t :=
      h1.add h2
    rw [hmain.deriv]
    ring
  refine ⟨V, hVc2, ?_, hVeq⟩
  intro t ht
  have h1 : deriv (deriv F) t = α * (5 + α) * (deriv V t * t + V t) + L * V t :=
    hIddF t ht
  have h2 := hIIddF t ht
  have key : α ^ 2 * t ^ 2 * deriv (deriv V) t
      = α * (5 + α) * (deriv V t * t + V t) + L * V t
        - 2 * α ^ 2 * V t - 4 * α ^ 2 * t * deriv V t := by
    rw [← h1, h2]; ring
  calc α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t
      = (α * (5 + α) * (deriv V t * t + V t) + L * V t
          - 2 * α ^ 2 * V t - 4 * α ^ 2 * t * deriv V t)
        + α * (3 * α - 5) * t * deriv V t + (α ^ 2 - 5 * α - L) * V t := by rw [key]
      _ = 0 := by ring

end Work.FTS.StrongEps.EComparison
