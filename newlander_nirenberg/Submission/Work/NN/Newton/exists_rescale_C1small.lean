import Mathlib
import Submission.Work.NN.Final.DbarSolvableAux
import Submission.Work.NN.Final.holderNormCongr
import Submission.Work.NN.Newton.exists_local_bounds_of_contDiffAt_two
import Submission.Work.NN.Newton.bounds_comp_apply_proj

/-! Guidance from the project lead (the requester): see `Submission/Work/NN/Newton/DESIGN.md`.

# `Work.NN.Newton.exists_rescale_C1small`

The rescaled perturbation `Atr J (Tsh T μ)` is the perturbation `Atr J T` evaluated at the rescaled
point `μ • z` (`Work.NN.Final.Atr_Tsh_eq`), and `Atr J T` is `C²` near `0` with `Atr J T 0 = 0`
(`Work.NN.Final.Atr_contDiffOn_aux`).  So all four pieces of the `C^{1,α}`-norm of a coefficient
`z ↦ Atr J T (μ • z) w j` on the bounded polydisc `pd n 1 4` are `O(μ)`: the sup and the order-`0`
seminorm from the Lipschitz bound on `Atr J T`, the first derivative from the bound on `fderiv`,
and the order-`1` seminorm from the Lipschitz bound on `fderiv` (which is `O(μ²)` before the
division by `‖z - z'‖^α`).  The two analytic ingredients are proved below
(`holderNorm_one_comp_smul_le_aux`) and imported when they are library lemmas
(`exists_local_bounds_of_contDiffAt_two`, `bounds_comp_apply_proj`).
-/

namespace Work.NN.Newton

open scoped ContDiff NNReal ENNReal
open Set

/-- At order `0` the within iterated derivative is the value, also for differences. -/
private lemma norm_iteratedFDerivWithin_zero_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Ω : Set X} (u v : X → ℂ) (x y : X) :
    ‖iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 v Ω y‖ = ‖u x - v y‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound
      (f := iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 v Ω y)
      (M := ‖u x - v y‖) (norm_nonneg _) (fun m => ?_)
    rw [sub_apply, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]
    simp
  · have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 v Ω y)
      (default : Fin 0 → X)
    rw [sub_apply, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply] at h
    simpa using h

/-- At order `1` the within iterated derivative on an open set is the differential, transported
by `continuousMultilinearCurryFin1`. -/
private lemma iteratedFDerivWithin_one_eq_curry' {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Ω : Set X} (hΩ : IsOpen Ω) {u : X → ℂ} {z : X} (hz : z ∈ Ω) :
    iteratedFDerivWithin ℝ 1 u Ω z
      = (continuousMultilinearCurryFin1 ℝ X ℂ).symm (fderiv ℝ u z) := by
  have h : continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDerivWithin ℝ 1 u Ω z)
      = fderiv ℝ u z := by
    ext v
    rw [continuousMultilinearCurryFin1_apply,
      iteratedFDerivWithin_one_apply (hΩ.uniqueDiffWithinAt hz)]
    simp [fderivWithin_of_isOpen hΩ hz]
  calc iteratedFDerivWithin ℝ 1 u Ω z
      = (continuousMultilinearCurryFin1 ℝ X ℂ).symm
          (continuousMultilinearCurryFin1 ℝ X ℂ (iteratedFDerivWithin ℝ 1 u Ω z)) :=
        (LinearIsometryEquiv.symm_apply_apply _ _).symm
    _ = (continuousMultilinearCurryFin1 ℝ X ℂ).symm (fderiv ℝ u z) := by rw [h]

/-- Norm of the difference of the order-`1` within iterated derivatives. -/
private lemma norm_iteratedFDerivWithin_one_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Ω : Set X} (hΩ : IsOpen Ω) (u : X → ℂ) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ‖iteratedFDerivWithin ℝ 1 u Ω x - iteratedFDerivWithin ℝ 1 u Ω y‖
      = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  rw [iteratedFDerivWithin_one_eq_curry' hΩ hx, iteratedFDerivWithin_one_eq_curry' hΩ hy,
    ← map_sub, LinearIsometryEquiv.norm_map]

/-- **The dilate of a function with a vanishing Lipschitz value and a Lipschitz derivative is
`C^{1,α}`-small.** -/
private theorem holderNorm_one_comp_smul_le_aux
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : IsOpen Ω) {B : ℝ} (hB : 1 ≤ B) (hΩB : ∀ z ∈ Ω, ‖z‖ ≤ B)
    {F : X → ℂ} (hF0 : F 0 = 0)
    {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hlip : ∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖F z - F w‖ ≤ K * ‖z - w‖)
    (hdiff : ∀ z, ‖z‖ ≤ ρ → DifferentiableAt ℝ F z)
    (hd2 : ∀ z, ‖z‖ ≤ ρ → ‖fderiv ℝ F z‖ ≤ K)
    (hd3 : ∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖fderiv ℝ F z - fderiv ℝ F w‖ ≤ K * ‖z - w‖)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hμB : μ * B ≤ ρ) :
    Work.CR.Flat.holderNorm 1 α (fun z => F (μ • z)) Ω
      ≤ ENNReal.ofReal (20 * K * μ * (B + 1)) := by
  set g : X → ℂ := fun z => F (μ • z) with hg
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  have hKμ : (0 : ℝ) ≤ K * μ := mul_nonneg hK (le_of_lt hμ)
  have hnorms : ∀ v : X, ‖μ • v‖ = μ * ‖v‖ := by
    intro v; rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
  -- every point of `μ • Ω` lies in the ball where the bounds hold
  have hnorm : ∀ z ∈ Ω, ‖μ • z‖ ≤ ρ := by
    intro z hz
    rw [hnorms]
    exact (mul_le_mul_of_nonneg_left (hΩB z hz) (le_of_lt hμ)).trans hμB
  -- ## the value bound: `iterDerivNorm 0`
  have hT0 : Work.CR.Flat.iterDerivNorm 0 g Ω ≤ ENNReal.ofReal (K * μ * B) := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z hz => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hlip (μ • z) 0 (hnorm z hz) (by simpa using hρ.le)
    rw [hF0, sub_zero, sub_zero] at h
    rw [hnorms] at h
    calc ‖g z‖ = ‖F (μ • z)‖ := rfl
      _ ≤ K * (μ * ‖z‖) := h
      _ ≤ K * (μ * B) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact mul_le_mul_of_nonneg_left (hΩB z hz) (le_of_lt hμ)
      _ = K * μ * B := by ring
  -- ## the value Hölder seminorm: `holderSeminorm 0`
  have hpow : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * B → t ^ (1 - α) ≤ 2 * B := by
    intro t ht0 ht
    have h1 : (0 : ℝ) ≤ 1 - α := sub_nonneg.mpr hα1.le
    calc t ^ (1 - α) ≤ (2 * B) ^ (1 - α) := Real.rpow_le_rpow ht0 ht h1
      _ ≤ (2 * B) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 2 * B := Real.rpow_one _
  have hdivpow : ∀ x : ℝ, 0 < x → x / x ^ α = x ^ (1 - α) := by
    intro x hx
    have h := Real.rpow_sub hx (1 : ℝ) α
    rw [Real.rpow_one] at h
    exact h.symm
  have hdist : ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖z - z'‖ ≤ 2 * B := by
    intro z hz z' hz'
    calc ‖z - z'‖ ≤ ‖z‖ + ‖z'‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hΩB z hz) (hΩB z' hz')
      _ = 2 * B := by ring
  have hS0 : Work.CR.Flat.holderSeminorm 0 α g Ω ≤ ENNReal.ofReal (K * μ * (2 * B)) := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hne => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hxz : z ≠ z' := hne
    have hpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    have hden : 0 < ‖z - z'‖ ^ α := Real.rpow_pos_of_pos hpos α
    have hnum : ‖iteratedFDerivWithin ℝ 0 g Ω z - iteratedFDerivWithin ℝ 0 g Ω z'‖
        = ‖g z - g z'‖ := norm_iteratedFDerivWithin_zero_sub g g z z'
    rw [hnum]
    have hd : ‖g z - g z'‖ ≤ K * μ * ‖z - z'‖ := by
      have h := hlip (μ • z) (μ • z') (hnorm z hz) (hnorm z' hz')
      rw [show μ • z - μ • z' = μ • (z - z') from by rw [smul_sub], hnorms] at h
      calc ‖g z - g z'‖ = ‖F (μ • z) - F (μ • z')‖ := rfl
        _ ≤ K * (μ * ‖z - z'‖) := h
        _ = K * μ * ‖z - z'‖ := by ring
    calc ‖g z - g z'‖ / ‖z - z'‖ ^ α
        ≤ (K * μ * ‖z - z'‖) / ‖z - z'‖ ^ α := div_le_div_of_nonneg_right hd hden.le
      _ = K * μ * (‖z - z'‖ / ‖z - z'‖ ^ α) := by ring
      _ = K * μ * ‖z - z'‖ ^ (1 - α) := by rw [hdivpow _ hpos]
      _ ≤ K * μ * (2 * B) := mul_le_mul_of_nonneg_left
          (hpow _ (norm_nonneg _) (hdist z hz z' hz')) hKμ
  -- ## the derivative bound: `iterDerivNorm 1`
  have hcomp : ∀ z ∈ Ω, fderiv ℝ g z = (fderiv ℝ F (μ • z)) ∘SL (μ • (1 : X →L[ℝ] X)) := by
    intro z hz
    have hgf : g = F ∘ (fun y : X => μ • y) := rfl
    rw [hgf, fderiv_comp z (hdiff (μ • z) (hnorm z hz)) ?_]
    · have hlin : fderiv ℝ (fun y : X => μ • y) z = μ • (1 : X →L[ℝ] X) := by
        have hfun : (fun y : X => μ • y) = ⇑(μ • (1 : X →L[ℝ] X)) := by
          funext y; simp
        rw [hfun]
        exact ContinuousLinearMap.fderiv (μ • (1 : X →L[ℝ] X)) (x := z)
      rw [hlin]
    · exact ContinuousLinearMap.differentiableAt (μ • (1 : X →L[ℝ] X)) (x := z)
  have hd1 : ∀ z ∈ Ω, ‖fderiv ℝ g z‖ ≤ K * μ := by
    intro z hz
    rw [hcomp z hz]
    refine ContinuousLinearMap.opNorm_le_bound _ hKμ (fun v => ?_)
    rw [ContinuousLinearMap.comp_apply]
    calc ‖fderiv ℝ F (μ • z) (μ • v)‖
        ≤ ‖fderiv ℝ F (μ • z)‖ * ‖μ • v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ F (μ • z)‖ * (μ * ‖v‖) := by rw [hnorms]
      _ ≤ K * (μ * ‖v‖) := mul_le_mul_of_nonneg_right (hd2 (μ • z) (hnorm z hz))
          (by positivity)
      _ = K * μ * ‖v‖ := by ring
  have hT1 : Work.CR.Flat.iterDerivNorm 1 g Ω ≤ ENNReal.ofReal (K * μ) := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_iteratedFDerivWithin_one g (hΩ.uniqueDiffWithinAt hz),
      fderivWithin_of_isOpen hΩ hz]
    exact hd1 z hz
  -- ## the derivative Hölder seminorm: `holderSeminorm 1`
  have hS1 : Work.CR.Flat.holderSeminorm 1 α g Ω ≤ ENNReal.ofReal (K * μ * (2 * B)) := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hne => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hxz : z ≠ z' := hne
    have hpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    have hden : 0 < ‖z - z'‖ ^ α := Real.rpow_pos_of_pos hpos α
    have hnum : ‖iteratedFDerivWithin ℝ 1 g Ω z - iteratedFDerivWithin ℝ 1 g Ω z'‖
        = ‖fderiv ℝ g z - fderiv ℝ g z'‖ := norm_iteratedFDerivWithin_one_sub hΩ g hz hz'
    rw [hnum]
    have hd : ‖fderiv ℝ g z - fderiv ℝ g z'‖ ≤ K * μ ^ 2 * ‖z - z'‖ := by
      rw [hcomp z hz, hcomp z' hz', ← ContinuousLinearMap.sub_comp]
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (mul_nonneg hK (sq_nonneg μ)) (norm_nonneg _)) (fun v => ?_)
      rw [ContinuousLinearMap.comp_apply]
      calc ‖(fderiv ℝ F (μ • z) - fderiv ℝ F (μ • z')) (μ • v)‖
          ≤ ‖fderiv ℝ F (μ • z) - fderiv ℝ F (μ • z')‖ * ‖μ • v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ F (μ • z) - fderiv ℝ F (μ • z')‖ * (μ * ‖v‖) := by rw [hnorms]
        _ ≤ (K * ‖μ • z - μ • z'‖) * (μ * ‖v‖) :=
            mul_le_mul_of_nonneg_right (hd3 _ _ (hnorm z hz) (hnorm z' hz')) (by positivity)
        _ = (K * (μ * ‖z - z'‖)) * (μ * ‖v‖) := by
            rw [show μ • z - μ • z' = μ • (z - z') from by rw [smul_sub], hnorms]
        _ = K * μ ^ 2 * ‖z - z'‖ * ‖v‖ := by ring
    have hμ2 : μ ^ 2 ≤ μ := by nlinarith [hμ, hμ1]
    calc ‖fderiv ℝ g z - fderiv ℝ g z'‖ / ‖z - z'‖ ^ α
        ≤ (K * μ ^ 2 * ‖z - z'‖) / ‖z - z'‖ ^ α := div_le_div_of_nonneg_right hd hden.le
      _ = K * μ ^ 2 * (‖z - z'‖ / ‖z - z'‖ ^ α) := by ring
      _ = K * μ ^ 2 * ‖z - z'‖ ^ (1 - α) := by rw [hdivpow _ hpos]
      _ ≤ K * μ ^ 2 * (2 * B) := mul_le_mul_of_nonneg_left
          (hpow _ (norm_nonneg _) (hdist z hz z' hz'))
          (mul_nonneg hK (sq_nonneg μ))
      _ ≤ K * μ * (2 * B) := by
          have hKB : (0 : ℝ) ≤ K * (2 * B) := mul_nonneg hK (by linarith)
          calc K * μ ^ 2 * (2 * B) = (K * (2 * B)) * μ ^ 2 := by ring
            _ ≤ (K * (2 * B)) * μ := mul_le_mul_of_nonneg_left hμ2 hKB
            _ = K * μ * (2 * B) := by ring
  -- ## assembly
  have hsplit : Work.CR.Flat.holderNorm 1 α g Ω
      = (Work.CR.Flat.iterDerivNorm 0 g Ω + Work.CR.Flat.holderSeminorm 0 α g Ω)
        + (Work.CR.Flat.iterDerivNorm 1 g Ω + Work.CR.Flat.holderSeminorm 1 α g Ω) := by
    rw [Work.CR.Flat.holderNorm]
    norm_num [Finset.sum_range_succ]
  rw [hsplit]
  refine le_trans (add_le_add (add_le_add hT0 hS0) (add_le_add hT1 hS1)) ?_
  have hA : (0 : ℝ) ≤ K * μ * B := mul_nonneg hKμ hB0
  have hB' : (0 : ℝ) ≤ K * μ * (2 * B) := mul_nonneg hKμ (by linarith)
  rw [← ENNReal.ofReal_add hA hB', ← ENNReal.ofReal_add hKμ hB']
  rw [← ENNReal.ofReal_add (add_nonneg hA hB') (add_nonneg hKμ hB')]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : K * μ * B + K * μ * (2 * B) + (K * μ + K * μ * (2 * B))
      = K * μ * (5 * B + 1) := by ring
  rw [h1]
  have h2 : K * μ * (5 * B + 1) ≤ K * μ * (20 * (B + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) hKμ
  linarith [h2]


/-- **Rescaling makes the perturbation `C^{1,α}`-small on the fixed polydisc.**

Let `J` be `C²` on an open `U ∋ 0` of `ℝ^{2n}` and `T` normalise `J 0`.  For every `ε > 0` there is
`μ₁ > 0` such that for all `0 < μ ≤ μ₁` every coefficient `z ↦ Atr J (Tsh T μ) z w j` (`‖w‖ ≤ 1`)
of the rescaled perturbation has `C^{1,α}`-norm `≤ ε` on `pd n 1 4`.  Since
`Atr J (Tsh T μ) z = Atr J T (μ z)` (`Work.NN.Final.Atr_Tsh_eq`) and `Atr J T 0 = 0`, the sup, the first
derivative and the order-`0` Hölder seminorm are `O(μ)` and the order-`1` Hölder seminorm is
`O(μ²)` (a Lipschitz bound on `D Atr` near `0`, from `C²`); this is `Work.NN.Final.exists_rescale_vecHolder_c` one
derivative higher. -/
theorem exists_rescale_C1small {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {U : Set (Work.NN.Final.EN n)}
    {J : Work.NN.Final.EN n → Work.NN.Final.EN n →L[ℝ] Work.NN.Final.EN n}
    {T : Work.NN.Final.EN n ≃L[ℝ] Submission.F n}
    (hU : IsOpen U) (h0U : (0 : Work.NN.Final.EN n) ∈ U) (hJ : ContDiffOn ℝ 2 J U)
    (hT : ∀ v, T (J 0 v) = Complex.I • T v) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ₁ : ℝ, 0 < μ₁ ∧ ∀ (μ : ℝ) (hμ : 0 < μ), μ ≤ μ₁ →
      ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
        Work.CR.Flat.holderNorm 1 α
            (fun z => Work.NN.Final.Atr J (Work.NN.Final.Tsh T μ (ne_of_gt hμ)) z w j)
            (Work.NN.Final.pd n (fun _ => 1) 4)
          ≤ ENNReal.ofReal ε := by
  -- ## Step 1: `Atr J T` is `C²` in a neighbourhood of `0`.
  have hVopen : IsOpen {z : Work.NN.Core.Cn n | Work.NN.Core.tupleDerivInv T z ∈ U} :=
    hU.preimage (Work.NN.Core.tupleDerivInv T).continuous
  have hV0 : (0 : Work.NN.Core.Cn n)
      ∈ {z : Work.NN.Core.Cn n | Work.NN.Core.tupleDerivInv T z ∈ U} := by
    show Work.NN.Core.tupleDerivInv T 0 ∈ U
    have hz : Work.NN.Core.tupleDerivInv T (0 : Work.NN.Core.Cn n) = 0 := by simp
    rw [hz]
    exact h0U
  have hAtrCd : ContDiffOn ℝ 2 (Work.NN.Final.Atr J T)
      {z : Work.NN.Core.Cn n | Work.NN.Core.tupleDerivInv T z ∈ U} :=
    Work.NN.Final.Atr_contDiffOn_aux (k := (2 : ℕ∞)) hJ
  have hAtrAt : ContDiffAt ℝ 2 (Work.NN.Final.Atr J T) 0 :=
    hAtrCd.contDiffAt (hVopen.mem_nhds hV0)
  have hA0 : Work.NN.Final.Atr J T 0 = 0 :=
    ContinuousLinearMap.ext fun v => Work.NN.Final.Atr_zero J T hT v
  -- ## Step 2: uniform local bounds for `Atr J T`.
  obtain ⟨ρ, hρpos, K, hK0, hb1, hb2, hb3, hb4, hb5⟩ :=
    exists_local_bounds_of_contDiffAt_two (F := Work.NN.Final.Atr J T) hAtrAt hA0
  -- ## Step 3: the scale.
  set C : ℝ := 100 * K + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hΩB : ∀ z ∈ Work.NN.Final.pd n (fun _ => 1) 4, ‖z‖ ≤ 4 := by
    intro z hz
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    intro j
    have hj := (Work.NN.Final.mem_pd.mp hz) j
    simp only [mul_one] at hj
    linarith [hj]
  refine ⟨min (min 1 (ρ / 4)) (ε / C), ?_, ?_⟩
  · exact lt_min (lt_min one_pos (by positivity)) (div_pos hε hCpos)
  · intro μ hμ hμle w hw j
    have hμle1 : μ ≤ 1 := le_trans hμle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hμle4 : μ ≤ ρ / 4 := le_trans hμle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hμleε : μ ≤ ε / C := le_trans hμle (min_le_right _ _)
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ :=
      bounds_comp_apply_proj (A := Work.NN.Final.Atr J T) hb1 hb2 hb3 hb4 hb5 w hw j
    have hμB : μ * 4 ≤ ρ := by
      have h := mul_le_mul_of_nonneg_right hμle4 (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have hkey :=
      holderNorm_one_comp_smul_le_aux
        (Ω := Work.NN.Final.pd n (fun _ => 1) 4)
        (B := 4) (F := fun y => (Work.NN.Final.Atr J T y w) j) (μ := μ)
        (Work.NN.Final.isOpen_pd (fun _ => 1) 4) (by norm_num) hΩB
        (by simp [hA0]) hK0 hρpos hf2 hf3 hf4 hf5 hα0 hα1 hμ hμle1 hμB
    have hcongr : Set.EqOn
        (fun z => Work.NN.Final.Atr J (Work.NN.Final.Tsh T μ (ne_of_gt hμ)) z w j)
        (fun z => (Work.NN.Final.Atr J T (μ • z) w) j)
        (Work.NN.Final.pd n (fun _ => 1) 4) := by
      intro z _
      show (Work.NN.Final.Atr J (Work.NN.Final.Tsh T μ (ne_of_gt hμ)) z) w j
        = (Work.NN.Final.Atr J T (μ • z)) w j
      rw [Work.NN.Final.Atr_Tsh_eq J T μ (ne_of_gt hμ) z]
      rw [show ((μ : ℂ) • z) = (μ : ℝ) • z from by simp]
    rw [Work.NN.Final.holderNorm_congr_of_eqOn hcongr 1 α]
    refine le_trans hkey (ENNReal.ofReal_le_ofReal ?_)
    have hCμ : C * μ ≤ ε := by
      have h := (le_div_iff₀ hCpos).mp hμleε
      linarith [h]
    have hKm : (100 : ℝ) * K * μ ≤ C * μ := by
      have hle : (100 : ℝ) * K ≤ C := by rw [hCdef]; linarith
      exact mul_le_mul_of_nonneg_right hle (le_of_lt hμ)
    nlinarith [hKm, hCμ]

end Work.NN.Newton
