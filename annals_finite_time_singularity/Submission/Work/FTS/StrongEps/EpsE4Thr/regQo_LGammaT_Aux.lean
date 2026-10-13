import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR0
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux`

Supporting bounds for `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT` (its §0--§3).

`𝓛_Γ^T x ∈ RegQo α 4` for every profile `x` of the class `ClassC α`, `α ∈ (0,1]`.

`RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f` (`EpsE4Thr/OpenClass.lean`).
The first two conjuncts are available (`smoothOpen_LGammaT_of_L12` with
`ClassCRHS.smoothOpen_L12_radial_classC`, and `ClassCHk.LGammaTMem` / `ClassCRHS.HkMemXnLGammaT`).
This file supplies the third.

## Route

`𝓛_Γ^T x = 𝓛̂x + Corr α x` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), where
`𝓛̂x = x + D_z x − 2x/(1+z) − 3D_θx/(1+z)` and, by `Transfer.Corr_eq_radA`,
`Corr α x = Γ(θ)·radA α x (z)` with
`radA α x z = −ampA α z·L₁₂(x)(z) + (ampB α z/c α)·L₁₂(Transport x)(0)`.

* `BdryTraces α 4 (𝓛̂x)`: the summands are `x`, `D_z x`, `D_θ x` (the `RegQo`-ports
  `regQo_dth_dz` plus monotonicity) and the radial multiples `x/(1+z)`, `D_θx/(1+z)`
  (`TracesAux.BdryTraces_psi_mul_open` with `PsiMul.zop_psi_bound`); additivity is
  `ClassC.bdryTraces_add`.
* `BdryTraces α 4 (Corr α x)`: the separated-product lemma
  `TracesAux.BdryTraces_Gam_mul_rad` with the radial trace hypotheses proved here from the
  bounds on `radA`: `‖D_z^b radA(x)‖ ≤ C z^{5/2}` for `z ∈ (0,1)` and `≤ C/z` for `z ≥ 1`.
  These come from the Leibniz expansion of `D_z^b (ampA·L₁₂ x)`
  (`OpenPkg.ProdOpen.leibniz_open_mixed`), the jets of `ampA` (`L12Aux.ampA_dzdIter_abs_le`),
  the jets of `ampB` (`DzBoundR0`) and the angular-moment bound `Qang x k = O(z^{3/2})`
  (`L12Aux.Qang_small_z`) together with its uniform boundedness
  (`StrongEps.classC_mixed_sup_le_four`).

All inputs are `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §0  Vocabulary -/

/-- `L₁₂` in the `Coercivity` and in the `Elliptic` vocabulary are the same radial function. -/
theorem L12f_eq_elliptic (f : Fn) :
    Work.Coercivity.L12f f = Work.Elliptic.L12 f := by
  funext z
  show (∫ s in Set.Ioi z,
      (∫ θ in Set.Icc 0 (π / 2), Work.Spaces.K θ * f s θ / s)) =
    ∫ r in Set.Ioi z, ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f r θ / r
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
    rw [Work.Elliptic.Ktheta_eq_K]

/-- `x` of class `ClassC` gives `L₁₂(x)(0) = 0` in the `Elliptic` vocabulary. -/
theorem elliptic_L12_zero {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    Work.Elliptic.L12 x 0 = 0 := by
  rw [← Work.FTS.H2.constructionL12_eq_ellipticL12]
  exact hx.l12

/-- `L₁₂dens x` is integrable on `(0,∞)` for a `ClassC` profile. -/
theorem integrableOn_L12dens {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens x) (Set.Ioi 0) := by
  have hF : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar x r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 x hx.reg hx.mem
  refine hF.const_mul 3 |> fun h => h.congr (Filter.Eventually.of_forall fun r => ?_)
  rw [Work.Elliptic.L12dens_eq_three_Fstar_div]

/-! ## §1  The angular-moment bounds -/

/-- The angular moment `Qang x k` of a `ClassC` profile is bounded on `(0,∞)`, uniformly in `z`. -/
theorem Qang_bdd {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn} (hx : Work.FTS.ClassC.ClassC α x)
    {k : ℕ} (hk : k ≤ 4) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℝ, 0 < z → |Work.Elliptic.Qang x k z| ≤ M := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  set T : ℝ := C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.StrongGlobal.Xn6 α x with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (div_nonneg hCpos.le (Real.sqrt_nonneg _)) (Work.Spaces.HkNorm_nonneg α 6 x)
  refine ⟨3 * (Real.pi / 2) * T + 1, by nlinarith [hT0, Real.pi_pos], fun z hz => ?_⟩
  have hKθ : ∀ θ ∈ Work.Spaces.Iθ, |Work.Elliptic.Ktheta θ| ≤ 3 := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos]⟩
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcsq : Real.cos θ ^ 2 ≤ 1 := by nlinarith
    rw [Work.Elliptic.Ktheta, abs_of_nonneg (by positivity)]
    nlinarith
  have hKzero : Work.Elliptic.Ktheta 0 = 0 := by simp [Work.Elliptic.Ktheta]
  have hKpi : Work.Elliptic.Ktheta (Real.pi / 2) = 0 := by
    rw [Work.Elliptic.Ktheta, Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ ≤ 3 * T := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hKzero, zero_mul, norm_zero]
      nlinarith [hT0, Real.pi_pos]
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [hKpi, zero_mul, norm_zero]
        nlinarith [hT0, Real.pi_pos]
      · rw [Real.norm_eq_abs, abs_mul]
        have hmix : |Work.Spaces.DzIter k x z θ| ≤ T := by
          have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, h0, h1⟩
          have h := hC α hα hx k 0 (by omega) hQd
          simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero, hT] using h
        exact mul_le_mul (hKθ θ hθ) hmix (abs_nonneg _) (by norm_num)
  calc |Work.Elliptic.Qang x k z|
      = |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ| := by
        rw [Work.Elliptic.Qang]
    _ = ‖∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ, (3 * T) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (MeasureTheory.integrable_const _) hae
    _ = 3 * T * (Real.pi / 2) := by
        rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
    _ ≤ 3 * (Real.pi / 2) * T + 1 := by
        nlinarith [hT0, Real.pi_pos]

/-! ## §2  Bounds for the radial jets of `L₁₂(x)` -/

/-- `L₁₂ x` is bounded on `[0,∞)`. -/
theorem L12f_bdd {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.L12 x z| ≤ D := by
  have hint := integrableOn_L12dens hx
  refine ⟨∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s|,
    MeasureTheory.integral_nonneg (fun _ => abs_nonneg _), fun z hz => ?_⟩
  have hsub : Set.Ioi z ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun s hs => Set.mem_Ioi.mpr (lt_of_le_of_lt hz hs)
  have hmono : (∫ s in Set.Ioi z, |Work.Elliptic.L12dens x s|)
      ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s| :=
    MeasureTheory.setIntegral_mono_set hint.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hsub
  calc |Work.Elliptic.L12 x z|
      = |∫ s in Set.Ioi z, Work.Elliptic.L12dens x s| := by rw [Work.Elliptic.L12]
    _ = ‖∫ s in Set.Ioi z, Work.Elliptic.L12dens x s‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ s in Set.Ioi z, ‖Work.Elliptic.L12dens x s‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ s in Set.Ioi z, |Work.Elliptic.L12dens x s| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s| := hmono

/-- Near the origin `L₁₂ x` is `O(z^{3/2})`, from the angular-moment bound on `Qang x 0`. -/
theorem L12f_small {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ z : ℝ, 0 < z → z < 1 → |Work.Elliptic.Qang x 0 z| ≤ C * z ^ ((3 : ℝ) / 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.L12 x z| ≤ D * z ^ ((3 : ℝ) / 2) := by
  have hint := integrableOn_L12dens hx
  refine ⟨C, hC.le, fun z hz hz1 => ?_⟩
  have hFTC := (Work.Elliptic.L12_values x hint (elliptic_L12_zero hx)).1 z hz.le
  rw [hFTC, abs_neg]
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hden : ∀ s ∈ Set.uIcc (0 : ℝ) z,
      |Work.Elliptic.L12dens x s| ≤ C * s ^ ((1 : ℝ) / 2) := by
    intro s hs
    rw [Set.uIcc_of_le hz0, Set.mem_Icc] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, Work.Elliptic.L12dens_eq_Qang_div, div_zero, abs_zero,
        Real.zero_rpow (by norm_num : ((1 : ℝ) / 2) ≠ 0), mul_zero]
    · have hs1 : s < 1 := lt_of_le_of_lt hs.2 hz1
      have hsq : |Work.Elliptic.Qang x 0 s| ≤ C * s ^ ((3 : ℝ) / 2) := hQ s h0 hs1
      have hspow : s ^ ((3 : ℝ) / 2) = s ^ ((1 : ℝ) / 2) * s := by
        rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add h0,
          Real.rpow_one, mul_comm]
      have hs1' : s ^ ((1 : ℝ) / 2) ≤ 1 := by
        have h := Real.rpow_le_rpow h0.le (le_of_lt hs1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rwa [Real.one_rpow] at h
      rw [Work.Elliptic.L12dens_eq_Qang_div, abs_div, abs_of_pos h0, div_le_iff₀ h0]
      rw [hspow] at hsq
      simpa only [mul_assoc] using hsq
  have h1 : |∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens x s|
      ≤ ∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hz0).trans ?_
    refine intervalIntegral.integral_mono_on hz0 ?_ ?_ ?_
    · have hI : MeasureTheory.IntegrableOn (fun s => |Work.Elliptic.L12dens x s|)
          (Set.Ioi (0 : ℝ)) := hint.abs
      have hIcc : MeasureTheory.IntegrableOn (fun s => |Work.Elliptic.L12dens x s|)
          (Set.uIcc (0 : ℝ) z) := by
        rw [Set.uIcc_of_le hz0]
        exact (integrableOn_Icc_iff_integrableOn_Ioc (a := (0 : ℝ)) (b := z) (by simp)).mpr
          (hI.mono_set Set.Ioc_subset_Ioi_self)
      exact hIcc.intervalIntegrable
    · exact (intervalIntegral.intervalIntegrable_rpow (Or.inl (by norm_num : (0 : ℝ) ≤ 1 / 2))).const_mul C
    · intro s hs
      exact hden s (by rw [Set.uIcc_of_le hz0]; exact hs)
  have h2 : (∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2))
      = C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    rw [show ((1 : ℝ) / 2 + 1) = (3 : ℝ) / 2 by norm_num]
    rw [Real.zero_rpow (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
    ring
  have h3 : C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) ≤ C * z ^ ((3 : ℝ) / 2) := by
    have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz0 _
    nlinarith [hC.le]
  calc |∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens x s|
      ≤ ∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2) := h1
    _ = C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) := h2
    _ ≤ C * z ^ ((3 : ℝ) / 2) := h3

/-- The `D_z`-jets of `L₁₂ x` are the angular moments: `D_z^{k+1} (L₁₂ x) = -Qang x k`. -/
theorem DzdIter_L12f_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (Work.Elliptic.L12 x) z = -Work.Elliptic.Qang x k z := by
  intro k hk z hz
  have hmem : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hx.reg 4 (by norm_num) hx.mem
  exact (Work.FTS.OpenPkg.l12_open_bundle α x hα hα1 hx.reg hmem (elliptic_L12_zero hx)).1
    k hk z hz

/-- The `D_z`-jets of `L₁₂ x` are bounded on `(0,∞)`. -/
theorem DzdIter_L12f_bdd {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter m (Work.Elliptic.L12 x) z| ≤ D := by
  obtain ⟨D₀, hD₀, hΛ⟩ := L12f_bdd hx
  obtain ⟨M0, hM0, hQ0⟩ := Qang_bdd hα hx (k := 0) (by omega)
  obtain ⟨M1, hM1, hQ1⟩ := Qang_bdd hα hx (k := 1) (by omega)
  obtain ⟨M2, hM2, hQ2⟩ := Qang_bdd hα hx (k := 2) (by omega)
  obtain ⟨M3, hM3, hQ3⟩ := Qang_bdd hα hx (k := 3) (by omega)
  refine ⟨D₀ + M0 + M1 + M2 + M3, by positivity, fun m hm z hz => ?_⟩
  interval_cases m
  · exact le_trans (hΛ z hz.le) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 0 (by omega) z hz, abs_neg]
    exact le_trans (hQ0 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 1 (by omega) z hz, abs_neg]
    exact le_trans (hQ1 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 2 (by omega) z hz, abs_neg]
    exact le_trans (hQ2 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 3 (by omega) z hz, abs_neg]
    exact le_trans (hQ3 z hz) (by linarith)

/-- The `D_z`-jets of `L₁₂ x` are `O(z^{3/2})` near the origin. -/
theorem DzdIter_L12f_small {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.DzdIter m (Work.Elliptic.L12 x) z| ≤ D * z ^ ((3 : ℝ) / 2) := by
  obtain ⟨D₀, hD₀, hΛ⟩ := L12f_small hx hC (hQ 0 (by omega))
  refine ⟨D₀ + C + C + C, by positivity, fun m hm z hz hz1 => ?_⟩
  have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
  interval_cases m
  · exact le_trans (hΛ z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 0 (by omega) z hz, abs_neg]
    exact le_trans (hQ 0 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 1 (by omega) z hz, abs_neg]
    exact le_trans (hQ 1 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 2 (by omega) z hz, abs_neg]
    exact le_trans (hQ 2 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 3 (by omega) z hz, abs_neg]
    exact le_trans (hQ 3 (by omega) z hz hz1) (by nlinarith)

/-! ## §3  Bounds for the radial jets of `ampB` -/

/-- The `D_z`-jets of `ampB α = 2z²/(1+z)³` are bounded by `C z²/(1+z)³`. -/
theorem DzdIter_ampB_bdd (α : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
        ≤ D * z ^ 2 / (1 + z) ^ 3 := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.StrongEps.ClassCRHS.DzBoundR0
  refine ⟨C, hC.le, fun b hb z hz => ?_⟩
  have hfun : Work.FTS.CoercivityFix.Transfer.ampB α
      = Work.FTS.StrongEps.ClassCRHS.SR0 := by
    funext w
    simp only [Work.FTS.CoercivityFix.Transfer.ampB, Work.FTS.StrongEps.ClassCRHS.SR0]
  rw [hfun]
  exact hCb b hb z hz

end Work.FTS.StrongEps.EpsE4Thr
