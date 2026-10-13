/-
# `ClassC_le` — the exponent-downward closure of the class `C`

The class `Work.FTS.ClassC.ClassC α` depends on `α` only through the weights of
`Work.Spaces.HkIntegrand` (`sin(2θ)^{-γ}` with `γ = 1 + α/10`) and through the `BdryTraces`
exponents `sin(2θ)^{1-γ}`.  Since `0 ≤ sin(2θ) ≤ 1` on the angular interval, every one of those
weights is **increasing** in `α`: for `α ≥ 1` and `θ ∈ Iθ`,

  `HkIntegrand 1 k g z θ ≤ HkIntegrand α k g z θ`,   `sin(2θ)^{1-γ(1)} ≤ sin(2θ)^{1-γ(α)}`.

Consequently `ClassC α g → ClassC 1 g` for `α ≥ 1` (the `α`-free fields `reg`, `norm`, `fsm`,
`axis`, `l12` are literally the same), and `Xn6 1 g ≤ Xn6 α g`.  This is what lets a statement
proved for `α ≤ 1` be transported to the whole range `α > 0` in `Theta_jets_le`.

Contents:

* `wTheta_le_of_one_le`, `HkIntegrand_one_le` — the pointwise weight comparisons;
* `HkMem_one_of` — the `HkMem` comparison (via `Work.Blocks.HkMem_of_majorant_aesm`);
* `HkSq_one_le` — the `HkSq` comparison;
* `bdryTraces_one_of` — the `BdryTraces` comparison;
* `classC_one_of`, `Xn6_one_le` — the class and norm comparisons.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.Blocks.HalfInfra
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS_EllLimOK.ThetaJets.thetaTraces_one_of

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular weight `wTheta` is increasing in `α` -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `γ(α) = 1 + α/10` is increasing. -/
theorem gam_le_gam {α : ℝ} (hα : 1 ≤ α) : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.gam]
  linarith

/-- **`wTheta` is increasing in `α`** on `Iθ`. -/
theorem wTheta_le_of_one_le {α : ℝ} (hα : 1 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.wTheta 1 θ ≤ Work.Spaces.wTheta α θ := by
  have hgam := gam_le_gam hα
  rcases (sin_two_nonneg_Iθ' hθ).lt_or_eq with hs | hs
  · rw [Work.Spaces.wTheta, Work.Spaces.wTheta]
    refine Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _) ?_
    linarith
  · have hs0 : Real.sin (2 * θ) = 0 := hs.symm
    have h1 : (-(Work.Spaces.gam 1 / 2)) ≠ 0 := by rw [Work.Spaces.gam]; norm_num
    have h2 : (-(Work.Spaces.gam α / 2)) ≠ 0 := by
      rw [Work.Spaces.gam]
      intro h
      linarith [hα]
    rw [Work.Spaces.wTheta, Work.Spaces.wTheta, hs0, Real.zero_rpow h1, Real.zero_rpow h2]

/-- `w ≥ 0`. -/
theorem w_nonneg' (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The pointwise comparison of the `ℋ^k`-integrands -/

/-- **The `ℋ^k`-integrand is increasing in `α`**: for `α ≥ 1` and `θ ∈ Iθ`,
`HkIntegrand 1 k g z θ ≤ HkIntegrand α k g z θ`. -/
theorem HkIntegrand_one_le {α : ℝ} (hα : 1 ≤ α) (k : ℕ) {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand 1 k g z θ ≤ Work.Spaces.HkIntegrand α k g z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add (le_refl _) ?_
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  split_ifs with h
  · have hw0 : (0 : ℝ) ≤ Work.Spaces.w z := w_nonneg' z
    have hle : Work.Spaces.Wt 1 z θ ≤ Work.Spaces.Wt α z θ := by
      rw [Work.Spaces.Wt, Work.Spaces.Wt]
      exact mul_le_mul_of_nonneg_left (wTheta_le_of_one_le hα hθ) hw0
    have h1nn : 0 ≤ Work.Spaces.Wt 1 z θ := by
      rw [Work.Spaces.Wt]
      exact mul_nonneg hw0 (Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
    have h2nn : 0 ≤ Work.Spaces.Wt α z θ := le_trans h1nn hle
    have habs : |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ|
        ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1nn, abs_of_nonneg h2nn]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    have h2 : |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ| ^ 2
        ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ) ^ 2
        = |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ| ^ 2 :=
          (sq_abs _).symm
      _ ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| ^ 2 := h2
      _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := sq_abs _
  · exact le_rfl

/-! ## The comparison of `HkMem` -/

/-- **`HkMem α k g → HkMem 1 k g` for `α ≥ 1`.** -/
theorem HkMem_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem 1 k g := by
  refine Work.Blocks.HkMem_of_majorant_aesm 1 k
    (M := fun z θ => Work.Spaces.HkIntegrand α k g z θ) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => Work.Spaces.HkIntegrand 1 k g 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp only [Work.Blocks.Half.HkIntegrand_zero_z]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
        (hsm.continuousOn_HkIntegrand 1 k) hpos
  · have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand 1 k g p.1 p.2)
      (hsm.continuousOn_HkIntegrand 1 k)
    exact hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  · intro z hz
    exact hmem.1 z hz
  · exact hmem.2
  · intro z hz θ hθ
    exact HkIntegrand_one_le hα k hθ

/-! ## The comparison of `HkSq` -/

/-- **`HkSq 1 k g ≤ HkSq α k g` for `α ≥ 1`.** -/
theorem HkSq_one_le {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) : Work.Spaces.HkSq 1 k g ≤ Work.Spaces.HkSq α k g := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · filter_upwards with z
    exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg 1 k g z θ)
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg 1 k g z θ))
      (hmem.1 z hz) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_one_le hα k hθ)

/-! ## The comparison of `BdryTraces` -/

/-- **`BdryTraces α k g → BdryTraces 1 k g` for `α ≥ 1`.** -/
theorem bdryTraces_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (htr : Work.FTS.Nonlin.BdryTraces α k g) : Work.FTS.Nonlin.BdryTraces 1 k g := by
  intro a b hab
  obtain ⟨h1, h2⟩ := htr a b hab
  refine ⟨h1, fun z hz => ?_⟩
  obtain ⟨h3, h4⟩ := h2 z hz
  have hgam : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := gam_le_gam hα
  constructor
  · refine squeeze_zero' ?_ ?_ h3
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)
  · refine squeeze_zero' ?_ ?_ h4
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)

/-! ## The class and norm comparisons -/

/-- **`ClassC α g → ClassC 1 g` for `α ≥ 1`.** -/
theorem classC_one_of {α : ℝ} (hα : 1 ≤ α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) : Work.FTS.ClassC.ClassC 1 g :=
  ⟨hg.norm, hg.reg, HkMem_one_of hα hg.reg hg.mem, HkMem_one_of hα hg.reg hg.mem8,
    HkMem_one_of hα hg.reg hg.mem10,
    bdryTraces_one_of hα hg.tr, bdryTraces_one_of hα hg.tr7, hg.fsm, hg.axis, hg.l12,
    thetaTraces_one_of hα hg.thTr⟩

/-- **`Xn6 1 g ≤ Xn6 α g` for `α ≥ 1`** on the class `ClassC α`. -/
theorem Xn6_one_le {α : ℝ} (hα : 1 ≤ α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.StrongGlobal.Xn6 1 g ≤ Work.FTS.StrongGlobal.Xn6 α g := by
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  show Work.Spaces.HkNorm 1 6 g ≤ Work.Spaces.HkNorm α 6 g
  rw [Work.Spaces.HkNorm]
  exact Real.sqrt_le_sqrt (HkSq_one_le hα hmem6)

end Work.FTS_EllLimOK.ThetaJets
