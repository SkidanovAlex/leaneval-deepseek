/-
# `Work.FTS.StrongPersist.H6Aux.CorrAux` — the auxiliary lemmas for `Corr_HkSq6`

The correction `Corr α f = 𝓛_Γ^T f − 𝓛̂ f` of the coercivity fix is, by
`CoercivityFix.Transfer.Corr_eq_radA`, the *separated* product

  `Corr α f z θ = Γ(θ)·radA α f z`,   `radA α f z = −ampA α z·L₁₂f(z) + (ampB α z/c α)·C₀f`,

of the angular function `Gam α` and a `z`-only radial profile.  This module collects the
consequences of that structure that the proof of `Corr_HkSq6` needs:

* `Corr_eq_sep` — `Corr` in separated form;
* `Gam_eq_c_mul_gamCoef`, `dthU_iter_Gam_eq`, `sepFactor_eq_Mth6` — the angular factor of the
  separation lemma at `C = Gam α` is exactly `c(α)²·Mth6 α`;
* `HkIntegrand_Corr_le` — the pointwise `ℋ⁶`-integrand bound
  `HkIntegrand α 6 (Corr α f) z θ ≤ c(α)²·Mth6 α θ·SlotSum (radA α f) z` for `θ ∈ Iθ`;
* `contDiffOn_six_ampA/ampB_div/radA/Corr` and `continuousOn_HkIntegrand_Corr` — the
  finite-order smoothness of `Corr` on the open quadrant, which supplies the continuity
  hypothesis of `LocData.HkMem_of_majorant`;
* `HkMem_Corr_of` and `HkSq_Corr_le_of` — the two conclusions of `Corr_HkSq6`, given the
  angular bound (`∫_θ Mth6 α ≤ Cang`) and the radial bound
  (`∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f`) as hypotheses.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf
import Submission.Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm HkIntegrand Dz Dth mixed)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §1 `Corr` in separated form -/

theorem Corr_eq_sep (α : ℝ) (f : Fn) :
    Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z := by
  funext z θ
  exact Work.FTS.CoercivityFix.Transfer.Corr_eq_radA α f z θ

/-- `Gam α = c(α)·gamCoef α` as functions (`c(α) ≠ 0` for `α ∈ (0,1]`). -/
theorem Gam_eq_c_mul_gamCoef {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.Gam α = fun θ => Work.Spaces.c α * Work.FTS.StrongPersist.gamCoef α θ := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (Work.FTS.StrongPersist.L3Aux.c_pos hα hα1)
  funext θ
  rw [Work.FTS.StrongPersist.gamCoef_eq_inv_mul]
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The iterated `D_θ`-derivatives of `Gam α` are `c(α)` times those of `gamCoef α`. -/
theorem dthU_iter_Gam_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    Work.Spaces.dthU^[i] (Work.Spaces.Gam α)
      = fun θ => Work.Spaces.c α
          * Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.gamCoef α) θ := by
  rw [Gam_eq_c_mul_gamCoef hα hα1]
  exact Work.FTS.StrongPersist.dthU_iter_const_mul (Work.Spaces.c α)
    (Work.FTS.StrongPersist.gamCoef α) i

/-- **The angular factor of the separation bound** at `C = Gam α` is exactly `c(α)²·Mth6 α`. -/
theorem sepFactor_eq_Mth6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then (Work.Spaces.dthU^[i] (Work.Spaces.Gam α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ := by
  have hGam : Work.Spaces.Gam α θ
      = Work.Spaces.c α * Work.FTS.StrongPersist.gamCoef α θ :=
    congrFun (Gam_eq_c_mul_gamCoef hα hα1) θ
  rw [Work.FTS.StrongPersist.Mth6, mul_add, Finset.mul_sum]
  congr 1
  · rw [hGam]; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, congrFun (dthU_iter_Gam_eq hα hα1 i) θ]
      ring
    · rw [if_neg h1, if_neg h1, mul_zero]

/-! ## §2 The pointwise `ℋ⁶`-integrand bound -/

/-- **The pointwise bound at the heart of the proof.**  For `θ ∈ Iθ` the `ℋ⁶`-integrand of
`Corr α f` is dominated by the product of the angular mass `c(α)²·Mth6 α θ` and the radial slot
sum `SlotSum (radA α f) z` of the radial profile of `Corr`. -/
theorem HkIntegrand_Corr_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : Fn) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 6 (Work.FTS.CoercivityFix.Corr α f) z θ
      ≤ (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
  have h := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 6)
    (C := Work.Spaces.Gam α) (B := Work.FTS.CoercivityFix.Transfer.radA α f)
    (z := z) (θ := θ) hθ
  rw [Corr_eq_sep α f]
  refine le_trans h (le_of_eq ?_)
  rw [sepFactor_eq_Mth6 hα hα1 θ, Work.FTS.StrongPersist.SlotSum]

/-! ## §3 The finite-order smoothness of `Corr` on the open quadrant -/

theorem contDiffOn_six_ampA {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 6 (Work.FTS.CoercivityFix.Transfer.ampA α) (Set.Ioi (0 : ℝ)) := by
  have hc : Work.Spaces.c α ≠ 0 := ne_of_gt (Work.FTS.StrongPersist.L3Aux.c_pos hα hα1)
  have hden : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have h1 : (1 : ℝ) + z ≠ 0 := by
      have : (0 : ℝ) < z := hz
      linarith
    exact mul_ne_zero hc (pow_ne_zero 2 h1)
  have hnum : ContDiffOn ℝ 6 (fun z : ℝ => 2 * z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul contDiffOn_id
  have hdenm : ContDiffOn ℝ 6 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
  exact hnum.div hdenm hden

theorem contDiffOn_six_ampB_div (α : ℝ) :
    ContDiffOn ℝ 6 (fun z : ℝ =>
      Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α) (Set.Ioi (0 : ℝ)) := by
  have hden : ∀ z ∈ Set.Ioi (0 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by
      have : (0 : ℝ) < z := hz
      linarith
    exact ne_of_gt (by positivity)
  have hnum : ContDiffOn ℝ 6 (fun z : ℝ => 2 * z ^ 2) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hdenm : ContDiffOn ℝ 6 (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  exact (hnum.div hdenm hden).div_const _

/-- `radA α f` is `C⁶` on `(0,∞)` — from the `C⁶`-smoothness of `L₁₂f`, which `HkMem α 7 f`
supplies (`contDiffOn6_L12_of`). -/
theorem contDiffOn_six_radA {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 6 (fun z => Work.Coercivity.L12f f z) (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z => Work.Coercivity.L12f f z)
        = fun z => Work.Construction.L12 f z := rfl
    rw [hfun]
    exact h
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact (((contDiffOn_six_ampA hα hα1).mul h12).neg).add
    ((contDiffOn_six_ampB_div α).mul contDiffOn_const)

/-- **`Corr α f` is `C⁶` on the open quadrant.** -/
theorem contDiffOn_six_Corr {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
      Work.FTS.EllipticEst.Q0 := by
  have hsep := Work.FTS.StrongPersist.linMem_sep_mul (α := α) (n := 6)
    (B := Work.FTS.CoercivityFix.Transfer.radA α f) (contDiffOn_six_radA hα hα1 hsm hmem7)
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z) := by
    funext z θ
    rw [Corr_eq_sep α f]
    show Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z
      = Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z)
    rw [congrFun (Gam_eq_c_mul_gamCoef hα hα1) θ]
    ring
  rw [hfun]
  have hconst : ContDiffOn ℝ 6 (fun _ : ℝ × ℝ => Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const
  refine (hconst.mul hsep).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Pi.mul_apply, Function.uncurry_apply_pair]

/-- **Continuity of the `ℋ⁶`-integrand of `Corr α f` on the open quadrant**: the hypothesis of
`LocData.HkMem_of_majorant`. -/
theorem continuousOn_HkIntegrand_Corr {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 6 (Work.FTS.CoercivityFix.Corr α f) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
  Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (le_refl 6)
    (contDiffOn_six_Corr hα hα1 hsm hmem7)

/-! ## §4 The two conclusions, given the angular and radial inputs -/

/-- The angular mass is nonnegative (`Mth6_nonneg` on `Iθ`). -/
theorem Mth6_integral_nonneg (α : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
  exact Work.FTS.StrongPersist.Mth6_nonneg α hθ

/-- **`HkMem α 6 (Corr α f)`** from the angular bound `∫_θ Mth6 α ≤ Cang` and the radial bound
`∫_z SlotSum (radA α f) ≤ Crad·HkSq α 6 f` (`LocData.HkMem_of_majorant` with the majorant
`M z θ = c(α)²·Mth6 α θ·SlotSum (radA α f) z`). -/
theorem HkMem_Corr_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {Cang : ℝ}
    (hang : ∀ β ∈ Set.Ioc 0 1,
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 β θ) ≤ Cang)
    {Crad : ℝ}
    (hrad : MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ Crad * Work.Spaces.HkSq α 6 f) :
    Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (f := Work.FTS.CoercivityFix.Corr α f)
    (M := fun z θ => (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
        * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
    ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_Corr hα hα1 hsm hmem7
  · intro z hz
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.c α) ^ 2
            * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          * Work.FTS.StrongPersist.Mth6 α θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.Mth6_integrable (α := α) hα hα1).const_mul _
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  · have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z => ((Work.Spaces.c α) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
      funext z
      have h1 : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.c α) ^ 2 * Work.FTS.StrongPersist.Mth6 α θ
              * Work.FTS.StrongPersist.SlotSum
                (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          = ∫ θ in Work.Spaces.Iθ,
              ((Work.Spaces.c α) ^ 2
                * Work.FTS.StrongPersist.SlotSum
                  (Work.FTS.CoercivityFix.Transfer.radA α f) z)
                * Work.FTS.StrongPersist.Mth6 α θ :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
      ring
    rw [hfun]
    exact hrad.1.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_Corr_le hα hα1 f hθ

/-- **The quantitative bound** `HkSq α 6 (Corr α f) ≤ 100·Cang·Crad·HkSq α 6 f`, from the same
two inputs (together with the `ℋ⁶`-membership, which makes the slices integrable). -/
theorem HkSq_Corr_le_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hmem6 : Work.Spaces.HkMem α 6 (Work.FTS.CoercivityFix.Corr α f))
    {Cang Crad : ℝ} (hCang : 0 ≤ Cang)
    (hang : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ) ≤ Cang)
    (hrad : MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ Crad * Work.Spaces.HkSq α 6 f) :
    Work.Spaces.HkSq α 6 (Work.FTS.CoercivityFix.Corr α f)
      ≤ (100 * Cang * Crad) * Work.Spaces.HkSq α 6 f := by
  have hc2 : (Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h := (Work.Spaces.c_bounds α hα hα1).2
    nlinarith [Work.FTS.StrongPersist.L3Aux.c_pos hα hα1]
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ :=
    Mth6_integral_nonneg α
  have hS0 : 0 ≤ ∫ z in Work.Spaces.Iz,
      Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z :=
    integral_nonneg fun z => Work.FTS.StrongPersist.SlotSum_nonneg _ z
  have hB0 : 0 ≤ Crad * Work.Spaces.HkSq α 6 f := le_trans hS0 hrad.2
  have hstep : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (Work.FTS.CoercivityFix.Corr α f) z θ)
        ≤ ((Work.Spaces.c α) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => ((Work.Spaces.c α) ^ 2
            * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          * Work.FTS.StrongPersist.Mth6 α θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.Mth6_integrable (α := α) hα hα1).const_mul _
    have h2 := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      h1
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => by
          refine le_trans (HkIntegrand_Corr_le hα hα1 f hθ) ?_
          exact le_of_eq (by ring)))
    rw [MeasureTheory.integral_const_mul] at h2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.CoercivityFix.Corr α f) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ((Work.Spaces.c α) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
          * Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      (hrad.1.const_mul _) hstep
  rw [Work.Spaces.HkSq]
  refine houter.trans ?_
  rw [MeasureTheory.integral_const_mul]
  calc ((Work.Spaces.c α) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ))
        * (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      ≤ ((Work.Spaces.c α) ^ 2 * Cang)
          * (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hang (sq_nonneg _)) hS0
    _ ≤ ((Work.Spaces.c α) ^ 2 * Cang) * (Crad * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hrad.2
          (mul_nonneg (sq_nonneg _) hCang)
    _ ≤ (100 * Cang) * (Crad * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hCang) hB0
    _ = (100 * Cang * Crad) * Work.Spaces.HkSq α 6 f := by ring

end Work.FTS.StrongPersist.H6Aux
