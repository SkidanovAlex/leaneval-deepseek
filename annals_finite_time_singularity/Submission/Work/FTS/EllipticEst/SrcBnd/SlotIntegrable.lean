/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of a single angular slot with an `ℋ²`-majorant

For a source `f` which is `C^∞` on the open quadrant and honestly in `ℋ²`
(`Work.Spaces.HkMem α 2 f`), an angular profile `σ` which is continuous on the quadrant and
nonnegative on `Iθ`, and a constant `C ≥ 0`, the slot integrand

  `θ ↦ w(z)² · (∂_θ^n f(z,θ))² · σ(θ)`

is dominated pointwise on `Iz × Iθ` by `C · HkIntegrand α 2 f z θ`.  Since the `ℋ²`-integrand
is honest (integrable on every angular slice, and with integrable `θ`-integral), the slot is
integrable on `Iθ` for every `z ∈ Iz`, and its `θ`-integral is integrable on `Iz`.

The measurability inputs are obtained from the regularity hypotheses: the uncurried slot is
continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`, hence a.e. strongly measurable both for
the product measure `(volume.restrict Iz).prod (volume.restrict Iθ)` and, after slicing, for
`volume.restrict Iθ` at every `z > 0` (`Work.Spaces.aesm_of_continuousOn_Qd`,
`Work.Spaces.aesm_slice_of_continuousOn_Qd`); at `z = 0` the slot vanishes identically because
`w 0 = 0`.

The module is complete: it contains no placeholders and rests only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.SrcBnd

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Preparatory lemmas -/

/-- The iterated `∂_θ`-derivatives of a function smooth on the open quadrant are smooth there. -/
theorem smoothOpen_pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n F) := by
  induction n with
  | zero => simpa using hF
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ]
      exact ih.pth

/-- The uncurried angular slot `w(z)² · (∂_θ^n f(z,θ))² · σ(θ)` is continuous on the open
quadrant, for `f` smooth on the quadrant and `σ ∘ snd` continuous there. -/
theorem continuousOn_slot {f : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} (n : ℕ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hσc : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.pthIter n f p.1 p.2) ^ 2 * σ p.2))
      Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hfθ : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter n f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (smoothOpen_pthIter hf n).continuousOn
  exact (hw.pow 2).mul ((hfθ.pow 2).mul hσc)

/-! ## The abstract integrability step -/

/-- **Integrability of a slot from an `ℋ²`-majorant.**

Let `G : ℝ → ℝ → ℝ` be nonnegative on `Iz × Iθ`, pointwise dominated there by
`C · HkIntegrand α 2 f` with `C ≥ 0`, with a.e. strongly measurable angular slices and a.e.
strongly measurable uncurried form on the product `(volume.restrict Iz).prod (volume.restrict Iθ)`.
If `f ∈ ℋ²` then every angular slice `G z ·` (`z ∈ Iz`) is integrable on `Iθ`, and
`z ↦ ∫_θ G z θ` is integrable on `Iz`. -/
theorem slot_integrable_of_bound {α : ℝ} {f G : ℝ → ℝ → ℝ} {C : ℝ}
    (hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hprod : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G z θ)
    (hmem : Work.Spaces.HkMem α 2 f) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      G z θ ≤ C * Work.Spaces.HkIntegrand α 2 f z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => G z θ) Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, G z θ) Work.Spaces.Iz := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  constructor
  · -- every angular slice of the slot is dominated by the (integrable) slice of the majorant
    intro z hz
    refine Integrable.mono' ((hmem.1 z hz).const_mul C) (hslice z hz) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem hmesθ (fun θ hθ => by
      rw [Real.norm_of_nonneg (hnn z hz θ hθ)]
      exact hbound z hz θ hθ)
  · -- the `θ`-integral of the slot is dominated by the integrable `θ`-integral of the majorant
    have hsub : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, G z θ) ≤ C * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 2 f z θ := by
      intro z hz
      calc (∫ θ in Work.Spaces.Iθ, G z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α 2 f z θ :=
            MeasureTheory.integral_mono_of_nonneg
              (MeasureTheory.ae_restrict_of_forall_mem hmesθ (fun θ hθ => hnn z hz θ hθ))
              ((hmem.1 z hz).const_mul C)
              (MeasureTheory.ae_restrict_of_forall_mem hmesθ
                (fun θ hθ => hbound z hz θ hθ))
        _ = C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 f z θ :=
            MeasureTheory.integral_const_mul C _
    refine Integrable.mono' (hmem.2.const_mul C) (hprod.integral_prod_right') ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    rw [Real.norm_of_nonneg
      (MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem hmesθ (fun θ hθ => hnn z hz θ hθ)))]
    exact hsub z hz

/-! ## The requested slot integrability -/

theorem SlotIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} (n : ℕ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hσc : ContinuousOn (fun p : ℝ × ℝ => σ p.2) Work.FTS.EllipticEst.Q0)
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hmem : Work.Spaces.HkMem α 2 f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ)
        ≤ C * Work.Spaces.HkIntegrand α 2 f z θ) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
        Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
      Work.Spaces.Iz := by
  have hcont := continuousOn_slot n hf hσc
  have hw0 : Work.Spaces.w 0 = 0 := by
    rw [Work.Spaces.w]
    norm_num
  refine slot_integrable_of_bound
    (G := fun z θ => (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n f z θ) ^ 2 * σ θ))
    ?_ ?_ ?_ hmem hC hbound
  · -- angular slices: continuity for `z > 0`, the identically zero function at `z = 0`
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => (Work.Spaces.w 0) ^ 2 *
          ((Work.Spaces.pthIter n f 0 θ) ^ 2 * σ θ)) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [hw0]
        ring
      rw [← hz0, hzero]
      exact MeasureTheory.aestronglyMeasurable_zero
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  · -- the uncurried slot is a.e. strongly measurable for the product measure
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · -- nonnegativity of the slot on the quadrant
    intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hσnn θ hθ))

end Work.FTS.EllipticEst.SrcBnd
