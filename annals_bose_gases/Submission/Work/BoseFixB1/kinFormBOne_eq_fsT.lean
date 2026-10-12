import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Sector.tensor_kinFormB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.kinFormBOne_eq_fsT` — the box kinetic word at one particle

The box-restricted `N`-body kinetic word of FS `eq:Def_HB` is

    `kinFormB N ℓ d s εT b Φ
       = ℓ⁻³ Σᵢ ∫_{x ∈ abox N ℓ} 1_{Λ(0)}(xᵢ) · 𝒯₀(fibre i Φ x)`,

where `𝒯 = fsT` is the one-body word of FS `eq:DefT` and `fibre N i Φ x` is the slot-`i`
fibre `z ↦ Φ(x with xᵢ = z)`.

At `N = 1` there is only one slot, and the fibre of a one-particle state is the state
itself (`X 1 = Fin 1 → ℝ³` has a unique slot).  Hence the configuration integral is the
integral of the box indicator `indU ℓ 0 (x 0)` over the one-particle box `abox 1 ℓ`, which
is the box volume `ℓ³`, and the normalisation `ℓ⁻³` cancels it:

    `kinFormB 1 ℓ d s εT b φ = 𝒯₀ (slotFun1 φ)`.

This is the `N = 1` anchor of the slot decomposition `kinFormB_succ_eq_slotSum`, where the
one-particle word `kinFormB 1` is the object on which the one-body localisation bounds
(`Work.BSKinetic.OneBodySmallBoxBound`, `Work.BoseFixB1.oneBodyKineticHalf`) are stated.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

-- NOTE: the token `ℝ³` is already a GLOBAL notation (`Submission/Work/BoseKinLoc/Defs.lean:84`),
-- which is in this file's import closure; a second `local notation "ℝ³"` here would make every
-- occurrence of `ℝ³` an `Ambiguous term`.  Do not re-add it.

/-! ## The fibre of a one-particle state -/

/-- With a single slot (`X 1 = Fin 1 → ℝ³`) the configuration carries no information: the
slot-`0` fibre of a one-particle state is the state itself. -/
lemma fibre_one_zero (φ : Submission.BoseGases.X 1 → ℝ) (x : Submission.BoseGases.X 1) :
    Work.BoseKinLoc.fibre 1 0 φ x = Work.BSKinetic.slotFun1 φ :=
  funext fun z => congrArg φ (funext fun j => by fin_cases j; simp)

/-! ## The box indicator integrates to the box volume -/

/-- The box indicator `θ₀ = 1_{Λ(0)}` integrates over the one-particle box to `ℓ³`.  This is
`integral_abox_indU_erase` at `n = 1` and the constant test function `1` (the product over
the empty erase-set is `1`, and the remaining factor is `(∫ 1)⁰ = 1`). -/
lemma integral_indU_zero_abox_one {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x in Submission.BoseGases.abox 1 ℓ, Work.BoseKinLoc.indU ℓ 0 (x 0)) = ℓ ^ 3 := by
  have h := Work.Sector.integral_abox_indU_erase (n := 1) (ℓ := ℓ) hℓ (0 : Fin 1)
    (fun _ : ℝ³ => (1 : ℝ))
  simpa using h

/-! ## The main identity -/

theorem kinFormBOne_eq_fsT {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (φ : Submission.BoseGases.X 1 → ℝ) :
    Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ
      = Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BSKinetic.slotFun1 φ) := by
  set c := Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BSKinetic.slotFun1 φ) with hc
  -- unfold `kinFormB`, evaluate the single-slot sum
  rw [show Work.BoseKinLoc.kinFormB 1 ℓ d s εT b φ
        = ℓ ^ (-3 : ℤ) * ∑ i : Fin 1, ∫ x in Submission.BoseGases.abox 1 ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre 1 i φ x) from rfl,
    Fin.sum_univ_one]
  -- the fibre is the state itself, so the word does not depend on the configuration
  have hcongr : (fun x : Submission.BoseGases.X 1 => Work.BoseKinLoc.indU ℓ 0 (x 0) *
        Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre 1 0 φ x))
      = fun x => Work.BoseKinLoc.indU ℓ 0 (x 0) * c := by
    funext x
    rw [fibre_one_zero φ x, hc]
  -- pull out the constant and evaluate the indicator integral
  rw [hcongr, MeasureTheory.integral_mul_const, integral_indU_zero_abox_one hℓ]
  have hz : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [zpow_neg]
    exact inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))
  calc ℓ ^ (-3 : ℤ) * (ℓ ^ 3 * c) = c * (ℓ ^ (-3 : ℤ) * ℓ ^ 3) := by ring
    _ = c := by rw [hz]; ring

end Work.BoseFixB1
