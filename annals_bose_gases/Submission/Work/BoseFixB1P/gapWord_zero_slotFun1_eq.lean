import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.gapWord_zero_slotFun1_eq`

The `N = 1` instance of the large-box slot identity
`Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus`: for the single-slot state
`slotFun1 φ` the large-box gap word (`Work.BoseKinLoc.gapWord`, i.e.
`bℓ⁻²Q_Λ` on the anchored box `Λ(0) = acube ℓ`) is exactly `bℓ⁻²` times the
excited count `cnPlus ℓ φ = Σᵢ‖Qᵢφ‖²`:

  `gapWord ℓ b 0 (slotFun1 φ) = b ℓ⁻² · cnPlus ℓ φ`.

Both sides are the `bℓ⁻²` multiple of an integral of `(ψ - m)²` against the box
measure, where `m` is the (box) mean of `ψ = slotFun1 φ`.  The only content is
that the *anchored* box integral over `acube ℓ` and the one-particle box
integral over `abox 1 ℓ` agree; this is the measure-preserving identification
`Work.MGroupInput.integral_abox_one` (`X 1 ≃ᵐ ℝ³` by evaluation at the unique
index of `Fin 1`).  The box mean of the fibre is `Work.BoseKinetic.aP`, which is
*x-independent* on `X 1` and equal to the moving-box mean `bsMean ℓ 0`.

Unlike `slotSum_gapWord_eq_b_cnPlus` no smoothness of `φ` is required: the
identity is a change of variables, valid for every `φ`.
-/

namespace Work.BoseFixB1P

open MeasureTheory

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false

theorem gapWord_zero_slotFun1_eq (ℓ b : ℝ) (φ : Submission.BoseGases.X 1 → ℝ) :
    Work.BoseKinLoc.gapWord ℓ b 0 (Work.BSKinetic.slotFun1 φ)
      = b * ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ φ := by
  -- The condensate mean `aP` of the one-slot state is the (constant) moving-box mean
  -- `bsMean ℓ 0`, because on `X 1` the update `Function.update x i y` forgets `x`.
  have hm : ∀ x : Submission.BoseGases.X 1,
      Submission.BoseGases.aP ℓ (0 : Fin 1) φ x
        = Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ) := by
    intro x
    simp only [Submission.BoseGases.aP, Work.BSKinetic.bsMean, Work.BSKinetic.slotFun1, one_div]
    congr 1
    have hfun : (fun y : ℝ³ => φ (Function.update x 0 y))
        = (fun z : ℝ³ => φ (fun _ => ℓ • 0 + z)) := by
      funext y
      congr 1
      funext j
      fin_cases j
      simp [Function.update]
    rw [hfun]
  -- The gap form is the anchored-box integral of `(slotFun1 φ - bsMean)²`.
  have hgap : Work.BoseKinLoc.gapBare ℓ 0 (Work.BSKinetic.slotFun1 φ)
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BSKinetic.slotFun1 φ z
            - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2 := by
    have hlam : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
      ext x
      simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
    simp only [Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, hlam]
  -- The excited count is the same integral over the one-particle box.
  have hcn : Submission.BoseGases.cnPlus ℓ φ
      = ∫ x in Submission.BoseGases.abox 1 ℓ,
          (Work.BSKinetic.slotFun1 φ (x 0)
            - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2 := by
    rw [Submission.BoseGases.cnPlus, Fin.sum_univ_one]
    have hfun : (fun x : Submission.BoseGases.X 1 =>
          (Submission.BoseGases.aQ ℓ (0 : Fin 1) φ x) ^ 2)
        = (fun x : Submission.BoseGases.X 1 =>
          (Work.BSKinetic.slotFun1 φ (x 0)
            - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2) := by
      funext x
      rw [Submission.BoseGases.aQ, hm x]
      congr 1
      congr 1
      show φ x = φ (fun _ : Fin 1 => x 0)
      congr 1
      funext j
      fin_cases j
      rfl
    rw [hfun]
  -- The two box integrals agree by the measure-preserving identification `X 1 ≃ᵐ ℝ³`.
  have hint : (∫ x in Submission.BoseGases.abox 1 ℓ,
        (Work.BSKinetic.slotFun1 φ (x 0)
          - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2)
      = ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BSKinetic.slotFun1 φ z
            - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2 :=
    Work.MGroupInput.integral_abox_one ℓ
      (fun z => (Work.BSKinetic.slotFun1 φ z
          - Work.BSKinetic.bsMean ℓ 0 (Work.BSKinetic.slotFun1 φ)) ^ 2)
  have hbare : Work.BoseKinLoc.gapBare ℓ 0 (Work.BSKinetic.slotFun1 φ)
      = Submission.BoseGases.cnPlus ℓ φ := by
    rw [hgap, hcn, hint]
  rw [Work.BoseKinLoc.gapWord, hbare]

end

end Work.BoseFixB1P
