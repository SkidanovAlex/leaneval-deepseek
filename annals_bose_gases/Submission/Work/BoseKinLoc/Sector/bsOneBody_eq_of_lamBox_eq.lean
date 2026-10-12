import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.box_inv_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.bsOneBody_eq_of_lamBox_eq`

The windowed kinetic form `bsOneBody ℓ F u ψ` sees the one-body state `ψ` only through the
product `χ_u · Q_{Λ(u)}ψ`.  Both factors are *box-local*:

* the window `χ_u = bsWin ℓ u` is supported in the moving box `Λ(u) = lamBox ℓ u`
  (`Work.BoseKinLoc.Word.bsWin_eq_zero_of_not_mem_lamBox`, from the support lemma
  `Work.BSKinetic.tsupport_bsWin_subset_bsBox`);
* on the box, the mean-free projection `Q_uψ = bsQ ℓ u ψ = ψ − bsMean ℓ u ψ` agrees as soon
  as `ψ` does, because the box mean `bsMean ℓ u ψ` is an integral over `Λ(u)`
  (`Work.BoseKinLoc.Sector.Qfree_eq_of_lamBox_eq`).

Hence `ψ = ψ'` on `Λ(u)` forces the two windowed states `χ_u·Q_uψ` and `χ_u·Q_uψ'` to be the
same function, and therefore the Fourier integral `bsOneBody` agrees.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Sector

open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bsOneBody_eq_of_lamBox_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) (u : ℝ³)
    {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ Work.BoseKinLoc.lamBox ℓ u → ψ z = ψ' z) :
    Work.BSKinetic.bsOneBody ℓ F u ψ = Work.BSKinetic.bsOneBody ℓ F u ψ' := by
  -- the mean-free states agree on the box
  have hQ : ∀ z : ℝ³, z ∈ lamBox ℓ u → bsQ ℓ u ψ z = bsQ ℓ u ψ' z :=
    Qfree_eq_of_lamBox_eq hℓ u h
  -- hence the two windowed states are the same function
  have hfun : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ))
      = (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ' z : ℂ)) := by
    funext z
    by_cases hz : z ∈ lamBox ℓ u
    · rw [hQ z hz]
    · rw [Word.bsWin_eq_zero_of_not_mem_lamBox hℓ u hz]
      simp
  unfold bsOneBody
  rw [hfun]

end Work.BoseKinLoc.Sector
