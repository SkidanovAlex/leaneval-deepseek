import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imagesFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The two spellings of the *(slot `i`, coordinate `j`)*-direction of `X n` coincide:
`Work.BoseBoxFock.slotDirVec` (the fibre vocabulary) and `Submission.BoseGases.kcDir`
(the kinetic-bridge vocabulary) are the same vector. -/
lemma imgFibreDchiSelf_slotDirVec_eq_kcDir {n : ℕ} (i : Fin n) (j : Fin 3) :
    slotDirVec i j = Submission.BoseGases.kcDir n i j := rfl

/-- `aQ` is free for the derivative in its *own* slot. -/
lemma imgFibreDchiSelf_fderiv_aQ_slotDirVec {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {F : Submission.BoseGases.X n → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (x : Submission.BoseGases.X n) (j : Fin 3) :
    fderiv ℝ (Submission.BoseGases.aQ ℓ i F) x (slotDirVec i j)
      = fderiv ℝ F x (slotDirVec i j) := by
  rw [imgFibreDchiSelf_slotDirVec_eq_kcDir, Submission.BoseGases.fderiv_aQ_kcDir hℓ i hF x j]

theorem imgFibreDchiSelf {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {F : Submission.BoseGases.X n → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Work.BoseBoxFock.imgFibreDχ ℓ p (Submission.BoseGases.aQ ℓ p.1 F)
      ≤ Work.BoseBoxFock.imgFibreDχ ℓ p F := by
  refine le_of_eq ?_
  unfold imgFibreDχ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hsum : (∑ j : Fin 3,
        (fderiv ℝ (Submission.BoseGases.aQ ℓ p.1 F) x (slotDirVec p.1 j)) ^ 2)
      = ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by
      rw [imgFibreDchiSelf_fderiv_aQ_slotDirVec hℓ p.1 hF x j])
  simp only [hsum]

end Work.BoseBoxFock
