import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
import Submission.Work.ESYRound5.Energy.pairSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

theorem pair_coord_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      g z.1 z.2)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => g (x i) (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  -- Two distinct labels force at least two particles, so `n = M + 2`.
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 2 :=
    ⟨n - 2, by have := Work.BoseFixB2.Pot.two_le_of_ne hij; omega⟩
  -- The second label is reached from the first by `succAbove`.
  obtain ⟨b', hb'⟩ : ∃ b' : Fin (M + 1), i.succAbove b' = j :=
    Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  rw [← hb']
  -- Restricting an integrable function of the two slots to the cube square and
  -- pulling it back over the box (`integrableOn_abox_comp_pair_coord`).
  exact Work.ESYRound5.Energy.integrableOn_abox_comp_pair_coord (M := M) hℓ.le i b'
    hg.integrableOn

end Work.BoseFixB3.CS.Pieces
