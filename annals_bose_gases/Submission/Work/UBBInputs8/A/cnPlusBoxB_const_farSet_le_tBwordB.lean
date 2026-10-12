import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.dlBox_eq_empty_of_mem_farSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

/-! Round 8, strand A (the kinetic clause audit).

Because the corpus's small-box projection `boxQ` carries no box indicator, the corpus's box word
`tBwordB N ℓ d ε c u` (which contains the gap term `tbGapCoeff (ℓd) ε · cnPlusBoxB N ℓ d u`, plus
the nonnegative spectral part) is **positive on the far set at the constant state** — although
the box `dlBox ℓ d u` is empty and FS's slide at that position carries no energy at all.  This
statement is the pointwise lower bound that makes the integrand of the kinetic residual
non-integrable (`A.not_integrable_tBwordB_const`).  Route: the corpus's
`Work.SmallBoxTBWord.tBword_ge_gapPart` (the gap part is a lower bound for `tBword`, needing
`0 ≤ a` with `a := ℓ`) + `Work.UBBInputs8.A.cnPlusBoxB_const_eq_of_mem_farSet`. -/
theorem cnPlusBoxB_const_farSet_le_tBwordB {N : ℕ} {ℓ d ε c μ : ℝ} (hN : 1 ≤ N)
    (hℓ : 0 < ℓ) (hd : 0 < d) (hε : 0 < ε) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d μ) :
    Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
        * ((N : ℝ) * ((MeasureTheory.volume : MeasureTheory.Measure
            (Submission.BoseGases.X N)) (Submission.BoseGases.abox N ℓ)).toReal)
      ≤ Work.SmallBoxTBWord.tBwordB N ℓ d ε c u
          (fun _ : Submission.BoseGases.X N => (1 : ℝ)) := by
  -- On the far set the sliding box `B(u) = dlBox ℓ d u` is empty.
  have hbox : Submission.BoseGases.dlBox ℓ d u = ∅ :=
    dlBox_eq_empty_of_mem_farSet hℓ hd hu
  -- hence the box mean in every slot vanishes ...
  have hboxP : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i
        (fun _ : Submission.BoseGases.X N => (1 : ℝ)) x = 0 := by
    intro i x
    simp [Work.SmallBoxTBWord.boxP, hbox]
  -- ... the corpus (indicator-free) projection `boxQ` acts as the identity ...
  have hQ : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i
        (fun _ : Submission.BoseGases.X N => (1 : ℝ)) x = 1 := by
    intro i x
    simp [Work.SmallBoxTBWord.boxQ, hboxP i x]
  -- ... and the excited count of the constant state is `N·|abox N ℓ|`.
  have hcn : Work.SmallBoxTBWord.cnPlusBoxB N ℓ d u
        (fun _ : Submission.BoseGases.X N => (1 : ℝ))
      = (N : ℝ) * ((MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X N)) (Submission.BoseGases.abox N ℓ)).toReal := by
    unfold Work.SmallBoxTBWord.cnPlusBoxB Work.SmallBoxTBWord.cnPlusBox
    simp only [hQ, one_pow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
  rw [← hcn]
  exact Work.SmallBoxTBWord.tBword_ge_gapPart (le_of_lt hℓ)

end Work.UBBInputs8.A
