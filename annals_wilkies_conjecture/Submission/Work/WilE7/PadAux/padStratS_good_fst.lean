import Mathlib
import Submission.Work.WilE7.PadDefs

namespace Work.WilE7.PadAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7

theorem padStratS_good_fst (p q d : ℕ) (S : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (hj : S.j = q) (z : Fin (p + (d + q)) → ℝ)
    (hz : z ∈ (Work.WilE7.padStratS p q d S hj).X.set) (a : Fin (d + q)) :
    WilkiesDesign.E.eaEval (Work.WilE7.padStratS p q d S hj).X.c
      ((Work.WilE7.padStratS p q d S hj).h a) z = 0 := by
  -- Unfold the point set of the padded stratum.
  have hz' := hz
  rw [padStratS_X, padStrat_set] at hz'
  obtain ⟨hmem, hpin⟩ := hz'
  rw [tidy_set] at hmem
  have hgood := hGood _ hmem
  -- Put the chain of the padded stratum in the form `extend (midInj) (tidy S.X).c` so that
  -- all chain types below agree syntactically.
  change WilkiesDesign.E.eaEval
      (Work.WilE8.EAChain.extend (midInj p d q) (tidy S.X).c)
      ((Work.WilE7.padStratS p q d S hj).h a) z = 0
  refine Fin.addCases (fun a' => ?_) (fun b => ?_) a
  · -- inserted (pinned) coordinate
    rw [padStratS_h_castAdd, eaEval_pinAt]
    exact hpin a'
  · -- pulled-back defining function of the original stratum
    rw [padStratS_h, padHead_natAdd, eaEval_extend_midInj]
    exact hgood.1 (Fin.cast hj.symm b)

end Work.WilE7.PadAux
