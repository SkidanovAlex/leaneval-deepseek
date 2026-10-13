import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Sard.goodFDerivSurjective
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Sard
open WilkiesDesign WilkiesDesign.E
open Work.WilE9G

theorem goodFDerivSurjective_amb {N : ℕ} (S : Work.WilE9G.AmbStratum N) (hS : S.Good)
    {z : Fin N → ℝ} (hz : z ∈ S.X.set) :
    Function.Surjective
      (fderiv ℝ (fun z : Fin N → ℝ => fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a) z) z) := by
  have hrank := Work.WilE9G.AmbStratum_rank S hS hz
  rw [Work.WilE5.Strat.fderiv_pi_eaEval]
  exact pi_surjective_of_rank_eq_card (fun a i => eaEval S.X.c (eaD S.X.c i (S.h a)) z) hrank

end Work.WilE9G.Sard
