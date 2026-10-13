import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Mult.surjective_pi_of_rank_eq_card

namespace Work.WilE9G.Lagrange

theorem surjective_hBlock {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (hS : S.Good) (z : Fin (n + (1 + m)) → ℝ) (hz : z ∈ S.X.set) :
    Function.Surjective (fun vz : Fin (n + (1 + m)) → ℝ => fun a : Fin S.j =>
      ∑ l : Fin (n + (1 + m)), WilkiesDesign.E.eaEval S.X.c
        (WilkiesDesign.E.eaD S.X.c l (S.h a)) z * vz l) := by
  have hrank :
      (Matrix.of fun (a : Fin S.j) (l : Fin (n + (1 + m))) =>
        WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c l (S.h a)) z).rank = S.j :=
    Work.WilE9G.AmbStratum_rank S hS hz
  have hsurj := Work.WilE9G.Mult.surjective_pi_of_rank_eq_card
    (fun (a : Fin S.j) (l : Fin (n + (1 + m))) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c l (S.h a)) z) hrank
  intro w
  obtain ⟨vz, hvz⟩ := hsurj w
  refine ⟨vz, ?_⟩
  funext a
  have h := congrFun hvz a
  simpa using h

end Work.WilE9G.Lagrange
