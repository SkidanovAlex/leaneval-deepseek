import Mathlib
import Submission.Work.WilE5.Strat.DescP
import Submission.Work.WilE5.Strat.cover

namespace Work.WilE5.Strat

theorem levelP_eq_flatMap_descP {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (Ml : ℕ → ℕ)
    (NΦ : ℕ) (k : ℕ) :
    Work.WilE5.levelP X Ml NΦ k =
      (Work.WilE5.initStates X).flatMap (fun σ => Work.WilE5.Strat.descP X Ml NΦ σ k) := by
  induction k with
  | zero => simp [Work.WilE5.levelP_zero, Work.WilE5.Strat.descP_zero]
  | succ k ih =>
    show (Work.WilE5.levelP X Ml NΦ k).flatMap
        (fun σ => Work.WilE5.childrenP X.c Ml NΦ σ)
      = (Work.WilE5.initStates X).flatMap
          (fun σ => Work.WilE5.Strat.descP X Ml NΦ σ (k + 1))
    have h1 : (Work.WilE5.initStates X).flatMap
          (fun σ => Work.WilE5.Strat.descP X Ml NΦ σ (k + 1))
        = (Work.WilE5.initStates X).flatMap (fun σ =>
            (Work.WilE5.Strat.descP X Ml NΦ σ k).flatMap
              (fun τ => Work.WilE5.childrenP X.c Ml NΦ τ)) := by
      simp only [Work.WilE5.Strat.descP_succ]
    rw [h1, ← List.flatMap_assoc, ← ih]

end Work.WilE5.Strat
