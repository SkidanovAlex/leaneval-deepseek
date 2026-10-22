import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelAux

namespace Work.ANALYTIC.CechPt

/-- Telescoping along the chain `0, 1, …, n` of `Fin (n+1)`: the first differences of `a`
sum to `a 0 - a (last)`. -/
private theorem fin_telescope {n : ℕ} (a : Fin (n + 1) → ℤ) :
    (∑ j : Fin n, (a (Fin.castSucc j) - a (j.succ))) = a 0 - a (Fin.last n) := by
  have h1 := Fin.sum_univ_castSucc a
  have h2 := Fin.sum_univ_succ a
  rw [Finset.sum_sub_distrib]
  linarith

/-- The telescoping identity for the cut maps `midH t` (`t : Fin (q+3)`) together with the
two endpoint computations `midH 0 = rhoS` and `midH (last) = id`. -/
theorem midH_telescope {M q : ℕ} (y : Work.ANALYTIC.CechPt.Level.lev M (q+1)) (F : Work.ANALYTIC.CechPt.Level.lev M (q+1) → ℤ) :
    (∑ j : Fin (q+2), (F (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ), by omega⟩ y)
        - F (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ)+1, by omega⟩ y)))
      = F (Work.ANALYTIC.CechPt.Level.rhoS y) - F y := by
  have key := fin_telescope (fun t : Fin ((q+2)+1) => F (Work.ANALYTIC.CechPt.Level.midH t y))
  have hgoal : (∑ j : Fin (q+2), (F (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ), by omega⟩ y)
        - F (Work.ANALYTIC.CechPt.Level.midH ⟨(j:ℕ)+1, by omega⟩ y)))
      = ∑ j : Fin (q+2), (F (Work.ANALYTIC.CechPt.Level.midH (Fin.castSucc j) y)
        - F (Work.ANALYTIC.CechPt.Level.midH (j.succ) y)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show (⟨(j:ℕ), by omega⟩ : Fin ((q+1)+2)) = Fin.castSucc j from Fin.ext rfl,
        show (⟨(j:ℕ)+1, by omega⟩ : Fin ((q+1)+2)) = Fin.succ j from Fin.ext rfl]
  rw [hgoal]
  simpa only [Work.ANALYTIC.CechPt.Level.midH_zero, Work.ANALYTIC.CechPt.Level.midH_last] using key

end Work.ANALYTIC.CechPt
