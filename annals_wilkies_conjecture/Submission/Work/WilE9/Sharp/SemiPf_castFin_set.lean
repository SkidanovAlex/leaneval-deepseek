import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE7.reindex_eval
import Submission.Work.WilE8.Star.init_deg_fmt

namespace Work.WilE9.Sharp

open WilkiesDesign WilkiesDesign.E

/-- `SemiPf.castFin h` is literally the coordinate reindexing of `Work.WilE7.SemiPf.reindex`
along the equivalence `finCongr h` (they are the same structure: the chain coefficient is
`X.c.a j (Fin.cast h.symm i)` on both sides and the polynomials are renamed along
`Sum.map (Fin.cast h) id`). -/
theorem SemiPf.castFin_eq_reindex {a b : ℕ} (h : a = b) (X : WilkiesDesign.E.SemiPf a) :
    Work.WilE9.Sharp.SemiPf.castFin h X = Work.WilE7.SemiPf.reindex (finCongr h) X := rfl

theorem SemiPf_castFin_set {a b : ℕ} (h : a = b) (X : WilkiesDesign.E.SemiPf a) :
    (Work.WilE9.Sharp.SemiPf.castFin h X).set =
      {y : Fin b → ℝ | (fun i : Fin a => y (Fin.cast h i)) ∈ X.set} ∧
    (Work.WilE9.Sharp.SemiPf.castFin h X).fmt = X.fmt ∧
    (Work.WilE9.Sharp.SemiPf.castFin h X).deg = X.deg ∧
    (Work.WilE9.Sharp.SemiPf.castFin h X).basics.length = X.basics.length := by
  have hcast : Work.WilE9.Sharp.SemiPf.castFin h X
      = Work.WilE7.SemiPf.reindex (finCongr h) X := SemiPf.castFin_eq_reindex h X
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcast]
    exact Work.WilE7.reindex_eval.2 (finCongr h) X
  · rw [hcast, Work.WilE8.Star.semipf_fmt_reindex]
    simp only [WilkiesDesign.E.SemiPf.fmt]
    omega
  · rw [hcast]
    exact Work.WilE8.Star.semipf_deg_reindex (finCongr h) X
  · rw [hcast]
    simp only [Work.WilE7.SemiPf.reindex, List.length_map]

end Work.WilE9.Sharp
