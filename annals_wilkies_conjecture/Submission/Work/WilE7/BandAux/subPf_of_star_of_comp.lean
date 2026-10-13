import Mathlib
import Submission.Work.WilE7.GraphCellAux.subPf_projFirst
import Submission.Work.WilE7.GraphCellAux.subPf_list_iUnion
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE7.BandAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- A single `*`-piece is sub-Pfaffian, provided every connected component of every
semi-Pfaffian set is sub-Pfaffian (the hypothesis `hcomp`).  A `*`-piece is exactly
`projFirst n P.m '' connectedComponentIn P.X.set P.p`, so this is `subPf_projFirst` applied
to `hcomp P.X P.p`. -/
theorem subPf_starPiece_set {n : ℕ}
    (hcomp : ∀ {N : ℕ} (X : SemiPf N) (x : Fin N → ℝ),
      SubPf N (connectedComponentIn X.set x)) (P : StarPiece n) :
    SubPf n P.set :=
  Work.WilE7.GraphCellAux.subPf_projFirst (hcomp P.X P.p)

theorem subPf_of_star_of_comp {n F D : ℕ} {Y : Set (Fin n → ℝ)}
    (h : WilkiesDesign.E.Star F D n Y)
    (hcomp : ∀ {N : ℕ} (X : WilkiesDesign.E.SemiPf N) (x : Fin N → ℝ),
      WilkiesDesign.E.SubPf N (connectedComponentIn X.set x)) :
    WilkiesDesign.E.SubPf n Y := by
  obtain ⟨L, hY, -, -⟩ := h
  rw [hY]
  exact Work.WilE7.GraphCellAux.subPf_list_iUnion L (fun P => P.set)
    (fun P _ => subPf_starPiece_set hcomp P)

end Work.WilE7.BandAux
