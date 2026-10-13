/-
  Subproject WilE9G / Assembly — the API of `ambOf`.

  `ambOf S` is the ambient stratum `AmbStratum N` obtained from a frozen ambient stratum
  `S : Stratum 0 N` by the coordinate relabelling
  `Work.WilE9G.Amb.castEquiv N : Fin (0 + N) ≃ Fin N`.

  This file computes the point set, the `Good` predicate and the numeric invariants
  (`deg`, `X.fmt`, `X.basics.length`) of `ambOf S` on the nose.  Note that the invariant `deg`
  of an `AmbStratum` is `X.deg + ∑ a, atomDeg (S.h a)` — the same formula as for the frozen
  `Stratum.deg` — so its preservation is exactly the preservation of the semi-Pfaffian degree
  `SemiPf.deg` together with the preservation of `atomDeg` under a coordinate reindexing.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.ambOf
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-- The point set of `ambOf S`, in the form used in the API: reindexing the coordinates along
`Work.WilE9G.Amb.castEquiv N` pulls the set back. -/
theorem ambOf_X_set {N : ℕ} (S : Stratum 0 N) :
    (ambOf S).X.set =
      {z : Fin N → ℝ |
        (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ S.X.set} :=
  Work.WilE7.sp_reindex_set (Work.WilE9G.Amb.castEquiv N) S.X

/-- The degree of `ambOf S` is the degree of `S`: the semi-Pfaffian degree and the atom degrees
of the equations are both preserved by a coordinate reindexing. -/
theorem ambOf_deg {N : ℕ} (S : Stratum 0 N) :
    (ambOf S).deg = S.deg := by
  show AmbStratum.deg (ambOf S) = WilkiesDesign.E.Stratum.deg S
  simp only [ambOf, AmbStratum.deg, WilkiesDesign.E.Stratum.deg]
  congr 1
  · exact Work.WilE8.Star.semipf_deg_reindex (Work.WilE9G.Amb.castEquiv N) S.X
  · apply Finset.sum_congr rfl
    intro a _
    exact Work.WilE7.sp_atomDeg_reindex (Work.WilE9G.Amb.castEquiv N) (S.h a)

/-- The format of the semi-Pfaffian part of `ambOf S` is the format of `S.X`. -/
theorem ambOf_X_fmt {N : ℕ} (S : Stratum 0 N) : (ambOf S).X.fmt = S.X.fmt := by
  show (Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N) S.X).fmt = S.X.fmt
  rw [Work.WilE8.Star.semipf_fmt_reindex]
  simp only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add]

/-- The number of disjuncts of `ambOf S` is the number of disjuncts of `S`. -/
theorem ambOf_X_basics_length {N : ℕ} (S : Stratum 0 N) :
    (ambOf S).X.basics.length = S.X.basics.length :=
  List.length_map _

/-- **The API of `ambOf`.** The transport of a frozen ambient stratum `Stratum 0 N` to an
`AmbStratum N` preserves, on the nose, the point set (under the coordinate relabelling
`castEquiv N`), the `Good` predicate, and the three numeric invariants `deg`, `X.fmt` and
`X.basics.length`. -/
theorem ambOf_api {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    (Work.WilE9G.Assembly.ambOf S).X.set =
        {z : Fin N → ℝ |
          (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ S.X.set} ∧
      (S.Good → (Work.WilE9G.Assembly.ambOf S).Good) ∧
      (Work.WilE9G.Assembly.ambOf S).deg = S.deg ∧
      (Work.WilE9G.Assembly.ambOf S).X.fmt = S.X.fmt ∧
      (Work.WilE9G.Assembly.ambOf S).X.basics.length = S.X.basics.length :=
  ⟨ambOf_X_set S, fun h => Work.WilE9G.Amb.good_bwd S h, ambOf_deg S, ambOf_X_fmt S,
    ambOf_X_basics_length S⟩

end Work.WilE9G.Assembly
