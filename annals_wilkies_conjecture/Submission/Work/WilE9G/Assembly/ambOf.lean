/-
  Subproject WilE9G / Assembly — the transport of the frozen ambient strata `Stratum 0 N` to the
  ambient strata `AmbStratum N` of `WilE9G.Amb`.

  A frozen stratum `Stratum 0 N` lives in `ℝ^{0+N}`; an `AmbStratum N` lives in `ℝ^N`.  The two
  ambient dimensions are related by the (value preserving) coordinate relabelling
  `Work.WilE9G.Amb.castEquiv N = finCongr (Nat.zero_add N) : Fin (0+N) ≃ Fin N`, exactly as in
  `Work.WilE9G.Amb.stratum_zero_to_amb`, which proves that *some* `AmbStratum` obtained this way
  is `Good` iff the frozen stratum is.

  Here the transport is fixed as a *definition* rather than an existential, so that the numeric
  invariants (`deg`, `fmt`, `basics.length`) can be computed on the nose: the equations of
  `ambOf S` are the reindexed equations `EAPoly.reindex (castEquiv N) (S.h a)`, whence `atomDeg`
  is preserved (`Work.WilE7.sp_atomDeg_reindex`) and `(ambOf S).deg = S.deg`.
-/
import Mathlib
import Submission.Work.WilE9G.Reduce
import Submission.Work.WilE9G.Amb.stratum_zero_to_amb
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-- The ambient stratum `AmbStratum N` obtained from a frozen ambient stratum `S : Stratum 0 N`
by the coordinate relabelling `Work.WilE9G.Amb.castEquiv N : Fin (0 + N) ≃ Fin N`: the same
semi-Pfaffian set, pulled back along the relabelling, and the same equations, reindexed. -/
def ambOf {N : ℕ} (S : Stratum 0 N) : AmbStratum N :=
  ⟨Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N) S.X, S.j,
    fun a => Work.WilE7.EAPoly.reindex (Work.WilE9G.Amb.castEquiv N) (S.h a)⟩

@[simp] theorem ambOf_j {N : ℕ} (S : Stratum 0 N) : (ambOf S).j = S.j := rfl

@[simp] theorem ambOf_X_r {N : ℕ} (S : Stratum 0 N) : (ambOf S).X.r = S.X.r := rfl

@[simp] theorem ambOf_X_c {N : ℕ} (S : Stratum 0 N) :
    (ambOf S).X.c = Work.WilE7.EAChain.reindex (Work.WilE9G.Amb.castEquiv N) S.X.c := rfl

@[simp] theorem ambOf_X_basics {N : ℕ} (S : Stratum 0 N) :
    (ambOf S).X.basics =
      S.X.basics.map (Work.WilE7.Basic.reindex (Work.WilE9G.Amb.castEquiv N)) := rfl

@[simp] theorem ambOf_h {N : ℕ} (S : Stratum 0 N) (a : Fin S.j) :
    (ambOf S).h a = Work.WilE7.EAPoly.reindex (Work.WilE9G.Amb.castEquiv N) (S.h a) := rfl

end Work.WilE9G.Assembly
