/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The action of `G` on the oriented edges of the graphs of the pattern

`Basic.lean` registers the action of `G` on the oriented edges `AdjPair T` of a `G`-tree.  The
cocompactness and finite-generation arguments of `DESIGN_N13.md` §10.5 need the same for the
three graphs that carry the Dunwoody pattern:

* `chordGraph D` on the pattern points (`Dunwoody/Track.lean`),
* `regionGraph D` on the old vertices (`Dunwoody/Region.lean`),
* `dualGraph D` on the regions (`Dunwoody/TrackWall.lean`),

each of which is invariant under the `G`-action (`chordGraph_smul_adj`, `regionGraph_smul_adj`,
`dualGraph_smul_adj`).  The instances defined here let one *state* finiteness of the orbit
quotient of the oriented edges (`Finite (MulAction.orbitRel.Quotient G ...)`), which is the form
in which `IsCocompact` is stated for a `GTree` (`Basic.lean`).

The corresponding graph-theoretic statement used in §10.5 is: a group acting freely on a
connected graph with finitely many orbits of vertices and of oriented edges is finitely
generated.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Region
import Submission.Work.ORDunwoody.Dunwoody.TrackWall
import Submission.Work.ORDunwoody.regionRel_smul

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## Invariance of the region graph -/

/-- The region graph is invariant under the action of `G`. -/
theorem regionGraph_smul_adj (g : G) {u w : BaseV D} (h : (regionGraph D).Adj u w) :
    (regionGraph D).Adj (g • u) (g • w) := by
  rw [regionGraph_adj_iff] at h ⊢
  refine ⟨fun hc => h.1 (MulAction.injective g hc), ?_⟩
  rcases h.2 with h2 | h2
  · exact Or.inl (Work.ORDunwoody.regionRel_smul g h2)
  · exact Or.inr (Work.ORDunwoody.regionRel_smul g h2)

/-! ## The oriented edges of the three graphs -/

/-- **The action of `G` on the oriented edges of the chord graph.** -/
noncomputable instance instMulActionChordAdj :
    MulAction G {p : MidV D × MidV D // (chordGraph D).Adj p.1 p.2} where
  smul g p := ⟨(g • p.1.1, g • p.1.2), chordGraph_smul_adj g p.2⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul G p.1.1) (one_smul G p.1.2))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h p.1.1) (mul_smul g h p.1.2))

/-- **The action of `G` on the oriented edges of the region graph.** -/
noncomputable instance instMulActionRegionAdj :
    MulAction G {p : BaseV D × BaseV D // (regionGraph D).Adj p.1 p.2} where
  smul g p := ⟨(g • p.1.1, g • p.1.2), regionGraph_smul_adj g p.2⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul G p.1.1) (one_smul G p.1.2))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h p.1.1) (mul_smul g h p.1.2))

/-- **The action of `G` on the oriented edges of the dual graph.** -/
noncomputable instance instMulActionDualAdj :
    MulAction G {p : Region D × Region D // (dualGraph D).Adj p.1 p.2} where
  smul g p := ⟨(g • p.1.1, g • p.1.2), dualGraph_smul_adj g p.2⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul G p.1.1) (one_smul G p.1.2))
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h p.1.1) (mul_smul g h p.1.2))

end Work.ORDunwoody.Dunwoody
