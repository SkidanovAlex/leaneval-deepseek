import Mathlib
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.Dunwoody.ResolutionAssembly

set_option autoImplicit false

universe u

namespace Work.ORDunwoody

/-- **Dunwoody's resolution theorem** (Guiardel–Levitt [GL17, Proposition 2.17], constant case;
Dunwoody [Dun85]).  A finitely presented group `G` acting cocompactly on a tree `T` is dominated
by a cocompact `G`-tree `S` with finitely generated vertex and edge stabilizers.

The tree is the dual of Dunwoody's pattern in the doubly subdivided Cayley complex `Λ''` of a
finite presentation of `G`:

* the pattern points are the midpoints of the cells of `Λ''` (`Dunwoody/Source.lean`);
* two pattern points of a face are joined by a chord — with the same label — according to the
  canonical matching of the fibres (`Dunwoody/Chord.lean`);
* the tracks are the components of the chord graph (`Dunwoody/Track.lean`) and the regions the
  classes of `RegionRel` (`Dunwoody/Region.lean`);
* the side function of a track is the integral of the counting cochain `phi τ`
  (`Dunwoody/AlphaSide.lean`, `Dunwoody/ResRegionSide.lean`), which makes the dual graph a tree
  (`Dunwoody/ResolutionAssembly.lean`).

The tree `S = resDualGT D` is cocompact (`resDualGT_isCocompact`), has finitely generated vertex
and edge stabilizers (`resDualGT_hasFGVertexStab`, `resDualGT_hasFGEdgeStab`) and dominates `T`
through the colour of a region (`resDualGT_dominates`).  The construction is assembled in
`Dunwoody/ResolutionAssembly.lean` as `resDunwoodyResolution_holds`, which is what the proof below
invokes; `Dunwoody/DualTree.lean` and `Dunwoody/RegionAlpha.lean` are an alternative assembly of
the same construction. -/
theorem dunwoodyResolution (G : Type u) [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) (hf : Group.IsFinitelyPresented G) (hc : T.IsCocompact) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T :=
  Dunwoody.resDunwoodyResolution_holds G T hf hc

end Work.ORDunwoody
