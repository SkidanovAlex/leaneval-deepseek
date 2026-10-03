/-
# The transported datum uses every arrow and every relator of the small model

`SmallDatum.smallDatum S P D hrel` is the transport of a datum `D` in a groupoid presentation `P`
along a skeleton `S` of the graph `V` (`Submission/Work/Case1/SmallDatum.lean`), taken to the small
presentation `SmallPres.smallPresentation S P D hrel` (`Submission/Work/Case1/SmallPresentation.lean`).

Here we prove that this transport *keeps everything*:

* every arrow of the small graph `S.Vx` is used by the transported datum, and
* every relator of the small presentation is used by the transported datum.

The first conjunct is genuinely a statement about *all* arrows of `S.Vx`, and `S.Vx` is in bijection
with `Quiver.Total V` through the skeleton, so the hypothesis that `D` uses every arrow of `V`
(`hpair`) is exactly what is needed.  The second conjunct, on the other hand, holds for an arbitrary
datum: the relators of `smallPresentation` are by construction indexed by the relators occurring in
`D`, and each of them is used by the corresponding term of `D`.

The two halves are proved by the companion files `Submission/Work/Case1/rawArrows_enc_mem.lean`
(the encoding of an arrow used by `D` is an arrow used by `smallDatum S P D hrel`) and
`Submission/Work/Case1/usedRelator_smallDatum.lean` (every relator of the small presentation is
used), and assembled here.
-/
import Mathlib
import Submission.Work.Case1.SmallDatum
import Submission.Work.Case1.SmallPresentation
import Submission.Work.ORLocInd.Howie.Datum
import Submission.Work.Case1.dec_totalMap_injective
import Submission.Work.Case1.rawArrows_enc_mem
import Submission.Work.Case1.usedRelator_smallDatum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

/-- The encoding of the decoding of an arrow of the small graph is that arrow: `S.enc` and `S.dec`
are mutually inverse on arrows (`Skel.dec_totalMap_enc_totalMap` gives one composite, and
`dec_totalMap_injective` upgrades it to the other). -/
theorem enc_dec_totalMap_eq_self {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {W : Type u} (S : Skel V W) (e : Quiver.Total S.Vx) :
    PrefunctorAux.totalMap S.enc (PrefunctorAux.totalMap S.dec e) = e :=
  dec_totalMap_injective S (by rw [Skel.dec_totalMap_enc_totalMap])

/-- **The transported datum uses everything.**  If the datum `D` uses every arrow of `V`, then the
transported datum `smallDatum S P D hrel` uses every arrow of the small graph `S.Vx` and every
relator of the small presentation `smallPresentation S P D hrel`. -/
theorem smallDatum_usesEverything {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    {W : Type u} (S : Work.Case1.Skel V W) (P : Work.ORLocInd.Howie.Presentation V) {v : V}
    {n : ℕ} (D : Work.ORLocInd.Howie.Datum P v n)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i)
    (hpair : ∀ e : Quiver.Total V, e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D) :
    (∀ e : Quiver.Total S.Vx,
        e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList
          (Work.Case1.SmallDatum.smallDatum S P D hrel)) ∧
      (∀ i : (Work.Case1.SmallPres.smallPresentation S P D hrel).ι,
        Work.ORLocInd.Howie.UsedRelator (Work.Case1.SmallDatum.smallDatum S P D hrel) i) := by
  refine ⟨?_, usedRelator_smallDatum S P D hrel⟩
  intro e
  -- write the arrow as the encoding of the arrow of `V` that it decodes to
  rw [← enc_dec_totalMap_eq_self S e, Datum.usedArrowsList]
  have h := hpair (PrefunctorAux.totalMap S.dec e)
  rw [Datum.usedArrowsList, List.mem_append, List.mem_map] at h
  rcases h with h' | ⟨g, hg, hge⟩
  · -- an arrow occurring in the paths of `D`
    exact List.mem_append.mpr (Or.inl (rawArrows_enc_mem S P D hrel h'))
  · -- the reverse of an arrow occurring in the paths of `D`
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
      ⟨PrefunctorAux.totalMap S.enc g, rawArrows_enc_mem S P D hrel hg, by
        rw [← PrefunctorAux.totalMap_totalReverse, hge]⟩))

end Work.Case1
