import Mathlib
import Submission.Work.Case1.Skeleton
import Submission.Work.Case1.SmallPresentation
import Submission.Work.Case1.SmallTransfer
import Submission.Work.Case1.exists_smallDatum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace Work.Case1

open Work.ORLocInd.Howie

/-- **A faithful small model of a datum.**  A datum `D` in a presentation over `V : Type v`
(whose arrows and vertices are all used by `D`, by `hpair`/`hrel`/`hconn`) has a *combinatorial
copy* over a graph `V' : Type u` whose vertices and arrows are indexed by finite types (`Fin`'s),
for *any* universe `u`.

The construction is the "skeleton" encoding.  Since `hconn` and `hpair` say that every vertex of
`V` is reached by a path whose arrows are used by `D`, every vertex is a vertex of `D`'s span, and
every arrow of `V` occurs in `D.usedArrowsList`; hence

* `V' := Fin M` with `M = D.visitedList.dedup.length`, the encoding of the vertices being their
  index in the deduplicated visited list (`List.idxOf`/`List.get` on
  `D.visitedList.dedup`, with the round-trip lemmas `List.getElem_idxOf`, `List.idxOf_getElem`);
* the arrows `V' u w` are the `i : Fin k` with `srcIdx i = u` and `tgtIdx i = w`, where
  `k = D.usedArrowsList.dedup.length` and `srcIdx`/`tgtIdx` are read off from the corresponding
  entry of the list (`hpair` gives that every arrow of `V` is one of them, so the encoding of
  arrows is a bijection `Total V ≃ Fin k`; the inverse of the index of an arrow is that arrow);
* reversal is the involution `i ↦ idxOf (totalReverse (get i))` on `Fin k`, which is an involution
  because `totalReverse` is (write `D.usedArrowsList` as `raw ++ raw.map totalReverse` or prove
  `get (idxOf (totalReverse (get i))) = totalReverse (get i)` and use injectivity of `idxOf`).

Then transport, along this bijection,

* the relators of `P` that are used by `D` (`hrel`; index them by `Fin k'` with the order
  inherited from `P.ι` through the bijection, so that `staggered` transfers),
* the code `P.edgeOf`: take `P'.α := Fin N` with `N` the number of distinct codes among the used
  arrows, ordered by the order type of `P.α` restricted to them (`CodeSeparates` transfers from
  `hsep`),
* every path appearing in `D` (the `γ_j`, the `δ`'s and the relators of the terms); an arrow of a
  path is an element of `D.usedArrowsList`, hence has an index.

The datum `D'` is the transported datum: `D'.γ j` is the encoded `D.γ j`, the terms are the encoded
terms (with the relator index and sign transported), and `D'.W = D.W`.  All the properties
(`reduced`, `cyclicallyReduced`, `notProperPower`, `staggered`, `measure`, `usedArrowsList`,
`UsedRelator`, connectivity) are transported because the encoding is a bijection on paths whose
inverse preserves `arrowList`, `pmul`, `red`, `compPower` and the endpoints.

The final clause is the transfer: the *decoding* map on the free groupoids
(`VertexGroup v' →* VertexGroup v`, `decode`), which sends each encoded path to the path it encodes,
is a monomorphism (`decode_P = decode_Q → P = Q`, by induction on the length using the bijection on
arrows), sends `D'.γ j` to `D.γ j`, and sends each relator conjugate of `P'` to a relator conjugate
of `P` (the relators of `P'` decode to the relators of `P` by construction), hence
`P'.relatorNormalClosure v' ≤ comap decode (P.relatorNormalClosure v)`.

USE SITE: this is used (with `v := u`, `u := u`) with `D` the output datum of
`Work.ORLocInd.Howie.case1_descent_univ` (so `hconn`, `hpair`, `hrel` hold), to move the datum into
the universe `u` of the statement of `Work.ORLocInd.Howie.case1_descent`; note the caller needs
`D'.measure ≤ D.measure` (equality is stated, which is stronger) and the transfer as stated. -/
theorem smallModel {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (v : V) {n : ℕ}
    (D : Work.ORLocInd.Howie.Datum P v n)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x))
    (hpair : ∀ e : Quiver.Total V, e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D)
    (hrel : ∀ i : P.ι, Work.ORLocInd.Howie.UsedRelator D i) :
    ∃ (V' : Type u) (_ : Quiver V') (_ : Quiver.HasInvolutiveReverse V') (_ : DecidableEq V')
      (P' : Work.ORLocInd.Howie.Presentation V') (v' : V') (D' : Work.ORLocInd.Howie.Datum P' v' n),
      P'.CodeSeparates ∧ D'.measure = D.measure ∧ D'.W = D.W ∧
      (∀ e : Quiver.Total V', e ∈ Work.ORLocInd.Howie.Datum.usedArrowsList D') ∧
      (∀ i : P'.ι, Work.ORLocInd.Howie.UsedRelator D' i) ∧
      (∀ x : V', Nonempty (Quiver.Path v' x)) ∧
      ((∀ j, D'.γ j ∈ P'.relatorNormalClosure v') → ∀ j, D.γ j ∈ P.relatorNormalClosure v) := by
  classical
  -- the skeleton of the datum, built in the universe `u`
  let W : Type u := ULift.{u,0} (Fin 1)
  let S : Skel V W := SmallDatum.smallSkel D hconn hpair W
  -- the transported presentation and datum
  let P' : Work.ORLocInd.Howie.Presentation S.Vx := SmallPres.smallPresentation S P D hrel
  obtain ⟨D', hW, hmeas, hused, hrel', hconn', hdec⟩ :=
    SmallDatum.exists_smallDatum S P D hrel hpair hconn
  refine ⟨S.Vx, Skel.instQuiverVx S, Skel.instReverseVx S, inferInstance, P', S.encObj v, D',
    SmallPres.codeSeparates_smallPresentation S P D hsep hpair hrel, hmeas, hW, hused, hrel',
    hconn', ?_⟩
  intro h j
  have h1 : SmallTransfer.decode S v (D'.γ j) ∈ P.relatorNormalClosure v :=
    SmallTransfer.decode_relatorNormalClosure S P D hrel (h j)
  rwa [hdec j] at h1

end Work.Case1
