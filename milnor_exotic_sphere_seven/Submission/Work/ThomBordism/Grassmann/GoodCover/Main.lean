import Mathlib
import Submission.Work.ThomBordism.Grassmann.GoodCover.Assembly
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.ThomBordism.Grassmann.GoodCover.grassmannGoodCover
import Submission.Work.ThomBordism.Grassmann.GoodCover.pieceConnectedOfContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 3: `Th γ` is `(k-1)`-connected, from a good cover of the Grassmannian

This file reduces `Work.ThomBordism.Grassmann.ThomSpaceConnected` (item 3 of the chapter) to two
geometric inputs about the oriented Grassmannian `G = G̃r_k(ℝ^{k+m})` and its tautological bundle
`γ`:

* `GoodCover.Existence.grassmannGoodCover` — a finite good cover of `G` subordinate to the chart
  cells `baseSet S`: a finite family `U i` of open sets covering `G`, with each `U i` contained in a
  chart cell and every *nonempty* finite intersection `⋂ i ∈ S, U i` contractible;

* `pieceConnectedOfContractible` — for `U` open, `U ⊆ baseSet S₀` for some chart `S₀` and `U`
  contractible, the piece `far 1 ∪ π⁻¹ U ⊆ Th γ` is `(k-1)`-connected.

The first is pure manifold theory (a consequence of
`Work.ThomBordism.Grassmann.Torsion.goodCoverSubordinate`), the second is the classical statement
that the "Thom space of the rank-`k` bundle over a contractible piece of the base is `(k-1)`-
connected"; the point of the good cover is that it makes the intersections of the cover
contractible, which is exactly what the piece statement needs (for the *chart-cell* cover the
corresponding statement fails).

## Main declarations

* `thomSpaceConnected_of_inputs` — the reduction to the two inputs;
* `thomSpaceConnected` — item 3, once the inputs are available.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **The piece over the empty set is the far region**, hence contractible. -/
theorem pieceCover_empty (k m : ℕ) : pieceCover k m (∅ : Set (OG k m)) = Torsion.far k m 1 := by
  rw [pieceCover, Set.preimage_empty, Set.image_empty, Set.union_empty]

/-- **The `(k-1)`-connectivity of the piece over the empty set.** -/
theorem pieceConnected_empty (k m : ℕ) :
    ∀ j : ℕ, j < k → ∀ x : ↥(pieceCover k m (∅ : Set (OG k m))),
      Subsingleton (HomotopyGroup (Fin j) ↥(pieceCover k m (∅ : Set (OG k m))) x) := by
  intro j _ x
  haveI : ContractibleSpace ↥(pieceCover k m (∅ : Set (OG k m))) := by
    rw [pieceCover_empty]
    exact Torsion.contractibleFar k m
  exact Work.Stems.subsingleton_of_contractible x

/-- **Item 3 from the two geometric inputs.**

`hgood` is a finite good cover of the Grassmannian subordinate to the chart cells, and `hpiece` is
the connectivity of the Thom-space piece over any contractible chart piece. -/
theorem thomSpaceConnected_of_inputs (k m : ℕ)
    (hgood : ∃ (m' : ℕ) (_ : 1 ≤ m') (U : Fin m' → Set (OG k m)) (r : Fin m' → ChartIdx k m),
      (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m'), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) ∧
      (∀ i, U i ⊆ (tautologicalBundle k m).baseSet (r i)))
    (hpiece : ∀ (S₀ : ChartIdx k m) (U : Set (OG k m)), IsOpen U →
      U ⊆ (tautologicalBundle k m).baseSet S₀ → Nonempty ↥U → ContractibleSpace ↥U →
      ∀ j : ℕ, j < k → ∀ x : ↥(pieceCover k m U),
        Subsingleton (HomotopyGroup (Fin j) ↥(pieceCover k m U) x)) :
    ThomSpaceConnected k m := by
  classical
  obtain ⟨m', hm', U, r, hUopen, hUcov, hUgood, hUsub⟩ := hgood
  refine thomSpaceConnected_of_pieces k m m' hm' U hUopen hUcov ?_
  intro S hS j hj x
  have hSne : S.Nonempty := hS
  by_cases hne : (⋂ i ∈ S, U i).Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hsub : (⋂ i ∈ S, U i) ⊆ (tautologicalBundle k m).baseSet (r i₀) := by
      intro y hy
      exact hUsub i₀ (Set.mem_iInter₂.mp hy i₀ hi₀)
    have hopen : IsOpen (⋂ i ∈ S, U i) :=
      isOpen_biInter_finset (fun i _ => hUopen i)
    haveI : ContractibleSpace ↥(⋂ i ∈ S, U i) := hUgood S hSne hne
    have hne' : Nonempty ↥(⋂ i ∈ S, U i) := Set.nonempty_coe_sort.mpr hne
    exact subsingleton_of_set_eq (j := j) (iInter_pieceCover k m U S)
      (fun y => hpiece (r i₀) (⋂ i ∈ S, U i) hopen hsub hne' inferInstance j hj y) x
  · have hemp : (⋂ i ∈ S, U i) = (∅ : Set (OG k m)) := Set.not_nonempty_iff_eq_empty.mp hne
    have hset : (⋂ i ∈ S, pieceCover k m (U i)) = pieceCover k m (∅ : Set (OG k m)) := by
      rw [iInter_pieceCover k m U S, hemp]
    exact subsingleton_of_set_eq (j := j) hset (fun y => pieceConnected_empty k m j hj y) x

/-- **Item 3 of the chapter: the Thom space of the tautological oriented bundle is
`(k-1)`-connected.**

This is the statement required by `Submission/Work/Drive/RationalHurewicz.lean`
(`Work.Drive.RationalHurewiczStable`): every `π_i(Th γ, ∞)` with `i < k` is trivial.

It is obtained from the two inputs of `thomSpaceConnected_of_inputs`:
`grassmannGoodCover` (the finite good cover of the Grassmannian subordinate to the chart cells) and
`pieceConnectedOfContractible` (the `(k-1)`-connectivity of the Thom-space piece over a
contractible chart piece). -/
theorem thomSpaceConnected (k m : ℕ) : ThomSpaceConnected k m :=
  thomSpaceConnected_of_inputs k m (GoodCover.grassmannGoodCover k m)
    (fun S₀ U hUopen hUsub hUne hUc =>
      GoodCover.pieceConnectedOfContractible k m S₀ U hUopen hUsub hUne hUc)

end

end Work.ThomBordism.Grassmann
