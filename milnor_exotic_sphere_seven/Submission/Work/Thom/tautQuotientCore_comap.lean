import Mathlib
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The tautological quotient commutes with pullback (G2a)

For a complex bundle `Z` of rank `m + 1` over `B` and a continuous map `f : B' → B`, the
canonical map of punctured total spaces
`punctMap Z f : ↥(zeroComplement (realification (bundleComap Z f))) → ↥(zeroComplement (realification Z))`
is `p ↦ (f p.1, p.2)` (`Work.Thom.punctMap_apply`).  This module proves that the **tautological
quotient** `Q = π^*Z / ℂ·s` commutes with pullback along it:

`bundleComap (tautQuotientCore Z) (punctMap Z f) = tautQuotientCore (bundleComap Z f)`.

Both sides are `VectorBundleCore`s over `↥(zeroComplement (realification (bundleComap Z f)))` with
index type `ι × Fin (m + 1)`; by `Work.Thom.bundleCore_ext` it suffices to compare the three data
`baseSet`, `indexAt`, `coordChange`, and for each of them the comparison reduces to the same two
facts about the local trivializations:

* `Work.Thom.localTriv_snd_punctMap` — the fiber coordinate read in the `j`-th chart of the
  pullback bundle at `p` is the fiber coordinate read in the `j`-th chart of `Z` at `(f p.1, p.2)`;
* `Work.Thom.tqCoord_comap` — the chosen non-vanishing coordinate of the tautological section
  agrees, `tqCoord Z (punctMap Z f p) = tqCoord (bundleComap Z f) p`.

The second is the delicate point: `tqCoord` is a `Classical.choose`, and the two witnesses are
`Classical.choose`s over *propositionally equal* predicates on the *same* type `Fin (m + 1)`.  Such
choices do agree: predicate equality promotes the first proof to a proof of the second predicate
(`Classical.choose.congr_simp`, the `Eq.rec`-coherence of `Classical.choose` in its predicate), and
two proofs of one proposition give the same witness by proof irrelevance.  This is exactly the
canonicity of the tautological quotient bought by the explicit index map of
`Work.Thom.exists_tautQuotientCore`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Comparison of the local trivializations of a pullback core**: the `i`-th fiber coordinate of a
point `p` of `bundleComap Z f` is the `i`-th fiber coordinate of the corresponding point
`(f p.1, p.2)` of `Z`.  (`VectorBundleCore.localTriv` is the gluing-data trivialization
`x ↦ (x.1, coordChange (indexAt x.1) i x.1 x.2)`, and both `indexAt` and `coordChange` of a
pullback core are those of `Z` composed with `f`.) -/
theorem localTriv_snd_bundleComap {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B B' : Type}
    [TopologicalSpace B] [TopologicalSpace B'] {F : Type} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {ι : Type} (Z : VectorBundleCore 𝕜 B F ι) (f : C(B', B)) (i : ι)
    (p : (bundleComap Z f).TotalSpace) :
    ((bundleComap Z f).localTriv i p).2 = (Z.localTriv i (⟨f p.1, p.2⟩ : Z.TotalSpace)).2 := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    bundleComap_indexAt, bundleComap_coordChange]

/-- **The local trivializations of `Z` and of `bundleComap Z f`, compared at the punctured total
spaces**: for the point `p` of the punctured total space of the pullback, the fiber coordinate in
the `i`-th chart of `Z` at the image point `punctMap Z f p` is the fiber coordinate in the `i`-th
chart of the pullback. -/
theorem localTriv_snd_punctMap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B))
    (i : ι) (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    (Z.localTriv i ((punctMap Z f p) : (realification Z).TotalSpace)).2
      = ((bundleComap Z f).localTriv i
          (p : (realification (bundleComap Z f)).TotalSpace)).2 := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    bundleComap_indexAt, bundleComap_coordChange, punctMap_apply]

/-- **The chosen non-vanishing coordinate of the tautological section is natural under pullback.**

Both sides are `Classical.choose`s over predicates on the *same* type `Fin (m + 1)` (the coordinate
type of the fiber), and the two predicates are equal: the identity of the predicates is
`Work.Thom.localTriv_snd_punctMap` together with `Work.Thom.punctMap_apply`.  Equality of the
predicates lets the first witness be transported to a witness of the second predicate
(`Classical.choose.congr_simp`), and any two witnesses of one predicate agree
(`Subsingleton.elim`). -/
theorem tqCoord_comap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B))
    (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    tqCoord Z (punctMap Z f p) = tqCoord (bundleComap Z f) p := by
  have hL := exists_coord_ne_zero_localTriv Z (punctMap Z f p)
  have hR := exists_coord_ne_zero_localTriv (bundleComap Z f) p
  change Classical.choose hL = Classical.choose hR
  -- the preferred base index agrees
  have hidx : Z.indexAt ((punctMap Z f p) : (realification Z).TotalSpace).proj
      = (bundleComap Z f).indexAt
          (p : (realification (bundleComap Z f)).TotalSpace).proj := by
    rw [punctMap_apply]
    rfl
  -- the two predicates ("the `k`-th coordinate is non-zero") are equal
  have hpred : (fun k : Fin (m + 1) =>
        ((Z.localTriv (Z.indexAt ((punctMap Z f p) : (realification Z).TotalSpace).proj)
          ((punctMap Z f p) : (realification Z).TotalSpace))).2 k ≠ 0)
      = (fun k : Fin (m + 1) =>
        (((bundleComap Z f).localTriv ((bundleComap Z f).indexAt
            (p : (realification (bundleComap Z f)).TotalSpace).proj)
          (p : (realification (bundleComap Z f)).TotalSpace))).2 k ≠ 0) := by
    funext k
    rw [← hidx, localTriv_snd_punctMap Z f _ p]
  calc Classical.choose hL = Classical.choose (hpred ▸ hL) :=
        Classical.choose.congr_simp hpred hL
    _ = Classical.choose hR := congrArg Classical.choose (Subsingleton.elim _ _)

/-- **The memberships in the charts of the tautological quotient match under `punctMap`.**  This is
the set-theoretic content of the comparison of the base sets: the base point is `f p.1`, and the
non-vanishing condition is the same by `Work.Thom.localTriv_snd_punctMap`. -/
theorem mem_tqBaseSet_comap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B))
    (i : ι) (k : Fin (m + 1)) (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    punctMap Z f p ∈ tqBaseSet Z i k ↔ p ∈ tqBaseSet (bundleComap Z f) i k := by
  rw [tqBaseSet, tqBaseSet, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [bundleComap_baseSet, Set.mem_preimage, punctMap_apply] using h1,
      by simpa only [localTriv_snd_punctMap Z f i p] using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [bundleComap_baseSet, Set.mem_preimage, punctMap_apply] using h1,
      by simpa only [← localTriv_snd_punctMap Z f i p] using h2⟩

/-- **G2a: the tautological quotient commutes with pullback.**  Both sides are gluing data over
`↥(zeroComplement (realification (bundleComap Z f)))` with index type `ι × Fin (m + 1)`, so by
`Work.Thom.bundleCore_ext` it suffices to compare `baseSet`, `indexAt` and `coordChange`; for each
of these, the defining equations of `Work.Thom.tautQuotientCore`
(`tautQuotientCore_baseSet`, `tautQuotientCore_indexAt`, `tautQuotientCore_coordChange`) reduce the
comparison to `Work.Thom.mem_tqBaseSet_comap`, `Work.Thom.punctMap_apply` together with
`Work.Thom.tqCoord_comap`, and `Work.Thom.localTriv_snd_punctMap`. -/
theorem tautQuotientCore_comap {m : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (f : C(B', B)) :
    Work.Thom.bundleComap (Work.Thom.tautQuotientCore Z) (Work.Thom.punctMap Z f)
      = Work.Thom.tautQuotientCore (Work.Thom.bundleComap Z f) := by
  refine bundleCore_ext ?_ ?_ ?_
  · -- the base sets
    funext ik
    obtain ⟨i, k⟩ := ik
    simp only [bundleComap_baseSet, tautQuotientCore_baseSet]
    ext p
    exact mem_tqBaseSet_comap Z f i k p
  · -- the index maps
    funext p
    rw [bundleComap_indexAt, tautQuotientCore_indexAt Z (punctMap Z f p),
      tautQuotientCore_indexAt (bundleComap Z f) p]
    refine Prod.ext ?_ ?_
    · rw [punctMap_apply]
      rfl
    · exact tqCoord_comap Z f p
  · -- the transition functions
    rintro ⟨i, k⟩ ⟨j, l⟩ x
    apply ContinuousLinearMap.ext
    intro z
    rw [bundleComap_coordChange,
      tautQuotientCore_coordChange Z i j k l (punctMap Z f x) z,
      tautQuotientCore_coordChange (bundleComap Z f) i j k l x z,
      localTriv_snd_punctMap Z f j x, punctMap_apply, bundleComap_coordChange]

end

end Work.Thom
