import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.A7V18.LayerInTransport
import Submission.Work.CORE3.A7V18.MapQuotientCenterIso
import Submission.Work.CORE3.A7V18.LayerInQuotientCenterIso
import Submission.Work.CORE3.MDataAux
import Submission.Work.ASM.oddCore_odd
import Submission.Work.DSTR.layerShape

namespace Work.CORE3.A7V18

open Subgroup

/-- **`E ⊓ O(X) ≤ Z(E)`, `subgroupOf` form.**  For a quasisimple `E` in a finite group `X`, the
odd core of `X` meets `E` only in the centre of `E`; here stated as
`(E ⊓ O(X)).subgroupOf E ≤ Z(↥E)`.

This is `Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center` (which gives
`E ⊓ O(X) ≤ (Z(↥E)).map E.subtype`) rewritten in the internal form needed by
`Work.CORE3.A7V18.MapQuotientCenterIso`. -/
theorem inf_oddCore_subgroupOf_le_center {X : Type*} [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp) {E : Subgroup X} (hEq : Work.GW2.IsQuasisimple E) :
    (E ⊓ Work.GW2.oddCore X).subgroupOf E ≤ Subgroup.center ↥E := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp
    (Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center hFT hEq
      (Subgroup.mem_inf.mpr ⟨hx.1, hx.2⟩))
  have hzx' : z = x := Subtype.ext hzx
  rwa [← hzx']

/-- **The image of the layer in `↥M ⧸ O(↥M)` is quasisimple and has the same central quotient.**

Let `M ≤ G` be finite, `E := Work.GW2.layer ↥M` quasisimple and normal in `↥M`, and put
`O := Work.GW2.oddCore ↥M`, `Ē := E.map (QuotientGroup.mk' O) ≤ ↥M ⧸ O`.  Then `Ē` is normal in
`↥M ⧸ O`, quasisimple, nontrivial, and `Ē/Z(Ē) ≅ E/Z(E)` — the last isomorphism transported to
the ambient group, i.e. `↥(layerIn M) ⧸ Z(layerIn M) ≃* ↥Ē ⧸ Z(Ē)`.

This is the transport used by the `E(M)/Z(E(M)) ≅ A₇` step of `Work.CORE3.A7V18.A7QuotientClose`
(following `A7V18/QuasisimpleMapOddCore.lean`, whose private `map_quotient_of_central_inf` does
the same for an `A₇` target; here the target is left arbitrary).

Proof plan: `E ⊓ O ≤ Z(E)` — its image in the simple group `E/Z(E)` is normal, so it is `⊥` or
everything; the second alternative would make `E/Z(E)` a quotient of the odd group `E ⊓ O`,
which is solvable by Feit–Thompson (`hFT`) — contradicting `E/Z(E)` simple non-abelian (a
perfect non-trivial group has non-abelian central quotient).  Then `E ⊓ O ≤ Z(E)` gives
`Z(Ē) = Z(E)/(E ⊓ O)` and `Ē/Z(Ē) ≅ E/Z(E)` by the third isomorphism theorem, and `Ē ≠ ⊥`
because `E ≤ O` would make the perfect `E ≠ 1` solvable.  Finally `layerIn M = E.map M.subtype`
is the isomorphic copy of `E` in `G` (`Subgroup.equivMapOfInjective`,
`QuotientGroup.congr` + `Subgroup.map_center_eq`, as in `A7V18/LayerInTransport.lean`). -/
theorem LayerMapOddCoreIso {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hFT : Work.GW2.FeitThompsonProp) (hEn : (Work.GW2.layer ↥M).Normal)
    (hQ : Work.GW2.IsQuasisimple (Work.GW2.layer ↥M)) :
    ((Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M))).Normal ∧
      Work.GW2.IsQuasisimple ((Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M))) ∧
      ((Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M))) ≠ ⊥ ∧
      Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
        (↥((Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M))) ⧸
          Subgroup.center ↥((Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M))))) := by
  -- `E := layer ↥M` is normal and quasisimple in `↥M`; `E ⊓ O(↥M) ≤ Z(E)`
  -- (`isQuasisimple_inf_oddCore_le_center`, via Feit–Thompson) and `E ⊄ O(↥M)` (otherwise the
  -- perfect, nontrivial `E` would be solvable, again by Feit–Thompson).  Hence the general
  -- transport `MapQuotientCenterIso` applies to `N := oddCore ↥M`.
  obtain ⟨h1, h2, h3, h4⟩ :=
    MapQuotientCenterIso (Work.GW2.layer ↥M) (Work.GW2.oddCore ↥M) hEn hQ
      (inf_oddCore_subgroupOf_le_center hFT hQ)
      (Work.DSTR.not_le_oddCore_of_isQuasisimple hFT hQ)
  -- `h4 : (↥E ⧸ Z ↥E) ≃* (↥Ē ⧸ Z Ē)`; the remaining transport
  -- `↥(layerIn M) ⧸ Z ≃* ↥E ⧸ Z` is the definitional identification of `layerIn M` with
  -- `(layer ↥M).map M.subtype` along the injective inclusion `↥M →* G`.
  obtain ⟨eA⟩ := h4
  obtain ⟨eB⟩ := LayerInQuotientCenterIso M
  exact ⟨h1, h2, h3, ⟨eB.trans eA⟩⟩

end Work.CORE3.A7V18
