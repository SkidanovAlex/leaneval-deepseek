import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.RED.QuotientSylowDihedral

/-!
# A Sylow `2`-subgroup of a `2`-group covering `A₇` over an odd centre is dihedral

Let `G` be a finite group, `S` a Sylow `2`-subgroup of `G` with `|S| = 8`, and `E ≤ G` a
subgroup with `S ≤ E` such that `E / Z(E) ≃* A₇` and the centre `Z(E)` has odd order.  Then
`S ≃* DihedralGroup 4`.

The proof is the standard reduction to the quotient:

* since `S ≤ E ≤ G` and `S` is a Sylow `2`-subgroup of `G`, the index `|E : S|` divides the odd
  number `|G : S|`, so `S` is a Sylow `2`-subgroup of `E`; formally `S.subtype hSE`;
* an odd-order subgroup meets a Sylow `2`-subgroup trivially, so `S ⊓ Z(E) = ⊥` and the quotient
  map `E →* E ⧸ Z(E)` is injective on `S`, whence `S ≃* S·Z(E)/Z(E)`
  (`Work.RED.QuotientSylowAux`);
* the image of `S` is a Sylow `2`-subgroup of `E ⧸ Z(E)` (`Sylow.mapSurjective`), hence, along
  `E ⧸ Z(E) ≃* A₇`, a Sylow `2`-subgroup of `A₇`, which is `DihedralGroup 4` by the model fact
  `Work.GW2.A7ModelProp`;
* transporting the `DihedralGroup 4` structure back along these isomorphisms finishes.
-/

namespace Work.CORE4.A7SI

open Subgroup

theorem SylowDihedral4 {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) {E : Subgroup G} (hSE : (S : Subgroup G) ≤ E)
    (hcard : Nat.card (S : Subgroup G) = 8)
    (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)))
    (hZodd : Odd (Nat.card (Subgroup.center ↥E)))
    (ha7 : Work.GW2.A7ModelProp) :
    Nonempty ((S : Subgroup G) ≃* DihedralGroup 4) := by
  -- Step 1: `S` is a Sylow `2`-subgroup of `E`.
  let P : Sylow 2 ↥E := S.subtype hSE
  have hPcarrier : (P : Subgroup ↥E) = (S : Subgroup G).subgroupOf E :=
    Sylow.coe_subtype (P := S) hSE
  have hisoS : Nonempty ((S : Subgroup G) ≃* (P : Subgroup ↥E)) :=
    ⟨((MulEquiv.subgroupCongr hPcarrier).trans (Subgroup.subgroupOfEquivOfLe hSE)).symm⟩
  -- Step 2: `S` (i.e. `P`) meets the odd-order centre of `E` trivially.
  let Z : Subgroup ↥E := Subgroup.center ↥E
  have hker : (P : Subgroup ↥E) ⊓ Z = ⊥ :=
    Work.RED.QuotientSylowAux.sylow_inf_eq_bot P Z hZodd
  -- Step 3: the image of `P` in the quotient `↥E ⧸ Z(E)` is a Sylow `2`-subgroup, and
  -- `P` is isomorphic to that image.
  let Pq : Sylow 2 (↥E ⧸ Z) := P.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hPq : (Pq : Subgroup (↥E ⧸ Z)) = (P : Subgroup ↥E).map (QuotientGroup.mk' Z) :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z) P
  have hisoP : Nonempty ((P : Subgroup ↥E) ≃* (Pq : Subgroup (↥E ⧸ Z))) := by
    obtain ⟨e⟩ := Work.RED.QuotientSylowAux.mulEquiv_map_quotientMk P Z hker
    exact ⟨e.trans (MulEquiv.subgroupCongr hPq.symm)⟩
  -- Step 4: transport along `↥E ⧸ Z(E) ≃* A₇` to a Sylow `2`-subgroup of `A₇`.
  obtain ⟨φ⟩ := hA7
  let S7 : Sylow 2 (alternatingGroup (Fin 7)) :=
    Pq.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hS7 : (S7 : Subgroup (alternatingGroup (Fin 7))) =
      (Pq : Subgroup (↥E ⧸ Z)).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective Pq
  have hisoQ : Nonempty ((Pq : Subgroup (↥E ⧸ Z)) ≃*
      (S7 : Subgroup (alternatingGroup (Fin 7)))) :=
    ⟨(Subgroup.equivMapOfInjective (Pq : Subgroup (↥E ⧸ Z)) φ.toMonoidHom
        φ.injective).trans (MulEquiv.subgroupCongr hS7.symm)⟩
  -- Step 5: in `A₇` every Sylow `2`-subgroup is `DihedralGroup 4`, and assemble.
  obtain ⟨e7⟩ := ha7.2.1 S7
  obtain ⟨eSP⟩ := hisoS
  obtain ⟨ePQ⟩ := hisoP
  obtain ⟨eQ7⟩ := hisoQ
  exact ⟨eSP.trans (ePQ.trans (eQ7.trans e7))⟩

end Work.CORE4.A7SI
