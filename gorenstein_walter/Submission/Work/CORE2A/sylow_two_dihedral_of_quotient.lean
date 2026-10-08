import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.RED.QuotientSylowDihedral

/-!
# CORE2A: Sylow 2-subgroups of a central extension by an odd-order centre

Let `E` be a finite group whose centre `Z(E)` has **odd** order, and suppose that
`E ⧸ Z(E)` is either the alternating group `A₇` or a group `PSL(2, q)` with `q = p ^ k`
odd, `q ≥ 5`.  Then every Sylow 2-subgroup of `E` is dihedral.

The proof is the standard reduction to the quotient:

* an odd-order subgroup meets a 2-subgroup trivially, so `P ⊓ Z(E) = ⊥` for every Sylow
  2-subgroup `P ≤ E` (the order of the intersection divides both `|P|`, a power of `2`,
  and `|Z(E)|`, which is odd);
* hence the quotient map `E →* E ⧸ Z(E)` is injective on `P`, so `P ≃* P·Z(E)/Z(E)`;
* the image `P·Z(E)/Z(E)` has order `|P|`, i.e. the 2-part of `|E|` (dividing by the odd
  number `|Z(E)|` does not change the 2-part), so it is a Sylow 2-subgroup of `E ⧸ Z(E)`
  (`Sylow.mapSurjective`);
* in `A₇` every Sylow 2-subgroup is `DihedralGroup 4` (`Work.GW2.A7ModelProp`), and in
  `PSL(2, q)` it is dihedral (`Work.GW2.L2SylowDihedralProp`); transporting along the
  composite isomorphism finishes.

The two elementary ingredients about the quotient are the colleague lemmas
`Work.RED.QuotientSylowAux.sylow_inf_eq_bot` and
`Work.RED.QuotientSylowAux.mulEquiv_map_quotientMk`.
-/

open scoped MatrixGroups
open Subgroup

namespace Work.CORE2A

theorem sylow_two_dihedral_of_quotient {E : Type} [Group E] [Finite E]
    (hA7 : Work.GW2.A7ModelProp) (hL2 : Work.GW2.L2SylowDihedralProp)
    (hcenter : Odd (Nat.card (Subgroup.center E)))
    (hq : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) ∨
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
            Nonempty ((E ⧸ Subgroup.center E) ≃*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    ∀ P : Sylow 2 E, ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup E) ≃* DihedralGroup n) := by
  intro P
  -- An odd-order subgroup meets a Sylow 2-subgroup trivially.
  have hker : (P : Subgroup E) ⊓ Subgroup.center E = ⊥ :=
    Work.RED.QuotientSylowAux.sylow_inf_eq_bot P (Subgroup.center E) hcenter
  -- The image of `P` in the quotient is a Sylow 2-subgroup of `E ⧸ Z(E)`.
  let Pq : Sylow 2 (E ⧸ Subgroup.center E) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center E))
  have hPq : (Pq : Subgroup (E ⧸ Subgroup.center E)) =
      (P : Subgroup E).map (QuotientGroup.mk' (Subgroup.center E)) :=
    Sylow.coe_mapSurjective (f := QuotientGroup.mk' (Subgroup.center E))
      (QuotientGroup.mk'_surjective (Subgroup.center E)) P
  -- `P` is isomorphic to its image in the quotient.
  have hPiso : Nonempty (↥(P : Subgroup E) ≃* ↥(Pq : Subgroup (E ⧸ Subgroup.center E))) := by
    obtain ⟨e⟩ :=
      Work.RED.QuotientSylowAux.mulEquiv_map_quotientMk P (Subgroup.center E) hker
    exact ⟨e.trans (MulEquiv.subgroupCongr hPq).symm⟩
  rcases hq with hA7q | hL2q
  · -- Case `E ⧸ Z(E) ≃* A₇`, whose Sylow 2-subgroups are `DihedralGroup 4`.
    obtain ⟨φ⟩ := hA7q
    let S : Sylow 2 (alternatingGroup (Fin 7)) :=
      Pq.mapSurjective (f := φ.toMonoidHom) φ.surjective
    have hS : (S : Subgroup (alternatingGroup (Fin 7))) =
        (Pq : Subgroup (E ⧸ Subgroup.center E)).map φ.toMonoidHom :=
      Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective Pq
    obtain ⟨eS⟩ := hA7.2.1 S
    obtain ⟨eP⟩ := hPiso
    exact ⟨4, by norm_num, ⟨eP.trans
      ((Subgroup.equivMapOfInjective (Pq : Subgroup (E ⧸ Subgroup.center E)) φ.toMonoidHom
        φ.injective).trans ((MulEquiv.subgroupCongr hS).symm.trans eS))⟩⟩
  · -- Case `E ⧸ Z(E) ≃* PSL(2, q)` with `q = p ^ k ≥ 5` odd.
    obtain ⟨p, k, hp, hoddp, hge, hφ⟩ := hL2q
    obtain ⟨φ⟩ := hφ
    let S : Sylow 2 (PSL(2, GaloisField p k)) :=
      Pq.mapSurjective (f := φ.toMonoidHom) φ.surjective
    have hS : (S : Subgroup (PSL(2, GaloisField p k))) =
        (Pq : Subgroup (E ⧸ Subgroup.center E)).map φ.toMonoidHom :=
      Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective Pq
    obtain ⟨n, hn, eS⟩ := hL2 p k hoddp hge S
    obtain ⟨eSn⟩ := eS
    obtain ⟨eP⟩ := hPiso
    exact ⟨n, hn, ⟨eP.trans
      ((Subgroup.equivMapOfInjective (Pq : Subgroup (E ⧸ Subgroup.center E)) φ.toMonoidHom
        φ.injective).trans ((MulEquiv.subgroupCongr hS).symm.trans eSn))⟩⟩

end Work.CORE2A
