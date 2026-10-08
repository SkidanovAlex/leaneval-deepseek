import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.RED.QuotientSylowDihedral

open scoped MatrixGroups
open Subgroup

namespace Work.CORE4

/-!
# Every 2-subgroup of odd index of a central extension by an odd-order centre is dihedral

This is the CORE4 copy of `Work.CORE2A.sylow_two_dihedral_of_quotient`
(`Submission/Work/CORE2A/sylow_two_dihedral_of_quotient.lean`), which cannot be imported here
because `CORE2A/Defs.lean` (through `ASM/Defs.lean`) and `Submission.Work.CORE4.Defs` both
declare the `Work.GW2` vocabulary.

The mathematical content is the standard reduction to the quotient `E ⧸ Z(E)`:

* an odd-order subgroup meets a 2-subgroup trivially, so `P ⊓ Z(E) = ⊥` for every Sylow
  2-subgroup `P ≤ E` (the order of the intersection divides both `|P|`, a power of `2`,
  and `|Z(E)|`, which is odd);
* hence the quotient map `E →* E ⧸ Z(E)` is injective on `P`, so `P ≃* P·Z(E)/Z(E)`;
* the image `P·Z(E)/Z(E)` is a Sylow 2-subgroup of `E ⧸ Z(E)` (`Sylow.mapSurjective`);
* in `A₇` every Sylow 2-subgroup is `DihedralGroup 4` (`Work.GW2.A7ModelProp`), and in
  `PSL(2, q)` it is dihedral (`Work.GW2.L2SylowDihedralProp`); transporting along the
  composite isomorphism finishes.

The two elementary ingredients about the quotient are the colleague lemmas
`Work.RED.QuotientSylowAux.sylow_inf_eq_bot` and
`Work.RED.QuotientSylowAux.mulEquiv_map_quotientMk`.

The deliverable `Work.CORE4.QuotientSylowDihedral` is the Sylow form below transported to an
arbitrary 2-subgroup of odd index (`IsPGroup.toSylow`).
-/

/-- Sylow form of the statement: every Sylow 2-subgroup of a finite group `E` with odd centre
whose quotient by its centre is `A₇` or `PSL(2,q)` (`q = p^k` odd, `q ≥ 5`) is dihedral. -/
theorem sylow_two_dihedral_of_center_quotient {E : Type} [Group E] [Finite E]
    (hA7 : Work.GW2.A7ModelProp) (hL2 : Work.GW2.L2SylowDihedralProp)
    (hcenter : Odd (Nat.card (Subgroup.center E)))
    (hq : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) ∨
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
            Nonempty ((E ⧸ Subgroup.center E) ≃*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    ∀ P : Sylow 2 E, ∃ n : ℕ, 2 ≤ n ∧
      Nonempty (↥(P : Subgroup E) ≃* DihedralGroup n) := by
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

/-- Every `2`-subgroup of odd index of a finite group `E` with odd centre whose quotient by its
centre is `A₇` or `PSL(2,q)` (`q = p^k` odd, `q ≥ 5`) is isomorphic to `DihedralGroup n`, `n ≥ 2`.

Hint: this is a verbatim re-proof of `Work.CORE2A.sylow_two_dihedral_of_quotient`
(`Submission/Work/CORE2A/sylow_two_dihedral_of_quotient.lean`), which cannot be imported here
because CORE2A/Defs.lean and RED/Defs.lean redeclare the `Work.GW2` vocabulary.  The two aux
lemmas it needs ARE importable from `Submission.Work.RED.QuotientSylowDihedral`:
`Work.RED.QuotientSylowAux.sylow_inf_eq_bot` and
`Work.RED.QuotientSylowAux.mulEquiv_map_quotientMk` (that module's namespace is `Work.RED.GW2`,
which does not clash with `Work.GW2` from `Submission.Work.CORE4.Defs`).
`Subgroup.relIndex_top_right : Q.relIndex ⊤ = Q.index` converts the hypothesis into
`¬ 2 ∣ Q.index`, so `IsPGroup.toSylow` applies. -/
theorem QuotientSylowDihedral {E : Type} [Group E] [Finite E]
    (hA7 : Work.GW2.A7ModelProp) (hL2 : Work.GW2.L2SylowDihedralProp)
    (hcenter : Odd (Nat.card (Subgroup.center E)))
    (hq : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) ∨
          ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
            Nonempty ((E ⧸ Subgroup.center E) ≃*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    ∀ Q : Subgroup E, IsPGroup 2 Q → ¬ 2 ∣ Q.relIndex ⊤ →
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥Q ≃* DihedralGroup n) := by
  intro Q hQ2 hQidx
  -- A 2-subgroup of odd index is a Sylow 2-subgroup.
  have hQndvd : ¬ 2 ∣ Q.index := by
    rwa [Subgroup.relIndex_top_right] at hQidx
  let P : Sylow 2 E := hQ2.toSylow hQndvd
  have hPcoe : (P : Subgroup E) = Q := IsPGroup.toSylow_coe hQ2 hQndvd
  obtain ⟨n, hn, he⟩ := sylow_two_dihedral_of_center_quotient hA7 hL2 hcenter hq P
  obtain ⟨e⟩ := he
  exact ⟨n, hn, ⟨(MulEquiv.subgroupCongr hPcoe).trans e⟩⟩

end Work.CORE4
