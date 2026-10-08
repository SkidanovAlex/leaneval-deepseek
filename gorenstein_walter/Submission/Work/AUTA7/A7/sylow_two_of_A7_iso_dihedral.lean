import Mathlib
import Submission.Work.AUTA7.A7.SylowTwoSubgroup
import Submission.Work.AUTA7.A7.SylowFacts

namespace Work.AUTA7.A7

/-!
# Subgroups of order `8` of a group isomorphic to `A₇` are dihedral

`|A₇| = 2520 = 8 · 315`, so a subgroup of order `8` of `A₇` is a Sylow `2`-subgroup.  All Sylow
`2`-subgroups of `A₇` are conjugate, and one of them, `dihToA7.range = ⟨(0 1 2 3)(4 5),
(0 2)(4 5)⟩`, is dihedral of order `8` (`equivSylowD0`).  Hence every subgroup of order `8` of
`A₇` — and, by transporting along an isomorphism, of any group isomorphic to `A₇` — is isomorphic
to `DihedralGroup 4`.
-/

/-- **A subgroup of order `8` of a group isomorphic to `A₇` is dihedral.** -/
theorem sylow_two_of_A7_iso_dihedral {L : Type*} [Group L] [Finite L]
    (φ : L ≃* alternatingGroup (Fin 7)) (D : Subgroup L) (hD : Nat.card D = 8) :
    Nonempty (D ≃* DihedralGroup 4) := by
  classical
  -- The image of `D` under the isomorphism `L ≃* A₇`.
  set D' : Subgroup (alternatingGroup (Fin 7)) := D.map φ.toMonoidHom
  have e1 : D ≃* D' := Subgroup.equivMapOfInjective D φ.toMonoidHom φ.injective
  have hcardD' : Nat.card ↥D' = 8 := by
    rw [← Nat.card_congr e1.toEquiv]
    exact hD
  -- `D'` is a `2`-group of order `8`, hence a Sylow `2`-subgroup of `A₇`.
  have hisP : IsPGroup 2 D' := IsPGroup.of_card (n := 3) (by rw [hcardD']; norm_num)
  have hnotdvd : ¬ 2 ∣ D'.index := by
    have h := Subgroup.card_mul_index D'
    rw [hcardD', Work.A7.card_alternatingGroup_seven] at h
    rintro ⟨k, hk⟩
    rw [hk] at h
    omega
  let P : Sylow 2 (alternatingGroup (Fin 7)) := hisP.toSylow hnotdvd
  have hP : (P : Subgroup (alternatingGroup (Fin 7))) = D' := IsPGroup.toSylow_coe hisP hnotdvd
  -- `D ≃* D' ≃* P ≃* D₀ ≃* DihedralGroup 4`.
  have e2 : D' ≃* ↥P := (MulEquiv.subgroupCongr hP).symm
  have e3 : ↥P ≃* ↥sylowD0 := Sylow.equiv P sylowD0
  have e4 : ↥sylowD0 ≃* DihedralGroup 4 := equivSylowD0
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

end Work.AUTA7.A7
