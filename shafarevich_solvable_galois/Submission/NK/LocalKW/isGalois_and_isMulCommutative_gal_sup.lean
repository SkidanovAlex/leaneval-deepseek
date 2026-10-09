import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Abelian Galois group of a compositum of normal abelian subextensions

Let `Ω / F` be a Galois extension, and let `E` and `K` be intermediate fields which are normal
(hence Galois) over `F`, with abelian Galois groups.  Then the compositum `E ⊔ K` is Galois over
`F` and its Galois group is abelian.

Normality of the compositum is `IntermediateField.normal_sup`; separability is inherited from
`Ω`.  For the commutativity, the restriction map

`Gal(E ⊔ K / F) →* Gal(↥E'/F) × Gal(↥K'/F)`

(where `E'`, `K'` are `E`, `K` viewed as intermediate fields of `E ⊔ K`) is injective because
`E' ⊔ K' = ⊤`.  The target is abelian: `↥E' ≅ₐ[F] ↥E` and `↥K' ≅ₐ[F] ↥K`, so their Galois groups
are abelian by hypothesis (`IsAbelianGalois.of_algHom`).
-/

namespace NK.LocalKW

open scoped IntermediateField
open AlgEquiv
open IntermediateField

theorem isGalois_and_isMulCommutative_gal_sup {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [IsGalois F Ω] [Algebra.IsSeparable F Ω] (E K : IntermediateField F Ω)
    [Normal F ↥E] [Normal F ↥K]
    (hE : ∀ σ τ : ↥E ≃ₐ[F] ↥E, σ * τ = τ * σ)
    (hK : ∀ σ τ : ↥K ≃ₐ[F] ↥K, σ * τ = τ * σ) :
    IsGalois F ↥(E ⊔ K) ∧ (∀ σ τ : ↥(E ⊔ K) ≃ₐ[F] ↥(E ⊔ K), σ * τ = τ * σ) := by
  classical
  have hG : IsGalois F ↥(E ⊔ K) := ⟨⟩
  refine ⟨hG, ?_⟩
  let L : IntermediateField F Ω := E ⊔ K
  let E' : IntermediateField F L := E.restrict le_sup_left
  let K' : IntermediateField F L := K.restrict le_sup_right
  -- `E` and `K` generate `L`
  have hsup : E' ⊔ K' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict le_sup_left, lift_restrict le_sup_right]
  -- the hypotheses give abelian Galois groups for `E` and `K`
  have hEA : IsAbelianGalois F ↥E := { is_comm := ⟨hE⟩ }
  have hKA : IsAbelianGalois F ↥K := { is_comm := ⟨hK⟩ }
  -- normality of `E` and `K` transfers to `E'` and `K'`
  have hE'normal : Normal F ↥E' :=
    Normal.of_algEquiv (restrictAlgEquiv (F := E) (E := L) le_sup_left)
  have hK'normal : Normal F ↥K' :=
    Normal.of_algEquiv (restrictAlgEquiv (F := K) (E := L) le_sup_right)
  -- and so does commutativity of the Galois group
  have hE'A : IsAbelianGalois F ↥E' :=
    IsAbelianGalois.of_algHom ((restrictAlgEquiv (F := E) (E := L) le_sup_left).symm.toAlgHom)
  have hK'A : IsAbelianGalois F ↥K' :=
    IsAbelianGalois.of_algHom ((restrictAlgEquiv (F := K) (E := L) le_sup_right).symm.toAlgHom)
  have hE'comm : ∀ a b : Gal(↥E'/F), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  have hK'comm : ∀ a b : Gal(↥K'/F), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  -- the restriction map to the product of the two Galois groups
  let rE : Gal(↥L/F) →* Gal(↥E'/F) := restrictNormalHom ↥E'
  let rK : Gal(↥L/F) →* Gal(↥K'/F) := restrictNormalHom ↥K'
  let r : Gal(↥L/F) →* Gal(↥E'/F) × Gal(↥K'/F) := rE.prod rK
  -- it is injective because an automorphism fixing `E'` and `K'` fixes `E' ⊔ K' = ⊤`
  have hinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxE : x ∈ E'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h2 : rE x = 1 := by
        have h3 := congrArg Prod.fst hx
        simpa [r] using h3
      exact (restrictNormal_eq_one_iff E' x).mp h2 y hy
    have hxK : x ∈ K'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h2 : rK x = 1 := by
        have h3 := congrArg Prod.snd hx
        simpa [r] using h3
      exact (restrictNormal_eq_one_iff K' x).mp h2 y hy
    have hmem : x ∈ (E' ⊔ K').fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hxE, hxK⟩
    simpa [hsup, IntermediateField.fixingSubgroup_top] using hmem
  intro σ τ
  -- the target of `r` is abelian, so `r` identifies `σ * τ` with `τ * σ`
  have hprod : ∀ a b : Gal(↥E'/F) × Gal(↥K'/F), a * b = b * a := by
    intro a b
    exact Prod.ext (hE'comm a.1 b.1) (hK'comm a.2 b.2)
  have key : r (σ * τ) = r (τ * σ) := by
    rw [map_mul, map_mul]
    exact hprod (r σ) (r τ)
  exact hinj key

end NK.LocalKW
