import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Counting the complements of a submodule

If `S ≤ U` are submodules of a finite-dimensional vector space `M` over a field `K`, we count the
submodules `T ≤ U` that are complements of `S` in `U`, i.e. with `T ⊓ S = ⊥` and `T ⊔ S = U`.

The answer is `|K| ^ ((dim U - dim S) * dim S)`, as one expects: passing to the quotient `U ⧸ S`,
such complements are the graphs of linear maps `U ⧸ S → S`, and the space of those has dimension
`(dim U - dim S) * dim S`.

The proof goes through an abstract statement `card_complements_aux` for a fixed ambient space `N`:
* complements of `P` in `N` are the linear maps `N →ₗ ↥P` restricting to the identity on `P`
  (`Submodule.isComplEquivProj`),
* these form a torsor over the linear maps `N →ₗ ↥P` vanishing on `P`, i.e. over `N ⧸ P →ₗ ↥P`,
* and the latter is a vector space of dimension `finrank (N ⧸ P) * finrank P`.

The transfer from `M` to `↥U` uses the order isomorphism `Submodule.mapIic`.
-/

namespace Commons.LinearAlgebra.Submodule

open scoped Classical

/-- Shifting by a fixed projection `p₀ : N →ₗ ↥P` with `p₀|_P = id` gives a bijection between
linear maps that restrict to the identity on `P` and linear maps that vanish on `P`. -/
private noncomputable def projEquivKer {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    (P : Submodule K N) (p0 : N →ₗ[K] ↥P) (hp0 : ∀ x : ↥P, p0 x = x) :
    {f : N →ₗ[K] ↥P // ∀ x : ↥P, f x = x} ≃ {g : N →ₗ[K] ↥P // ∀ x : ↥P, g x = 0} where
  toFun f := ⟨f.1 - p0, by
    intro x
    rw [LinearMap.sub_apply, f.2 x, hp0 x, sub_self]⟩
  invFun g := ⟨g.1 + p0, by
    intro x
    rw [LinearMap.add_apply, g.2 x, hp0 x, zero_add]⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    simp
  right_inv g := by
    apply Subtype.ext
    ext x
    simp

/-- Linear maps `N →ₗ ↥P` vanishing on `P` correspond to linear maps `N ⧸ P →ₗ ↥P`. -/
private noncomputable def kerEquivQuot {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    (P : Submodule K N) :
    {g : N →ₗ[K] ↥P // ∀ x : ↥P, g x = 0} ≃ (N ⧸ P →ₗ[K] ↥P) where
  toFun g := P.liftQ g.1 (by
    intro x hx
    rw [LinearMap.mem_ker]
    exact g.2 ⟨x, hx⟩)
  invFun φ := ⟨φ.comp P.mkQ, by
    intro x
    rw [LinearMap.comp_apply, Submodule.mkQ_apply]
    have hx : (Submodule.Quotient.mk (x : N) : N ⧸ P) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr x.2
    rw [hx, map_zero]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply]
  right_inv φ := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply]

/-- The number of complements of a submodule `P` in a finite-dimensional vector space `N` over a
field `K` equals `|K| ^ ((dim N - dim P) * dim P)`. -/
theorem card_complements_aux {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] (P : Submodule K N) :
    Nat.card {Q : Submodule K N // IsCompl Q P} =
      Nat.card K ^ ((Module.finrank K N - Module.finrank K P) * Module.finrank K P) := by
  obtain ⟨Q0, hQ0⟩ := P.exists_isCompl
  have hp0 : ∀ x : ↥P, P.projectionOnto Q0 hQ0 x = x := fun x => P.projectionOnto_apply_left hQ0 x
  calc
    Nat.card {Q : Submodule K N // IsCompl Q P}
        = Nat.card {Q : Submodule K N // IsCompl P Q} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun Q => isCompl_comm))
    _ = Nat.card {f : N →ₗ[K] ↥P // ∀ x : ↥P, f x = x} :=
          Nat.card_congr P.isComplEquivProj
    _ = Nat.card {g : N →ₗ[K] ↥P // ∀ x : ↥P, g x = 0} :=
          Nat.card_congr (projEquivKer P (P.projectionOnto Q0 hQ0) hp0)
    _ = Nat.card (N ⧸ P →ₗ[K] ↥P) := Nat.card_congr (kerEquivQuot P)
    _ = Nat.card K ^ Module.finrank K (N ⧸ P →ₗ[K] ↥P) := Module.natCard_eq_pow_finrank
    _ = Nat.card K ^ (Module.finrank K (N ⧸ P) * Module.finrank K ↥P) := by
          rw [Module.finrank_linearMap]
    _ = Nat.card K ^ ((Module.finrank K N - Module.finrank K ↥P) * Module.finrank K ↥P) := by
          rw [Submodule.finrank_quotient]

/-- Transferring the complement condition from `M` to the submodule `↥U`. -/
lemma isCompl_comap_subtype_iff {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S U : Submodule K M) (h : S ≤ U) {T : Submodule K M} (hT : T ≤ U) :
    (T ⊓ S = ⊥ ∧ T ⊔ S = U) ↔
      IsCompl (T.comap U.subtype) (S.comap U.subtype) := by
  have hT' : ((Submodule.mapIic U) (T.comap U.subtype)).1 = T := by
    rw [Submodule.coe_mapIic_apply, Submodule.map_comap_subtype, inf_of_le_right hT]
  have hS' : ((Submodule.mapIic U) (S.comap U.subtype)).1 = S := by
    rw [Submodule.coe_mapIic_apply, Submodule.map_comap_subtype, inf_of_le_right h]
  have h1 : (Submodule.mapIic U) (T.comap U.subtype) = ⟨T, hT⟩ := Subtype.ext hT'
  have h2 : (Submodule.mapIic U) (S.comap U.subtype) = ⟨S, h⟩ := Subtype.ext hS'
  rw [(Submodule.mapIic U).isCompl_iff, h1, h2, Set.Iic.isCompl_iff, disjoint_iff]

/-- Complements of `S` in `U` (inside `M`) correspond to complements of `S.comap U.subtype` in
`↥U`. -/
private noncomputable def complementEquiv {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (S U : Submodule K M) (h : S ≤ U) :
    {T : Submodule K M // T ≤ U ∧ T ⊓ S = ⊥ ∧ T ⊔ S = U} ≃
      {Q : Submodule K ↥U // IsCompl Q (S.comap U.subtype)} where
  toFun T := ⟨T.1.comap U.subtype, (isCompl_comap_subtype_iff S U h T.2.1).mp T.2.2⟩
  invFun Q := ⟨Q.1.map U.subtype,
    ⟨Submodule.map_subtype_le U Q.1,
      (isCompl_comap_subtype_iff S U h (Submodule.map_subtype_le U Q.1)).mpr (by
        rw [Submodule.comap_map_eq_of_injective (Submodule.subtype_injective U) Q.1]
        exact Q.2)⟩⟩
  left_inv T := by
    apply Subtype.ext
    change (T.1.comap U.subtype).map U.subtype = T.1
    rw [Submodule.map_comap_subtype, inf_of_le_right T.2.1]
  right_inv Q := by
    apply Subtype.ext
    change (Q.1.map U.subtype).comap U.subtype = Q.1
    exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective U) Q.1

theorem card_complements {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (S U : Submodule K M) (h : S ≤ U) :
    Nat.card {T : Submodule K M // T ≤ U ∧ T ⊓ S = ⊥ ∧ T ⊔ S = U} =
      Nat.card K ^ ((Module.finrank K ↥U - Module.finrank K ↥S) * Module.finrank K ↥S) := by
  have hfin : Module.finrank K ↥(S.comap U.subtype) = Module.finrank K ↥S :=
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  rw [Nat.card_congr (complementEquiv S U h), card_complements_aux (S.comap U.subtype), hfin]

end Commons.LinearAlgebra.Submodule