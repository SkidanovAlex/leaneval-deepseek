import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open _root_.SSGRoute
open scoped Pointwise

/-!
# Ramification is preserved by an isomorphism of algebraically closed fields

This file supplies the transport of the local notion `IsRamifiedIn` along a `ℚ`-algebra
isomorphism `σ : A ≃ₐ[ℚ] ℚ̄`: a place `B` of `ℚ̄` is ramified in `K.map σ` if and only if the
place `B.comap σ` of `A` is ramified in `K`.

The transfer is implemented by the conjugation bijection
`τ ↦ σ.symm.trans (τ.trans σ)` between `A ≃ₐ[ℚ] A` and `ℚ̄ ≃ₐ[ℚ] ℚ̄`.  Three ingredients are
isolated below:

* `comap_valuation_lt_one_iff_ringHom` — the `valuation (·) < 1` condition of `B.comap f` is the
  condition of `B` evaluated at `f (·)` (the two valuations are equivalent, being attached to the
  same valuation subring);
* `smul_comap_algEquiv` — pulling back along `σ` intertwines the pointwise conjugation action with
  the transport of places: `τ • (B.comap σ) = ((σ.symm.trans (τ.trans σ)) • B).comap σ`; this,
  together with injectivity of `B ↦ B.comap σ`, gives the decomposition-group statement
  `mem_decomp_comap_algEquiv`;
* `mem_fixingSubgroup_comap_algEquiv` — `τ` fixes `K` iff `σ.symm.trans (τ.trans σ)` fixes
  `K.map σ`, because the latter sends `σ x` to `σ (τ x)`.

`isInertia_comap_algEquiv` combines the first two into the inertia statement, and the main theorem
follows by transporting the witnessing element of the inertia group back and forth.
-/

section GeneralField

variable {K L : Type*} [Field K] [Field L]

/-- **Comparison of the `(-).valuation (·) < 1` condition along a `comap` (general ring
homomorphism).**  The valuation attached to `B.comap f` is equivalent to the pullback `B.valuation`
along `f`, so the two induce the same unit ball. -/
lemma comap_valuation_lt_one_iff_ringHom (B : ValuationSubring L) (f : K →+* L) (x : K) :
    (B.comap f).valuation x < 1 ↔ B.valuation (f x) < 1 := by
  have hsub : (B.comap f).valuation.valuationSubring =
      (B.valuation.comap f).valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  have heq : (B.comap f).valuation.IsEquiv (B.valuation.comap f) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq, Valuation.comap_apply]

end GeneralField

section Transfer

variable {A : Type} [Field A] [Algebra ℚ A]

/-- **Pulling back places along an isomorphism is injective.**  A place `B` of `ℚ̄` is the image
under `σ` of `B.comap σ`, so `B` is determined by `B.comap σ`. -/
lemma comap_ringHom_injective (σ : A ≃ₐ[ℚ] SSGRoute.QBar) :
    Function.Injective (fun V : ValuationSubring SSGRoute.QBar =>
      V.comap (σ : A →+* SSGRoute.QBar)) := by
  intro V W h
  have hVW : V.comap (σ : A →+* SSGRoute.QBar) = W.comap (σ : A →+* SSGRoute.QBar) := h
  have h' : ∀ z : A, z ∈ V.comap (σ : A →+* SSGRoute.QBar) ↔
      z ∈ W.comap (σ : A →+* SSGRoute.QBar) := fun z => by rw [hVW]
  ext y
  have hy := h' (σ.symm y)
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at hy
  have hσ : (σ : A →+* SSGRoute.QBar) (σ.symm y) = y := by
    show σ (σ.symm y) = y
    rw [AlgEquiv.apply_symm_apply]
  rwa [hσ] at hy

/-- **The conjugation action of `A ≃ₐ[ℚ] A` on places commutes with pulling back along `σ`.**
Pulling back the translate of `B` by `σ.symm.trans (τ.trans σ)` is the translate of `B.comap σ` by
`τ`.  (The corresponding statement with the roles of `σ` and `σ.symm` exchanged is
`Work.SSGRoute`'s `isConjPlace_pushforward`.) -/
lemma smul_comap_algEquiv (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (B : ValuationSubring SSGRoute.QBar)
    (τ : A ≃ₐ[ℚ] A) :
    τ • (B.comap (σ : A →+* SSGRoute.QBar)) =
      ((σ.symm.trans (τ.trans σ)) • B).comap (σ : A →+* SSGRoute.QBar) := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_smul_pointwise_iff_exists]
    refine ⟨σ s, hs, ?_⟩
    rw [← hsx]
    show (σ.symm.trans (τ.trans σ)) • (σ s) = σ (τ • s)
    rw [show ((σ.symm.trans (τ.trans σ)) • (σ s) : SSGRoute.QBar)
        = σ (τ (σ.symm (σ s))) from rfl, AlgEquiv.symm_apply_apply, AlgEquiv.smul_def]
  · intro hx
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨t, ht, htσx⟩ := hx
    have htσx' : (σ.symm.trans (τ.trans σ)) t = σ x := by
      simpa [AlgEquiv.smul_def] using htσx
    refine ⟨σ.symm t, ?_, ?_⟩
    · show σ (σ.symm t) ∈ B
      rw [AlgEquiv.apply_symm_apply]; exact ht
    · have h2 : σ (τ (σ.symm t)) = σ x := by
        rw [← htσx']
        exact (show (σ.symm.trans (τ.trans σ)) t = σ (τ (σ.symm t)) from rfl)
      have h3 : τ (σ.symm t) = x := σ.injective h2
      rwa [AlgEquiv.smul_def]

/-- **The decomposition group of a pulled back place is the conjugate decomposition group.** -/
lemma mem_decomp_comap_algEquiv (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (B : ValuationSubring SSGRoute.QBar)
    (τ : A ≃ₐ[ℚ] A) :
    τ ∈ decomp ℚ (B.comap (σ : A →+* SSGRoute.QBar)) ↔
      (σ.symm.trans (τ.trans σ)) ∈ decomp ℚ B := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_comap_algEquiv]
  constructor
  · intro h; exact comap_ringHom_injective σ h
  · intro h; rw [h]

/-- **Inertia is preserved by the conjugation transfer.** -/
lemma isInertia_comap_algEquiv (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (B : ValuationSubring SSGRoute.QBar)
    (τ : A ≃ₐ[ℚ] A) :
    IsInertia ℚ (B.comap (σ : A →+* SSGRoute.QBar)) τ ↔
      IsInertia ℚ B (σ.symm.trans (τ.trans σ)) := by
  simp only [IsInertia]
  constructor
  · rintro ⟨hd, hv⟩
    refine ⟨(mem_decomp_comap_algEquiv σ B τ).mp hd, fun y hy => ?_⟩
    have hx : σ.symm y ∈ B.comap (σ : A →+* SSGRoute.QBar) := by
      rw [ValuationSubring.mem_comap]
      show σ (σ.symm y) ∈ B
      rwa [AlgEquiv.apply_symm_apply]
    have h1 := hv (σ.symm y) hx
    rw [comap_valuation_lt_one_iff_ringHom] at h1
    have hcoe : (σ : A →+* SSGRoute.QBar) (τ (σ.symm y) - σ.symm y)
        = (σ.symm.trans (τ.trans σ)) y - y := by
      rw [show (σ : A →+* SSGRoute.QBar) (τ (σ.symm y) - σ.symm y)
          = σ (τ (σ.symm y) - σ.symm y) from rfl, map_sub]
      rw [show σ (τ (σ.symm y)) = (σ.symm.trans (τ.trans σ)) y from rfl,
          AlgEquiv.apply_symm_apply]
    rwa [hcoe] at h1
  · rintro ⟨hd, hv⟩
    refine ⟨(mem_decomp_comap_algEquiv σ B τ).mpr hd, fun x hx => ?_⟩
    have hy : σ x ∈ B := by
      show (σ : A →+* SSGRoute.QBar) x ∈ B
      rw [← ValuationSubring.mem_comap]
      exact hx
    have h2 := hv (σ x) hy
    have hcoe : (σ : A →+* SSGRoute.QBar) (τ x - x)
        = (σ.symm.trans (τ.trans σ)) (σ x) - σ x := by
      rw [show (σ : A →+* SSGRoute.QBar) (τ x - x) = σ (τ x - x) from rfl, map_sub]
      rw [show (σ.symm.trans (τ.trans σ)) (σ x) = σ (τ (σ.symm (σ x))) from rfl,
          AlgEquiv.symm_apply_apply]
    rw [comap_valuation_lt_one_iff_ringHom]
    simpa only [hcoe] using h2

/-- **Fixed fields are exchanged by the conjugation transfer.**  A conjugate `ρ` fixes `K.map σ`
exactly when `τ` fixes `K`, because `ρ (σ x) = σ (τ x)`. -/
lemma mem_fixingSubgroup_comap_algEquiv (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (K : IntermediateField ℚ A)
    (τ : A ≃ₐ[ℚ] A) :
    τ ∈ K.fixingSubgroup ↔
      (σ.symm.trans (τ.trans σ)) ∈ (K.map σ.toAlgHom).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    show (σ.symm.trans (τ.trans σ)) (σ x) = σ x
    rw [show (σ.symm.trans (τ.trans σ)) (σ x) = σ (τ (σ.symm (σ x))) from rfl,
        AlgEquiv.symm_apply_apply, h x hx]
  · intro h x hx
    have hσx : (σ.symm.trans (τ.trans σ)) (σ x) = σ x := by
      apply h
      rw [IntermediateField.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [show (σ.symm.trans (τ.trans σ)) (σ x) = σ (τ (σ.symm (σ x))) from rfl,
        AlgEquiv.symm_apply_apply] at hσx
    exact σ.injective hσx

/-- The conjugation map `τ ↦ σ.symm.trans (τ.trans σ)` is inverted on the other side by
`ρ ↦ σ.trans (ρ.trans σ.symm)`. -/
lemma trans_conj_inv (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (ρ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) :
    σ.symm.trans ((σ.trans (ρ.trans σ.symm)).trans σ) = ρ := by
  ext y
  show σ (σ.symm (ρ (σ (σ.symm y)))) = ρ y
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end Transfer

/-- **Ramification is preserved by an isomorphism of fields.**  For `σ : A ≃ₐ[ℚ] ℚ̄`, a subfield `K ⊆ A` and a place `B` of `ℚ̄`, the place `B.comap σ` of `A` is ramified in `K/ℚ` exactly when `B` is ramified in `K.map σ`/`ℚ`.  This is the transport used in `abs_discr_le_of_bddDegree_unramifiedOutside` to pass from an arbitrary algebraic closure of `ℚ` to `ℚ̄`.  The proof is the conjugation bijection `τ ↦ σ.symm.trans (τ.trans σ)` between `A ≃ₐ[ℚ] A` and `ℚ̄ ≃ₐ[ℚ] ℚ̄`: because `σ` is onto, `σ '' (B.comap σ) = B` and the comap valuation satisfies `(B.comap σ).valuation a < 1 ↔ B.valuation (σ a) < 1`, so `IsInertia ℚ (B.comap σ) τ ↔ IsInertia ℚ B (σ.symm.trans (τ.trans σ))`; and `τ ∈ K.fixingSubgroup ↔ σ.symm.trans (τ.trans σ) ∈ (K.map σ.toAlgHom).fixingSubgroup` since `ρ (σ x) = σ (τ x)`.  Relevant library lemmas: `ValuationSubring.mem_comap`, `ValuationSubring.mem_smul_pointwise_iff_exists`, `ValuationSubring.valuation_lt_one_iff_not_isUnit`, `place_basics.isInertia_conj`, `place_basics.decomp_conj`. -/
theorem isRamifiedIn_comap_algEquiv_proved (A : Type) [Field A] [Algebra ℚ A]
    (σ : A ≃ₐ[ℚ] SSGRoute.QBar) (K : IntermediateField ℚ A)
    (B : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsRamifiedIn ℚ K (B.comap (σ : A →+* SSGRoute.QBar)) ↔
      SSGRoute.IsRamifiedIn ℚ (K.map σ.toAlgHom) B := by
  simp only [SSGRoute.IsRamifiedIn]
  constructor
  · rintro ⟨τ, hI, hτ⟩
    exact ⟨σ.symm.trans (τ.trans σ), (isInertia_comap_algEquiv σ B τ).mp hI,
      fun hmem => hτ ((mem_fixingSubgroup_comap_algEquiv σ K τ).mpr hmem)⟩
  · rintro ⟨ρ, hI, hρ⟩
    refine ⟨σ.trans (ρ.trans σ.symm), ?_, ?_⟩
    · rw [isInertia_comap_algEquiv, trans_conj_inv]
      exact hI
    · rw [mem_fixingSubgroup_comap_algEquiv, trans_conj_inv]
      exact hρ

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
