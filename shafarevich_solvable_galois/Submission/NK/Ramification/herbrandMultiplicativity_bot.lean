/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicativity of the Herbrand function in the degenerate case `M = ⊥`

`NK.Ramification.HerbrandMultiplicativity A M` (Serre, *Local Fields*, IV §3 Prop. 15) is the
identity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` for a tower `K ⊆ M ⊆ L` with `M/K` Galois.  The present
file proves the case `M = ⊥`, i.e. the case of the trivial subextension `K ⊆ M`.  Since
`(⊥ : IntermediateField K L) = Set.range (algebraMap K L)` is the image of `K`, both factors on
the right are then the identity:

* `φ_{M/K} = id`, because the only `K`-algebra automorphism of `↥⊥` is the identity
  (`Subsingleton (↥⊥ ≃ₐ[K] ↥⊥)`, from the surjectivity of `algebraMap K ↥⊥`), so the whole
  ramification filtration of the trivial extension is trivial and
  `herbrandRat_eq_id_of_forall_eq_bot` applies;
* `φ_{L/M} = φ_{L/K}`, because `L ≃ₐ[K] L` and `L ≃ₐ[↥⊥] L` are the same group acting on `L` in
  the same way: the bijection is `AlgEquiv.extendScalarsHomOfSurjective` (the algebra map
  `K → ↥⊥` is surjective because `↥⊥` *is* the image of `K`), it carries the stabiliser of the
  valuation ring `A` onto the stabiliser (`galBotEquiv_smul`), and it identifies the higher
  ramification subgroups `G_i` of the two normalisations (`mem_ramificationSubgroup_decompEquiv`).
  Consequently the lower indices `g_i` agree (`natCard_ramificationSubgroup_bot`) and with them
  the Herbrand function (`herbrandRat_bot`).

The general multiplicativity theorem is *not* proved here; see
`Submission/Work/Ramification/README.md`, §5.
-/
import Mathlib
import Submission.NK.Ramification.Tower
import Submission.NK.Ramification.herbrandRat_eq_id_of_forall_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## The bottom intermediate field: `K`- and `↥⊥`-structures agree -/

/-- The algebra map `K → ↥(⊥ : IntermediateField K L)` is surjective, because `⊥` is the image
of `K` in `L` (`IntermediateField.coe_bot`).  Equivalently, `(IntermediateField.botEquiv K L).symm`
has this algebra map as its underlying function. -/
lemma surjective_algebraMap_bot :
    Function.Surjective (algebraMap K ↥(⊥ : IntermediateField K L)) :=
  fun x => ⟨(IntermediateField.botEquiv K L) x, by
    simpa only [IntermediateField.botEquiv_symm] using
      (IntermediateField.botEquiv K L).symm_apply_apply x⟩

/-- **`Gal(L/K) ≃* Gal(L/↥⊥)`**: because `K → ↥⊥` is surjective, every `K`-algebra automorphism
of `L` is an `↥⊥`-algebra automorphism and conversely.  Both directions are the identity on the
underlying function (`coe_galBotEquiv`). -/
noncomputable def galBotEquiv :
    (L ≃ₐ[K] L) ≃* (L ≃ₐ[↥(⊥ : IntermediateField K L)] L) :=
  AlgEquiv.extendScalarsHomOfSurjective (A := L) (R := K)
    (S := ↥(⊥ : IntermediateField K L)) surjective_algebraMap_bot

/-- `galBotEquiv` does not change the underlying function. -/
lemma coe_galBotEquiv (σ : L ≃ₐ[K] L) : ⇑(galBotEquiv σ) = ⇑σ := by
  rw [galBotEquiv, AlgEquiv.extendScalarsHomOfSurjective_apply]
  rfl

/-- The two actions of `L ≃ₐ[K] L` and `L ≃ₐ[↥⊥] L` on a valuation subring agree under
`galBotEquiv`, since the action only sees the underlying function on `L`. -/
lemma galBotEquiv_smul (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    galBotEquiv σ • A = σ • A := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor <;> rintro ⟨a, ha, rfl⟩
  · exact ⟨a, ha, by rw [AlgEquiv.smul_def, AlgEquiv.smul_def, coe_galBotEquiv]⟩
  · exact ⟨a, ha, by rw [AlgEquiv.smul_def, AlgEquiv.smul_def, coe_galBotEquiv]⟩

/-- The same for the inverse direction of `galBotEquiv`. -/
lemma galBotEquiv_symm_smul (A : ValuationSubring L)
    (τ : L ≃ₐ[↥(⊥ : IntermediateField K L)] L) :
    galBotEquiv.symm τ • A = τ • A := by
  rw [← galBotEquiv_smul A (galBotEquiv.symm τ), MulEquiv.apply_symm_apply]

/-- **The decomposition subgroups agree**: `galBotEquiv` restricts to an isomorphism between the
stabilisers of `A`. -/
noncomputable def decompEquiv (A : ValuationSubring L) :
    A.decompositionSubgroup K ≃* A.decompositionSubgroup ↥(⊥ : IntermediateField K L) where
  toFun σ := ⟨galBotEquiv σ, by
    rw [MulAction.mem_stabilizer_iff, galBotEquiv_smul]
    exact (MulAction.mem_stabilizer_iff).mp σ.2⟩
  invFun τ := ⟨galBotEquiv.symm (τ : L ≃ₐ[↥(⊥ : IntermediateField K L)] L), by
    rw [MulAction.mem_stabilizer_iff, galBotEquiv_symm_smul]
    exact (MulAction.mem_stabilizer_iff).mp τ.2⟩
  left_inv σ := Subtype.ext (MulEquiv.symm_apply_apply galBotEquiv (σ : L ≃ₐ[K] L))
  right_inv τ := Subtype.ext
    (MulEquiv.apply_symm_apply galBotEquiv (τ : L ≃ₐ[↥(⊥ : IntermediateField K L)] L))
  map_mul' σ τ := rfl

/-- `decompEquiv` is compatible with the actions on `A`. -/
lemma smul_decompEquiv_eq (A : ValuationSubring L) (σ : A.decompositionSubgroup K) (x : A) :
    (decompEquiv A σ) • x = σ • x := by
  apply Subtype.ext
  rw [coe_smul A (decompEquiv A σ) x, coe_smul A σ x]
  exact congrFun (coe_galBotEquiv (σ : L ≃ₐ[K] L)) (x : L)

/-! ## The lower indices and the Herbrand function -/

/-- `decompEquiv` restricts to an isomorphism between the higher ramification subgroups
`G_i`, in the two normalisations `L/K` and `L/↥⊥`. -/
lemma mem_ramificationSubgroup_decompEquiv (A : ValuationSubring L) (i : ℕ)
    (σ : A.decompositionSubgroup K) :
    (decompEquiv A σ) ∈ ramificationSubgroup (K := ↥(⊥ : IntermediateField K L)) A i ↔
      σ ∈ ramificationSubgroup (K := K) A i := by
  simp only [mem_ramificationSubgroup_iff]
  exact forall_congr' fun x => by rw [smul_decompEquiv_eq]

/-- **The lower indices `g_i` agree** for the two normalisations `L/K` and `L/↥⊥`. -/
lemma natCard_ramificationSubgroup_bot (A : ValuationSubring L) (i : ℕ) :
    Nat.card ↥(ramificationSubgroup (K := K) A i) =
      Nat.card ↥(ramificationSubgroup (K := ↥(⊥ : IntermediateField K L)) A i) :=
  Nat.card_congr (Equiv.subtypeEquiv (decompEquiv A).toEquiv
    fun σ => (mem_ramificationSubgroup_decompEquiv A i σ).symm)

/-- **The Herbrand function of `L/K` is that of `L/↥⊥`**, the two lower-index sequences being
equal.  This is the second factor of the multiplicativity identity in the case `M = ⊥`. -/
lemma herbrandRat_bot (A : ValuationSubring L) (u : ℚ) :
    herbrandRat (K := K) A u = herbrandRat (K := ↥(⊥ : IntermediateField K L)) A u := by
  have h : ∀ i, lowerIndex (K := K) A i = lowerIndex (K := ↥(⊥ : IntermediateField K L)) A i :=
    natCard_ramificationSubgroup_bot A
  simp only [herbrandRat, h]

/-! ## The trivial extension `↥⊥/K` -/

/-- **The trivial extension has no automorphisms**: every `K`-algebra automorphism of `↥⊥` is the
identity, because `↥⊥` is the image of `K`. -/
lemma subsingleton_algEquiv_bot :
    Subsingleton (↥(⊥ : IntermediateField K L) ≃ₐ[K] ↥(⊥ : IntermediateField K L)) :=
  ⟨fun σ τ => AlgEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := surjective_algebraMap_bot (K := K) (L := L) x
    rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩

/-- **The ramification filtration of the trivial extension is trivial**: the whole filtration
lives inside the decomposition subgroup, which is a subgroup of the trivial group. -/
lemma ramificationSubgroup_comap_bot_eq_bot (A : ValuationSubring L) (i : ℕ) :
    ramificationSubgroup (K := K) (A.comap (algebraMap ↥(⊥ : IntermediateField K L) L)) i = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun σ _ => Subtype.ext ?_
  exact (subsingleton_algEquiv_bot (K := K) (L := L)).allEq _
    (1 : ↥(⊥ : IntermediateField K L) ≃ₐ[K] ↥(⊥ : IntermediateField K L))

/-- **`φ_{↥⊥/K}` is the identity**, the ramification filtration of the trivial extension being
everywhere trivial.  This is the first factor of the multiplicativity identity for `M = ⊥`. -/
lemma herbrandRat_comap_bot (A : ValuationSubring L) (u : ℚ) :
    herbrandRat (K := K) (A.comap (algebraMap ↥(⊥ : IntermediateField K L) L)) u = u :=
  herbrandRat_eq_id_of_forall_eq_bot _
    (fun i => ramificationSubgroup_comap_bot_eq_bot A i) u

/-! ## The result -/

theorem herbrandMultiplicativity_bot {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    NK.Ramification.HerbrandMultiplicativity (K := K) A ⊥ := by
  intro u
  rw [herbrandRat_bot A u, herbrandRat_comap_bot A]

end

end NK.Ramification
