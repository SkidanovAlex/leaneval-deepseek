/-
# Surjectivity of the Kummer character for a Kummer extension

Let `K` be a field containing a primitive `n`-th root of unity `ζ`, and let `L/K` be a finite
Galois extension of exponent dividing `n` which is a *Kummer extension*: `L` is generated over
`K` by the `n`-th roots in `L` of elements of `K`.

The Kummer pairing `Gal(L/K) × (Kˣ ∩ (Lˣ)^n) → μ_n`, `(σ, a) ↦ σ α / α` (where `α ^ n = a`),
is encoded by `kummerCharacter hζ : kummerSubgroup n K L →* (Gal(L/K) →* rootsOfUnity n K)`.
The main theorem here, `kummerCharacter_surjective_of_isKummerExtension`, is one half of the
perfectness of this pairing, namely the classical statement of Kummer theory that **every**
character `Gal(L/K) →* μ_n` is a Kummer character:

`∀ χ : Gal(L/K) →* rootsOfUnity n K, ∃ a, kummerCharacter hζ a = χ`.

## Strategy

The pairing is a biadditive map into the abelian group `μ_n(K)`, giving two injections:

* `kummerPairing : (Kˣ ∩ (Lˣ)^n)/(Kˣ)^n ⟶ (Gal(L/K) →* μ_n)`, injective by
  `kummerPairing_injective` (the kernel is the group of `n`-th powers in `Kˣ`), and
* its "transpose" `kummerCharacterFlipQuotient : Gal(L/K) ⟶ ((Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* μ_n)`,
  injective because `L` is generated over `K` by `n`-th roots, so that an automorphism acting
  trivially in the pairing is trivial (`eq_one_of_forall_kummerCharacter_eq_one`).

Since both sides are finite of the same cardinality, the first injection is bijective, which is
exactly the required surjectivity.  Counting characters is the classical duality statement for
finite abelian groups of exponent dividing `n` over a field with enough `n`-th roots of unity:
`Nat.card (A →* μ_n) = Nat.card A` (`card_monoidHom_rootsOfUnity`), and the Kummer quotient
`(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n` has exponent dividing `n` (`pow_n_eq_one_kummerQuotient`).

As a byproduct we obtain that the Kummer quotient has the same cardinality as the Galois group,
`card_kummerQuotient_eq_card_gal`.
-/
import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_eq_one_iff
import Submission.Work.Kummer.eq_one_of_forall_kummerCharacter_eq_one
import Submission.Work.Kummer.card_monoidHom_rootsOfUnity
import Submission.Work.Kummer.pow_n_eq_one_kummerQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

set_option linter.style.haveILetI false

namespace Work.Kummer

open IntermediateField

section Flip

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- The Kummer pairing with its arguments swapped: `σ ↦ (a ↦ χ_a(σ))`, as a homomorphism
in `σ`. -/
noncomputable def kummerCharacterFlip (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) →* (kummerSubgroup n K L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := fun a => kummerCharacter hζ a σ
      map_one' := by
        have h : kummerCharacter hζ (1 : kummerSubgroup n K L) = 1 :=
          kummerCharacter_eq_one_of_mem_nthPower hζ
            (one_mem ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)))
        simpa using congrArg (fun f : Gal(L/K) →* rootsOfUnity n K => f σ) h
      map_mul' := fun a b => by
        show kummerCharacter hζ (a * b) σ = kummerCharacter hζ a σ * kummerCharacter hζ b σ
        rw [kummerCharacter_mul hζ a b, MonoidHom.mul_apply] }
  map_one' := MonoidHom.ext fun a => by
    show kummerCharacter hζ a (1 : Gal(L/K)) = 1
    exact map_one (kummerCharacter hζ a)
  map_mul' := fun σ τ => MonoidHom.ext fun a => by
    show kummerCharacter hζ a (σ * τ) = kummerCharacter hζ a σ * kummerCharacter hζ a τ
    exact map_mul (kummerCharacter hζ a) σ τ

@[simp]
lemma kummerCharacterFlip_apply (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K))
    (a : kummerSubgroup n K L) :
    kummerCharacterFlip hζ σ a = kummerCharacter hζ a σ := rfl

/-- The Kummer pairing separates points of `Gal(L/K)` when `L/K` is a Kummer extension: a
`K`-automorphism acting trivially in the pairing is trivial. -/
theorem kummerCharacterFlip_injective (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (hL : IsKummerExtension n K L) :
    Function.Injective (kummerCharacterFlip (K := K) (L := L) hζ) := by
  have hker : ∀ σ : Gal(L/K), kummerCharacterFlip hζ σ = 1 → σ = 1 := by
    intro σ hσ
    refine eq_one_of_forall_kummerCharacter_eq_one hζ hL σ (fun a => ?_)
    have h := congrArg (fun f : kummerSubgroup n K L →* rootsOfUnity n K => f a) hσ
    simpa using h
  intro σ τ hστ
  have h1 : kummerCharacterFlip hζ (σ * τ⁻¹) = 1 := by
    rw [map_mul, hστ, map_inv, mul_inv_cancel]
  have h2 := hker (σ * τ⁻¹) h1
  rwa [mul_inv_eq_one] at h2

/-- **The Galois group of a Kummer extension is abelian.** -/
theorem mul_comm_gal_of_isKummerExtension (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (hL : IsKummerExtension n K L) (σ τ : Gal(L/K)) : σ * τ = τ * σ :=
  kummerCharacterFlip_injective hζ hL (by rw [map_mul, map_mul, mul_comm])

end Flip

section QuotientFlip

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- The Kummer character at a fixed automorphism `σ`, as a homomorphism on the Kummer
quotient `(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n`. -/
noncomputable def kummerCharacterLift (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K)) :
    kummerQuotient n K L →* rootsOfUnity n K :=
  QuotientGroup.lift ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L))
    (kummerCharacterFlip hζ σ) (fun x hx => by
      have h : kummerCharacter hζ x σ = 1 :=
        congrArg (fun f : Gal(L/K) →* rootsOfUnity n K => f σ)
          (kummerCharacter_eq_one_of_mem_nthPower hζ hx)
      simpa using h)

lemma kummerCharacterLift_mk (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K))
    (a : kummerSubgroup n K L) :
    kummerCharacterLift hζ σ
      (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a)
      = kummerCharacter hζ a σ :=
  rfl

/-- The flipped Kummer pairing, descended to the Kummer quotient. -/
noncomputable def kummerCharacterFlipQuotient (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) →* (kummerQuotient n K L →* rootsOfUnity n K) where
  toFun := kummerCharacterLift hζ
  map_one' := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    show kummerCharacterLift hζ 1
      (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) x) = 1
    rw [kummerCharacterLift_mk]
    exact map_one (kummerCharacter hζ x)
  map_mul' := fun σ τ => by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [MonoidHom.mul_apply]
    show kummerCharacterLift hζ (σ * τ)
        (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) x)
      = kummerCharacterLift hζ σ
          (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) x)
        * kummerCharacterLift hζ τ
          (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) x)
    rw [kummerCharacterLift_mk]
    exact map_mul (kummerCharacter hζ x) σ τ

@[simp]
lemma kummerCharacterFlipQuotient_mk (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K))
    (a : kummerSubgroup n K L) :
    kummerCharacterFlipQuotient hζ σ
      (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a)
      = kummerCharacter hζ a σ := by
  show kummerCharacterLift hζ σ
      (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a)
      = kummerCharacter hζ a σ
  exact kummerCharacterLift_mk hζ σ a

/-- The descended flipped pairing separates points of `Gal(L/K)`. -/
theorem kummerCharacterFlipQuotient_injective (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (hL : IsKummerExtension n K L) :
    Function.Injective (kummerCharacterFlipQuotient (K := K) (L := L) hζ) := by
  have hker : ∀ σ : Gal(L/K), kummerCharacterFlipQuotient hζ σ = 1 → σ = 1 := by
    intro σ hσ
    refine eq_one_of_forall_kummerCharacter_eq_one hζ hL σ (fun a => ?_)
    have h1 : kummerCharacterFlipQuotient hζ σ
        (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a) = 1 := by
      rw [hσ]
      rfl
    exact h1
  intro σ τ hστ
  have h1 : kummerCharacterFlipQuotient hζ (σ * τ⁻¹) = 1 := by
    rw [map_mul, hστ, map_inv, mul_inv_cancel]
  have h2 := hker (σ * τ⁻¹) h1
  rwa [mul_inv_eq_one] at h2

end QuotientFlip

section Count

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- **Counting form of Kummer theory.**  For a Kummer extension `L/K` of exponent dividing `n`
over a field `K` containing a primitive `n`-th root of unity `ζ`, the quotient
`(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n` has the same cardinality as the Galois group `Gal(L/K)`.

Indeed the Kummer pairing gives injections `(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n → (Gal(L/K) →* μ_n)` and
`Gal(L/K) → ((Kˣ ∩ (Lˣ)^n)/(Kˣ)^n →* μ_n)`, and both duals have cardinality equal to that of
the corresponding group, by duality for finite abelian groups of exponent dividing `n`. -/
theorem card_kummerQuotient_eq_card_gal (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (hexp : Monoid.exponent Gal(L/K) ∣ n) (hL : IsKummerExtension n K L) :
    Nat.card (kummerQuotient n K L) = Nat.card Gal(L/K) := by
  classical
  haveI hRoot : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic K n⟩
  -- The Galois group is commutative, so that duality applies to it.
  have hcomm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ :=
    mul_comm_gal_of_isKummerExtension hζ hL
  let hG' : Group Gal(L/K) := inferInstance
  letI : CommGroup Gal(L/K) := { hG' with mul_comm := hcomm }
  have hpowG : ∀ g : Gal(L/K), g ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp
  -- Finiteness of the two dual groups.
  haveI hfinHom : Finite (Gal(L/K) →* rootsOfUnity n K) :=
    Finite.of_injective (fun f : Gal(L/K) →* rootsOfUnity n K => (f : Gal(L/K) → rootsOfUnity n K))
      (fun f g h => MonoidHom.ext (congr_fun h))
  haveI hfinQ : Finite (kummerQuotient n K L) :=
    Finite.of_injective (kummerPairing hζ) (kummerPairing_injective hζ)
  haveI hfinQHom : Finite (kummerQuotient n K L →* rootsOfUnity n K) :=
    Finite.of_injective
      (fun f : kummerQuotient n K L →* rootsOfUnity n K =>
        (f : kummerQuotient n K L → rootsOfUnity n K))
      (fun f g h => MonoidHom.ext (congr_fun h))
  -- Both duals have as many elements as the group they are dual to.
  have hcardG : Nat.card (Gal(L/K) →* rootsOfUnity n K) = Nat.card Gal(L/K) :=
    card_monoidHom_rootsOfUnity (K := K) hpowG
  have hcardQ : Nat.card (kummerQuotient n K L →* rootsOfUnity n K) =
      Nat.card (kummerQuotient n K L) :=
    card_monoidHom_rootsOfUnity (G := kummerQuotient n K L) (K := K) (n := n)
      (fun q => pow_n_eq_one_kummerQuotient q)
  refine le_antisymm ?_ ?_
  · -- the pairing is injective modulo `n`-th powers
    rw [← hcardG]
    exact Nat.card_le_card_of_injective _ (kummerPairing_injective hζ)
  · -- the pairing separates points of the Galois group
    rw [← hcardQ]
    exact Nat.card_le_card_of_injective _ (kummerCharacterFlipQuotient_injective hζ hL)

end Count

/-- **Surjectivity of the Kummer character.**  For a finite Galois extension `L/K` of exponent
dividing `n` which is generated over `K` by `n`-th roots of elements of `K`, and with `K`
containing a primitive `n`-th root of unity `ζ`, every character `Gal(L/K) →* μ_n` is the Kummer
character of some element of the Kummer subgroup `Kˣ ∩ (Lˣ)^n`. -/
theorem kummerCharacter_surjective_of_isKummerExtension {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (hL : IsKummerExtension n K L)
    (χ : Gal(L/K) →* rootsOfUnity n K) :
    ∃ a : kummerSubgroup n K L, kummerCharacter hζ a = χ := by
  classical
  haveI hRoot : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic K n⟩
  have hcomm : ∀ σ τ : Gal(L/K), σ * τ = τ * σ :=
    mul_comm_gal_of_isKummerExtension hζ hL
  let hG' : Group Gal(L/K) := inferInstance
  letI : CommGroup Gal(L/K) := { hG' with mul_comm := hcomm }
  have hpowG : ∀ g : Gal(L/K), g ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp
  haveI hfinHom : Finite (Gal(L/K) →* rootsOfUnity n K) :=
    Finite.of_injective (fun f : Gal(L/K) →* rootsOfUnity n K => (f : Gal(L/K) → rootsOfUnity n K))
      (fun f g h => MonoidHom.ext (congr_fun h))
  -- The pairing has equally many elements on both sides, so injectivity is bijectivity.
  have hcard : Nat.card (kummerQuotient n K L) = Nat.card (Gal(L/K) →* rootsOfUnity n K) := by
    rw [card_kummerQuotient_eq_card_gal hζ hexp hL,
      ← card_monoidHom_rootsOfUnity (K := K) hpowG]
  have hbij := (Nat.bijective_iff_injective_and_card (kummerPairing hζ)).mpr
    ⟨kummerPairing_injective hζ, hcard⟩
  obtain ⟨q, hq⟩ := hbij.2 χ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) q
  exact ⟨a, by rw [← kummerPairing_mk hζ a]; exact hq⟩

end Work.Kummer
