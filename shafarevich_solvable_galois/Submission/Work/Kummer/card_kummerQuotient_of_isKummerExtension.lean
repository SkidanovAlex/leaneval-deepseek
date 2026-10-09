/-
The cardinality of the Kummer quotient

For `L/K` a finite Galois extension with `K` containing a primitive `n`-th root of unity `ζ`
and `Gal(L/K)` of exponent dividing `n`, Kummer theory says that the Kummer pairing
`Gal(L/K) × (Kˣ ∩ (Lˣ)^n)/(Kˣ)^n → μ_n` is a perfect pairing.  In particular the Kummer quotient
`(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n` has the same cardinality as the Galois group, hence as `[L : K]`.

Here we avoid constructing the inverse of the Kummer pairing.  We only use the two
non-degeneracy statements, which are available as `kummerPairing_injective` (the pairing is
injective modulo `n`-th powers, i.e. non-degenerate in the second variable) and
`eq_one_of_forall_kummerCharacter_eq_one` (an automorphism killing the pairing is trivial, i.e.
non-degeneracy in the first variable).  Together with the duality theorem for finite abelian
groups (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`) these force the two cardinalities to
coincide.
-/
import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerCharacter_eq_one_iff
import Submission.Work.Kummer.eq_one_of_forall_kummerCharacter_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

open IntermediateField

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- The transpose of the Kummer pairing: `Gal(L/K)` acts on the Kummer quotient by evaluation,
`σ ↦ (x ↦ kummerPairing x σ)`. -/
noncomputable def kummerPairingTranspose (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) →* (kummerQuotient n K L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := fun x => kummerPairing hζ x σ
      map_one' := by simp
      map_mul' := by intro x y; simp }
  map_one' := by ext x; simp
  map_mul' := by intro σ τ; ext x; simp

@[simp]
lemma kummerPairingTranspose_apply (hζ : IsPrimitiveRoot ζ n) (σ : Gal(L/K))
    (x : kummerQuotient n K L) :
    kummerPairingTranspose hζ σ x = kummerPairing hζ x σ := rfl

/-- Non-degeneracy of the Kummer pairing in the first variable, in the form that the transpose
map `Gal(L/K) → (Kummer quotient →* μ_n)` is injective. -/
lemma kummerPairingTranspose_injective (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] (hL : IsKummerExtension n K L) :
    Function.Injective (kummerPairingTranspose (K := K) (L := L) hζ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine le_antisymm (fun σ hσ => ?_) bot_le
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hσ
  refine eq_one_of_forall_kummerCharacter_eq_one hζ hL σ (fun a => ?_)
  have h1 : kummerPairingTranspose hζ σ (QuotientGroup.mk' _ a) = 1 := by
    rw [hσ]; rfl
  rw [kummerPairingTranspose_apply, kummerPairing_mk] at h1
  exact h1

/-- The Kummer quotient has exponent dividing `n`: the `n`-th power of every class is trivial. -/
lemma exponent_kummerQuotient_dvd :
    Monoid.exponent (kummerQuotient n K L) ∣ n := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => ?_)
  refine QuotientGroup.induction_on x (fun a => ?_)
  change (QuotientGroup.mk' ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) a) ^ n = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr ⟨(a : Kˣ), by simp⟩

/-- The canonical projection onto the abelianization is surjective. -/
lemma abelianization_of_surjective :
    Function.Surjective (Abelianization.of (G := Gal(L/K))) := by
  intro y
  exact QuotientGroup.induction_on y (fun a => ⟨a, (Abelianization.mk_eq_of a).symm⟩)

/-- Composing with the inclusion `μ_n ↪ Kˣ` is injective on monoid homomorphisms. -/
lemma subtype_comp_rootsOfUnity_injective {A : Type*} [Monoid A] :
    Function.Injective
      (fun φ : A →* rootsOfUnity n K =>
        (Subgroup.subtype (rootsOfUnity n K)).comp φ) := by
  intro φ ψ h
  apply MonoidHom.ext
  intro a
  exact Subgroup.subtype_injective (rootsOfUnity n K) (DFunLike.congr_fun h a)

theorem card_kummerQuotient_of_isKummerExtension {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (hL : IsKummerExtension n K L) :
    Nat.card (kummerQuotient n K L) = Module.finrank K L := by
  -- `K` has enough `n`-th roots of unity, since it contains the primitive root `ζ`.
  haveI hK : HasEnoughRootsOfUnity K n :=
    { prim := ⟨ζ, hζ⟩, cyc := rootsOfUnity.isCyclic K n }
  haveI hfinG : Finite Gal(L/K) := inferInstance
  haveI hfinMu : Finite (rootsOfUnity n K) := inferInstance
  haveI hfinHomG : Finite (Gal(L/K) →* rootsOfUnity n K) :=
    Finite.of_injective
      (fun f : Gal(L/K) →* rootsOfUnity n K => (f : Gal(L/K) → rootsOfUnity n K))
      DFunLike.coe_injective
  -- The Kummer quotient is finite, as it embeds into `Gal(L/K) →* μ_n`.
  haveI hfinA : Finite (kummerQuotient n K L) :=
    Finite.of_injective (kummerPairing hζ) (kummerPairing_injective hζ)
  haveI hfinHomA : Finite (kummerQuotient n K L →* rootsOfUnity n K) :=
    Finite.of_injective
      (fun f : kummerQuotient n K L →* rootsOfUnity n K =>
        (f : kummerQuotient n K L → rootsOfUnity n K)) DFunLike.coe_injective
  haveI hfinHomGab : Finite (Abelianization Gal(L/K) →* rootsOfUnity n K) :=
    Finite.of_injective
      (fun f : Abelianization Gal(L/K) →* rootsOfUnity n K =>
        (f : Abelianization Gal(L/K) → rootsOfUnity n K)) DFunLike.coe_injective
  -- `K` has enough roots of unity for the exponents of the two groups involved.
  haveI hKA : HasEnoughRootsOfUnity K (Monoid.exponent (kummerQuotient n K L)) :=
    HasEnoughRootsOfUnity.of_dvd K (exponent_kummerQuotient_dvd (K := K) (L := L) (n := n))
  haveI hfinGab : Finite (Abelianization Gal(L/K)) := inferInstance
  haveI hKGab : HasEnoughRootsOfUnity K (Monoid.exponent (Abelianization Gal(L/K))) :=
    HasEnoughRootsOfUnity.of_dvd K
      ((Group.exponent_quotient_dvd (commutator Gal(L/K))).trans hexp)
  -- Non-degeneracy in the first variable: `|Gal(L/K)| ≤ |Kummer quotient|`.
  have hle1 : Nat.card Gal(L/K) ≤ Nat.card (kummerQuotient n K L) := by
    have h1 : Nat.card Gal(L/K) ≤ Nat.card (kummerQuotient n K L →* rootsOfUnity n K) :=
      Nat.card_le_card_of_injective (kummerPairingTranspose hζ) (kummerPairingTranspose_injective hζ hL)
    have h2 : Nat.card (kummerQuotient n K L →* rootsOfUnity n K)
        ≤ Nat.card (kummerQuotient n K L →* Kˣ) :=
      Nat.card_le_card_of_injective
        (fun φ : kummerQuotient n K L →* rootsOfUnity n K =>
          (Subgroup.subtype (rootsOfUnity n K)).comp φ)
        (subtype_comp_rootsOfUnity_injective (K := K) (n := n))
    have h3 : Nat.card (kummerQuotient n K L →* Kˣ) = Nat.card (kummerQuotient n K L) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (kummerQuotient n K L) K
    exact (h1.trans h2).trans (le_of_eq h3)
  -- Non-degeneracy in the second variable: `|Kummer quotient| ≤ |Gal(L/K)|`.
  -- The pairing lands in `μ_n ⊆ (Kˣ)`, and homomorphisms into an abelian group factor through
  -- the abelianization; both steps only shrink the cardinality.
  have hle2 : Nat.card (kummerQuotient n K L) ≤ Nat.card Gal(L/K) := by
    have h1 : Nat.card (kummerQuotient n K L)
        ≤ Nat.card (Abelianization Gal(L/K) →* rootsOfUnity n K) :=
      Nat.card_le_card_of_injective
        (fun x : kummerQuotient n K L =>
          (Abelianization.lift (A := rootsOfUnity n K)) (kummerPairing hζ x))
        (by
          intro x y hxy
          exact kummerPairing_injective hζ
            ((Abelianization.lift (A := rootsOfUnity n K)).injective hxy))
    have h2 : Nat.card (Abelianization Gal(L/K) →* rootsOfUnity n K)
        ≤ Nat.card (Abelianization Gal(L/K) →* Kˣ) :=
      Nat.card_le_card_of_injective
        (fun φ : Abelianization Gal(L/K) →* rootsOfUnity n K =>
          (Subgroup.subtype (rootsOfUnity n K)).comp φ)
        (subtype_comp_rootsOfUnity_injective (K := K) (n := n))
    have h3 : Nat.card (Abelianization Gal(L/K) →* Kˣ)
        = Nat.card (Abelianization Gal(L/K)) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Abelianization Gal(L/K)) K
    have h4 : Nat.card (Abelianization Gal(L/K)) ≤ Nat.card Gal(L/K) :=
      Nat.card_le_card_of_surjective (Abelianization.of) abelianization_of_surjective
    exact ((h1.trans h2).trans (le_of_eq h3)).trans h4
  have hEqA : Nat.card (kummerQuotient n K L) = Nat.card Gal(L/K) := le_antisymm hle2 hle1
  rw [hEqA, IsGalois.card_aut_eq_finrank K L]

end Work.Kummer
