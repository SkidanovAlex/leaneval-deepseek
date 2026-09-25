import Mathlib
import Submission.Work.Tower.CyclotomicBase.Defs
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.isCyclotomicExtension_Zfield
import Submission.Work.Tower.CyclotomicBase.ker_unitsMap_inf_ker_unitsMap_eq_bot
import Submission.Work.Tower.CyclotomicBase.exists_unitsMap_eq_one_and
import Submission.Work.Tower.CyclotomicBase.inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one
import Submission.Work.Tower.CyclotomicBase.ramificationIdxIn_cyc

/-!
# The inertia subgroup of the prime `rᵢ` in `ℚ(ζ_D)`

Let `r : Fin ℓ → ℕ` be a family of pairwise distinct primes and `D = ∏ᵢ rᵢ`.  Then `ℚ(ζ_D)` has
Galois group `(ℤ/D)ˣ` (via `galEquiv`), and the inertia subgroup of a prime `P` of `𝓞 ℚ(ζ_D)`
lying over the rational prime `rᵢ` is the subgroup of `Gal(ℚ(ζ_D)/ℚ)` corresponding to the units
that are `1` modulo `D / rᵢ`:

`Ideal.inertia Gal(ℚ(ζ_D)/ℚ) P = (inertiaSub r i).comap (galEquiv r)`.

The proof has two halves:

* `≤`: `rᵢ` is unramified in the inertia field `Zfield r i = ℚ(ζ_{D/rᵢ})`, so the inertia group is
  contained in the fixing subgroup of that field, which is exactly the subgroup in question
  (`inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one`).

* `=`: both sides have cardinality `rᵢ - 1`.  For the left hand side this is
  `Ideal.card_inertia_eq_ramificationIdxIn` combined with the computation
  `(span {rᵢ}).ramificationIdxIn (𝓞 ℚ(ζ_D)) = rᵢ - 1` (`ramificationIdxIn_cyc`); for the right hand
  side it is `φ(D)/φ(D/rᵢ) = φ(rᵢ) = rᵢ - 1`.
-/

set_option linter.style.haveILetI false

open NumberField

namespace Work.Tower.CyclotomicBase

variable {ℓ : ℕ}

/-- `r i` is unramified in the inertia field `Zfield r i = ℚ(ζ_{D/rᵢ})`. -/
lemma ramificationIdxIn_Zfield (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ) :
    (Ideal.span {(r i : ℤ)}).ramificationIdxIn (𝓞 ↥(Zfield r i)) = 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI hmz : NeZero (D r / r i) := ⟨by
    have h := Nat.div_mul_cancel (r_dvd_D r i)
    intro h0
    rw [h0, zero_mul] at h
    exact NeZero.ne (D r) h.symm⟩
  haveI hcyc : IsCyclotomicExtension {D r / r i} ℚ ↥(Zfield r i) :=
    isCyclotomicExtension_Zfield r hr i
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (K := ↥(Zfield r i))
    (m := D r / r i) (r i) (not_dvd_div_D r hr hrinj i)

/-- The inertia subgroup of `rᵢ` in `(ℤ/D)ˣ` has `rᵢ - 1` elements. -/
lemma card_inertiaSub (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ) :
    Nat.card (inertiaSub r i) = r i - 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  have hpos : 0 < D r / r i :=
    Nat.pos_of_mul_pos_right (by rw [Nat.div_mul_cancel (r_dvd_D r i)]; exact D_pos r hr)
  haveI hmz : NeZero (D r / r i) := ⟨hpos.ne'⟩
  have hcop : (r i).Coprime (D r / r i) :=
    (hr i).coprime_iff_not_dvd.mpr (not_dvd_div_D r hr hrinj i)
  have hidx : (inertiaSub r i).index = (D r / r i).totient := by
    rw [inertiaSub, Subgroup.index_ker]
    rw [show (ZMod.unitsMap (div_r_dvd_D r i)).range = ⊤ from
      MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (div_r_dvd_D r i))]
    rw [Nat.card_congr (Subgroup.topEquiv (G := (ZMod (D r / r i))ˣ)).toEquiv,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardZ : Nat.card (ZMod (D r))ˣ = (D r).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have key : (D r).totient = (r i).totient * (D r / r i).totient := by
    conv_lhs => rw [D_eq_mul_div r i]
    rw [Nat.totient_mul hcop]
  have hcard := (inertiaSub r i).card_mul_index
  rw [hidx, hcardZ, key] at hcard
  rw [(Nat.mul_right_cancel_iff (Nat.totient_pos.mpr hpos)).mp hcard, Nat.totient_prime (hr i)]

/-- Passing to the preimage under the isomorphism `galEquiv` does not change the cardinality. -/
lemma card_comap_galEquiv (r : Fin ℓ → ℕ) [NeZero (D r)] (i : Fin ℓ) :
    Nat.card ((inertiaSub r i).comap (galEquiv r).toMonoidHom) = Nat.card (inertiaSub r i) :=
  Nat.card_congr (Equiv.subtypeEquiv (galEquiv r).toEquiv fun σ => by simp [Subgroup.mem_comap])

/-- The cardinality of the inertia group of `P` is the ramification index of `rᵢ`. -/
lemma card_inertia_eq (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ)
    (P : Ideal (NumberField.RingOfIntegers (Cyc r))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(r i : ℤ)})] :
    Nat.card (Ideal.inertia Gal(Cyc r/ℚ) P) = r i - 1 := by
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  haveI hcyc : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI hgal : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(Cyc r/ℚ)) (Ideal.span {(r i : ℤ)}) P,
    ramificationIdxIn_cyc r hr hrinj i]

theorem inertia_eq_inertiaSub {ℓ : ℕ} (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hrinj : Function.Injective r) [NeZero (D r)] (i : Fin ℓ)
    (P : Ideal (NumberField.RingOfIntegers (Cyc r))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(r i : ℤ)})] :
    Ideal.inertia Gal(Cyc r/ℚ) P = (inertiaSub r i).comap (galEquiv r).toMonoidHom := by
  haveI hcyc : IsCyclotomicExtension {D r} ℚ (Cyc r) := isCyclotomicExtension_cyc r
  haveI hgal : IsGalois ℚ (Cyc r) := IsCyclotomicExtension.isGalois {D r} ℚ (Cyc r)
  haveI hgalZ : IsGalois ℚ ↥(Zfield r i) := isGalois_Zfield r i
  haveI : Fact (Nat.Prime (r i)) := ⟨hr i⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [← fixingSubgroup_Zfield r i]
    refine inertia_le_fixingSubgroup_of_ramificationIdxIn_eq_one (K := Cyc r) (Zfield r i) (r i)
      P (Ideal.under (𝓞 ↥(Zfield r i)) P) ?_
    exact ramificationIdxIn_Zfield r hr hrinj i
  · rw [card_inertia_eq r hr hrinj i P, card_comap_galEquiv r i, card_inertiaSub r hr hrinj i]

end Work.Tower.CyclotomicBase
