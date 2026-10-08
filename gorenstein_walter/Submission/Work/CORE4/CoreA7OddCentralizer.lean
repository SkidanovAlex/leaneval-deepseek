import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CardThreeConj

namespace Work.CORE4

open Subgroup

/-- A finite group whose order divides `3` is cyclic: its order is `1` or `3`, and a group of
prime order is cyclic. -/
theorem CardDvdThreeIsCyclic {A : Type} [Group A] [Finite A] (h : Nat.card A ∣ 3) :
    IsCyclic A := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h1 | h3
  · have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    exact @isCyclic_of_subsingleton A _ hsub
  · have hprime : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card (p := 3) h3

/-- **The odd part of the centralizer of an involution of `A₇` is cyclic and is inverted by its
normalizer.**

Let `G ≅ A₇`, let `τ ∈ G` be an involution and let `A ≤ C_G(τ)` have odd order.  Then `A` has
order dividing `3`: `φ(A)` lies in the centralizer of the involution `φ τ` of `A₇`, which has
order `24` (`A7ModelProp`), so `|A| = |φ(A)|` divides `24` and, being odd, divides `3`.

A group of order dividing `3` is cyclic, and every automorphism of such a group is the identity or
the inversion, which gives the second half of the claim. -/
theorem CoreA7OddCentralizer
    (ha7 : Work.GW2.A7ModelProp)
    (G : Type) [Group G] [Finite G]
    (φ : G ≃* alternatingGroup (Fin 7))
    (τ : G) (hτ : orderOf τ = 2)
    (A : Subgroup G) (hA : A ≤ Subgroup.centralizer ({τ} : Set G))
    (hodd : Odd (Nat.card A)) :
    IsCyclic A ∧ ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ a ∈ A,
      g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  -- `φ τ` is again an involution, and `φ(A) ≤ C_{A₇}(φ τ)`.
  have hord' : orderOf (φ τ) = 2 :=
    (orderOf_injective (φ : G →* alternatingGroup (Fin 7)) φ.injective τ).trans hτ
  let B : Subgroup (alternatingGroup (Fin 7)) := A.map φ.toMonoidHom
  have hcardB : Nat.card B = Nat.card A := Subgroup.card_map_of_injective φ.injective
  have hleB : B ≤ Subgroup.centralizer ({φ τ} : Set (alternatingGroup (Fin 7))) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨a, ha, rfl⟩ := hb
    have hcomm : a * τ = τ * a := by
      have h := hA ha
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    show φ a * φ τ = φ τ * φ a
    rw [← map_mul, ← map_mul, hcomm]
  -- `|A|` is an odd divisor of `|C_{A₇}(φ τ)| = 24`, hence of `3`.
  have hdvd3 : Nat.card A ∣ 3 := by
    have hdvd24 : Nat.card B ∣ 24 := by
      have h1 := Subgroup.card_dvd_of_le hleB
      rwa [ha7.2.2.1 (φ τ) hord'] at h1
    have hdvd3B : Nat.card B ∣ 3 := by
      have hcop : Nat.Coprime (Nat.card B) 8 :=
        (Nat.coprime_two_right.mpr (hcardB ▸ hodd)).pow_right 3
      have h8 : Nat.card B ∣ 8 * 3 := by norm_num; exact hdvd24
      exact hcop.dvd_of_dvd_mul_left h8
    rwa [hcardB] at hdvd3B
  exact ⟨CardDvdThreeIsCyclic hdvd3, fun g hg a ha => CardThreeConj A hdvd3 g hg a ha⟩

end Work.CORE4
