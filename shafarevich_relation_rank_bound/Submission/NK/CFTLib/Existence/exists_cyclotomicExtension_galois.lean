import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Existence of a cyclotomic extension with abelian Galois group of degree prime to `p`

Let `K` be a number field and `p` a prime such that `K` contains no primitive `p`-th root of
unity.  Then there is a finite Galois extension `K' / K` containing a primitive `p`-th root of
unity `ζ`, whose Galois group is commutative and whose degree over `K` is not divisible by `p`.

We take `K' = CyclotomicField p K`, the splitting field of `cyclotomic p K`, which is the
cyclotomic extension `K(ζ_p)`.  It is a number field, Galois over `K`, and its Galois group is
commutative because a `K`-automorphism sends a primitive `p`-th root of unity `ζ` to another
primitive `p`-th root of unity, i.e. to a power `ζ ^ k` with `k` a unit of `ℤ/p`; this gives an
injective monoid homomorphism `Gal(K'/K) →* (ZMod p)ˣ`.  Since `K'/K` is Galois, its degree is the
order of its Galois group, hence at most `p - 1`, which is prime to `p`.
-/

namespace NK.CFTLib.Existence

theorem exists_cyclotomicExtension_galois
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (h : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (_ : FiniteDimensional K K') (ζ : K') (_ : IsPrimitiveRoot ζ p),
      IsGalois K K' ∧ IsMulCommutative (K' ≃ₐ[K] K') ∧ ¬ p ∣ Module.finrank K K' := by
  classical
  let K' := CyclotomicField p K
  have hne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hneZ : NeZero p := ⟨hne⟩
  have hcyc : IsCyclotomicExtension {p} K K' := inferInstance
  obtain ⟨ζ, hζ⟩ := hcyc.exists_isPrimitiveRoot (Set.mem_singleton p) hne
  refine ⟨K', CyclotomicField.instField p K, inferInstance, inferInstance, ?_, ζ, hζ, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {p} K K'
  · exact IsCyclotomicExtension.isGalois {p} K K'
  · exact IsCyclotomicExtension.isMulCommutative {p} K K'
  · haveI hgal : IsGalois K K' := IsCyclotomicExtension.isGalois {p} K K'
    haveI hfin : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {p} K K'
    have hb : Nat.card (K' ≃ₐ[K] K') ≤ Nat.card (ZMod p)ˣ :=
      Nat.card_le_card_of_injective (hζ.autToPow K) (IsPrimitiveRoot.autToPow_injective K hζ)
    have hb2 : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient p,
        Nat.totient_prime (Fact.out : p.Prime)]
    have hle : Module.finrank K K' ≤ p - 1 := by
      rw [← IsGalois.card_aut_eq_finrank K K']
      exact le_of_le_of_eq hb hb2
    have hpos : 0 < Module.finrank K K' := Module.finrank_pos
    intro hdvd
    have hple : p ≤ Module.finrank K K' := Nat.le_of_dvd hpos hdvd
    omega

end NK.CFTLib.Existence
