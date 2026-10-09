import Mathlib
import Submission.NK.CFTLib.Existence.exists_cyclotomicExtension_galois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# A cyclotomic extension with **cyclic** Galois group

This is `NK.CFTLib.Existence.exists_cyclotomicExtension_galois` with the additional conclusion
that the Galois group of `K' / K` is *cyclic* — which is what the Kummer-count descent needs (it
requires a generator `σ` of `Gal(K' / K)`).

Since `K' = CyclotomicField p K` is `K(ζ_p)`, every `K`-automorphism of `K'` is determined by the
power of `ζ` it sends `ζ` to, so `Gal(K'/K) →* (ZMod p)ˣ` is injective
(`IsPrimitiveRoot.autToPow_injective`, available because `K'` is a `{p}`-cyclotomic extension of
`K`); as `(ZMod p)ˣ` is cyclic (`ZMod.isCyclic_units_prime`), so is `Gal(K'/K)`
(`isCyclic_of_injective`).
-/

namespace NK.CFTLib.Existence

theorem exists_cyclotomicExtension_galois_isCyclic
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (h : ¬ ∃ ζ : K, IsPrimitiveRoot ζ p) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (_ : FiniteDimensional K K') (ζ : K') (_ : IsPrimitiveRoot ζ p),
      IsGalois K K' ∧ IsMulCommutative (K' ≃ₐ[K] K') ∧ IsCyclic (K' ≃ₐ[K] K') ∧
        ¬ p ∣ Module.finrank K K' := by
  classical
  let K' := CyclotomicField p K
  have hne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hneZ : NeZero p := ⟨hne⟩
  haveI hcycE : IsCyclotomicExtension {p} K K' := inferInstance
  obtain ⟨ζ, hζ⟩ := hcycE.exists_isPrimitiveRoot (Set.mem_singleton p) hne
  haveI hfin : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {p} K K'
  haveI hgal : IsGalois K K' := IsCyclotomicExtension.isGalois {p} K K'
  haveI hunits : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  have hcyc : IsCyclic (K' ≃ₐ[K] K') :=
    isCyclic_of_injective (IsPrimitiveRoot.autToPow K hζ)
      (IsPrimitiveRoot.autToPow_injective K hζ)
  have hndvd : ¬ p ∣ Module.finrank K K' := by
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
  exact ⟨K', CyclotomicField.instField p K, inferInstance, inferInstance, inferInstance, ζ, hζ,
    inferInstance, inferInstance, hcyc, hndvd⟩

end NK.CFTLib.Existence
