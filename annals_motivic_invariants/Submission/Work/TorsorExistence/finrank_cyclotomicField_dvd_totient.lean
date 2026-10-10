import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

open Polynomial

/-- The degree over `K` of the `m`-th cyclotomic field `K(ζ_m)` divides `Nat.totient m`:
the Galois group of `K(ζ_m)/K` embeds into `(ZMod m)ˣ` via the cyclotomic character
(`IsPrimitiveRoot.autToPow`), and `|(ZMod m)ˣ| = φ(m)`.  Over a field of characteristic zero
the cyclotomic extension is Galois of degree `|Gal(K(ζ_m)/K)|`. -/
theorem finrank_cyclotomicField_dvd_totient {K : Type*} [Field K] [CharZero K] (m : ℕ) [NeZero m] :
    Module.finrank K (CyclotomicField m K) ∣ Nat.totient m := by
  haveI : NeZero (m : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  haveI : IsCyclotomicExtension {m} K (CyclotomicField m K) :=
    CyclotomicField.isCyclotomicExtension m K
  haveI : FiniteDimensional K (CyclotomicField m K) :=
    IsCyclotomicExtension.finiteDimensional {m} K (CyclotomicField m K)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K (CyclotomicField m K)
      (Set.mem_singleton m) (NeZero.ne m)
  haveI : IsGalois K (CyclotomicField m K) := IsCyclotomicExtension.isGalois {m} K _
  -- the cyclotomic character `Gal(K(ζ_m)/K) →* (ZMod m)ˣ` is injective
  have hfin : Function.Injective (hζ.autToPow K) := hζ.autToPow_injective K
  have h1 : Nat.card (CyclotomicField m K ≃ₐ[K] CyclotomicField m K) ∣ Nat.card (ZMod m)ˣ :=
    Subgroup.card_dvd_of_injective (hζ.autToPow K) hfin
  have h2 : Nat.card (ZMod m)ˣ = Nat.totient m := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h3 : Nat.card (CyclotomicField m K ≃ₐ[K] CyclotomicField m K) =
      Module.finrank K (CyclotomicField m K) :=
    IsGalois.card_aut_eq_finrank K (CyclotomicField m K)
  rw [← h3, ← h2]
  exact h1

end Work.TorsorExistence
