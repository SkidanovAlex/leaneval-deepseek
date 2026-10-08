import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `m`-th power map on a finite field is surjective when `m` is coprime to `|K| - 1`

For a finite field `K` and a natural number `m` coprime to `|K| - 1`, every nonzero
element of `K` is an `m`-th power.

The multiplicative group `Kˣ` has order `|K| - 1` and is cyclic. The `m`-th power
map `powMonoidHom m : Kˣ →* Kˣ` has kernel of order `gcd (|Kˣ|) m = 1`, hence is
injective, hence (the group being finite) surjective. Applying surjectivity to the
unit `Units.mk0 x hx` exhibits an `m`-th root of the nonzero element `x`.
-/

namespace Commons.FieldTheory.FiniteField

/-- In a finite field `K`, if `m` is coprime to `|K| - 1`, then every nonzero
element is an `m`-th power. -/
theorem exists_pow_eq_of_coprime_card_sub_one {K : Type*} [Field K] [Fintype K] {m : ℕ}
    (hm : Nat.Coprime m (Nat.card K - 1)) (x : K) (hx : x ≠ 0) : ∃ y : K, y ^ m = x := by
  -- `|Kˣ| = |K| - 1`, so `m` is coprime to the order of the unit group.
  have hcop : Nat.Coprime m (Nat.card Kˣ) := by
    rw [Nat.card_units]; exact hm
  -- The `m`-th power map on `Kˣ` has trivial kernel.
  have hker : Nat.card (powMonoidHom m : Kˣ →* Kˣ).ker = 1 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.Coprime.gcd_eq_one hcop.symm
  have hinj : Function.Injective (powMonoidHom m : Kˣ →* Kˣ) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ hker
  -- Injectivity of an endomorphism of a finite group implies surjectivity.
  have hsurj : Function.Surjective (powMonoidHom m : Kˣ →* Kˣ) :=
    Finite.surjective_of_injective hinj
  obtain ⟨u, hu⟩ := hsurj (Units.mk0 x hx)
  refine ⟨(u : K), ?_⟩
  have hval : (((powMonoidHom m) u : Kˣ) : K) = x := by
    rw [hu, Units.val_mk0]
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val] at hval
  exact hval

end Commons.FieldTheory.FiniteField