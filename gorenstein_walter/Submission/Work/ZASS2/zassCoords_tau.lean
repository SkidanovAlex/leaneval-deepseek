import Mathlib
import Submission.Work.ZASS.Leaf9

namespace Work.ZASS2

/-!
# Area ZASS2: the additive structure of the translation coordinate `τ`

Given field coordinates `C : ZassCoords G X inf zero U` (`Θ : X ≃ Option C.E`, `U` acting by
translations `y ↦ y + τ u`), the translation map `τ : U → C.E` is an additive bijection and
`C.E` has odd (or zero) characteristic as soon as `U` has odd exponent `p`:

* `C.τ 1 = 0` and `C.τ (u₁ * u₂) = C.τ u₁ + C.τ u₂` -- evaluate the equivariance formula
  `Θ ((u : G) • x) = (Θ x).map (· + τ u)` at `x = zero` (where `Θ zero = some 0`) and compare
  the two ways of computing `Θ ((u₁ * u₂) • zero)`;
* `(2 : C.E) ≠ 0` -- `τ` is surjective, so some `u` has `τ u = 1`; then `u ^ p = 1` gives
  `(p : C.E) * 1 = τ (u ^ p) = τ 1 = 0`, i.e. `(p : C.E) = 0`.  Writing `p = 2 * m + 1` for an
  odd `p`, having `(2 : C.E) = 0` would then force `1 = (2 : C.E) * m + 1 = 0`.
-/

open Work.GW2

theorem zassCoords_tau {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : Work.GW2.ZassCoords G X inf zero U) {p : ℕ} (hp : Odd p) (hexp : ∀ u ∈ U, u ^ p = 1) :
    C.τ 1 = 0 ∧ (∀ u₁ u₂ : U, C.τ (u₁ * u₂) = C.τ u₁ + C.τ u₂) ∧ (2 : C.E) ≠ 0 := by
  classical
  -- The translation formula, evaluated at `zero` (where `Θ zero = some 0`).
  have htrans : ∀ u : U, C.Θ ((u : G) • zero) = some (C.τ u) := by
    intro u
    rw [C.trans u zero, C.Θ_zero]
    simp
  -- `τ` is additive.
  have hadd : ∀ u₁ u₂ : U, C.τ (u₁ * u₂) = C.τ u₁ + C.τ u₂ := by
    intro u₁ u₂
    have hcoe : (((u₁ * u₂ : U)) : G) • zero = (u₁ : G) • ((u₂ : G) • zero) := by
      rw [Subgroup.coe_mul, mul_smul]
    have a : C.Θ (((u₁ * u₂ : U) : G) • zero) = some (C.τ (u₁ * u₂)) := htrans (u₁ * u₂)
    have b : C.Θ (((u₁ * u₂ : U) : G) • zero) = some (C.τ u₂ + C.τ u₁) := by
      rw [hcoe, C.trans u₁ ((u₂ : G) • zero), htrans u₂]
      simp
    rw [add_comm (C.τ u₁)]
    exact Option.some.inj (a.symm.trans b)
  -- `τ 1 = 0`.
  have ht1 : C.τ 1 = 0 := by
    have h := htrans 1
    rw [Subgroup.coe_one, one_smul, C.Θ_zero] at h
    exact Option.some.inj h.symm
  -- `τ` sends powers to multiples.
  have hpow : ∀ (u : U) (n : ℕ), C.τ (u ^ n) = (n : C.E) * C.τ u := by
    intro u n
    induction n with
    | zero => rw [pow_zero, ht1, Nat.cast_zero, zero_mul]
    | succ n ih =>
        rw [pow_succ, hadd, ih, Nat.cast_succ, add_mul, one_mul]
  -- Surjectivity of `τ` gives `(p : C.E) = 0`.
  have hpE : (p : C.E) = 0 := by
    obtain ⟨u, hu⟩ := C.τ_bij.surjective 1
    have hup : u ^ p = 1 := by
      have h2 : ((u ^ p : U) : G) = ((1 : U) : G) := by
        push_cast
        exact hexp (u : G) u.2
      exact Subtype.coe_injective h2
    have h := hpow u p
    rw [hup, ht1, hu, mul_one] at h
    exact h.symm
  refine ⟨ht1, hadd, ?_⟩
  -- `p` odd and `(p : C.E) = 0` force `(2 : C.E) ≠ 0`.
  obtain ⟨m, hm⟩ := hp
  intro h2
  have hp1 : (p : C.E) = (2 : C.E) * (m : C.E) + 1 := by
    rw [hm]
    push_cast
    ring
  rw [hp1, h2, zero_mul, zero_add] at hpE
  exact one_ne_zero hpE

end Work.ZASS2
