import Mathlib
import Submission.Work.ZassenhausSuzuki.Tits

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Tits endomorphism of `GF(2^(2n+1))` is a Tits endomorphism

`Work.ZassenhausSuzuki.titsTheta n` is the `(n+1)`-fold Frobenius `x ↦ x ^ 2 ^ (n+1)` of
`GF(2 ^ (2n+1))`.  To be a **Tits endomorphism** (`IsTitsTheta`) it has to satisfy two
things (BG Definition 5.5):

* `θ (θ x) = x ^ 2` for all `x` — this is `titsTheta_sq_apply`, proved in `Tits`;
* `θ ≠ 1`, which is what `titsTheta_ne_one` below supplies, and which is where the
  hypothesis `1 ≤ n` enters: on a field every element with `x ^ 2 = x` is `0` or `1`, while
  `GF(2 ^ (2n+1))` has at least `8` elements.

The auxiliary `card_le_two_of_sq_eq_self` records the second point in the form in which it
is used: a finite field all of whose elements satisfy `x ^ 2 = x` has at most two elements.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki

/-- A finite field in which every element satisfies `x ^ 2 = x` has at most two elements:
`x ^ 2 = x` says `x * (x - 1) = 0`, so `x = 0` or `x = 1` in a domain, and hence the whole
field injects into `Fin 2` by `x ↦ 0` if `x = 0` and `x ↦ 1` otherwise. -/
theorem card_le_two_of_sq_eq_self {K : Type*} [Field K] [Fintype K]
    (h : ∀ x : K, x ^ 2 = x) : Fintype.card K ≤ 2 := by
  classical
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    have hmul : x * (x - 1) = 0 := by
      have h1 : x ^ 2 - x = 0 := by rw [h x]; ring
      calc x * (x - 1) = x ^ 2 - x := by ring
        _ = 0 := h1
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  have hinj : Function.Injective (fun x : K => if x = 0 then (0 : Fin 2) else 1) := by
    intro x y hxy
    rcases h01 x with hx | hx <;> rcases h01 y with hy | hy <;> simp_all
  have hle := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_fin] at hle

/-- `titsTheta n` is not the identity for `n ≥ 1`.  Otherwise `x ^ 2 = θ (θ x) = x` for all
`x`, so every element of `GF(2 ^ (2n+1))` would be `0` or `1`, contradicting the cardinality
`2 ^ (2n+1) ≥ 8`. -/
theorem titsTheta_ne_one (n : ℕ) (hn : 1 ≤ n) : titsTheta n ≠ 1 := by
  haveI : Fintype (GaloisField 2 (2 * n + 1)) := Fintype.ofFinite _
  intro hθ
  have hx : ∀ x : GaloisField 2 (2 * n + 1), titsTheta n x = x := by
    intro x
    rw [hθ]
    rfl
  have hsq : ∀ x : GaloisField 2 (2 * n + 1), x ^ 2 = x := by
    intro x
    rw [← titsTheta_sq_apply n x, hx (titsTheta n x), hx x]
  have hcard : Fintype.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * n + 1) (by omega)
  have h8 : 8 ≤ 2 ^ (2 * n + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := card_le_two_of_sq_eq_self hsq
  omega

theorem isTitsTheta_titsTheta (n : ℕ) (hn : 1 ≤ n) :
    Work.ZassenhausSuzuki.IsTitsTheta (Work.ZassenhausSuzuki.titsTheta n) :=
  ⟨titsTheta_ne_one n hn, fun x => titsTheta_sq_apply n x⟩

end Work.ZassenhausSuzuki
