import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For a prime `p ≡ 1 (mod 4)`, the equation `α ^ 2 = -1` has exactly two
solutions in `ZMod p`.

Indeed `-1` is a square modulo such a prime (`ZMod.exists_sq_eq_neg_one_iff`).
If `x` is a square root of `-1`, then the other root is `-x ≠ x` (because `p`
is odd), and any root `y` satisfies `(y - x) * (y + x) = y ^ 2 - x ^ 2 = 0`,
so in the field `ZMod p` we get `y = x` or `y = -x`. -/
theorem sq_roots_neg_one_mod_prime_eq_two {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ({α : ZMod p | α ^ 2 = -1}.ncard) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_ne2 : p ≠ 2 := by
    intro hp2
    rw [hp2] at hp4
    norm_num at hp4
  -- `-1` is a square modulo `p`
  have hp4ne3 : p % 4 ≠ 3 := by omega
  rcases (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp4ne3 with ⟨x, hx⟩
  have hx2 : x ^ 2 = -1 := by
    rw [pow_two]
    exact hx.symm
  -- the roots are exactly `x` and `-x`
  have hroots :
      ({α : ZMod p | α ^ 2 = -1} : Set (ZMod p)) = ({x, -x} : Set (ZMod p)) := by
    ext y
    constructor
    · intro hy
      have hy' : y ^ 2 = -1 := by simpa using hy
      have hy2 : y ^ 2 = x ^ 2 := by rw [hy', hx2]
      have hprod : (y - x) * (y + x) = 0 := by
        calc
          (y - x) * (y + x) = y ^ 2 - x ^ 2 := by ring
          _ = 0 := by rw [hy2]; ring
      rcases mul_eq_zero.mp hprod with hsub | hadd
      · simp [sub_eq_zero.mp hsub]
      · simp [eq_neg_of_add_eq_zero_left hadd]
    · intro hy
      rcases hy with hxy | hxny
      · rw [hxy]
        simpa using hx2
      · rw [hxny]
        simpa [neg_sq] using hx2
  -- and the two roots are distinct because `p` is odd
  have hx0 : x ≠ 0 := by
    intro h0
    have hz : (-1 : ZMod p) = 0 := by
      rw [← hx2, h0]
      simp
    have hneg0 : (-1 : ZMod p) ≠ 0 := by
      intro hn
      have h1 : (1 : ZMod p) = 0 := neg_eq_zero.mp hn
      exact one_ne_zero h1
    exact hneg0 hz
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h1p | h2p
    · have hp2 : 2 ≤ p := Nat.Prime.two_le hp
      omega
    · rw [h2p] at hp4
      norm_num at hp4
  have hne : x ≠ -x := by
    intro h
    have hmul2 : (2 : ZMod p) * x = 0 := by
      calc
        (2 : ZMod p) * x = x + x := by ring
        _ = x + -x := congrArg (fun t : ZMod p => x + t) h
        _ = 0 := by ring
    exact h2ne ((mul_eq_zero.mp hmul2).resolve_right hx0)
  rw [hroots]
  exact Set.ncard_pair hne

end Commons.NumberTheory.FriedlanderIwaniec