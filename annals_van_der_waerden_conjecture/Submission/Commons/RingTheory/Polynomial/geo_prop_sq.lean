import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.ModEq

open Polynomial

namespace Commons.RingTheory.Polynomial

/-- Geometric-sieve proposition (Bhargava, Annals of Math 2025, Prop. in §7 / Case III of Theorem 1):
if an integer polynomial `g` vanishes on the whole residue class `c mod p` to order at least `p²`
(`g (c + p·d) ≡ 0 mod p²` for every integer `d`), then its derivative at `c` is divisible by `p`.
Proof route: Taylor shift `taylor c g`; its higher coefficients vanish mod `p²` upon evaluation at
multiples of `p`; subtract the `d = 0` case. -/
theorem geo_prop_sq {p : ℕ} (hp : Nat.Prime p) (g : Polynomial ℤ) (c : ℤ)
    (hstab : ∀ d : ℤ, Int.ModEq ((p : ℤ) ^ 2) (g.eval (c + (p : ℤ) * d)) 0) :
    Int.ModEq (p : ℤ) (g.derivative.eval c) 0 := by
  -- The prime `p` is a nonzero integer.
  have hpz_ne : ((p : ℤ) ≠ 0) := by
    exact_mod_cast (Nat.Prime.ne_zero hp)
  -- Instantiate the stability hypothesis at `d = 0` and `d = 1`:
  -- both `g.eval c` and `g.eval (c + p)` are divisible by `p²`.
  have h0 : Int.ModEq ((p : ℤ) ^ 2) (g.eval c) 0 := by
    simpa using hstab 0
  have h1 : Int.ModEq ((p : ℤ) ^ 2) (g.eval (c + (p : ℤ))) 0 := by
    simpa using hstab 1
  have d0 : (p : ℤ) ^ 2 ∣ g.eval c := (Int.modEq_zero_iff_dvd).1 h0
  have d1 : (p : ℤ) ^ 2 ∣ g.eval (c + (p : ℤ)) := (Int.modEq_zero_iff_dvd).1 h1
  -- Second-order Taylor expansion of `g` at `c` with increment `p` (valid in any
  -- commutative ring):  g (c + p) = g c + p · g' c + c₂ · p².
  rcases exists_mul_sq_add_linear_part_eq_eval_add (R := ℤ) g c (p : ℤ) with ⟨c₂, hT⟩
  -- Rearrange:  p · g' c = (g (c + p) − g c) − c₂ · p².
  have hT' : g.eval (c + (p : ℤ)) - g.eval c - c₂ * (p : ℤ) ^ 2 = (p : ℤ) * g.derivative.eval c := by
    rw [← hT]
    ring
  -- The right hand side is a difference of terms each divisible by `p²`,
  -- hence `p² ∣ p · g' c`.
  have hmain : ((p : ℤ) ^ 2) ∣ (p : ℤ) * g.derivative.eval c := by
    rw [← hT']
    exact dvd_sub (dvd_sub d1 d0) (dvd_mul_left ((p : ℤ) ^ 2) c₂)
  rcases hmain with ⟨k, hk⟩
  -- Cancel the nonzero factor `p`: `g' c = p · k`, i.e. `p ∣ g' c`.
  have hdiv : (p : ℤ) ∣ g.derivative.eval c := by
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ hpz_ne
    calc
      (p : ℤ) * g.derivative.eval c = (p : ℤ) ^ 2 * k := hk
      _ = (p : ℤ) * ((p : ℤ) * k) := by ring
  exact (Int.modEq_zero_iff_dvd).2 hdiv

end Commons.RingTheory.Polynomial