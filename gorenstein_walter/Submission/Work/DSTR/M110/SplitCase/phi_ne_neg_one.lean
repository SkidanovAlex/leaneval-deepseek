/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `phiHom σ` never takes the value `-1`

For `F = GF(p^k)` with `p` odd and `σ : F ≃+* F` an automorphism of odd order `r`,
the map `phiHom σ : Fˣ →* Fˣ, u ↦ u / σu` avoids `-1`.

If `u / σu = -1` then `σu = -u`, whence `σⁿu = (-1)ⁿ u` for every `n`; taking
`n = r` and using `σ ^ r = 1` gives `u = -u` (as `r` is odd), so `2u = 0` and,
`u` being a unit, `2 = 0` in `F` -- impossible since `char F = p` is odd.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.CardRangeDefs

namespace Work.DSTR.M110.SplitCase

open Work.DSTR.M110.SplitAux

theorem phi_ne_neg_one (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 1 ≤ k)
    (hr : r.Prime) (hro : Odd r) [DecidableEq (GaloisField p k)]
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : orderOf σ = r)
    (u : (GaloisField p k)ˣ) :
    Work.DSTR.M110.SplitCase.phiHom (GaloisField p k) σ u ≠ -1 := by
  intro h
  -- Push the relation `u / σu = -1` down to the field.
  have hval : (u : GaloisField p k) * (σ (u : GaloisField p k))⁻¹ = -1 := by
    have h1 := congrArg (fun x : (GaloisField p k)ˣ => (x : GaloisField p k)) h
    simpa using h1
  have hsne : σ (u : GaloisField p k) ≠ 0 := by
    have hh : (unitMap (GaloisField p k) σ u : GaloisField p k) ≠ 0 := Units.ne_zero _
    simpa using hh
  -- hence `σu = -u`
  have hu : σ (u : GaloisField p k) = -(u : GaloisField p k) := by
    have h2 : (u : GaloisField p k) = -(σ (u : GaloisField p k)) := by
      have hh := congrArg (fun x : GaloisField p k => x * σ (u : GaloisField p k)) hval
      simpa using hh
    have h3 : -(u : GaloisField p k) = σ (u : GaloisField p k) := by
      have hh := congrArg (fun x : GaloisField p k => -x) h2
      simpa using hh
    exact h3.symm
  -- iteration: `σⁿu = (-1)ⁿ u`
  have hiter : ∀ n : ℕ, (σ ^ n) (u : GaloisField p k) =
      ((-1 : GaloisField p k) ^ n) * (u : GaloisField p k) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [pow_succ']
        change σ ((σ ^ m) (u : GaloisField p k)) = _
        rw [ih, map_mul, map_pow, map_neg, map_one, hu, pow_succ]
        ring
  have hpow : σ ^ r = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hkey : (u : GaloisField p k) = (-1 : GaloisField p k) ^ r * (u : GaloisField p k) := by
    have hh := hiter r
    rw [hpow] at hh
    simpa using hh
  -- `r` odd, so `u = -u`
  have hneg : (u : GaloisField p k) = -(u : GaloisField p k) := by
    rw [Odd.neg_one_pow hro, neg_one_mul] at hkey
    exact hkey
  have hsum : (u : GaloisField p k) + (u : GaloisField p k) = 0 := by
    have hh := congrArg (fun x : GaloisField p k => x + (u : GaloisField p k)) hneg
    simpa using hh
  have h2u : (2 : GaloisField p k) * (u : GaloisField p k) = 0 := by
    rw [two_mul]; exact hsum
  -- a unit forces `2 = 0`, contradicting odd characteristic
  have h2zero : (2 : GaloisField p k) = 0 := by
    rcases mul_eq_zero.mp h2u with hh | hh
    · exact hh
    · exact absurd hh (Units.ne_zero u)
  have h2ne : (2 : GaloisField p k) ≠ 0 := by
    intro hc
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp hc
    have hp2 : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd h1 (Fact.out : p.Prime).ne_one
      · exact h1
    subst hp2
    exact absurd hp (by norm_num)
  exact h2ne h2zero

end Work.DSTR.M110.SplitCase
