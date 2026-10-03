/-
# `Submission.Work.FIArea6Hecke.R.heckeLam_chiTriv_localFactor_coprime`

The **coprime local Euler factor** of the Hecke `L`-function of the principal strict character
`chiTriv d` (the indicator of the units of `ℤ[i]/(4d)`, *FI* (16.16) with `χ` principal).

For a rational prime `p` with `p ∤ 4d` the local factor at `p` of `Σ_n λ(n)n^{-s}` is the product
of the two Tate local factors of `ζ(s)` and of `L(s,χ₄)`, `χ₄` being the quadratic character
modulo `4`,

  `Σ_{e ≥ 0} λ(p^e)·p^{-es} = (1 - p^{-s})^{-1}·(1 - χ₄(p)·p^{-s})^{-1}`.

The arithmetic input is that the `p`-power Hecke eigenvalues of the principal character are
`λ(p) = 1 + χ₄(p)` (respectively `2` at a split prime and `0` at an inert one) and
`λ(p²) = 2 + χ₄(p)` (respectively `3` and `1`), which is `Work.FIArea6Hecke.R.chiTrivLocalPrime`.
The local recursion `heckeLam_localInverse` then converts these two values into the closed form of
the full local generating series, and the remaining step is the elementary identity
`1 - (1+χ)X + χX² = (1-X)(1-χX)` together with `inv_eq_of_mul_eq_one_left`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea6Hecke.R.chiTrivLocalPrime
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.zfrAux

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

theorem heckeLam_chiTriv_localFactor_coprime {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ 4 * d) :
    ∀ s : ℂ, 1 < s.re →
      (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ e)
          * (((p : ℂ) ^ (-s)) ^ e))
        = ((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s)))⁻¹ := by
  -- `chiTriv d` is `principalChar d`: the multiplicative indicator of the units mod `4d`
  have hmul : ∀ z w : GaussianInt,
      Work.FIArea6Hecke.R.chiTriv d (z * w)
        = Work.FIArea6Hecke.R.chiTriv d z * Work.FIArea6Hecke.R.chiTriv d w :=
    fun z w => Work.FIArea5.S16Hecke.principalChar_mul d z w
  have h1 : Work.FIArea6Hecke.R.chiTriv d 1 = 1 :=
    Work.FIArea5.S16Hecke.principalChar_one d
  have hb : ∀ z : GaussianInt, ‖Work.FIArea6Hecke.R.chiTriv d z‖ ≤ 1 :=
    fun z => Work.FIArea5.S16Hecke.norm_principalChar_le_one d z
  -- the two local eigenvalues `λ(p)`, `λ(p²)`
  obtain ⟨hA, hB⟩ := Work.FIArea6Hecke.R.chiTrivLocalPrime hd hp hpd
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    exact hpd ⟨2 * d, by ring⟩
  -- `χ₄(p) = ±1` because `p` is odd
  have hχ : Work.FIArea6Hecke.R.chi4fun p = 1 ∨ Work.FIArea6Hecke.R.chi4fun p = -1 := by
    rcases hp.eq_two_or_odd' with h | hodd
    · exact absurd h hp2
    · obtain ⟨m, hm⟩ := hodd
      rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1' | h3
      · left
        rw [Work.FIArea6Hecke.R.chi4fun_prime hp, if_neg hp2, if_pos h1']
      · right
        rw [Work.FIArea6Hecke.R.chi4fun_prime hp, if_neg hp2, if_neg (by omega : ¬ p % 4 = 1)]
  intro s hs
  -- the local parameter `X = p^{-s}` has modulus `< 1` for `re s > 1`
  have hX : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    rw [← Complex.ofReal_natCast p, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re,
      Real.rpow_lt_one_iff_of_pos hpos]
    left
    exact ⟨by exact_mod_cast hp.one_lt, by linarith⟩
  -- the local recursion in closed form
  have hInv := Work.FIArea5.S16Hecke.heckeLam_localInverse (chi := Work.FIArea6Hecke.R.chiTriv d)
    (k := 0) hp hmul h1 hb hX
  -- the quadratic factor `1 - λ(p)X + (λ(p)² - λ(p²))X²` is `(1 - X)(1 - χ₄(p)X)`
  have hpoly :
      1 - Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 p * ((p : ℂ) ^ (-s))
        + ((Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 p) ^ 2
            - Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ 2))
              * ((p : ℂ) ^ (-s)) ^ 2
      = (1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s)) := by
    rcases hχ with h | h <;> rw [hA, hB, h] <;> ring
  rw [hpoly] at hInv
  exact (inv_eq_of_mul_eq_one_left hInv).symm

end Work.FIArea6Hecke.R
