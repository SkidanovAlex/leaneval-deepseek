import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6HeckeV2

open scoped BigOperators
open Work.FIArea5.S16Hecke

theorem tsum_log_norm_heckeFp {chi : GaussianInt → ℂ} {k : ℤ} {s : ℂ} (hs : 1 < s.re)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    (∑' p : Nat.Primes, Real.log ‖Work.FIArea5.S16Hecke.heckeFp chi k p s‖)
      = Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi k s‖ := by
  classical
  have hs0 : 0 < s.re := by linarith
  -- The local factor and its reciprocal multiply to one, so the local factor never vanishes.
  have hFG : ∀ p : Nat.Primes, heckeFp chi k p s * heckeGp chi k p s = 1 :=
    fun p => heckeFp_mul_heckeGp chi k p s hmul h1 hb hs0
  have hFne : ∀ p : Nat.Primes, heckeFp chi k p s ≠ 0 := fun p hp => by
    have h := hFG p
    rw [hp, zero_mul] at h
    exact zero_ne_one h
  -- The reciprocal local factors are `1 + O(p ^ (-σ))`, so their logs are summable.
  have hbnd : Summable (fun p : Nat.Primes => ‖heckeGp chi k p s - 1‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_heckeGp_sub_one_le chi k p s hmul hb hs0)
      (((Nat.Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left 9)
  have hGsum : Summable (fun p : Nat.Primes => Real.log ‖heckeGp chi k p s‖) := by
    have := Summable.summable_log_norm_one_add
      (f := fun p : Nat.Primes => heckeGp chi k p s - 1) hbnd
    refine this.congr (fun p => ?_)
    simp
  -- `‖F_p‖ = ‖G_p‖⁻¹`, hence `log ‖F_p‖ = - log ‖G_p‖`, so the logs of the local factors
  -- are summable too.
  have hlogF : ∀ p : Nat.Primes,
      Real.log ‖heckeFp chi k p s‖ = -Real.log ‖heckeGp chi k p s‖ := by
    intro p
    have hnorm : ‖heckeFp chi k p s‖ * ‖heckeGp chi k p s‖ = 1 := by
      rw [← norm_mul, hFG p, norm_one]
    have hFi : ‖heckeFp chi k p s‖ = (‖heckeGp chi k p s‖)⁻¹ :=
      eq_inv_of_mul_eq_one_left hnorm
    rw [hFi, Real.log_inv]
  have hFsum : Summable (fun p : Nat.Primes => Real.log ‖heckeFp chi k p s‖) := by
    refine hGsum.neg.congr (fun p => ?_)
    exact (hlogF p).symm
  -- The Euler product of the Hecke `L`-series.
  have hpL : HasProd (fun p : Nat.Primes => heckeFp chi k p s) (heckeLSeries chi k s) :=
    heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs
  have hnormprod : ∏' p : Nat.Primes, ‖heckeFp chi k p s‖ = ‖heckeLSeries chi k s‖ := by
    rw [← Multipliable.norm_tprod hpL.multipliable, hpL.tprod_eq]
  -- Exponentiate the sum of logs to recover the modulus of the `L`-series.
  have hrexp : Real.exp (∑' p : Nat.Primes, Real.log ‖heckeFp chi k p s‖)
      = ∏' p : Nat.Primes, ‖heckeFp chi k p s‖ :=
    Real.rexp_tsum_eq_tprod (fun p => norm_pos_iff.mpr (hFne p)) hFsum
  have hmain : Real.exp (∑' p : Nat.Primes, Real.log ‖heckeFp chi k p s‖)
      = ‖heckeLSeries chi k s‖ := by rw [hrexp, hnormprod]
  have hlog := congrArg Real.log hmain
  rw [Real.log_exp] at hlog
  exact hlog

end Work.FIArea6HeckeV2
