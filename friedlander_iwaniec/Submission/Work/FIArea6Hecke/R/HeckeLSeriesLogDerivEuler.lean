/-
# `Submission.Work.FIArea6Hecke.R.HeckeLSeriesLogDerivEuler`

**The logarithmic derivative of the Hecke `L`-series as a sum over primes.**  For a (completely
multiplicative) bounded character `χ` on `ℤ[i]` with `χ 1 = 1` and `1 < re s`,

  `(log L(·,ψ))'(s) = Σ_p (log F_p)'(s)`,   `F_p = heckeFp χ k p` the local Euler factor,

i.e. `logDeriv (heckeLSeries χ k) s = Σ'_p logDeriv (heckeFp χ k p) s`.

This is the identity that converts the global logarithmic derivative into a sum of *local* pieces,
so that the `(3,4,1)` inequality can be checked prime by prime.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

theorem HeckeLSeriesLogDerivEuler (chi : GaussianInt → ℂ) (k : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi k) s
      = ∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi k p) s := by
  obtain ⟨C₂, -, hC₂⟩ := heckeFp_logDeriv_bound
  have hdiff : ∀ p : Nat.Primes, DifferentiableOn ℂ (Work.FIArea5.S16Hecke.heckeFp chi k p)
      {z : ℂ | 1 < z.re} :=
    fun p => differentiableOn_heckeFp (chi := chi) (k := k) (p := p) hb
  have hne : ∀ p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi k p s ≠ 0 :=
    fun p => heckeFp_ne_zero h1 hmul hb (by linarith)
  have hsummC : Summable (fun p : Nat.Primes =>
      C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))) := by
    have h := (summable_primes_log_mul_rpow hs).mul_left C₂
    refine h.congr (fun p => ?_)
    ring
  have hsumm : Summable (fun p : Nat.Primes =>
      logDeriv (Work.FIArea5.S16Hecke.heckeFp chi k p) s) :=
    Summable.of_norm_bounded hsummC (fun p => hC₂ chi k p s h1 hmul hb hs)
  have hnez : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi k p s) ≠ 0 := by
    have hL : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi k p s)
        = Work.FIArea5.S16Hecke.heckeLSeries chi k s :=
      (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs).tprod_eq
    rw [hL]
    exact Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi k h1 hmul hb hs
  have hkey := logDeriv_tprod_eq_tsum (s := {z : ℂ | 1 < z.re})
    (f := fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeFp chi k p)
    (isOpen_lt continuous_const Complex.continuous_re) hs hne hdiff hsumm
    (heckeFp_multipliableLocallyUniformlyOn chi k h1 hmul hb) hnez
  have hprod_eq : (fun z : ℂ => ∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi k p z)
      =ᶠ[𝓝 s] Work.FIArea5.S16Hecke.heckeLSeries chi k := by
    refine Filter.eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) (fun z hz => ?_)
    exact (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hz).tprod_eq
  rw [← (logDeriv_congr_nhds hprod_eq).eq_of_nhds, hkey]

end

end Work.FIArea6Hecke.R
