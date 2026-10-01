import Mathlib
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.DhExplicit.iteratedDerivDigammaHalf
import Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole

open Complex Filter
open scoped Topology

namespace Work.LinnikAreas.TuranOther

/-!
# The derivatives of `logDeriv Gammaℝ` as a Hurwitz-zeta type series

For `k ≥ 1` and `Re t > 0` we prove

`(logDeriv Γ_ℝ)^{(k)}(t) = (-1)^{k+1} k! ∑_{n ≥ 0} (t + 2n)^{-(k+1)}`.

Since `Γ_ℝ(z) = π^{-z/2} Γ(z/2)`, we have `logDeriv Γ_ℝ z = -(log π)/2 + ψ(z/2)/2` on the right
half-plane (`logDeriv_GammaR_off_pole`); the halving chain rule
`iteratedDerivDigammaHalf` and the Hurwitz-zeta series `digammaDerivSeries` for `ψ^{(k)}` then
give the claim after the termwise reindexing `(t/2 + n) = (t + 2n)/2`.
-/

private lemma isOpen_re_pos' : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma div_two_re' (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]; simp [Complex.normSq]; ring

private theorem gammaRDerivSeries_aux (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 0 < t.re) :
    iteratedDeriv k (fun z : ℂ => logDeriv Complex.Gammaℝ z) t =
      (-1) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, (1 / (t + (2 * (n : ℂ)))) ^ (k + 1) := by
  have hk0 : 0 < k := hk
  have hw2 : 0 < (t / 2).re := by rw [div_two_re']; linarith
  -- on the right half-plane, `logDeriv Γ_ℝ` is the constant `-(log π)/2` plus `ψ(z/2)/2`
  have hev : (fun z : ℂ => logDeriv Complex.Gammaℝ z) =ᶠ[𝓝 t]
      fun z : ℂ => (-(Complex.log (Real.pi : ℂ)) / 2) + (1 / 2) * Complex.digamma (z / 2) := by
    filter_upwards [isOpen_re_pos'.mem_nhds ht] with z hz
    have hz2 : ∀ m : ℕ, z / 2 ≠ -((m : ℕ) : ℂ) := by
      intro m h
      have hre : (z / 2).re = -((m : ℝ)) := by rw [h]; simp
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hzre : 0 < (z / 2).re := by rw [div_two_re']; linarith
      linarith only [hre, hm, hzre]
    rw [Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole z hz2]
    ring
  rw [hev.iteratedDeriv_eq k]
  rw [iteratedDeriv_const_add hk0]
  rw [iteratedDeriv_const_mul_field]
  rw [Work.LinnikAreas.DhExplicit.iteratedDerivDigammaHalf k ht]
  -- the Hurwitz-zeta series for `ψ^{(k)}` at `t/2`
  have hHas := Work.LinnikAreas.FarRepel.digammaDerivSeries k hk hw2
  have hterm : ∀ n : ℕ, (1 / (t / 2 + (n : ℂ))) ^ (k + 1)
      = (2 : ℂ) ^ (k + 1) * (1 / (t + (2 * (n : ℂ)))) ^ (k + 1) := by
    intro n
    have hden : t / 2 + (n : ℂ) = (t + 2 * (n : ℂ)) / 2 := by ring
    rw [hden, div_div_eq_mul_div, one_mul,
      show (2 : ℂ) / (t + 2 * (n : ℂ)) = 2 * (1 / (t + 2 * (n : ℂ))) by ring, mul_pow]
  have hHas' : HasSum (fun n : ℕ =>
      ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (1 / (t + (2 * (n : ℂ)))) ^ (k + 1))
      (iteratedDeriv k Complex.digamma (t / 2)) :=
    hHas.congr_fun fun n => by rw [hterm n]; ring
  have hval : iteratedDeriv k Complex.digamma (t / 2)
      = ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ) * (2 : ℂ) ^ (k + 1))
        * (∑' n : ℕ, (1 / (t + (2 * (n : ℂ)))) ^ (k + 1)) := by
    rw [← hHas'.tsum_eq, tsum_mul_left]
  rw [hval]
  have hpow : (1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hkey : (1 / 2 : ℂ) * ((1 / 2) ^ k * (((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (2 : ℂ) ^ (k + 1)) * (∑' n : ℕ, (1 / (t + (2 * (n : ℂ)))) ^ (k + 1))))
      = ((1 / 2 : ℂ) ^ (k + 1) * (2 : ℂ) ^ (k + 1))
          * ((-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
              * (∑' n : ℕ, (1 / (t + (2 * (n : ℂ)))) ^ (k + 1))) := by
    rw [pow_succ]; ring
  rw [hkey, hpow, one_mul]

theorem gammaRDerivSeries (k : ℕ) (hk : 1 ≤ k) {t : ℂ} (ht : 0 < t.re) :
    iteratedDeriv k (fun z : ℂ => logDeriv Complex.Gammaℝ z) t =
      (-1) ^ (k + 1) * (k.factorial : ℂ) * ∑' n : ℕ, (1 / (t + (2 * (n : ℂ)))) ^ (k + 1) :=
  gammaRDerivSeries_aux k hk ht

end Work.LinnikAreas.TuranOther
