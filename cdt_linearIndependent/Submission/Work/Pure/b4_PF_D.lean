/-
# `Li₂(x) − Li₂(φ) = D`, the descent numerator of the pure function `B₄`

`Work.Pure.b4Ds` is the truncated form (`Submission.Work.Pure.b4_PF_aux`) of the
series `D = Σ_{k≥1} k⁻²·(x^k − φ^k)`, `φ = x/(x−1) = Submission.CDT.sympPhi`.
Here we prove that it is exactly `Li₂(x) − Li₂(φ)`:

  `b4Li2 − b4Li2.subst sympPhi = b4Ds`.

Coefficientwise, for `n : ℕ`,

`coeff n (Li₂ − Li₂∘φ) = (if n = 0 then 0 else 1/n²) − Σ_{m ≤ n} coeff m Li₂ · coeff n (φ^m)`,

while

`coeff n b4Ds = Σ_{k ≤ n} w_k·(coeff n (X^{k+1}) − coeff n (φ^{k+1}))`,

`w_k = 1/(k+1)²`.  Since `φ` has zero constant term (`coeff_pow_lt_one`), the
coefficients of `φ^m` vanish below degree `m`, so

* the `X`-terms contribute only `k = n−1`, i.e. exactly `coeff n b4Li2`
  (`P1` below), and
* the `φ`-terms, after the shift `m = k+1`, are the substituted `Li₂` coefficients
  (`P2` below; the two end terms `m = 0` and `m = n+1` vanish).

The whole bookkeeping is finite, over `ℚ`, and axiom-free.
-/
import Mathlib
import Submission.Work.Pure.b4_PF_aux

open PowerSeries

namespace Work.Pure

open Submission.CDT

theorem b4_PF_D : Work.Pure.b4Li2 - Work.Pure.b4Li2.subst Submission.CDT.sympPhi = Work.Pure.b4Ds := by
  ext n
  rw [map_sub, coeff_b4Ds, coeff_subst_range b4Li2 coeff_sympPhi_zero n]
  -- the `X`-part of `b4Ds`: only `k = n-1` survives
  have P1 :
      (∑ k ∈ Finset.range (n + 1),
          b4wt k * PowerSeries.coeff n ((X : PowerSeries ℚ) ^ (k + 1)))
        = PowerSeries.coeff n b4Li2 := by
    rcases n with _ | j
    · simp
    · rw [Finset.sum_eq_single j]
      · rw [PowerSeries.coeff_X_pow]
        simp [b4wt, coeff_b4Li2]
      · intro k _ hkj
        rw [PowerSeries.coeff_X_pow, if_neg]
        · ring
        · omega
      · intro hj
        exact absurd (Finset.mem_range.mpr (by omega)) hj
  -- the `φ`-part of `b4Ds`, shifted by one index, is the substituted `Li₂`
  have P2 :
      (∑ k ∈ Finset.range (n + 1), b4wt k * PowerSeries.coeff n (sympPhi ^ (k + 1)))
        = ∑ m ∈ Finset.range (n + 1),
            PowerSeries.coeff m b4Li2 * PowerSeries.coeff n (sympPhi ^ m) := by
    let G : ℕ → ℚ := fun m => PowerSeries.coeff m b4Li2 * PowerSeries.coeff n (sympPhi ^ m)
    have hGG : ∀ k, b4wt k * PowerSeries.coeff n (sympPhi ^ (k + 1)) = G (k + 1) := by
      intro k
      simp [G, b4wt, coeff_b4Li2]
    rw [Finset.sum_congr rfl (fun k _ => hGG k)]
    have h1 := Finset.sum_range_succ' G n
    have h2 := Finset.sum_range_succ (fun k => G (k + 1)) n
    have hG0 : G 0 = 0 := by simp [G, coeff_b4Li2]
    have hGn : G (n + 1) = 0 := by
      simp only [G]
      rw [coeff_pow_lt_one coeff_sympPhi_zero (show n < n + 1 by omega), mul_zero]
    rw [h1, h2, hG0, hGn]
  have hR :
      (∑ k ∈ Finset.range (n + 1),
          b4wt k * PowerSeries.coeff n ((X : PowerSeries ℚ) ^ (k + 1) - sympPhi ^ (k + 1)))
        = (∑ k ∈ Finset.range (n + 1),
              b4wt k * PowerSeries.coeff n ((X : PowerSeries ℚ) ^ (k + 1)))
          - (∑ k ∈ Finset.range (n + 1),
              b4wt k * PowerSeries.coeff n (sympPhi ^ (k + 1))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by rw [map_sub]; ring)
  rw [hR, P1, P2]

end Work.Pure
