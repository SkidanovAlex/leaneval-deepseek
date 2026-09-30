import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.Ssum.Defs
import Submission.Work.BMF.Ssum.Prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Ssum

/-- Ford's key comparison (5.2) at one value of `z = n + u`: the double sum
`∑_{a ≤ M₁} ∑_{b ≤ M₂} (n + ab + u)^{-it}` is the exponential sum `Usum` evaluated at `z = n+u`,
up to the Taylor error `t * (M₁M₂)^{k+2} / ((k+1) z^{k+1})`.

Route (Ford, *Vinogradov's integral*, (5.1)-(5.2)): put `z := n + u > 0` and `x := ab/z ∈ [0,1]`
(the hypothesis `(M₁:ℝ)*(M₂:ℝ) ≤ n + u` gives `ab ≤ M₁M₂ ≤ z`). Then
`(n+ab+u)^{-it} = z^{-it} · exp (-it log (1+x))` with `‖z^{-it}‖ = 1`, and
`exp (-it log (1+x))` differs from `eZ ((t/2π) * ∑_{l=1}^{k} (-1)^l x^l / l)` by at most
`t * x^{k+1}/(k+1)`; the sharp Taylor remainder estimate (Ford's (5.1)), namely
`|Real.log (1+x) - ∑_{j=1}^{k} (-1)^{j-1} x^j/j| ≤ x^{k+1}/(k+1)` for `0 ≤ x ≤ 1`, has to be
established inside the proof (e.g. by the derivative/monotonicity route of
`Real.sum_range_le_log_div`, whose derivative of the remainder is `(-1)^k x^k/(1+x)`), and
`‖eZ a - eZ b‖ ≤ 2π |a-b|`. Unfolding `Usum` and `gam` turns the phase into exactly
`(t/2π) ∑_{l=1}^k (-1)^l x^l/l`. Finally `∑_{a≤M₁}∑_{b≤M₂} (ab)^{k+1} ≤ M₁^{k+2} M₂^{k+2}`. -/
theorem norm_ab_sum_sub_Usum_le (k : ℕ) (hk : 1 ≤ k) (t u : ℝ) (n M₁ M₂ : ℕ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hMz : (M₁ : ℝ) * (M₂ : ℝ) ≤ (n : ℝ) + u) :
    ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂,
        ((((n : ℝ) + (a : ℝ) * (b : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((n : ℝ) + u))‖
        + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 2)
            / (((k : ℝ) + 1) * (((n : ℝ) + u) ^ (k + 1))) := by
  have hz_pos : (0 : ℝ) < (n : ℝ) + u := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
      have h1' : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
      have h2' : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM₂
      nlinarith
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [h1, hu, hn]
  -- (1) triangle inequality: the smoothed sum plus the total single-term error
  have hkey := norm_double_sum_sub_le
    (fun a b => ((((n : ℝ) + (a : ℝ) * (b : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))
    (fun a b => eZ (logphase t ((n : ℝ) + u))
      * eZ (Uphase k t ((n : ℝ) + u) ((a : ℝ) * (b : ℝ))))
    M₁ M₂
  refine le_trans hkey ?_
  -- (2) the smoothed sum is `eZ (logphase t z) · Usum`
  have hG : (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂,
        eZ (logphase t ((n : ℝ) + u))
          * eZ (Uphase k t ((n : ℝ) + u) ((a : ℝ) * (b : ℝ))))
      = eZ (logphase t ((n : ℝ) + u))
          * Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((n : ℝ) + u)) := by
    rw [show Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((n : ℝ) + u))
        = ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂,
            eZ (Uphase k t ((n : ℝ) + u) ((a : ℝ) * (b : ℝ))) from rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum]
  rw [hG, norm_mul, eZ_norm, one_mul]
  refine add_le_add le_rfl ?_
  -- (3) the single-term comparison (Ford's (5.2) for one value of `ab`)
  have hterm : ∀ a ∈ Finset.Icc 1 M₁, ∀ b ∈ Finset.Icc 1 M₂,
      ‖((((n : ℝ) + (a : ℝ) * (b : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))
        - eZ (logphase t ((n : ℝ) + u))
          * eZ (Uphase k t ((n : ℝ) + u) ((a : ℝ) * (b : ℝ)))‖
      ≤ t * (((a : ℝ) * (b : ℝ)) / ((n : ℝ) + u)) ^ (k + 1) / ((k : ℝ) + 1) := by
    intro a ha b hb
    have haM : a ≤ M₁ := (Finset.mem_Icc.mp ha).2
    have hbM : b ≤ M₂ := (Finset.mem_Icc.mp hb).2
    have h1 : (a : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast haM
    have h2 : (b : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hbM
    have hc0 : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by positivity
    have hle : (a : ℝ) * (b : ℝ) ≤ (n : ℝ) + u := by
      have h3 : (a : ℝ) * (b : ℝ) ≤ (M₁ : ℝ) * (M₂ : ℝ) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      linarith
    have hbase : ((((n : ℝ) + (a : ℝ) * (b : ℝ) + u : ℝ)) : ℂ)
        = ((((n : ℝ) + u) + (a : ℝ) * (b : ℝ) : ℝ) : ℂ) := by
      congr 1
      ring
    rw [hbase]
    exact norm_cpow_sub_eZ_mul_le k t ht ((n : ℝ) + u) ((a : ℝ) * (b : ℝ)) hz_pos hc0 hle
      (taylog_log_remainder k (by positivity) ((div_le_one hz_pos).mpr hle))
      (Uphase_two_pi k t ((n : ℝ) + u) ((a : ℝ) * (b : ℝ)) hz_pos)
  refine le_trans (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb) ?_
  -- (4) summing the errors and collecting the closed form
  calc ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂,
        t * (((a : ℝ) * (b : ℝ)) / ((n : ℝ) + u)) ^ (k + 1) / ((k : ℝ) + 1)
      = t / ((k : ℝ) + 1)
          * (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ Finset.Icc 1 M₂, ((a : ℝ) * (b : ℝ)) ^ (k + 1))
          / ((n : ℝ) + u) ^ (k + 1) := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [div_pow]
        ring
    _ ≤ t / ((k : ℝ) + 1)
          * ((M₁ : ℝ) ^ (k + 2) * (M₂ : ℝ) ^ (k + 2)) / ((n : ℝ) + u) ^ (k + 1) := by
        apply div_le_div_of_nonneg_right _ (pow_pos hz_pos (k + 1)).le
        apply mul_le_mul_of_nonneg_left _ (div_nonneg ht (by positivity))
        exact sum_Icc_mul_pow_le k M₁ M₂
    _ = t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 2)
          / (((k : ℝ) + 1) * (((n : ℝ) + u) ^ (k + 1))) := by
        rw [← mul_pow]
        field_simp

end Work.BMF.Ssum
