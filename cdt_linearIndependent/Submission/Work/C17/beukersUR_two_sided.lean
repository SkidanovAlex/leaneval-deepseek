/-
# `Work.C17.beukersUR_two_sided`: the two-sided bound on the Beukers coefficients

For `b ≥ 3` and every `n`, with `α = b + √(b²−1)`,

`αⁿ/(n+1) ≤ beukersUR b n ≤ αⁿ`.

The proof identifies the generating series `U b = Σ_n u_n(b) Xⁿ` with the
product `Sα α · Sα β`, where `β = b − √(b²−1)` and
`Sα γ = Σ_k c_k γᵏ Xᵏ`, `c_k = C(2k,k)/4ᵏ`, is the formal series of
`(1 − γX)^{-1/2}`.  Indeed both `U b` and `Sα α · Sα β` are square roots of
`(1 − 2bX + X²)^{-1}` with constant coefficient `1`
(`Usq_mul` and `Ssq_mul`/`Sseries_sq`), hence equal by `sqrt_unique`.
Extracting coefficients gives `u_n = Σ_k c_k c_{n−k} αᵏ β^{n−k}`; since
`Σ_k c_k c_{n−k} = 1` (`cR_convolution`) and `0 ≤ β ≤ α`, every term is at
most `c_k c_{n−k} αⁿ`, giving the upper bound, while the single term `k = n`
is `c_n αⁿ ≥ αⁿ/(n+1)` (`cb_lower`), giving the lower bound.

Reusable pieces live in the sibling modules `beukersUR_defs`, `Sseries_sq`,
`Usq_mul`, `sqrt_unique`, `cb_lower` under `Submission/Work/C17/`.
-/
import Mathlib
import Submission.CDT.Beukers
import Submission.Work.C17.beukersUR_defs
import Submission.Work.C17.Sseries_sq
import Submission.Work.C17.sqrt_unique
import Submission.Work.C17.cb_lower
import Submission.Work.C17.Usq_mul


namespace Work.C17

open PowerSeries

noncomputable section

lemma cR_nonneg (k : ℕ) : 0 ≤ cR k := by
  rw [cR]
  positivity

/-- `Σ_n α^n X^n` is the inverse of `1 - αX`. -/
lemma geom_mul (α : ℝ) :
    PowerSeries.mk (fun n => α ^ n) * (1 - PowerSeries.C α * PowerSeries.X) = 1 := by
  have hmk : PowerSeries.mk (fun n => α ^ n)
      = PowerSeries.rescale α (PowerSeries.mk 1) := by
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, Pi.one_apply, mul_one]
  have hres : (1 - PowerSeries.C α * PowerSeries.X : PowerSeries ℝ)
      = PowerSeries.rescale α (1 - PowerSeries.X) := by
    rw [map_sub, map_one, PowerSeries.rescale_X]
  rw [hmk, hres, ← map_mul (PowerSeries.rescale α),
    PowerSeries.mk_one_mul_one_sub_eq_one ℝ, map_one]

lemma Ssq_mul (α : ℝ) : (Sα α) ^ 2 * (1 - PowerSeries.C α * PowerSeries.X) = 1 := by
  have h : (Sα α) ^ 2 = PowerSeries.mk (fun n => α ^ n) := by
    ext n
    rw [Sseries_sq, PowerSeries.coeff_mk]
  rw [h, geom_mul]

theorem beukersUR_two_sided (b : ℝ) (hb : 3 ≤ b) (n : ℕ) :
    (b + Real.sqrt (b ^ 2 - 1)) ^ n / ((n : ℝ) + 1) ≤ Submission.CDT.beukersUR b n ∧
      Submission.CDT.beukersUR b n ≤ (b + Real.sqrt (b ^ 2 - 1)) ^ n := by
  set s : ℝ := Real.sqrt (b ^ 2 - 1) with hs
  set α : ℝ := b + s with hα
  set β : ℝ := b - s with hβ
  have hs2 : s ^ 2 = b ^ 2 - 1 := by
    rw [hs]; exact Real.sq_sqrt (by nlinarith [hb])
  have hsnn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsleb : s ≤ b := by
    rw [hs]
    have h := Real.sqrt_le_sqrt (show b ^ 2 - 1 ≤ b ^ 2 by nlinarith [hb])
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ b)] at h
  have hβnn : 0 ≤ β := by rw [hβ]; linarith
  have hαnn : 0 ≤ α := by rw [hα]; linarith
  have hβleα : β ≤ α := by rw [hα, hβ]; linarith
  have hαβmul : α * β = 1 := by
    rw [hα, hβ]
    have : (b + s) * (b - s) = b ^ 2 - s ^ 2 := by ring
    rw [this, hs2]; ring
  have hαβsum : α + β = 2 * b := by rw [hα, hβ]; ring
  have hQ : (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)
      = 1 - PowerSeries.C (2 * b) * PowerSeries.X + PowerSeries.X ^ 2 := by
    have e1 : (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)
        = 1 - (PowerSeries.C α + PowerSeries.C β) * PowerSeries.X
            + (PowerSeries.C α * PowerSeries.C β) * PowerSeries.X ^ 2 := by ring
    rw [e1, ← map_add (PowerSeries.C : ℝ →+* PowerSeries ℝ),
      ← map_mul (PowerSeries.C : ℝ →+* PowerSeries ℝ), hαβsum, hαβmul,
      map_one (PowerSeries.C : ℝ →+* PowerSeries ℝ)]
    ring
  have hG : ((Sα α) * (Sα β)) ^ 2
      * (1 - PowerSeries.C (2 * b) * PowerSeries.X + PowerSeries.X ^ 2) = 1 := by
    rw [← hQ]
    calc ((Sα α) * (Sα β)) ^ 2
          * ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X))
        = ((Sα α) ^ 2 * (1 - PowerSeries.C α * PowerSeries.X))
          * ((Sα β) ^ 2 * (1 - PowerSeries.C β * PowerSeries.X)) := by ring
      _ = 1 := by rw [Ssq_mul α, Ssq_mul β, mul_one]
  have hU := Usq_mul b
  have hconstG : PowerSeries.constantCoeff ((Sα α) * (Sα β)) = 1 := by
    rw [map_mul, coefficient_zero_Sα, coefficient_zero_Sα, one_mul]
  have hTG : U b = (Sα α) * (Sα β) :=
    sqrt_unique hU hG (coefficient_zero_U b) hconstG
  have hcoeff : ∀ m, Submission.CDT.beukersUR b m
      = ∑ k ∈ Finset.range (m + 1), cR k * cR (m - k) * (α ^ k * β ^ (m - k)) := by
    intro m
    rw [← coeff_U b m, hTG, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (Sα α) * PowerSeries.coeff j (Sα β)) m]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [coeff_Sα, coeff_Sα]
    ring
  have hupper : Submission.CDT.beukersUR b n ≤ α ^ n := by
    rw [hcoeff n]
    calc ∑ k ∈ Finset.range (n + 1), cR k * cR (n - k) * (α ^ k * β ^ (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1), cR k * cR (n - k) * α ^ n := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have h1 : α ^ k * β ^ (n - k) ≤ α ^ n := by
            have h2 : β ^ (n - k) ≤ α ^ (n - k) := pow_le_pow_left₀ hβnn hβleα (n - k)
            calc α ^ k * β ^ (n - k) ≤ α ^ k * α ^ (n - k) :=
                  mul_le_mul_of_nonneg_left h2 (pow_nonneg hαnn k)
              _ = α ^ (k + (n - k)) := (pow_add α k (n - k)).symm
              _ = α ^ n := by rw [Nat.add_sub_of_le hk_le]
          exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (cR_nonneg k) (cR_nonneg (n - k)))
      _ = α ^ n * (∑ k ∈ Finset.range (n + 1), cR k * cR (n - k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = α ^ n := by rw [cR_convolution n, mul_one]
  have hlower : α ^ n / ((n : ℝ) + 1) ≤ Submission.CDT.beukersUR b n := by
    rw [hcoeff n]
    have hnn : ∀ k ∈ Finset.range (n + 1),
        0 ≤ cR k * cR (n - k) * (α ^ k * β ^ (n - k)) := by
      intro k hk
      exact mul_nonneg (mul_nonneg (cR_nonneg k) (cR_nonneg (n - k)))
        (mul_nonneg (pow_nonneg hαnn k) (pow_nonneg hβnn (n - k)))
    have hsingle := Finset.single_le_sum (f := fun k => cR k * cR (n - k) * (α ^ k * β ^ (n - k)))
      hnn (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hval : cR n * cR (n - n) * (α ^ n * β ^ (n - n)) = cR n * α ^ n := by
      simp [cR_zero]
    rw [hval] at hsingle
    have hcn : (1 : ℝ) / ((n : ℝ) + 1) ≤ cR n := by
      have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
      have hn : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
      have hR : (4 : ℝ) ^ n ≤ ((n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast cb_lower n
      rw [cR, div_le_div_iff₀ hn h4, one_mul]
      linarith
    have h1 : α ^ n / ((n : ℝ) + 1) ≤ cR n * α ^ n := by
      have h := mul_le_mul_of_nonneg_right hcn (pow_nonneg hαnn n)
      simpa [div_eq_mul_inv, mul_comm] using h
    linarith
  exact ⟨hlower, hupper⟩

end

end Work.C17
