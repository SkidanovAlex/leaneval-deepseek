import Mathlib
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FITop4.Defs4
import Submission.Work.FIArea6Hecke.S16CleanDefs

namespace Work.FIArea6Road

/-- **Vertical Mellin bound uniform in the band `1/2 ≤ σ ≤ 2`.**

For a `C²` bump `p : ℝ → ℝ` with `0 ≤ p ≤ 1`, supported in `(N, (1+θ)N]` (where `N = Pa.N`,
`θ = Pa.θ` come from the numerical set-up `Pa`), whose first two derivatives satisfy the mollifier
bounds `|p^{(k)}| ≤ c_k (θN)^{-k}` (`c_k = Work.FITop4.cMoll k`, `k ≤ 2`), the Mellin transform
decays vertically as

`‖mellin p (σ + iy)‖ ≤ 10^7 · θ · N^σ · (1 + (θy)²)^{-1}`.

The mathematical content is `Work.FIArea6.S16MellinVerticalBound`; the only work here is to feed
it the two structural facts hidden in `Pa.Params`: `N ≥ 1` (so `N > 0`) and `θ ≤ 1`
(`θ = (log x)^{-A'}` with `log x > 1`, since `x ≥ 3`, and `A' > 0`), and to translate the
hypothesis `hpd` at `k = 2` into the form `|p''| ≤ 2^20 / (θN)²` it expects. -/
theorem MellinVerticalOfHpd
    (Pa : Work.FITop.Params) (p : ℝ → ℝ) (σ y : ℝ)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hpd : ∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ)))
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hy : y ≠ 0) :
    ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 10 ^ 7 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * y) ^ 2)⁻¹ := by
  have hNpos : 0 < Pa.N := by linarith [Pa.hN1]
  have hθNpos : 0 < Pa.θ * Pa.N := mul_pos Pa.hθ0 hNpos
  -- `x ≥ 3` forces `log x > 1 > 0`.
  have h3x : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : (1 : ℝ) < Real.log (Pa.x : ℝ) :=
    lt_of_lt_of_le (by linarith [Real.log_three_gt_d9]) (Real.log_le_log (by norm_num) h3x)
  -- `A' ≥ 2A + 2^20 > 0`.
  have hA'pos : 0 < Pa.A' := by
    have h2 : (0:ℝ) < (2:ℝ)^(20:ℕ) := by norm_num
    linarith [Pa.hA, Pa.hA']
  -- `θ = (log x)^{-A'} ≤ 1`.
  have hθ1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ, Real.rpow_neg (by linarith : (0:ℝ) ≤ Real.log (Pa.x:ℝ))]
    exact le_of_lt (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hlog hA'pos))
  -- Translate `hpd` at `k = 2` into `|p''| ≤ 2^20 / (θN)²`.
  have hd2 : ∀ u : ℝ, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N)^2 := by
    intro u
    have h := hpd 2 (by norm_num) u
    have heq : Work.FITop4.cMoll 2 * (Pa.θ * Pa.N) ^ (-(2:ℝ)) = 1048576 / (Pa.θ * Pa.N)^2 := by
      have e : (Pa.θ * Pa.N) ^ (-(2:ℝ)) = ((Pa.θ * Pa.N)^2)⁻¹ := by
        rw [Real.rpow_neg hθNpos.le, Real.rpow_two]
      rw [Work.FITop4.cMoll, e, div_eq_mul_inv]
      norm_num
    exact le_trans h (le_of_eq heq)
  have hb := Work.FIArea6.S16MellinVerticalBound p Pa.N Pa.θ σ hNpos Pa.hθ0 hθ1 hpC hp0 hp1
    hpsupp hd2 hσ hσ2 y hy
  have h10 : (10:ℝ)^7 = 10000000 := by norm_num
  rw [h10]
  exact hb

end Work.FIArea6Road
