import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Work.LinnikAreas.Density4.Udecay.abel_finite_identity
import Submission.Work.LinnikAreas.Density4.Udecay.rpow_diff_summable
import Submission.Work.LinnikAreas.Density4.Udecay.muRecipSum_uniform_bound
import Submission.Work.LinnikAreas.Density4.Udecay.tendsto_muRecip_mul_rpow
import Submission.Work.LinnikAreas.Density4.Udecay.summable_moebius_div_rpow

namespace Work.LinnikAreas.Density4.Udecay

open Filter Finset
open scoped Topology

/-- **Abel/Mellin identity for the Möbius reciprocal sums.**  For `s > 0` the Abel-weighted
series `Σ_m (Σ_{n ≤ m} μ(n)/n) · (m^{-s} - (m+1)^{-s})` converges, and its sum equals the
Dirichlet series `Σ_n μ(n)/n^{1+s}`.

The finite Abel summation identity `abel_finite_identity` writes the `M`-th partial sum of the
Abel series as the `M`-th partial sum of the Dirichlet series minus the boundary term
`muRecipSum M · (M+1)^{-s}`; the boundary term tends to `0` (`tendsto_muRecip_mul_rpow`), and the
partial Dirichlet sums tend to the Dirichlet series (`summable_moebius_div_rpow`). Summability of
the Abel series itself follows by comparison of `|muRecipSum m|` with the uniform bound
`muRecipSum_uniform_bound` and the absolutely summable step weights `rpow_diff_summable`. -/
theorem mellin_abel_tsum {s : ℝ} (hs : 0 < s) :
    Summable (fun m : ℕ => Commons.NumberTheory.Moebius.muRecipSum m * ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s))) ∧
    (∑' m : ℕ, Commons.NumberTheory.Moebius.muRecipSum m * ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)))
      = ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ) := by
  -- Summability of the Abel series, by comparison with the telescoping step weights.
  have hsum_f : Summable (fun m : ℕ =>
      Commons.NumberTheory.Moebius.muRecipSum m * ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s))) := by
    obtain ⟨C, _hC, hbound⟩ := muRecipSum_uniform_bound
    refine Summable.of_norm_bounded
      (g := fun m : ℕ => C * |(m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)|)
      ((rpow_diff_summable hs).mul_left C) (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound m) (abs_nonneg _)
  refine ⟨hsum_f, ?_⟩
  -- Summability of the limiting Dirichlet series.
  have hsum_g : Summable (fun n : ℕ =>
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)) :=
    summable_moebius_div_rpow hs
  -- The two partial-sum sequences.
  let F : ℕ → ℝ := fun N => ∑ m ∈ Finset.range N,
      Commons.NumberTheory.Moebius.muRecipSum m * ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s))
  let G : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N,
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)
  have hGlim : Filter.Tendsto (fun M : ℕ => G (M + 1)) Filter.atTop
      (nhds (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hsum_g.hasSum.tendsto_sum_nat
  -- Finite Abel summation turns `F (M+1)` into `G (M+1)` minus the boundary term.
  have hlim : Filter.Tendsto (fun M : ℕ => F (M + 1)) Filter.atTop
      (nhds (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))) := by
    have h1 : (fun M : ℕ => F (M + 1))
        = fun M : ℕ => G (M + 1)
            - Commons.NumberTheory.Moebius.muRecipSum M * ((M : ℝ) + 1) ^ (-s) := by
      funext M
      exact abel_finite_identity s M
    rw [h1]
    simpa using hGlim.sub (tendsto_muRecip_mul_rpow hs)
  have hlimF : Filter.Tendsto F Filter.atTop
      (nhds (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
  -- Convergence of the partial sums identifies the sum of the Abel series.
  exact (hsum_f.hasSum_iff_tendsto_nat).mpr hlimF |>.tsum_eq

end Work.LinnikAreas.Density4.Udecay
