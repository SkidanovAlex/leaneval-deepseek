import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Identity.psiTail_tendsto_zero
import Submission.Work.RHContract.Identity.primeTail_nonneg
import Submission.Work.RHContract.Identity.primeTail_le
import Submission.Work.RHContract.Identity.PsiErr.psi_sub_id_div_mul_log_tendsto_zero
import Submission.Work.RHContract.Identity.TailSplit.integral_psi_mul_kW_eq
import Submission.Work.RHContract.Identity.Abel.mangoldt_sum_eq_psi_add_integral
import Submission.Work.RHContract.Identity.Regroup.logRatioSum_sub_primeTail_eq_mangoldt
import Submission.Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW

/-!
# `Work.RHContract.Identity.logRatioSum_eq_psiTail` — Mertens' identity (Lemma I)

The unconditional exact identity

`logRatioSum x = γ + log log x + (ψ x − x)/(x log x) − J(x) + tail(x)`   (`x ≥ 2`),

where `J = psiTail = ∫_x^∞ (ψ t − t) k(t) dt` and `tail = primeTail`.

## Structure of the proof

1. `∑_{n ≤ x} Λ n / (n log n) = logRatioSum x − primeTail x` (regrouping of the double sum over
   prime powers: `logRatioSum` is `∑_p ∑_{k≥1} 1/(k p^k)` and `primeTail` removes the part
   `k > e_p`).  — `Regroup.logRatioSum_sub_primeTail_eq_mangoldt`
2. Abel summation with `f(t) = 1/(t log t)` (`f' = −kW`):
   `∑_{n ≤ x} Λ n / (n log n) = ψ x/(x log x) + ∫_2^x ψ t k(t) dt`.
   — `Abel.mangoldt_sum_eq_psi_add_integral`
3. Splitting the integral with `∫_2^∞ = ∫_2^x + ∫_x^∞`, the antiderivative `log log t − 1/log t`
   of `t k(t)`, and `∫_x^∞ (ψ − t) k = psiTail x`:
   `∫_2^x ψ k = ∫_2^∞ (ψ − t) k − J(x) + (log log x − 1/log x) − (log log 2 − 1/log 2)`.
   — `TailSplit.integral_psi_mul_kW_eq` (with the integrability
   `TailInt.integrableOn_psi_sub_id_mul_kW`)
4. Hence the identity holds with the explicit constant
   `c* = ∫_2^∞ (ψ − t) k − log log 2 + 1/log 2` in place of `γ`.
5. Letting `x → ∞` identifies `c* = γ`: the left-hand side tends to `γ` by Mertens' third
   theorem (`Mertens.sum_log_prime_ratio_real_tendsto`), while each of the three error terms
   tends to `0`: `(ψ x − x)/(x log x) → 0` (`PsiErr.psi_sub_id_div_mul_log_tendsto_zero`,
   from Chebyshev's elementary bound `ψ x ≤ (log 4 + 4) x`), `J(x) → 0`
   (`Identity.psiTail_tendsto_zero`), and `tail(x) → 0` (`Identity.primeTail_le`, i.e.
   `tail x ≤ 5/√x` for `x ≥ 100`, squeezed against `5/√x`).
-/

namespace Work.RHContract.Identity

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The constant `c* = ∫_2^∞ (ψ t − t) k(t) dt − log log 2 + 1/log 2` of the identity; step 5
shows it is `Real.eulerMascheroniConstant`. -/
private def cstar : ℝ :=
  (∫ t in Set.Ioi (2 : ℝ), (Chebyshev.psi t - t) * Work.RHContract.kW t)
    - Real.log (Real.log 2) + 1 / Real.log 2

/-- The error term `(ψ x − x)/(x log x) − J(x) + tail(x)`, which tends to `0`. -/
private def err (y : ℝ) : ℝ :=
  (Chebyshev.psi y - y) / (y * Real.log y) - Work.RHContract.psiTail y
    + Work.RHContract.primeTail y

/-! ## Step 1–4: the identity with the explicit constant `c*` -/

private lemma logRatioSum_eq_cstar_plus (x : ℝ) (hx : 2 ≤ x) :
    Commons.NumberTheory.Mertens.logRatioSum x =
      cstar + Real.log (Real.log x) + (Chebyshev.psi x - x) / (x * Real.log x)
        - Work.RHContract.psiTail x + Work.RHContract.primeTail x := by
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t) (Set.Ioi 2) :=
    TailInt.integrableOn_psi_sub_id_mul_kW (le_refl (2 : ℝ))
  have hkey : Commons.NumberTheory.Mertens.logRatioSum x - Work.RHContract.primeTail x =
      cstar + Real.log (Real.log x) + (Chebyshev.psi x - x) / (x * Real.log x)
        - Work.RHContract.psiTail x := by
    rw [Regroup.logRatioSum_sub_primeTail_eq_mangoldt x hx,
      Abel.mangoldt_sum_eq_psi_add_integral x hx, TailSplit.integral_psi_mul_kW_eq x hx hint]
    unfold cstar
    have hx0 : x ≠ 0 := by linarith
    have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    have h20 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
    ring
  linarith

/-! ## Step 5: the constant is `γ` -/

private lemma primeTail_tendsto_zero_local :
    Tendsto Work.RHContract.primeTail atTop (nhds 0) := by
  refine squeeze_zero'
    (f := fun y : ℝ => Work.RHContract.primeTail y)
    (g := fun y : ℝ => 5 / Real.sqrt y) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with y hy
    exact primeTail_nonneg y hy
  · filter_upwards [Filter.eventually_ge_atTop (100 : ℝ)] with y hy
    exact primeTail_le y hy
  · -- `5/√x → 0`
    have h : Tendsto (fun y : ℝ => 5 * (Real.sqrt y)⁻¹) atTop (nhds 0) := by
      simpa using (Real.tendsto_sqrt_atTop.inv_tendsto_atTop.const_mul 5)
    refine h.congr (fun y => ?_)
    rw [div_eq_mul_inv]

private lemma cstar_eq_euler : cstar = Real.eulerMascheroniConstant := by
  have hcorpus : Tendsto
      (fun y : ℝ => Commons.NumberTheory.Mertens.logRatioSum y - Real.log (Real.log y))
      atTop (nhds Real.eulerMascheroniConstant) := by
    simpa [Commons.NumberTheory.Mertens.logRatioSum] using
      Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
  have herr : Tendsto err atTop (nhds 0) := by
    have h : Tendsto (fun y : ℝ => (Chebyshev.psi y - y) / (y * Real.log y)
        - Work.RHContract.psiTail y + Work.RHContract.primeTail y) atTop (nhds 0) := by
      simpa using
        ((PsiErr.psi_sub_id_div_mul_log_tendsto_zero.sub psiTail_tendsto_zero).add
          primeTail_tendsto_zero_local)
    exact h
  have h1 : Tendsto (fun y : ℝ => cstar + err y) atTop (nhds cstar) := by
    simpa using (tendsto_const_nhds.add herr : Tendsto (fun y : ℝ => cstar + err y) atTop
      (nhds (cstar + 0)))
  have h2 : Tendsto (fun y : ℝ => cstar + err y) atTop (nhds Real.eulerMascheroniConstant) :=
    hcorpus.congr' (by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with y hy
      have h := logRatioSum_eq_cstar_plus y hy
      simp only [err]
      linarith)
  exact tendsto_nhds_unique h1 h2

/-! ## The target -/

theorem logRatioSum_eq_psiTail (x : ℝ) (hx : 2 ≤ x) :
    Commons.NumberTheory.Mertens.logRatioSum x =
      Real.eulerMascheroniConstant + Real.log (Real.log x) + (Chebyshev.psi x - x) / (x * Real.log x)
        - Work.RHContract.psiTail x + Work.RHContract.primeTail x := by
  rw [logRatioSum_eq_cstar_plus x hx, cstar_eq_euler]

end

end Work.RHContract.Identity
