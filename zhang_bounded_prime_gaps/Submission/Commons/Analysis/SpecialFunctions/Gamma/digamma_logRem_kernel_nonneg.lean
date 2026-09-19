import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The nonnegativity kernel of the digamma log-remainder integral

For every `t > 0` we have

`0 ≤ 1 / (exp t - 1) - 1 / t + 1 / 2`.

This is the elementary inequality behind the estimate of
`∫ 1/(e^t-1) - 1/t + 1/2 · e^{-xt}` (see
`digamma_logRem_kernelIntegral`).  We prove it by multiplying by the
positive number `2 t (e^t - 1)`, which reduces the claim to

`0 ≤ t e^t - 2 e^t + t + 2`   (for `t ≥ 0`).

The latter function has derivative `1 + (t - 1) e^t`; its derivative is
nonnegative on `[0, ∞)` because `(1 - t) e^t ≤ 1` there, and this last
fact follows from the elementary bound `x + 1 ≤ e^x`.
-/

noncomputable section
open scoped Topology
open Set

namespace Commons.Analysis.SpecialFunctions.Gamma

private def fA : ℝ → ℝ := id * Real.exp
private def fB : ℝ → ℝ := (fun _ : ℝ => (2 : ℝ)) * Real.exp
private def H1 : ℝ → ℝ := fun u => 1 + (u - 1) * Real.exp u
private def H : ℝ → ℝ := fA - fB + id + fun _ : ℝ => (2 : ℝ)

private lemma exp_aux_nonneg (t : ℝ) : (1 - t) * Real.exp t ≤ 1 := by
  rcases le_total 1 t with h1 | h1
  · have hprod : (1 - t) * Real.exp t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_nonneg t)
    linarith
  · have hsub : 1 - t ≤ Real.exp (-t) := by
      simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-t)
    have hmult : (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_right hsub (Real.exp_pos t).le
    have hR : Real.exp (-t) * Real.exp t = 1 := by
      rw [Real.exp_neg]
      exact inv_mul_cancel₀ (Real.exp_ne_zero t)
    exact le_trans hmult (by rw [hR])

private lemma H1_nonneg (t : ℝ) : 0 ≤ H1 t := by
  unfold H1
  have h := exp_aux_nonneg t
  nlinarith

private lemma H_hasDerivAt (t : ℝ) :
    HasDerivAt H ((1 * Real.exp t + t * Real.exp t) - (0 * Real.exp t + (2 : ℝ) * Real.exp t)
      + 1 + 0) t := by
  have hA : HasDerivAt fA (1 * Real.exp t + t * Real.exp t) t := by
    dsimp [fA]
    exact (hasDerivAt_id t).mul (Real.hasDerivAt_exp t)
  have hB : HasDerivAt fB (0 * Real.exp t + (2 : ℝ) * Real.exp t) t := by
    dsimp [fB]
    exact (hasDerivAt_const t (2 : ℝ)).mul (Real.hasDerivAt_exp t)
  dsimp [H]
  exact ((hA.sub hB).add (hasDerivAt_id t)).add (hasDerivAt_const t (2 : ℝ))

private lemma H_deriv (t : ℝ) : deriv H t = H1 t := by
  have hh := H_hasDerivAt t
  rw [hh.deriv]
  unfold H1
  ring

private lemma H_diff : Differentiable ℝ H := by
  intro t
  exact (H_hasDerivAt t).differentiableAt

private lemma H_monoOn : MonotoneOn H (Ici (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
  · exact H_diff.continuous.continuousOn
  · exact H_diff.differentiableOn.mono (interior_subset)
  · intro x hx
    have hx0 : 0 < x := by rwa [interior_Ici, mem_Ioi] at hx
    rw [H_deriv]
    exact H1_nonneg x

private lemma H_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ H t := by
  have hmono := H_monoOn
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := by simp
  have htI : t ∈ Ici (0 : ℝ) := by simpa using ht
  have hm := hmono h0 htI ht
  have hH0 : H 0 = 0 := by
    dsimp [H, fA, fB]
    norm_num [Real.exp_zero]
  simpa [hH0] using hm

/-- For `t > 0`, the digamma log-remainder kernel is nonnegative. -/
theorem digamma_logRem_kernel_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / (Real.exp t - 1) - 1 / t + 1 / 2 := by
  have hE1 : 1 < Real.exp t := (Real.one_lt_exp_iff.mpr ht)
  have hEm1 : 0 < Real.exp t - 1 := sub_pos.mpr hE1
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hc : 0 < 2 * t * (Real.exp t - 1) := by positivity
  have hnum : 0 ≤ t * Real.exp t - (2 : ℝ) * Real.exp t + t + 2 := by
    simpa [H, fA, fB] using H_nonneg (le_of_lt ht)
  have hcalc : (2 * t * (Real.exp t - 1)) * (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2)
      = t * Real.exp t - (2 : ℝ) * Real.exp t + t + 2 := by
    field_simp [ht0, sub_ne_zero.mpr (ne_of_gt hE1)]
    ring
  have hcA : 0 ≤ (2 * t * (Real.exp t - 1)) * (1 / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) := by
    rw [hcalc]
    exact hnum
  exact (mul_le_mul_iff_of_pos_left hc).mp (by simpa using hcA)

end Commons.Analysis.SpecialFunctions.Gamma