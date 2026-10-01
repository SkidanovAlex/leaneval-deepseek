import Mathlib

/-!
# The completed L-function of a nontrivial Dirichlet character has finite vanishing order

For a nontrivial Dirichlet character `ψ`, the completed L-function `Λ(s, ψ)` is an entire
function, and it is not identically zero (e.g. `Λ(2, ψ) = L(2, ψ) · γ_ψ(2) ≠ 0`, using the
nonvanishing of `L(2, ψ)` for `Re 2 ≥ 1` and `Γ_ℝ(2), Γ_ℝ(3) ≠ 0`).  By the identity principle
for analytic functions on the connected domain `ℂ`, an entire function which is not identically
zero cannot vanish on a neighbourhood of any point.  Hence the analytic vanishing order of `Λ(·, ψ)`
is finite at every point.

This is the content of `completedLFunction_analyticOrderAt_ne_top` below; it is the basic input
allowing one to speak of the *multiplicity* of a zero of `Λ(·, ψ)` at an arbitrary point `z`, or
of the logarithmic derivative of `Λ(·, ψ)` as a meromorphic function with simple poles at the
zeros of `Λ(·, ψ)`.
-/

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex

/-- **The completed L-function of a nontrivial Dirichlet character is not locally zero.**

Since `Λ(·, ψ)` is entire and not identically zero, and `ℂ` is (pre)connected, the identity
principle forces it to be nonzero off a discrete set; in particular it is not eventually zero
near any point, so its analytic vanishing order is never `⊤`. -/
theorem completedLFunction_analyticOrderAt_ne_top {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (z : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction ψ) z ≠ ⊤ := by
  classical
  -- `Λ(·, ψ)` is entire.
  have hdiff := DirichletCharacter.differentiable_completedLFunction hψ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ) Set.univ :=
    fun w _ => hdiff.analyticAt w
  -- and it does not vanish at `s = 2`, hence is not the zero function.
  have h2 : DirichletCharacter.completedLFunction ψ 2 ≠ 0 := by
    intro h0
    have hgf : ψ.gammaFactor 2 ≠ 0 := by
      rcases ψ.even_or_odd with h | h
      · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
      · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
    have hL : DirichletCharacter.LFunction ψ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (by norm_num)
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ 2
        (Or.inl (by norm_num : (2 : ℂ) ≠ 0)), h0, zero_div] at hL
    exact hL rfl
  -- Suppose `Λ(·, ψ)` vanished on a neighbourhood of `z`.  The identity principle on the
  -- connected set `ℂ` would then make it identically zero, contradicting `h2`.
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero := han.eq_of_eventuallyEq (analyticOnNhd_const (v := (0 : ℂ))) htop
  exact h2 (congrFun hzero 2)

end Work.LinnikAreas.OtherCharRepel
