import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

set_option linter.unusedVariables false

/-- The quantitative half of `hKerConstWlInf_l`: for the radial profile `hKer` and an arbitrary
level `l`, the function `(z,θ) ↦ c·hKer z` lies in `𝒲^{l,∞}` and its norm is at most
`|c|·Σ_{k≤l} k!(k+1)`, uniformly in `α`.

All positive `D_θ`-iterates of a `θ`-independent function vanish identically, so the second
(angular) block of `WlInf` is `0` and only the `l+1` radial summands survive, each bounded by
`|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`). -/
theorem hKerConstWlInf_l_aux (l : ℕ) (α c : ℝ) :
    Work.Spaces.WlInfMem α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α l (fun z _ : ℝ => c * Work.Spaces.hKer z)
        ≤ |c| * (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))) := by
  -- every positive `D_θ`-iterate of a `θ`-independent function vanishes
  have hDth : ∀ j : ℕ, Work.Spaces.DthIter (j + 1) (fun z θ => c * Work.Spaces.hKer z)
      = fun _ _ => (0 : ℝ) := by
    intro j
    induction j with
    | zero => funext z θ; simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    | succ j ih =>
        rw [show j + 1 + 1 = (j + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  have hpzIter0 : ∀ k : ℕ, Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]
  -- the pointwise bounds of the radial summands
  have hrad : ∀ k : ℕ, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ|
        ≤ |c| * ((k.factorial : ℝ) * (k + 1)) := by
    intro k z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun _ : ℝ => c) Work.Spaces.hKer z θ]
    rw [show (z + 1) ^ k * (c * deriv^[k] Work.Spaces.hKer z)
        = c * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.Spaces.pzIter_hKer_bound k z hz) (abs_nonneg c)
  have hmem : Work.Spaces.WlInfMem α l (fun z θ => c * Work.Spaces.hKer z) := by
    constructor
    · intro k hk
      exact ⟨|c| * ((k.factorial : ℝ) * (k + 1)), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact hrad k z hz θ hθ⟩
    · intro j hj k hk hj1 hjk
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hj1]
        exact hDth (j - 1)
      refine ⟨0, fun y hy => ?_⟩
      rcases hy with ⟨z, hz', θ, hθ, rfl⟩
      simp only []
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
      ≤ ∑ k ∈ Finset.range (l + 1), (|c| * ((k.factorial : ℝ) * (k + 1))) :=
    Finset.sum_le_sum fun k _ => Work.Spaces.supAbs_le (hrad k)
  have h2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
      if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => ?_))
    by_cases hc : 1 ≤ j ∧ k + j ≤ l
    · rw [if_pos hc]
      refine Work.Spaces.supAbs_le (fun z hz' θ hθ => ?_)
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hc.1]
        exact hDth (j - 1)
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
    · rw [if_neg hc]
  calc (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
          (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
        + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs
              (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
      ≤ (∑ k ∈ Finset.range (l + 1), (|c| * ((k.factorial : ℝ) * (k + 1)))) + 0 := add_le_add h1 h2
    _ = |c| * (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))) := by
        rw [add_zero, Finset.mul_sum]

/-- The `𝒲^{l,∞}`-norm of a constant multiple of the radial profile `hKer(z) = z/(1+z)²`, at an
*arbitrary* level `l`: `(z,θ) ↦ c·hKer z` is `θ`-independent, so all its positive `D_θ`-iterates
vanish identically and only the `l+1` radial summands `sup |(z+1)^k hKer^{(k)}|` survive, each
bounded by `|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`).  Hence
`WlInfMem α l (fun z _ => c * hKer z)` and `WlInf α l (fun z _ => c * hKer z) ≤ C_l·|c|` with
`C_l = Σ_{k≤l} k!(k+1)`, for every `α` and every `c` (no `α`-dependence at all).

This is the level-`l` version of the proved `Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf`
(the case `l = 4`, constant `200`). -/
theorem hKerConstWlInf_l (l : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α c : ℝ),
    Work.Spaces.WlInfMem α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α l (fun z _ : ℝ => c * Work.Spaces.hKer z) ≤ C * |c| := by
  refine ⟨max 1 (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun α c => ?_⟩
  obtain ⟨hmem, hb⟩ := hKerConstWlInf_l_aux l α c
  refine ⟨hmem, le_trans hb ?_⟩
  rw [mul_comm |c| (∑ k ∈ Finset.range (l + 1), ((k.factorial : ℝ) * (k + 1)))]
  exact mul_le_mul_of_nonneg_right (le_max_right 1 _) (abs_nonneg c)

end Work.FTS.StrongEps.H5
