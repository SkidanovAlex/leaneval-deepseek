import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux

open scoped Real

/-- Reindexing helper: a `range (m+2)`-sum whose `0`-th term vanishes can be written as a
sum over `Icc 1 (m+1)`. -/
theorem sum_range_succ_eq_sum_Icc (m : ℕ) (g : ℕ → ℝ) (h0 : g 0 = 0) :
    ∑ r ∈ Finset.range (m + 2), g r = ∑ r ∈ Finset.Icc 1 (m + 1), g r := by
  have hset : Finset.Ico 1 (m + 2) = Finset.Icc 1 (m + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hIco : ∑ k ∈ Finset.Ico 1 (m + 2), g k = ∑ k ∈ Finset.range (m + 1), g (k + 1) := by
    rw [Finset.sum_Ico_eq_sum_range g 1 (m + 2)]
    have hsub : m + 2 - 1 = m + 1 := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  rw [Finset.sum_range_succ' g (m + 1), h0, add_zero, ← hIco, hset]

/-- The exact angular expansion `D_θ^{m+1} f = Σ_{r ≥ 1} a_{m+1,r} ∂_θ^r f` combined with the
divisibility bound `|a_{m+1,r}| ≤ K_r sin(2θ)^r` expresses `D_θ^{m+1} f` as a finite linear
combination of the *plain* angular derivatives `∂_θ^r f`, `1 ≤ r ≤ m+1`, with weights
`K_r sin(2θ)^r`.

This is the "Pth-slot" expansion used by the `EllipticEstimates` chain: it converts the
weighted operator `D_θ^{m+1}` into a sum of plain derivatives with the good weight
`sin(2θ)^r`, which is exactly what the `H^k` bookkeeping apparatus consumes. -/
theorem dthIter_abs_le_pthIter_sum (m : ℕ) :
    ∃ Kc : ℕ → ℝ, (∀ r : ℕ, 0 < Kc r) ∧
      ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
        (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
        θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.Spaces.DthIter (m + 1) f z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ| := by
  classical
  have hex : ∀ r : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ θ : ℝ,
      |selfdth.dthCoef (m + 1) r θ| ≤ K * |Real.sin (2 * θ)| ^ r :=
    fun r => selfdth.DthCoef_sin_pow_bound (m + 1) r
  refine ⟨fun r => Classical.choose (hex r), fun r => (Classical.choose_spec (hex r)).1, ?_⟩
  intro f z θ hf hθ
  have hsin : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
  have hexp := selfdth.DthIter_expansion_local (m + 1) f z θ hf
  have h0 : (fun r => selfdth.dthCoef (m + 1) r θ * Work.Spaces.pthIter r f z θ) 0 = 0 := by
    show selfdth.dthCoef (m + 1) 0 θ * Work.Spaces.pthIter 0 f z θ = 0
    simp [selfdth.dthCoef_succ_zero m]
  have hsum := sum_range_succ_eq_sum_Icc m
    (fun r => selfdth.dthCoef (m + 1) r θ * Work.Spaces.pthIter r f z θ) h0
  rw [hexp, hsum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro r hr
  have hle := (Classical.choose_spec (hex r)).2 θ
  rw [abs_mul]
  calc |selfdth.dthCoef (m + 1) r θ| * |Work.Spaces.pthIter r f z θ|
      ≤ (Classical.choose (hex r) * |Real.sin (2 * θ)| ^ r)
          * |Work.Spaces.pthIter r f z θ| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = Classical.choose (hex r) * (Real.sin (2 * θ)) ^ r
          * |Work.Spaces.pthIter r f z θ| := by
        rw [abs_of_pos hsin]

end Work.FTS.EllipticEst.remov.Baux
