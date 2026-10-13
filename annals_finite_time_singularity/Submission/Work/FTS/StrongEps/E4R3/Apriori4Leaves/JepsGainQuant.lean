import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.HkSq_Jeps_step_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/JepsGainQuant.lean` — S3 (PROVED, corollary of `HkSq_Jeps_step_le`)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S3; REVIEW fix F3: range `1 ≤ k ≤ 7`,
corollary of the proved `StrongEps.HkSq_Jeps_step_le`; do NOT use the stub `HkSq_Jeps_succ_le`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **(S3)** quantitative one-derivative gain of `J_ε`: `|J_ε f|²_{k+1} ≤ (Cg/ε)² |f|²_k`. -/
theorem Jeps_gain_quant {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ α ∈ Ioc (0 : ℝ) 1, ∀ k : ℕ, 1 ≤ k → k ≤ 7 → ∀ ε ∈ Ioc (0 : ℝ) 1,
      ∀ f : Fn, (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkSq α (k + 1) (Jeps ρ ε f) ≤ (Cg / ε) ^ 2 * Work.Spaces.HkSq α k f := by
  obtain ⟨C, hC, hstep⟩ := HkSq_Jeps_step_le ρ hρ
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro α hα k hk1 hk7 ε hε f hf hmem
  have hf' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad := hf
  have h := (hstep α hα (k + 1) (by omega) (by omega) ε hε f hf'
    (by simpa using hmem)).2
  simp only [Nat.add_sub_cancel] at h
  have hsq : (Real.sqrt C / ε) ^ 2 = C * (ε⁻¹) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hC.le, div_eq_mul_inv, inv_pow]
  rw [hsq]
  exact h

end Work.FTS.StrongEps.EpsE4Thr.E4R4
