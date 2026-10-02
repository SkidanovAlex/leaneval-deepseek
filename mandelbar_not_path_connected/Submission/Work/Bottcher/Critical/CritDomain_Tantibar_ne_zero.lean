import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Critical

open LeanEval.ComplexAnalysis (Tantibar)

/-- The Green function commutes with the iterates of the tricorn map with the factor `2^n`:
`G_c (T_c^[n] z) = 2^n G_c z`. -/
theorem green_iterate_Tantibar (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.Bottcher.green c z := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Work.Bottcher.Green.green_comm, ih, pow_succ]
      ring

theorem CritDomain_Tantibar_ne_zero (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    ∀ n : ℕ, (LeanEval.ComplexAnalysis.Tantibar c)^[n] z ≠ 0 := by
  intro n hn
  have hiter := green_iterate_Tantibar c z n
  rw [hn, ← Work.Bottcher.greenParam_def] at hiter
  have hgz : 0 ≤ Work.Bottcher.green c z := Work.Bottcher.Green.green_nonneg c z
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hle : Work.Bottcher.green c z ≤ (2 : ℝ) ^ n * Work.Bottcher.green c z := by
    calc Work.Bottcher.green c z = 1 * Work.Bottcher.green c z := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ n * Work.Bottcher.green c z :=
          mul_le_mul_of_nonneg_right hpow hgz
  have : Work.Bottcher.greenParam c < Work.Bottcher.green c z := hz
  linarith [hiter]

end Work.Bottcher.Critical
