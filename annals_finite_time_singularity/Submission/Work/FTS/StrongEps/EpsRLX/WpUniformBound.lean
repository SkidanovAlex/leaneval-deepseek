import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileFacts
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-!
# `Work.FTS.StrongEps.EpsRLX.WpUniformBound`

**A uniform `ℋ⁵`-bound on the projected-mollified profile `Wp ρ ε u = Pz (J_ε u)`.**

The datum `ProfileData α C₀ B ε ρ u` bounds only the *order-`6`* norm of `u`
(`HkNorm α 6 u ≤ B`).  The profile facts (`ProfileFacts`) give

* `EpsSq α u ≤ C/(γ-1)² · HkSq α 1 u` (the `X`-norm of the datum with the `1/(γ-1)`-price),
* `HkSq α 6 (Wp ρ ε u) ≤ C · (C/ε)¹² · EpsSq α u` (one factor `C/ε` per derivative),

and `HkSq α 1 u ≤ HkSq α 6 u = (HkNorm α 6 u)² ≤ B²`.  Hence

  `HkSq α 5 (Wp ρ ε u) ≤ HkSq α 6 (Wp ρ ε u) ≤ (C/(γ-1) · (C/ε)⁶ · B)²`,

and taking square roots (the bound being nonnegative) gives the statement.  In particular the
`ℋ⁵`-size of the profile is proportional to `B`, uniformly in `α` and `ε`, with the sole
`(C/ε)⁶` price of the mollifier and the `1/(γ-1)` price of the angular Hardy inequality.
-/

/-- The elementary identity behind the final constant: the product appearing in the chain of
inequalities is the square of the stated bound.  (Pure field algebra; `ring` cannot see it
directly because it treats `((γ-1)²)⁻¹` and `((γ-1)⁻¹)²` as distinct normal forms, so the
divisions are unfolded first.) -/
private theorem sq_prod_eq (C d e B : ℝ) :
    C * (C / e) ^ 12 * (C / d ^ 2 * B ^ 2) = (C / d * (C / e) ^ 6 * B) ^ 2 := by
  rw [div_eq_mul_inv]
  ring

theorem WpUniformBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, 0 ≤ B →
      ∀ {u : Work.FTS.Galerkin.Fn}, Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsRLX.ProfileFacts ρ hρ
  refine ⟨C, hCpos, ?_⟩
  intro α hα ε hε C₀ B hB u hd
  obtain ⟨hmem_u, hsq_u, h3, hmem_W, hsq_W, htr, hmem7W, h8⟩ := hC α hα ε hε hd
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- `ℋ⁶`-membership of the projected-mollified profile, read off the order-`7` fact
  have hmem6W : Work.Spaces.HkMem α 6 (Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hd.cls.reg 6 (by norm_num) hmem7W
  have h56 : Work.Spaces.HkSq α 5 (Wp ρ ε u) ≤ Work.Spaces.HkSq α 6 (Wp ρ ε u) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem6W
  have h16 : Work.Spaces.HkSq α 1 u ≤ Work.Spaces.HkSq α 6 u :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hd.hkmem
  -- the datum bound `HkNorm α 6 u ≤ B` squared
  have h6B : Work.Spaces.HkSq α 6 u ≤ B ^ 2 := by
    have h := hd.hknorm
    rw [Work.Spaces.HkNorm] at h
    calc Work.Spaces.HkSq α 6 u = (Real.sqrt (Work.Spaces.HkSq α 6 u)) ^ 2 :=
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 u)).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hcf : 0 ≤ C * (C / ε) ^ 12 :=
    mul_nonneg hCpos.le (pow_nonneg (div_nonneg hCpos.le hε0.le) 12)
  -- the chain of profile facts
  have hchain : Work.Spaces.HkSq α 5 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    refine le_trans h56 ?_
    refine le_trans h3 (mul_le_mul_of_nonneg_left ?_ hcf)
    exact le_trans hsq_u (mul_le_mul_of_nonneg_left (le_trans h16 h6B)
      (div_nonneg hCpos.le (pow_pos hγpos 2).le))
  have ht : 0 ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B :=
    mul_nonneg (mul_nonneg (div_nonneg hCpos.le hγpos.le)
      (pow_nonneg (div_nonneg hCpos.le hε0.le) 6)) hB
  have heq := sq_prod_eq C (Work.Spaces.gam α - 1) ε B
  rw [Work.Spaces.HkNorm, Real.sqrt_le_iff]
  exact ⟨ht, le_trans hchain (le_of_eq heq)⟩

end Work.FTS.StrongEps.EpsRLX
