/-
# `N0Aux.B4SepDefs` — the level-`4` separated blocks

The level-`4` energy of a *separated* function `(z,θ) ↦ C θ · B z` factorises: with
`D_θ = dthU` (the angular derivation `sin(2θ)·d/dθ`) and `D_z^q = DzIter q`,

  `HkIntegrand α 4 (C·B) z θ ≤ AngBlk4 α C θ · SlotSum4 B z`,

where

* `AngBlk4 α C` is the angular block `C² sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 4} (dthU^i C)² sin(2θ)^{-γ}`
  (the angular factor produced by `L6Aux.HkIntegrandSepLeGen` at `k = 4`), and
* `SlotSum4 B` is the radial slot sum `Σ_{q ≤ 4} (D_z^q B)² w²`.

This is the level-`4` analogue of `L3Aux.HkIntegrand_sep_le`/`angMaj` (order three) and of
`L6Aux.HkIntegrandSepLeGen`/`StrongPersist.SlotSum` (order six).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false

/-- The angular block at order four: the `η`-weighted square of `C` plus the `γ`-weighted
squares of its `dthU`-jets of orders `1..4`. -/
def AngBlk4 (α : ℝ) (C : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 5,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The radial slot sum at order four: the `w²`-weighted squares of the `D_z`-slots of the
radial profile `B`, up to order `4`. -/
def SlotSum4 (B : ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∑ q ∈ Finset.range 5,
    (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2

@[simp] theorem AngBlk4_apply (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) : AngBlk4 α C θ =
    (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 5,
          (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := rfl

@[simp] theorem SlotSum4_apply (B : ℝ → ℝ) (z : ℝ) : SlotSum4 B z =
    ∑ q ∈ Finset.range 5,
      (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

/-- `AngBlk4` is `angMaj` (order three) plus the order-four jet term. -/
theorem AngBlk4_eq_angMaj_add (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) :
    AngBlk4 α C θ = Work.FTS.StrongPersist.L3Rhs.angMaj α C θ
      + (Work.Spaces.dthU^[4] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  simp only [AngBlk4, Work.FTS.StrongPersist.L3Rhs.angMaj]
  rw [Finset.sum_range_succ, if_pos (show (1 : ℕ) ≤ 4 by norm_num)]
  ring

/-- The `η`-sunmand of `AngBlk4` is nonnegative on `Iθ`. -/
theorem AngBlk4_nonneg {α : ℝ} {C : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ AngBlk4 α C θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [AngBlk4]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  · rw [if_neg h1]

/-- `SlotSum4` is nonnegative. -/
theorem SlotSum4_nonneg (B : ℝ → ℝ) (z : ℝ) : 0 ≤ SlotSum4 B z :=
  Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
