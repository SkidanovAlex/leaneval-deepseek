import Mathlib
import Submission.GeometryOfNumbers.WedgeLemma1a
import Submission.GeometryOfNumbers.WedgeHigherBlocks

/-!
# Model Proposition 1, part 1 (exp form) — flow estimates for planes close to x₀

The paper's Prop 1 part 1: for a rational `k`-plane `v` close to `x` and `t > 0` with
`e^{-t(1/ℓ+1/(d−ℓ))} = d(v,x)`, the pure tensor `ṽ` representing `v` satisfies
`‖π₊(a_t ṽ)‖ ≳ ‖a_t ṽ‖` (block-0 dominance) and `‖a_t ṽ‖ ≲ e^{-tk/ℓ} H(v)`.

Model statement (coordinate model, `x = x₀ = modelX ℓ`, flow coefficients
`a = exp(−t/ℓ)`, `b = exp(t/(d−ℓ))`): for a pure tensor `w = ιMulti u` of a plane transverse
to `x₀ᗮ` whose first block dominates (`b·‖w₁‖ ≤ a·‖w₀‖`), we get
* `‖a_t w‖ ≤ ((k+1)·2^k) · a^k · ‖w₀‖`   (`model_prop1_part1_upper`, from
  `WedgeHigherBlocks.pureTensor_flow_le`), and
* `‖block₀(a_t w)‖ ≥ ‖a_t w‖/((k+1)·2^k)`   (`model_prop1_part1_dominance`, from
  `pureTensor_flow_block0_dominance`).

The cone hypothesis follows from distance smallness via the pure-tensor Lemma-1(a) converse
(`WedgeLemma1a.pureTensor_blockRatio_le_planeResidual`): if `δ = planeResidual V x₀ ≤ 1/2`
and `2√k·δ ≤ e^{-t(1/ℓ+1/(d−ℓ))}` then `‖w₁‖ ≤ 2√k·δ·‖w₀‖ ≤ e^{-t(1/ℓ+1/(d−ℓ))}‖w₀‖`, i.e.
`b·‖w₁‖ ≤ a·‖w₀‖` (`blockRatio_small_of_distSmall`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

namespace Submission.ModelProp1Part1

variable {d : ℕ}

/-- **Model Prop 1 part 1, flow upper bound (exp form)**: with flow coefficients
`a = exp(-t/ℓ)` (on `x₀`) and `b = exp(t/(d−ℓ))` (on `x₀ᗮ`) and the cone hypothesis
`b·‖w₁‖ ≤ a·‖w₀‖`, the flowed pure tensor satisfies `‖a_t w‖ ≤ (k+1)·2^k·a^k·‖w₀‖`. -/
theorem model_prop1_part1_upper {d k ℓ : ℕ} (hk : 0 < k) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖)
    (t : ℝ) (hcone : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
        Real.exp (-t / (ℓ : ℝ)) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    ‖exteriorPower.map k (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (exteriorPower.ιMulti ℝ k u)‖ ≤
      ((k : ℝ) + 1) * (2 : ℝ) ^ k * (Real.exp (-t / (ℓ : ℝ))) ^ k *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  have ha : 0 < Real.exp (-t / (ℓ : ℝ)) := Real.exp_pos _
  have hb : 0 ≤ Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := le_of_lt (Real.exp_pos _)
  simpa using (Submission.WedgeBlocks.pureTensor_flow_le (d := d) (k := k) ℓ hk
    (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ha hb u hu hbot hX hcone)

/-- **Model Prop 1 part 1, block-0 dominance (exp form)**: same hypotheses ⇒
`‖block₀(a_t w)‖ ≥ ‖a_t w‖ / ((k+1)·2^k)`. -/
theorem model_prop1_part1_dominance {d k ℓ : ℕ} (hk : 0 < k) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖)
    (t : ℝ) (hcone : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
        Real.exp (-t / (ℓ : ℝ)) *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
          (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (exteriorPower.ιMulti ℝ k u)) 0‖ ≥
      ‖exteriorPower.map k (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
        (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (exteriorPower.ιMulti ℝ k u)‖ /
        (((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  have ha : 0 < Real.exp (-t / (ℓ : ℝ)) := Real.exp_pos _
  have hb : 0 ≤ Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := le_of_lt (Real.exp_pos _)
  simpa using (Submission.WedgeBlocks.pureTensor_flow_block0_dominance (d := d) (k := k) ℓ hk
    (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ha hb u hu hbot hX hcone)

/-- **Distance smallness ⇒ cone hypothesis (Lemma 1(a) converse + exp algebra)**:
if `δ = planeResidual V x₀ ≤ 1/2` and `2√k·δ ≤ e^{-t(1/ℓ+1/(d−ℓ))}` then
`e^{t/(d−ℓ)}·‖w₁‖ ≤ e^{-t/ℓ}·‖w₀‖` (the cone hypothesis of the flow theorems). -/
theorem blockRatio_small_of_distSmall {d k ℓ : ℕ} (hk : 0 < k) (u : Fin k → RD d)
    (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥)
    (hδ12 : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
        (Submission.WedgeBlocks.modelX ℓ) ≤ 1 / 2)
    (t : ℝ) (hδexp : (2 : ℝ) * Real.sqrt (k : ℝ) *
        Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
          (Submission.WedgeBlocks.modelX ℓ) ≤
        Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ))))) :
    Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      Real.exp (-t / (ℓ : ℝ)) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  classical
  let X : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖
  let Y : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖
  let δ : ℝ := Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
    (Submission.WedgeBlocks.modelX ℓ)
  let S : ℝ := (1 : ℝ) / (ℓ : ℝ) + 1 / ((d : ℝ) - (ℓ : ℝ))
  have hδ12' : δ ≤ 1 / 2 := by simpa [δ] using hδ12
  have hδexp' : (2 : ℝ) * Real.sqrt (k : ℝ) * δ ≤ Real.exp (-t * S) := by
    simpa [δ, S] using hδexp
  have hX0 : 0 ≤ X := by dsimp [X]; exact norm_nonneg _
  have hY1 : Y ≤ (2 : ℝ) * Real.sqrt (k : ℝ) * δ * X := by
    have h := Submission.WedgeLemma1a.block1_le_mul_planeResidual (d := d) (k := k) ℓ hk u hu hbot hδ12
    simpa [X, Y, δ] using h
  have hYexp : Y ≤ Real.exp (-t * S) * X := by
    have hmid : ((2 : ℝ) * Real.sqrt (k : ℝ) * δ) * X ≤ Real.exp (-t * S) * X :=
      mul_le_mul_of_nonneg_right hδexp' hX0
    calc
      Y ≤ (2 : ℝ) * Real.sqrt (k : ℝ) * δ * X := hY1
      _ = ((2 : ℝ) * Real.sqrt (k : ℝ) * δ) * X := by ring
      _ ≤ Real.exp (-t * S) * X := hmid
  have hYexp2 : Real.exp (t * S) * Y ≤ X := by
    have hpos : 0 < Real.exp (t * S) := Real.exp_pos _
    calc
      Real.exp (t * S) * Y ≤ Real.exp (t * S) * (Real.exp (-t * S) * X) :=
            mul_le_mul_of_nonneg_left hYexp (le_of_lt hpos)
      _ = (Real.exp (t * S) * Real.exp (-t * S)) * X := by ring
      _ = X := by
            have hid : Real.exp (t * S) * Real.exp (-t * S) = 1 := by
              rw [← Real.exp_add]
              simp
            rw [hid, one_mul]
  have hident : Real.exp (-t / (ℓ : ℝ)) * Real.exp (t * S) = Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
    dsimp [S]
    rw [← Real.exp_add]
    congr 1
    ring
  have hfinal := mul_le_mul_of_nonneg_left hYexp2 (le_of_lt (Real.exp_pos (-t / (ℓ : ℝ))))
  change Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) * Y ≤ Real.exp (-t / (ℓ : ℝ)) * X
  calc
    Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) * Y
        = Real.exp (-t / (ℓ : ℝ)) * (Real.exp (t * S) * Y) := by
            rw [← hident, ← mul_assoc]
    _ ≤ Real.exp (-t / (ℓ : ℝ)) * X := hfinal

end Submission.ModelProp1Part1
