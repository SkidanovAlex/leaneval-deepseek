import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.BSKinetic.dSpace_eq_dBox_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.windowed_mean_free_bounds`

Pointwise/derivative bounds for the windowed mean-free function `z ↦ χ z * (φ1 z − m)`.

`χ` is a smooth cutoff vanishing off the centred box `acube ℓ`, `φ1` is smooth, `|φ1| ≤ S` and
`|∂_k φ1| ≤ S1` on the box, `|χ| ≤ Cχ` and `|∂_k χ| ≤ Dχ` everywhere, and `|m| ≤ S`.  Then the
product `χ · (φ1 − m)` is smooth, compactly supported, vanishes off the box, is bounded by
`Cχ(S+S)`, and its partial derivatives are bounded by `Cχ S1 + Dχ(S+S)`.

The only non-formal point is the derivative bound *outside* the box: there `χ` vanishes on a whole
neighbourhood (the complement of the closed box is open), so `fderiv ℝ χ = 0` and the derivative of
the product vanishes too — this is `fderiv_eq_zero_of_notMem_acube`.
-/

noncomputable section

open scoped ContDiff Topology Real

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

theorem windowed_mean_free_bounds {ℓ : ℝ} {χ φ1 : EuclideanSpace ℝ (Fin 3) → ℝ}
    {m S S1 Cχ Dχ : ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hχcs : HasCompactSupport χ)
    (hφ1 : ContDiff ℝ (⊤ : ENat) φ1)
    (htsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube ℓ → χ z = 0)
    (hS : 0 ≤ S) (hS1 : 0 ≤ S1) (hCχ : 0 ≤ Cχ) (hDχ : 0 ≤ Dχ)
    (hχb : ∀ z : EuclideanSpace ℝ (Fin 3), |χ z| ≤ Cχ)
    (hχd : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
        |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)| ≤ Dχ)
    (hφb : ∀ z ∈ Submission.BoseGases.acube ℓ, |φ1 z| ≤ S)
    (hφd : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)), z ∈ Submission.BoseGases.acube ℓ →
        |fderiv ℝ φ1 z (Submission.BoseGases.kcStdBasis k)| ≤ S1)
    (hm : |m| ≤ S) :
    ContDiff ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) => χ z * (φ1 z - m)) ∧
    HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => χ z * (φ1 z - m)) ∧
    (∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube ℓ →
        χ z * (φ1 z - m) = 0) ∧
    (∀ z : EuclideanSpace ℝ (Fin 3), |χ z * (φ1 z - m)| ≤ Cχ * (S + S)) ∧
    (∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
        |fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => χ z * (φ1 z - m)) z
            (Submission.BoseGases.kcStdBasis k)| ≤ Cχ * S1 + Dχ * (S + S)) := by
  have hSS : (0 : ℝ) ≤ S + S := by linarith
  -- the mean-free part `φ1 - m` is smooth
  have hψ : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => φ1 z - m) :=
    hφ1.sub contDiff_const
  -- 1. smoothness of the product
  have hsm : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => χ z * (φ1 z - m)) :=
    hχ.mul hψ
  -- 2. compact support
  have hcs : HasCompactSupport (fun z : ℝ³ => χ z * (φ1 z - m)) := hχcs.mul_right
  -- 3. vanishing off the box
  have hvanish : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube ℓ → χ z * (φ1 z - m) = 0 := by
    intro z hz
    rw [htsupp z hz, zero_mul]
  -- 4. sup bound
  have hbdd : ∀ z : ℝ³, |χ z * (φ1 z - m)| ≤ Cχ * (S + S) := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · have hφ : |φ1 z - m| ≤ S + S :=
        (abs_sub (φ1 z) m).trans (add_le_add (hφb z hz) hm)
      rw [abs_mul]
      exact mul_le_mul (hχb z) hφ (abs_nonneg _) hCχ
    · rw [hvanish z hz, abs_zero]
      exact mul_nonneg hCχ hSS
  -- 5. derivative bound
  have hderiv : ∀ (k : Fin 3) (z : ℝ³),
      |fderiv ℝ (fun z : ℝ³ => χ z * (φ1 z - m)) z
          (Submission.BoseGases.kcStdBasis k)| ≤ Cχ * S1 + Dχ * (S + S) := by
    intro k z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · -- inside the box: the Leibniz rule and the bounds on `χ`, `φ1`
      have hzχ : DifferentiableAt ℝ χ z := hχ.differentiable (by norm_num) z
      have hzψ : DifferentiableAt ℝ (fun y : ℝ³ => φ1 y - m) z :=
        hψ.differentiable (by norm_num) z
      have hCLM : fderiv ℝ (fun y : ℝ³ => χ y * (φ1 y - m)) z
          = (φ1 z - m) • fderiv ℝ χ z + χ z • fderiv ℝ φ1 z := by
        rw [show (fun y : ℝ³ => χ y * (φ1 y - m))
              = χ * (fun y : ℝ³ => φ1 y - m) from rfl,
            fderiv_mul hzχ hzψ, fderiv_sub_const m]
        exact add_comm _ _
      have hval : fderiv ℝ (fun y : ℝ³ => χ y * (φ1 y - m)) z
            (Submission.BoseGases.kcStdBasis k)
          = (φ1 z - m) * fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)
            + χ z * fderiv ℝ φ1 z (Submission.BoseGases.kcStdBasis k) := by
        rw [hCLM]
        simp [smul_eq_mul]
      have hφz : |φ1 z - m| ≤ S + S :=
        (abs_sub (φ1 z) m).trans (add_le_add (hφb z hz) hm)
      rw [hval]
      calc |(φ1 z - m) * fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)
              + χ z * fderiv ℝ φ1 z (Submission.BoseGases.kcStdBasis k)|
          ≤ |(φ1 z - m) * fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)|
            + |χ z * fderiv ℝ φ1 z (Submission.BoseGases.kcStdBasis k)| :=
              abs_add_le _ _
        _ = |φ1 z - m| * |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)|
            + |χ z| * |fderiv ℝ φ1 z (Submission.BoseGases.kcStdBasis k)| := by
              rw [abs_mul, abs_mul]
        _ ≤ (S + S) * Dχ + Cχ * S1 :=
              add_le_add (mul_le_mul hφz (hχd k z) (abs_nonneg _) hSS)
                (mul_le_mul (hχb z) (hφd k z hz) (abs_nonneg _) hCχ)
        _ = Cχ * S1 + Dχ * (S + S) := by ring
    · -- outside the box: the product is locally zero, so is its derivative
      have hz0 : fderiv ℝ (fun y : ℝ³ => χ y * (φ1 y - m)) z = 0 :=
        fderiv_eq_zero_of_notMem_acube (ℓ := ℓ) (ψ := fun y : ℝ³ => χ y * (φ1 y - m))
          hvanish z hz
      rw [hz0, show (0 : ℝ³ →L[ℝ] ℝ) (Submission.BoseGases.kcStdBasis k) = 0 from rfl,
        abs_zero]
      exact add_nonneg (mul_nonneg hCχ hS1) (mul_nonneg hDχ hSS)
  exact ⟨hsm, hcs, hvanish, hbdd, hderiv⟩

end Work.BSKinetic
