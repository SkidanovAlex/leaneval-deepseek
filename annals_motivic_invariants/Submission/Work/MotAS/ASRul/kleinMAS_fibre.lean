import Mathlib
import Submission.Work.MotAS.ASRul.det_submatrix_kleinMAS
import Submission.Work.MotK.CensusFibre.kleinFibre_eq_ker
import Submission.Work.MotAS.ASRulingMainAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRul

theorem kleinMAS_fibre (K : Type) [Field K] [CharP K 5] (a b g : K) (y c : Fin 5 → K)
    (hy : Work.MotAS.kleinPAS a b g y ≠ 0) (hc : c ≠ 0) :
    Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) c = 0 ↔
      ∃ μ : K, μ ≠ 0 ∧ ∀ i, Work.MotAS.kleinPAS a b g y i = μ * c i := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hker : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y)
      (Work.MotAS.kleinPAS a b g y) = 0 :=
    Work.MotAS.kleinMAS_mulVec_kleinPAS a b g h5 y
  constructor
  · -- Sufficiency: `kleinPAS y ≠ 0` makes some principal `4 × 4` minor invertible, so the kernel
    -- of `kleinMAS y` is one-dimensional and contains both `c` and `kleinPAS y`.
    intro hM
    obtain ⟨k, hk⟩ : ∃ k : Fin 5, Work.MotAS.kleinPAS a b g y k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (by funext i; exact h i)
    have hdet : ((Work.MotAS.ASRul.kleinMAS a b g y).submatrix k.succAbove
        k.succAbove).det ≠ 0 := by
      rw [Work.MotAS.ASRul.det_submatrix_kleinMAS K a b g y k]
      exact neg_ne_zero.mpr (pow_ne_zero 2 hk)
    have hprop : Work.MotAS.kleinPAS a b g y k • c = c k • Work.MotAS.kleinPAS a b g y :=
      Work.MotK.CensusFibre.smul_eq_smul_of_mulVec_eq_zero hker hM hdet
    have hck : c k ≠ 0 := by
      intro h0
      have h1 : Work.MotAS.kleinPAS a b g y k • c = 0 := by rw [hprop, h0, zero_smul]
      exact hc ((smul_eq_zero.mp h1).resolve_left hk)
    refine ⟨(c k)⁻¹ * Work.MotAS.kleinPAS a b g y k,
      mul_ne_zero (inv_ne_zero hck) hk, fun i => ?_⟩
    have hp : Work.MotAS.kleinPAS a b g y =
        ((c k)⁻¹ * Work.MotAS.kleinPAS a b g y k) • c := by
      have h2 := congrArg (fun w : Fin 5 → K => (c k)⁻¹ • w) hprop.symm
      simpa [smul_smul, inv_smul_smul₀ hck] using h2
    simpa using congrFun hp i
  · -- Necessity: `kleinPAS y = μ • c` with `μ ≠ 0`, and `kleinMAS y · kleinPAS y = 0`.
    rintro ⟨μ, hμ, hμ'⟩
    funext i
    have hgen : (∑ j, Work.MotAS.ASRul.kleinMAS a b g y i j * (μ * c j)) =
        ∑ j, Work.MotAS.ASRul.kleinMAS a b g y i j * Work.MotAS.kleinPAS a b g y j :=
      Finset.sum_congr rfl fun j _ => by rw [hμ' j]
    have h1 : (∑ j, Work.MotAS.ASRul.kleinMAS a b g y i j * (μ * c j)) = 0 := by
      rw [hgen]
      exact congrFun hker i
    have h2 : μ * (∑ j, Work.MotAS.ASRul.kleinMAS a b g y i j * c j) = 0 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun j _ => by ring).trans h1
    exact (mul_eq_zero.mp h2).resolve_left hμ

end Work.MotAS.ASRul
