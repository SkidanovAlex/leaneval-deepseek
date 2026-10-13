/-
  WilE9 / Ift — the "append" continuous linear map.

  Splitting ℝⁿ⁺ᑫ as the product ℝⁿ × ℝᑫ, the map `(v, w) ↦ Fin.append v w` is
  linear and continuous; it is the linear part of the identification of the implicit-function
  variables `(x, y)` with the ambient `Fin (n + q)` coordinates.  The chain rule
  `Work.WilE9.Ift.fderiv_eaEval_append` is stated in terms of it.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Ift

/-- `(v, w) ↦ Fin.append v w`, as a continuous linear map. -/
def appendCLM (n q : ℕ) : ((Fin n → ℝ) × (Fin q → ℝ)) →L[ℝ] (Fin (n + q) → ℝ) :=
  ContinuousLinearMap.pi fun s : Fin (n + q) =>
    Fin.append
      (fun i : Fin n =>
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin q → ℝ)))
      (fun l : Fin q =>
        (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin q → ℝ)))
      s

/-- The value of `appendCLM` on a pair is `Fin.append`. -/
@[simp] theorem appendCLM_apply (n q : ℕ) (v : Fin n → ℝ) (w : Fin q → ℝ) :
    appendCLM n q (v, w) = Fin.append v w := by
  ext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;>
    simp [appendCLM, ContinuousLinearMap.pi_apply]

end Work.WilE9.Ift
