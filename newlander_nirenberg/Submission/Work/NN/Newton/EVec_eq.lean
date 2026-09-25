import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Core.DbarCnPertAux

namespace Work.NN.Newton

/-- The derivative of the `j`-th coordinate function `y ↦ y j` is the `j`-th projection. -/
lemma fderiv_coordProj (n : ℕ) (j : Fin n) (z : Work.NN.Core.Cn n) :
    fderiv ℝ (fun y : Work.NN.Core.Cn n => y j) z
      = (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ) := by
  rw [show (fun y : Work.NN.Core.Cn n => y j)
        = (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ) from rfl]
  exact ContinuousLinearMap.fderiv _

/-- **The residual vector, coordinatewise.**  Unfolding `EVec` and `Lcoef`, the `j`-th component
of `E_k = (Lcoef A (·)_j k − ∂̄_k v_j)_j` is `(i/2)·(A z e_k)_j − ∂̄_k v_j z`, since the
derivative of the coordinate functional `y ↦ y_j` is the projection onto the `j`-th coordinate.
Hence `E_k = (i/2) • (A z e_k) − (∂̄_k v_j)_j` as a vector in `ℂⁿ`. -/
theorem EVec_eq {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (v : Fin n → Work.NN.Core.Cn n → ℂ) (k : Fin n) (z : Work.NN.Core.Cn n) :
    Work.NN.Newton.EVec A v k z
      = (Complex.I / 2) • (A z (Pi.single k (1 : ℂ)))
        - (fun j => Work.CR.Flat.dbarCoord k (v j) z) := by
  funext j
  simp only [Work.NN.Newton.EVec, Work.NN.Core.Lcoef, Pi.sub_apply, Pi.smul_apply]
  rw [fderiv_coordProj n j z]
  simp

end Work.NN.Newton
