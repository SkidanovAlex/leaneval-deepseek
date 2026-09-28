import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.Sig2.det_gram_of_int_basis

namespace Work.HP

open Matrix in
/-- Composing a lattice map with the unimodular linear map given by the matrix of a `ℤ`-basis
`e` of `ℤ^R` does not change the covolume. -/
theorem latCovol_comp_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (e : Module.Basis (Fin R) ℤ (Fin R → ℤ)) (Φ : LatMap (ι := ι) R) :
    latCovol (Φ.comp (Matrix.mulVecLin (Matrix.of (fun j i : Fin R => ((e i) j : ℝ))))) =
      latCovol Φ := by
  set A : Matrix (Fin R) (Fin R) ℝ := Matrix.of (fun j i : Fin R => ((e i) j : ℝ)) with hA
  have hbij : Function.Bijective (fun x : Fin R → ℤ => ∑ j, x j • e j) := by
    have hfun : (fun x : Fin R → ℤ => ∑ j, x j • e j) = e.equivFun.symm := by
      funext x; rw [Module.Basis.equivFun_symm_apply]
    rw [hfun]
    exact e.equivFun.symm.bijective
  have hrow : ∀ i : Fin R, A *ᵥ (Pi.basisFun ℝ (Fin R) i) = fun j => ((e i) j : ℝ) := by
    intro i
    rw [Pi.basisFun_apply, Matrix.mulVec_single_one]
    funext j
    simp [hA, Matrix.col]
  have hΨ : ∀ i : Fin R, (Φ.comp (Matrix.mulVecLin A)) (Pi.basisFun ℝ (Fin R) i)
      = Φ (fun k => ((e i) k : ℝ)) := by
    intro i
    rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, hrow i]
  have hgramΨ : Matrix.of (fun i j : Fin R =>
        inner ℝ ((Φ.comp (Matrix.mulVecLin A)) (Pi.basisFun ℝ (Fin R) i))
               ((Φ.comp (Matrix.mulVecLin A)) (Pi.basisFun ℝ (Fin R) j)))
      = Matrix.gram ℝ (fun i : Fin R => Φ (fun k => ((e i) k : ℝ))) := by
    ext i j
    rw [Matrix.of_apply, Matrix.gram_apply, hΨ i, hΨ j]
  have h1 : latCovol (Φ.comp (Matrix.mulVecLin A)) =
      Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin R => Φ (fun k => ((e i) k : ℝ))))) := by
    rw [latCovol, hgramΨ]
  have h2 : latCovol Φ =
      Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i)))) := by
    rw [latCovol]
    rw [show (Matrix.of (fun i j : Fin R =>
          inner ℝ (Φ (Pi.basisFun ℝ (Fin R) i)) (Φ (Pi.basisFun ℝ (Fin R) j))))
        = Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i)) from by
      ext i j
      rw [Matrix.of_apply, Matrix.gram_apply]]
  rw [h1, h2, Work.HP.Sig2.det_gram_of_int_basis e hbij Φ]

end Work.HP
