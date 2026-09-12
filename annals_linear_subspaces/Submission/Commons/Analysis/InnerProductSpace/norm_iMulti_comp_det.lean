import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

lemma norm_iMulti_comp_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} (hd : Module.finrank ℝ E = d)
    (f : E →ₗ[ℝ] E) (u : Fin d → E) (hu : LinearIndependent ℝ u) :
    ‖exteriorPower.ιMulti ℝ d (fun i => f (u i))‖ = |LinearMap.det f| * ‖exteriorPower.ιMulti ℝ d u‖ := by
  classical
  -- Because `u` is linearly independent of the right cardinality, it is a basis of `E`.
  let hcard : Fintype.card (Fin d) = Module.finrank ℝ E := by simpa [hd]
  let b : Module.Basis (Fin d) ℝ E := basisOfLinearIndependentOfCardEqFinrank' u hu hcard
  have hb_eq : ⇑b = u := by
    simpa [b] using (coe_basisOfLinearIndependentOfCardEqFinrank' u hu hcard)
  have hub : u = ⇑b := hb_eq.symm
  -- The matrix of `f` in the basis `b`.
  let A : Matrix (Fin d) (Fin d) ℝ := fun i j => b.repr (f (b j)) i
  -- Coordinates in the basis `b`: `f (b j)` is the linear combination with coefficients `A i j`.
  have hcoordb : ∀ j : Fin d, f (b j) = ∑ i : Fin d, A i j • b i := by
    intro j
    dsimp [A]
    exact (Module.Basis.sum_repr b (f (b j))).symm
  -- Wedge products transform by the determinant of the matrix.
  have hwedge_b : exteriorPower.ιMulti ℝ d (fun j => f (b j)) =
      A.det • exteriorPower.ιMulti ℝ d b := by
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul (K := ℝ) (E := E) (k := d)
      (u := b) (A := A) (w := fun j => f (b j)) hcoordb
  -- `A` is the matrix of `f` in the basis `b`, hence its determinant is the determinant of `f`.
  have hA_eq : A = LinearMap.toMatrix b b f := by
    ext i j
    rw [LinearMap.toMatrix_apply]
  have hdet : A.det = LinearMap.det f := by
    rw [hA_eq]
    exact LinearMap.det_toMatrix b f
  -- Transport from `b` back to `u`.
  calc
    ‖exteriorPower.ιMulti ℝ d (fun i => f (u i))‖
        = ‖exteriorPower.ιMulti ℝ d (fun j => f (b j))‖ := by
            congr 2
            funext j
            congr 1
            rw [hub]
    _ = ‖A.det • exteriorPower.ιMulti ℝ d b‖ := by rw [hwedge_b]
    _ = ‖A.det‖ * ‖exteriorPower.ιMulti ℝ d b‖ := by rw [norm_smul]
    _ = |A.det| * ‖exteriorPower.ιMulti ℝ d b‖ := by rw [Real.norm_eq_abs]
    _ = |LinearMap.det f| * ‖exteriorPower.ιMulti ℝ d b‖ := by rw [hdet]
    _ = |LinearMap.det f| * ‖exteriorPower.ιMulti ℝ d u‖ := by
            congr 1
            congr 1
            rw [hb_eq]

end Commons.Analysis.InnerProductSpace