import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.LinearAlgebra.Orthogonal

open LinearMap

/-- Over `ℝ` the determinant of the adjoint of an endomorphism equals its determinant. -/
lemma det_adjoint_eq_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) :
    LinearMap.det A.adjoint = LinearMap.det A := by
  rw [← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ E).toBasis A.adjoint,
      ← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ E).toBasis A]
  rw [LinearMap.toMatrix_adjoint]
  rw [Matrix.det_conjTranspose]
  simp

/-- The determinant of `1 - T` equals `-det T` for an endomorphism `T` of an odd-dimensional
real vector space. -/
lemma det_one_sub_eq_neg_det_sub_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hodd : Odd (Module.finrank ℝ E)) (T : E →ₗ[ℝ] E) :
    LinearMap.det (1 - T) = -LinearMap.det (T - 1) := by
  have h : (1 : E →ₗ[ℝ] E) - T = -(T - 1) := (neg_sub T 1).symm
  rw [h]
  rw [← neg_one_smul ℝ (T - 1), LinearMap.det_smul, hodd.neg_one_pow, neg_one_mul]

theorem odd_dim_det_one_fixed_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) (hodd : Odd (Module.finrank ℝ E))
    (hdet : LinearMap.det (f : E →ₗ[ℝ] E) = 1) :
    ∃ v : E, v ≠ 0 ∧ f v = v := by
  set T : E →ₗ[ℝ] E := (f : E →ₗ[ℝ] E) with hT
  have hadj : T.adjoint = (f.symm : E →ₗ[ℝ] E) := by
    rw [hT]; exact LinearIsometryEquiv.adjoint_toLinearMap_eq_symm f
  have hTadj : LinearMap.adjoint (T - 1) = T.adjoint - 1 := by
    change star (T - 1) = T.adjoint - 1
    rw [star_sub, star_one]
    rfl
  have hSdet : LinearMap.det T.adjoint = 1 := by
    rw [det_adjoint_eq_det, hT]; exact hdet
  have hST : T.adjoint * T = 1 := by
    rw [hadj, hT]
    ext x
    simp
  have hmul : T.adjoint - 1 = T.adjoint * (1 - T) := by
    rw [mul_sub, mul_one, hST]
  have h1 : LinearMap.det (T - 1) = LinearMap.det (T.adjoint - 1) := by
    rw [← det_adjoint_eq_det (T - 1), hTadj]
  have h2 : LinearMap.det (T.adjoint - 1) =
      LinearMap.det T.adjoint * LinearMap.det (1 - T) := by
    rw [hmul]; exact map_mul LinearMap.det _ _
  have hsign : LinearMap.det (1 - T) = -LinearMap.det (T - 1) :=
    det_one_sub_eq_neg_det_sub_one hodd T
  have hmain : LinearMap.det (T - 1) = -LinearMap.det (T - 1) := by
    calc LinearMap.det (T - 1)
        = LinearMap.det (T.adjoint - 1) := h1
      _ = LinearMap.det T.adjoint * LinearMap.det (1 - T) := h2
      _ = 1 * LinearMap.det (1 - T) := by rw [hSdet]
      _ = LinearMap.det (1 - T) := by rw [one_mul]
      _ = -LinearMap.det (T - 1) := hsign
  have key : LinearMap.det (T - 1) = 0 := by linarith [hmain]
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at key
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff (T - 1).ker).mp key
  rw [LinearMap.mem_ker] at hv
  have hTv : T v = v := by
    have h' := sub_eq_zero.mp hv
    simpa using h'
  refine ⟨v, hvne, ?_⟩
  simpa [hT] using hTv

end Commons.LinearAlgebra.Orthogonal