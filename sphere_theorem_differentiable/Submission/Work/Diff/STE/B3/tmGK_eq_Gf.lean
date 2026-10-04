import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.transport_Mf_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.Diff.STE.B3

theorem tmGK_eq_Gf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (htgt : Work.Diff.STE.flatToE (I := I) (M := M) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0) :
    Work.Diff.STE.B3.tmGK (I := I) (M := M) D j z
        (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
      = Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z) := by
  -- The frame matrix is invertible, so the clamped inverse `Finvf` is the honest inverse.
  have hdetU : IsUnit (Matrix.of (Ff (I := I) (M := M) D j z)).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hdetT : IsUnit ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).det := by
    rwa [Matrix.det_transpose]
  -- The frame-change identity `Mf = Ff · Gf · Ffᵀ` in matrix form (it only needs `htgt`).
  have hkeyL : Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
    rw [Mf_eq_of_target (I := I) (M := M) D h j a b htgt]
    conv_rhs => rw [Finset.sum_comm]
  have hkey : Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * (Matrix.of (Gf (I := I) (M := M) D h j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) := by
    rw [hkeyL, Matrix.mul_assoc]
  -- Conjugate by the inverse frame matrix.
  have h1 : (Matrix.of (Ff (I := I) (M := M) D j z))⁻¹
      * Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
    rw [hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mul]
  have h2 : Matrix.of (Finvf (I := I) (M := M) D j z)
      * Matrix.of (Mf (I := I) (M := M) D h j z)
      * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ
      = Matrix.of (Gf (I := I) (M := M) D h j z) := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.transpose_nonsing_inv, h1,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]
  simpa only [tmGK] using h2

end Work.Diff.STE.B3
