import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenRes
import Submission.Work.Idx.WPenPsi
import Submission.Work.Idx.blkPenProjDefs
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.Idx.circleIntegral_const
import Submission.Work.Idx.wRow_mul_wInv
import Submission.Work.Idx.wRow_delta_mul_wBA

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval Matrix.Norms.Operator

noncomputable section

/-- **The coefficient row annihilates the pencil projection (integral form).**

`wRow n D c : Matrix (Fin n) (Fin (D+1) × Fin n)` is the block row whose `k`-th block is `c_k`,
`blkPenProj X A B` is the Riesz projection `(2πi)⁻¹ ∮_{|z|=1} (z•A+B)⁻¹ A dz` of the matrix pencil
over `C(X, ℂ)`, and `wBA n D`/`wBB n D c` are the W linearisation of `c` (the pencil is
`z • wBA + wBB`), whose `wQ n D c z = ∑_j z^j • c_j` is the polynomial matrix it linearises.

Claim: under `hQ` (`wQ n D c` invertible on the unit circle, i.e. the pencil is,
`Work.Idx.wBlk_isUnit_of_wQ`), the row of coefficients annihilates the projection:
`wRow n D c * blkPenProj X (wBA n D) (wBB n D c) = 0`.

Route (integral computation): `wRow P = (2πi)⁻¹ • ∮ (wRow * pResA A B z) dz` — pull the constant
`wRow n D c` through the circle integral by `Work.KT.Fund.circleIntegral_const_mul` (integrability
again from `Work.Idx.continuousOn_res` and the unit hypothesis).  Pointwise, using
`Work.Idx.wInv_eq_ringInverse` (which needs `IsUnit (wQ n D c z)`, from `hQ`), the integrand is
`wRow n D c * wInv n D c z (Ring.inverse (wQ n D c z)) * wBA n D`.  The first factor is computed by
`Work.Idx.sum_c_mul_bInv`: blockwise `(wRow · wInv) j = if (j : ℕ) = D then 1 else 0`, i.e. it is
the block row `wRow n D (fun j => if (j : ℕ) = D then 1 else 0)` (the identity only in the last
block); multiplying that on the right by `wBA n D` gives `0` because the last block *row* of
`wBA n D` vanishes (`Work.Idx.bA_apply_last`, `blkOf_wBA`).  Then
`circleIntegral.integral_congr` finishes. -/
theorem wRow_mul_blkPenProj {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) :
    wRow n D c * blkPenProj X (wBA (A := C(X, ℂ)) n D) (wBB n D c) = 0 := by
  classical
  -- The pointwise algebraic fact: the integrand is annihilated by the row of coefficients.
  have hpt : ∀ z : ℂ, ‖z‖ = 1 →
      wRow n D c * (Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
        * wBA (A := C(X, ℂ)) n D) = 0 := by
    intro z hz
    have hQz : IsUnit (wQ (A := C(X, ℂ)) n D c z) := hQ z hz
    have hE : wQ (A := C(X, ℂ)) n D c z * Ring.inverse (wQ (A := C(X, ℂ)) n D c z) = 1 :=
      Ring.mul_inverse_cancel _ hQz
    rw [wInv_eq_ringInverse n D c z hQz, ← Matrix.mul_assoc, wRow_mul_wInv n D c z hE,
      wRow_delta_mul_wBA n D]
  -- The pencil is invertible on the unit circle.
  have hunit : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • wBA (A := C(X, ℂ)) n D + wBB n D c) := by
    intro z hz
    have hQz : IsUnit (wQ (A := C(X, ℂ)) n D c z) := hQ z hz
    have hE : wQ (A := C(X, ℂ)) n D c z * Ring.inverse (wQ (A := C(X, ℂ)) n D c z) = 1 :=
      Ring.mul_inverse_cancel _ hQz
    have hmul := wBlk_mul_wInv n D c z hE
    have hdet : (z • wBA (A := C(X, ℂ)) n D + wBB n D c).det *
        (wInv n D c z (Ring.inverse (wQ (A := C(X, ℂ)) n D c z))).det = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    exact ⟨⟨_, _, hdet, by rw [mul_comm, hdet]⟩, rfl⟩
  -- Continuity of the integrand on the unit circle.
  have hcont : ContinuousOn (fun z : ℂ => Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
      * wBA (A := C(X, ℂ)) n D) (Metric.sphere (0 : ℂ) 1) :=
    @Work.Idx.continuousOn_res (Matrix (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Matrix.instCompleteSpace (Fin (D + 1) × Fin n) (Fin (D + 1) × Fin n) C(X, ℂ))
      (wBA (A := C(X, ℂ)) n D) (wBB n D c) hunit
  -- The projection is the circle integral of `(2πi)⁻¹ • (zA+B)⁻¹A`.
  have hbridge : blkPenProj X (wBA (A := C(X, ℂ)) n D) (wBB n D c)
      = ∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • (Ring.inverse
          (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) := by
    rw [blkPenProj_eq]
    exact (circleIntegral.integral_smul (2 * Real.pi * Complex.I)⁻¹ (fun z : ℂ =>
      Work.KT.Idx.pResA (wBA (A := C(X, ℂ)) n D) (wBB n D c) z) 0 1).symm
  -- The coefficient row annihilates the circle integral.
  have hmain : wRow n D c * (∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • (Ring.inverse
      (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D)) = 0 := by
    apply Matrix.ext
    intro a q
    obtain ⟨i, β⟩ := q
    rw [Matrix.zero_apply, Matrix.mul_apply]
    have hFint : CircleIntegrable (fun z : ℂ => (2 * Real.pi * Complex.I)⁻¹ • (Ring.inverse
        (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D)) 0 1 :=
      (hcont.const_smul (2 * Real.pi * Complex.I)⁻¹).circleIntegrable zero_le_one
    have hentry : ∀ p : Fin (D + 1) × Fin n, ContinuousOn (fun z : ℂ => (Ring.inverse
        (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β))
        (Metric.sphere (0 : ℂ) 1) := by
      intro p
      refine ((BlkPen.matEntryCLM (X := X) p (i, β)).continuous.comp_continuousOn hcont).congr
        (fun z _ => ?_)
      rfl
    have hint : ∀ p : Fin (D + 1) × Fin n, CircleIntegrable (fun z : ℂ => (Ring.inverse
        (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β)) 0 1 :=
      fun p => (hentry p).circleIntegrable zero_le_one
    have hintS : ∀ p : Fin (D + 1) × Fin n, CircleIntegrable (fun z : ℂ =>
        (2 * Real.pi * Complex.I)⁻¹ • ((Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
          * wBA (A := C(X, ℂ)) n D) p (i, β))) 0 1 :=
      fun p => ((hentry p).const_smul (2 * Real.pi * Complex.I)⁻¹).circleIntegrable zero_le_one
    have hstep1 : ∀ p : Fin (D + 1) × Fin n,
        ((∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • (Ring.inverse
            (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D)) p (i, β))
          = ∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • ((Ring.inverse
              (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β)) := by
      intro p
      rw [BlkPen.circleIntegral_apply _ 0 1 p (i, β) hFint]
      exact circleIntegral.integral_congr zero_le_one (fun z _ => Matrix.smul_apply _ _ _ _)
    rw [Finset.sum_congr rfl (fun p _ => congrArg (fun x => wRow n D c a p * x) (hstep1 p))]
    have hstep2 : ∀ p : Fin (D + 1) × Fin n,
        wRow n D c a p * (∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • ((Ring.inverse
            (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β)))
          = ∮ z in C(0, 1), (2 * Real.pi * Complex.I)⁻¹ • (wRow n D c a p * ((Ring.inverse
              (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β))) := by
      intro p
      rw [(Work.KT.Fund.circleIntegral_const_mul (wRow n D c a p) (fun z : ℂ =>
        (2 * Real.pi * Complex.I)⁻¹ • ((Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
          * wBA (A := C(X, ℂ)) n D) p (i, β))) 0 1 (hintS p)).symm]
      exact circleIntegral.integral_congr zero_le_one
        (fun z _ => Algebra.mul_smul_comm (2 * Real.pi * Complex.I)⁻¹ (wRow n D c a p)
          ((Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
            * wBA (A := C(X, ℂ)) n D) p (i, β)))
    rw [Finset.sum_congr rfl (fun p _ => hstep2 p)]
    have hint2 : ∀ p ∈ (Finset.univ : Finset (Fin (D + 1) × Fin n)), CircleIntegrable
        (fun z : ℂ => (2 * Real.pi * Complex.I)⁻¹ • (wRow n D c a p * ((Ring.inverse
          (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β)))) 0 1 :=
      fun p _ => (((hentry p).const_mul (wRow n D c a p)).const_smul
        (2 * Real.pi * Complex.I)⁻¹).circleIntegrable zero_le_one
    rw [← circleIntegral.integral_fun_sum (s := (Finset.univ : Finset (Fin (D + 1) × Fin n)))
      (c := 0) (R := 1) (f := fun p z => (2 * Real.pi * Complex.I)⁻¹ • (wRow n D c a p *
        ((Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D)
          p (i, β)))) hint2]
    have hcongr : (∮ z in C(0, 1), ∑ p : Fin (D + 1) × Fin n, (2 * Real.pi * Complex.I)⁻¹ •
          (wRow n D c a p * ((Ring.inverse (z • wBA (A := C(X, ℂ)) n D + wBB n D c)
            * wBA (A := C(X, ℂ)) n D) p (i, β))))
        = ∮ z in C(0, 1), (0 : C(X, ℂ)) := by
      refine circleIntegral.integral_congr zero_le_one (fun z hz => ?_)
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hsum : ∑ p : Fin (D + 1) × Fin n, wRow n D c a p * ((Ring.inverse
          (z • wBA (A := C(X, ℂ)) n D + wBB n D c) * wBA (A := C(X, ℂ)) n D) p (i, β)) = 0 := by
        rw [← Matrix.mul_apply]
        simpa using congrFun (congrFun (hpt z hz1) a) (i, β)
      rw [← Finset.smul_sum, hsum, smul_zero]
    rw [hcongr, Work.Idx.circleIntegral_const (0 : C(X, ℂ)) 0 1]
  rw [hbridge]
  exact hmain

end

end Work.Idx
