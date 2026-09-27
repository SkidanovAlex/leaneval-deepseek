import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.matPenProj_eval

set_option linter.style.haveILetI false

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **Abstract form.** In a complex Banach algebra `R`, if `A * M = A` and the pencil
`z ↦ z • A + B` is invertible on the unit circle, then the pencil projection
`(2πi)⁻¹ ∮_{|z|=1} (z • A + B)⁻¹ A dz` is unchanged by right multiplication by `M`.

This is the scalar/abstract ingredient; the pointwise identity
`(zA+B)⁻¹ A M = (zA+B)⁻¹ A` needs only associativity and `A * M = A`, so it is `Ring.inverse`-free,
while `hunit` supplies the integrability of the integrand on the circle. -/
theorem penProj_mul_const_of_mul {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B M : R) (hM : A * M = A) (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    Work.KT.Idx.penProj A B * M = Work.KT.Idx.penProj A B := by
  have hcont : ContinuousOn (fun z : ℂ => Work.KT.Idx.pResA A B z) (Metric.sphere (0:ℂ) 1) :=
    continuousOn_res A B hunit
  have hint : CircleIntegrable (fun z : ℂ => Work.KT.Idx.pResA A B z) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  have hmul : Work.KT.Idx.pCirc A B 1 * M
      = ∮ z in C(0,1), Work.KT.Idx.pResA A B z * M :=
    (Work.KT.Fund.circleIntegral_mul_const M (fun z => Work.KT.Idx.pResA A B z) 0 1 hint).symm
  have hpt : (∮ z in C(0,1), Work.KT.Idx.pResA A B z * M)
      = (∮ z in C(0,1), Work.KT.Idx.pResA A B z) := by
    refine circleIntegral.integral_congr (by norm_num) (fun z _ => ?_)
    show Work.KT.Idx.pResA A B z * M = Work.KT.Idx.pResA A B z
    simp only [Work.KT.Idx.pResA]
    rw [mul_assoc, hM]
  calc Work.KT.Idx.penProj A B * M
      = ((2 * Real.pi * Complex.I)⁻¹ • Work.KT.Idx.pCirc A B 1) * M := rfl
    _ = (2 * Real.pi * Complex.I)⁻¹ • (Work.KT.Idx.pCirc A B 1 * M) := smul_mul_assoc _ _ _
    _ = (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0,1), Work.KT.Idx.pResA A B z * M) := by
          rw [hmul]
    _ = (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0,1), Work.KT.Idx.pResA A B z) := by rw [hpt]
    _ = Work.KT.Idx.penProj A B := rfl

/-- **Right multiplication by a matrix fixing `A` does not change the pencil projection.**

`blkPenProj X A B` is the Riesz projection `(2πi)⁻¹ ∮_{|z|=1} (z•A + B)⁻¹ A dz` of the matrix
pencil `z ↦ zA + B` over `C(X, ℂ)` (with the `L∞` operator norm on `Matrix ι ι C(X, ℂ)`, `ι` an
arbitrary finite type), computed through the `Fin`-indexed `Work.KT.Idx.penProj`.

Claim: if the constant matrix `M` satisfies `A * M = A`, then
`blkPenProj X A B * M = blkPenProj X A B`. -/
theorem blkPenProj_mul_of_mul {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B M : Matrix ι ι C(X, ℂ)) (hM : A * M = A)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    blkPenProj X A B * M = blkPenProj X A B := by
  letI hNR : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI hNA : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI hCS : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  exact @penProj_mul_const_of_mul (Matrix ι ι C(X, ℂ)) hNR hNA hCS A B M hM hunit

end

end Work.Idx
