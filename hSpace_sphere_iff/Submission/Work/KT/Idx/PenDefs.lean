import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.SpectralAux

/-!
# `Work.KT.Idx.PenDefs` — the pencil projection (Riesz projection of a linear matrix pencil)

This is the vocabulary for the Bott index of `Work.KT.FP.bott_index` (the Hatcher `ν` map), in a
self-contained form: for a complex Banach algebra `R` and `A B : R`,

* `pRes A B z = (z • A + B)⁻¹` — the resolvent of the pencil `z ↦ zA + B`;
* `pResA A B z = (zA+B)⁻¹ A` — the integrand;
* `pCirc A B r = ∮_{|z| = r} (zA+B)⁻¹ A dz` — the circle integral;
* `penProj A B = (2πi)⁻¹ • pCirc A B 1` — the "inside" (roots inside the unit circle) projection.

For `X` compact Hausdorff and `A B` matrices over `C(X, ℂ)`, `matPenProj X A B` is the same
element with the `L∞` operator norm as the Banach algebra structure on the matrix ring.  When the
pencil is invertible on the unit circle this is an idempotent matrix of continuous functions
(`Work.KT.Idx.penProj_idem`), whose `cls` in `K₀(C(X, ℂ))` is the index (Hatcher's `ν`) of the
clutching function.

(The same objects appear as `Work.KT.FP.pProj` / `Work.KT.FP.pProjB` / `Work.KT.FP.matPProj` in
the lead's `Submission/Work/KT/FP/PencilDefs.lean`; the definitions here are identical in content
and therefore definitionally equal, and they are kept separate only so that this file does not
depend on the still-changing FP vocabulary.)
-/

namespace Work.KT.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The resolvent of the pencil `z ↦ z • A + B`. -/
def pRes (A B : R) (z : ℂ) : R := Ring.inverse (z • A + B)

/-- The integrand `(z • A + B)⁻¹ * A` of the pencil projection. -/
def pResA (A B : R) (z : ℂ) : R := pRes A B z * A

/-- The circle integral `∮_{|z|=r} (zA+B)⁻¹ A dz`. -/
def pCirc (A B : R) (r : ℝ) : R := ∮ z in C(0, r), pResA A B z

/-- The "inside" spectral projection of the pencil `z ↦ zA + B`, computed on the unit circle. -/
def penProj (A B : R) : R := (2 * Real.pi * Complex.I)⁻¹ • pCirc A B 1

/-- The pencil projection for `Fin N`-indexed matrices over `C(X, ℂ)`, with the `L∞` operator norm
as the Banach algebra structure. -/
def matPenProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) : Matrix (Fin N) (Fin N) C(X, ℂ) :=
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  penProj A B

/-- The evaluation homomorphism at `t : unitInterval`, `C(X × I, ℂ) →+* C(X, ℂ)`. -/
def evalPull (X : Type) [TopologicalSpace X] (t : unitInterval) :
    C(X × unitInterval, ℂ) →+* C(X, ℂ) :=
  (pullAlg (ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const _ t))).toRingHom

end

end Work.KT.Idx
