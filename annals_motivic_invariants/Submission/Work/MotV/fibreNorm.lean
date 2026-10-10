import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.MotV.ordSumPoly
import Submission.Work.MotV.ordSumNeg
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

namespace FibreNormAux

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

variable {N : Type*} [Field N]

/-- The norm over `N[X]` of an element of the affine coordinate ring is the product of the element
with its negation-conjugate in the function field `N(E)`:
`Norm a = a · σ(a)`, where `σ` is the negation `[-1]`. -/
theorem norm_eq_mul_negAlgEquiv (E : WeierstrassCurve N) (a : CoordinateRing E) :
    algebraMap (Polynomial N) (MotC2.Func E) (Algebra.norm (Polynomial N) a)
      = algebraMap (CoordinateRing E) (MotC2.Func E) a *
        MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) a) := by
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [← hpq, CoordinateRing.norm_smul_basis]
  rw [MotC2.algebraMap_polynomial_eq_aeval_genX E]
  have h1 : algebraMap (CoordinateRing E) (MotC2.Func E) (p • (1 : CoordinateRing E))
      = Polynomial.aeval (MotC2.genX E) p := (MotC2.algebraMap_smul_eq_aeval N E p).1
  have h2 : algebraMap (CoordinateRing E) (MotC2.Func E)
        (q • (CoordinateRing.mk E Polynomial.X))
      = Polynomial.aeval (MotC2.genX E) q * MotC2.genY E :=
    (MotC2.algebraMap_smul_eq_aeval N E q).2
  have hsum : algebraMap (CoordinateRing E) (MotC2.Func E)
        (p • (1 : CoordinateRing E) + q • (CoordinateRing.mk E Polynomial.X))
      = Polynomial.aeval (MotC2.genX E) p + Polynomial.aeval (MotC2.genX E) q * MotC2.genY E := by
    rw [map_add, h1, h2]
  have hfix : ∀ P : Polynomial N,
      MotC2.negAlgEquiv E (Polynomial.aeval (MotC2.genX E) P)
        = Polynomial.aeval (MotC2.genX E) P := by
    intro P
    rw [← Polynomial.aeval_algHom_apply (MotC2.negAlgEquiv E) (MotC2.genX E) P,
      MotC2.negAlgEquiv_genX]
  rw [hsum]
  simp only [map_sub, map_mul, map_pow, map_add, Polynomial.aeval_C, Polynomial.aeval_X,
    hfix, MotC2.negAlgEquiv_genY]
  rw [← MotC2.genY_sq_relation E]
  first | refl_ring1 | ring

/-- Multiplicativity of `ordSum` over a finite set of places. -/
theorem ordSum_mul (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (S : Finset (Place N E))
    (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordSum E S (f * g) = ordSum E S f + ordSum E S g := by
  rw [ordSum, ordSum, ordSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  exact H.ord_mul Q.1 Q.2 f g hf hg

/-- The image of the norm in the function field is nonzero. -/
theorem algebraMap_norm_ne_zero (E : WeierstrassCurve N) (a : CoordinateRing E) (ha : a ≠ 0) :
    algebraMap (Polynomial N) (MotC2.Func E) (Algebra.norm (Polynomial N) a) ≠ 0 := by
  rw [norm_eq_mul_negAlgEquiv E a]
  refine mul_ne_zero ?_ ?_
  · exact fun h => ha (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  · intro h
    have h' : MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) a) =
        MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) 0) := by
      rw [map_zero, h, map_zero]
    exact ha (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E)
      ((MotC2.negAlgEquiv E).injective h'))

/-- The norm over `N[X]` of a nonzero element of the coordinate ring is a nonzero polynomial. -/
theorem norm_ne_zero (E : WeierstrassCurve N) (a : CoordinateRing E) (ha : a ≠ 0) :
    Algebra.norm (Polynomial N) a ≠ 0 := by
  intro h
  exact algebraMap_norm_ne_zero E a ha (by rw [h, map_zero])

/-- Assembly of `fibreNorm` from the polynomial fibre computation and the invariance of the fibre
order sum under the negation. -/
theorem fibreNorm_of [IsAlgClosed N] [DecidableEq N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E)
    (hPoly : ∀ (h : Polynomial N), h ≠ 0 → ∀ c : N,
      ordSum E (fibrePlaces E c) (algebraMap (Polynomial N) (MotC2.Func E) h)
        = 2 * (((h.roots.count c : ℕ)) : ℤ))
    (hNeg : ∀ (f : MotC2.Func E) (c : N),
      ordSum E (fibrePlaces E c) (MotC2.negAlgEquiv E f) = ordSum E (fibrePlaces E c) f)
    (a : CoordinateRing E) (ha : a ≠ 0) (c : N) :
    ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
  have hf0 : algebraMap (CoordinateRing E) (MotC2.Func E) a ≠ 0 :=
    fun h => ha (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  have hσ0 : MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) a) ≠ 0 := by
    intro h
    have h' : MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) a) =
        MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) 0) := by
      rw [map_zero, h, map_zero]
    exact ha (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E)
      ((MotC2.negAlgEquiv E).injective h'))
  have hpoly := hPoly (Algebra.norm (Polynomial N) a) (norm_ne_zero E a ha) c
  have hmain : ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a) +
      ordSum E (fibrePlaces E c)
        (MotC2.negAlgEquiv E (algebraMap (CoordinateRing E) (MotC2.Func E) a))
      = 2 * (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
    rw [← ordSum_mul E H (fibrePlaces E c) _ _ hf0 hσ0, ← norm_eq_mul_negAlgEquiv E a]
    exact hpoly
  have hll : ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a) +
      ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = 2 * (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
    rw [hNeg _ c] at hmain
    exact hmain
  have h2 : (2 : ℤ) * ordSum E (fibrePlaces E c)
        (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = 2 * (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
    linarith
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

end FibreNormAux

theorem fibreNorm {N : Type*} [Field N] [IsAlgClosed N] [DecidableEq N]
    (E : WeierstrassCurve N) [E.IsElliptic] (H : Work.MotV.H1Data N E)
    (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0) (c : N) :
    Work.MotV.ordSum E (Work.MotV.fibrePlaces E c)
        (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
      = (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) :=
  FibreNormAux.fibreNorm_of E H (ordSumPoly E H) (ordSumNeg E H) a ha c

end Work.MotV
