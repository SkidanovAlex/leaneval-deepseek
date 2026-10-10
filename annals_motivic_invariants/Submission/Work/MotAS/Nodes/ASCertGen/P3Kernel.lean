import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotAS.ASRul.sAS2_ruling_mem
import Submission.Work.MotAS.ASrulV_mem
import Submission.Work.MotAS.ASrulW_mem
import Submission.Work.MotAS.Nodes.ASCertGen.P2Line
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotAS.Nodes.ASGen` — The ruling line is in the kernel of the AS ruling matrix (piece 3/6)

This module is one piece of the split of `Submission/Work/MotAS/Nodes/ASCertDefsGen.lean`
(51 KB, `maxHeartbeats 100000000`), which never compiled within the build budget.  The pieces
below 25 KB each with `maxHeartbeats 4000000`; the aggregator `ASCertDefsGen` still exports the
whole `Work.MotAS.Nodes.ASGen` namespace, so no consumer has to change.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.Nodes.ASGen

/-! ## §3  The ruling line is in the kernel of the ruling matrix -/

/-- **The ruling line over the generic point of the residual curve is in the kernel of the AS
ruling matrix over the generic base point** (modulo the residual-curve ideal). -/
theorem AmatAS2_zvT_cvT {K : Type} [Field K] [CharP K 5] (a b g : K) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) a)
        (algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) b)
        (algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) g) (cvT a b g)) (zvT a b g)
      = 0 := by
  letI : Semiring (Work.MotC5N3.ASrulA a b g) :=
    (inferInstance : CommSemiring (Work.MotC5N3.ASrulA a b g)).toSemiring
  letI : CommSemiring (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : CommRing (Work.MotC5N3.ASrulA a b g) := inferInstance
  letI : Semiring (Polynomial (Work.MotC5N3.ASrulA a b g)) := inferInstance
  letI : CommSemiring (Polynomial (Work.MotC5N3.ASrulA a b g)) := inferInstance
  letI : CommRing (Polynomial (Work.MotC5N3.ASrulA a b g)) := inferInstance
  set φ : MvPolynomial (Fin 3) K →+* Polynomial (Work.MotC5N3.ASrulA a b g) :=
    (Polynomial.C).comp (asMk a b g) with hφ
  have hpa : φ (MvPolynomial.C a)
      = algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) a := asMk_polyC a b g a
  have hpb : φ (MvPolynomial.C b)
      = algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) b := asMk_polyC a b g b
  have hpc : φ (MvPolynomial.C g)
      = algebraMap K (Polynomial (Work.MotC5N3.ASrulA a b g)) g := asMk_polyC a b g g
  have hV : Matrix.mulVec (Work.MotAS.AmatAS2 (φ (MvPolynomial.C a)) (φ (MvPolynomial.C b))
        (φ (MvPolynomial.C g)) (fun k => φ (Work.MotAS.asBaseVec K k)))
        (fun k => φ (Work.MotAS.ASRul.kbRv a b g k)) = 0 := by
    refine AmatAS2_map_mulVec_zero φ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotAS.asBaseVec K) (Work.MotAS.ASRul.kbRv a b g) ?_
    funext i
    rw [hφ, RingHom.comp_apply]
    have hmem : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASRul.kbRv a b g) i
        ∈ Ideal.radical (Work.MotAS.ZIAS a b g) := Work.MotAS.ASrulV_mem K a b g i
    have h0 : asMk a b g (Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C g) (Work.MotAS.asBaseVec K))
        (Work.MotAS.ASRul.kbRv a b g) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [h0, map_zero]
    simp
  have hW : Matrix.mulVec (Work.MotAS.AmatAS2 (φ (MvPolynomial.C a)) (φ (MvPolynomial.C b))
        (φ (MvPolynomial.C g)) (fun k => φ (Work.MotAS.asBaseVec K k)))
        (fun k => φ (Work.MotAS.ASRul.kbRw a b g k)) = 0 := by
    refine AmatAS2_map_mulVec_zero φ (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotAS.asBaseVec K) (Work.MotAS.ASRul.kbRw a b g) ?_
    funext i
    rw [hφ, RingHom.comp_apply]
    have hmem : Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (Work.MotAS.asBaseVec K)) (Work.MotAS.ASRul.kbRw a b g) i
        ∈ Ideal.radical (Work.MotAS.ZIAS a b g) := Work.MotAS.ASrulW_mem K a b g i
    have h0 : asMk a b g (Matrix.mulVec (Work.MotAS.AmatAS2 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C g) (Work.MotAS.asBaseVec K))
        (Work.MotAS.ASRul.kbRw a b g) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [h0, map_zero]
    simp
  rw [hpa, hpb, hpc] at hV hW
  have hzv : zvT a b g = (Polynomial.X : Polynomial (Work.MotC5N3.ASrulA a b g))
        • (fun k => φ (Work.MotAS.ASRul.kbRv a b g k))
      + (fun k => φ (Work.MotAS.ASRul.kbRw a b g k)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zvT, hφ, RingHom.comp_apply]
    first | refl_ring1 | ring
  have hcv : cvT a b g = fun k => φ (Work.MotAS.asBaseVec K k) := by
    funext k
    simp only [cvT, hφ, RingHom.comp_apply]
  rw [hcv, hzv, Matrix.mulVec_add, Matrix.mulVec_smul, hV, hW]
  simp

end Work.MotAS.Nodes.ASGen
