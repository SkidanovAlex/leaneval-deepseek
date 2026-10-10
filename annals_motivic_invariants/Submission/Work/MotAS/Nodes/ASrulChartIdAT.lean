import Mathlib
import Submission.Work.MotAS.Nodes.ASCertGen.P3Kernel
import Submission.Work.MotAS.Nodes.ASrulChartIdFibre
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRul.kleinMAS_fibre
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulV2.Defs

import Submission.Work.MotAS.Nodes.ASrulChartIdPre

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace Work.MotAS.Nodes

open MvPolynomial

/-! ## §3  The base-point identity in `A[T]` -/

/-- **The chart identity in `A[T]`**: the image `P = kleinPAS y` of the source point recovers the
base-point coordinates. -/
theorem PV_chart (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (i : Fin 3) :
    PV K a b g 0 * Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
        (MvPolynomial.X i))
      = PV K a b g (Work.MotAS.asCh3 i) := by
  have hkerz : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS (algebraMap K (PQ K a b g) a)
      (algebraMap K (PQ K a b g) b) (algebraMap K (PQ K a b g) g)
      (Work.MotAS.Nodes.ASGen.zvT a b g))
      (Work.MotAS.Nodes.ASGen.cvT a b g) = 0 := by
    rw [← Work.MotAS.AmatAS2_mulVec]
    exact Work.MotAS.Nodes.ASGen.AmatAS2_zvT_cvT a b g
  have hcv : Work.MotAS.Nodes.ASGen.cvT a b g ≠ 0 := by
    intro h0
    have h1 : Work.MotAS.Nodes.ASGen.cvT a b g 0 = 0 := congrFun h0 0
    rw [Work.MotAS.Nodes.ASGen.cvT_zero a b g] at h1
    exact one_ne_zero h1
  have hPQ : PV K a b g = (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
      (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2 • QV K a b g := by
    rw [PV, QV, yV_eq K a b g hDZ, kleinPAS_smul']
  by_cases hQ : QV K a b g = 0
  · have hP : PV K a b g = 0 := by
      rw [hPQ, hQ, smul_zero]
    rw [hP]
    simp
  · have hprop := kleinMAS_fibre_domain (five_eq_zero_PQ K a b g)
      (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b) (algebraMap K (PQ K a b g) g)
      (Work.MotAS.Nodes.ASGen.zvT a b g) (Work.MotAS.Nodes.ASGen.cvT a b g) hQ hcv hkerz
    have hPQ : PV K a b g = (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
        (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2 • QV K a b g := by
      rw [PV, QV, yV_eq K a b g hDZ, kleinPAS_smul']
    have hQV : QV K a b g 0
          * Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
              (MvPolynomial.X i))
        = QV K a b g (Work.MotAS.asCh3 i) := by
      have h := hprop (Work.MotAS.asCh3 i)
      rw [cvT_asCh3 K a b g i, Work.MotAS.Nodes.ASGen.cvT_zero a b g, mul_one] at h
      exact h
    rw [hPQ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
            (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2
          * QV K a b g 0
          * Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
              (MvPolynomial.X i))
        = (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
            (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2
          * (QV K a b g 0
            * Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
                (MvPolynomial.X i))) from by ring,
      show (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
            (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2
          * (QV K a b g 0
            * Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
                (MvPolynomial.X i)))
        = (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
            (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g)) ^ 2
          * QV K a b g (Work.MotAS.asCh3 i) from by rw [hQV]]

end Work.MotAS.Nodes
