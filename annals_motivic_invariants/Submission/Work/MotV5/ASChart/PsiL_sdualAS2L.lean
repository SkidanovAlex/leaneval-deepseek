import Mathlib
import Submission.Work.MotV5.ASChart.ASChartLocalDefs
import Submission.Work.MotV5.ASChart.ASCore

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The value of `PsiL` on the target ruling quintic `sdualAS2L`

**Target.**
`PsiL a b g (sdualAS2L a b g) = invFL a b g ^ 5 * algebraMap (sAS2L a b g ^ 2)`.

## Proof route

* `sdualAS2L a b g = kleinSecDualAS (C a) (C b) (C g) (tchartL K)` (definitionally), and
  `PsiL a b g = aeval (phiFL ...)`; pushing `PsiL` through `kleinSecDualAS` with the naturality
  lemma `Work.MotAS.KleinTwI3AS_map_kleinSecDualAS` gives
  `PsiL (sdualAS2L) = kleinSecDualAS (PsiL (C a)) (PsiL (C b)) (PsiL (C g)) (PsiL ∘ tchartL)`.
* `PsiL (C c) = algebraMap _ _ c` (`PsiL_C`) and
  `PsiL ∘ tchartL = invFL • (algebraMap ∘ fwVecAS2L)` (`PsiL_tchart`).
* homogeneity of `kleinSecDualAS` (degree `5`, `kleinSecDualAS_smul_free`) pulls out `invFL ^ 5`.
* naturality *backwards* (`← KleinTwI3AS_map_kleinSecDualAS` for `algebraMap`) puts the remaining
  `algebraMap`-vector back as the image of `kleinSecDualAS (C a) (C b) (C g) (fwVecAS2L)`.
* the link identity I3 `Work.MotAS.KleinTwI3AS` gives
  `kleinSecDualAS (C a) (C b) (C g) (kleinPAS (C a) (C b) (C g) y) = kleinSecAS (C a) (C b) (C g) y ^ 2`
  with `y = stereoAS (C a) (C b) (pAS0L K) (chart3 K)`, i.e.
  `kleinSecDualAS (C a) (C b) (C g) (fwVecAS2L a b g) = sAS2L a b g ^ 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotV5.ASChart

theorem PsiL_sdualAS2L {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) :
    Work.MotV5.ASChart.PsiL a b g (Work.MotV5.ASChart.sdualAS2L a b g)
      = Work.MotV5.ASChart.invFL a b g ^ 5 *
        algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))
          (Work.MotV5.ASChart.sAS2L a b g ^ 2) := by
  -- naturality of `kleinSecDualAS` along `PsiL`
  have hnat : Work.MotAS.kleinSecDualAS ((Work.MotV5.ASChart.PsiL a b g) (MvPolynomial.C a))
      ((Work.MotV5.ASChart.PsiL a b g) (MvPolynomial.C b))
      ((Work.MotV5.ASChart.PsiL a b g) (MvPolynomial.C g))
      (fun j => (Work.MotV5.ASChart.PsiL a b g) (Work.MotV5.ASChart.tchartL K j))
      = (Work.MotV5.ASChart.PsiL a b g)
        (Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (Work.MotV5.ASChart.tchartL K)) :=
    Work.MotAS.KleinTwI3AS_map_kleinSecDualAS (Work.MotV5.ASChart.PsiL a b g).toRingHom
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (Work.MotV5.ASChart.tchartL K)
  -- naturality of `kleinSecDualAS` along `algebraMap`
  have hnat2 : Work.MotAS.kleinSecDualAS
        ((algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))) (MvPolynomial.C a))
        ((algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))) (MvPolynomial.C b))
        ((algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))) (MvPolynomial.C g))
        (fun i => (algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g)))
          (Work.MotV5.ASChart.fwVecAS2L a b g i))
      = (algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g)))
        (Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (Work.MotV5.ASChart.fwVecAS2L a b g)) :=
    Work.MotAS.KleinTwI3AS_map_kleinSecDualAS
      (algebraMap (MvPolynomial (Fin 3) K)
        (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g)))
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (Work.MotV5.ASChart.fwVecAS2L a b g)
  -- `C` is the structure map of the polynomial ring
  have hC : ∀ c : K, (algebraMap K (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))) c
      = (algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))) (MvPolynomial.C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g)), MvPolynomial.algebraMap_eq]
  -- the link identity I3
  have hI3 : Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotV5.ASChart.fwVecAS2L a b g) = Work.MotV5.ASChart.sAS2L a b g ^ 2 :=
    Work.MotAS.KleinTwI3AS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (Work.MotV5.ASChart.stereoAS (MvPolynomial.C a) (MvPolynomial.C b)
        (Work.MotV5.ASChart.pAS0L K) (Work.MotK.chart3 K)) h5
  rw [show Work.MotV5.ASChart.sdualAS2L a b g
      = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (Work.MotV5.ASChart.tchartL K) from rfl]
  rw [← hnat]
  rw [Work.MotV5.ASChart.PsiL_C a b g a, Work.MotV5.ASChart.PsiL_C a b g b,
    Work.MotV5.ASChart.PsiL_C a b g g]
  rw [Work.MotV5.ASChart.PsiL_tchart a b g]
  rw [Work.MotV5.ASChart.kleinSecDualAS_smul_free]
  rw [hC a, hC b, hC g, hnat2, hI3]

end Work.MotV5.ASChart
