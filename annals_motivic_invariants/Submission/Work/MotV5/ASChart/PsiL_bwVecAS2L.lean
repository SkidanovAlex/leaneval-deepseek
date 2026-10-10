import Mathlib
import Submission.Work.MotV5.ASChart.ASChartLocalDefs
import Submission.Work.MotV5.ASChart.ASCore

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.ASChart

/-
Route.  `bwVecAS2L a b g = kleinTwPi (pAS0L K) (kleinRAS (C a) (C b) (C g) (tchartL K))`
(definitionally).  Push the `K`-algebra hom `PsiL a b g` through this polynomial expression with
`Work.MotV5.ASChart.map_kleinTwPi_free` and `Work.MotAS.KleinTwScalarAS_map_kleinRAS`; use
`PsiL_C : PsiL (C c) = algebraMap _ _ c` (so `PsiL ∘ pAS0L = algebraMap ∘ pAS0L`) and
`PsiL_tchart : PsiL ∘ tchartL = invFL • (algebraMap ∘ fwVecAS2L)` (both in `ASChartLocalDefs`).
`Work.MotV5.ASChart.kleinRAS_smul_free` (degree 3) and `kleinTwPi_smul_free` pull out `invFL^3`,
and naturality backwards puts the result back as the `algebraMap` of
`kleinTwPi (pAS0L K) (kleinRAS (C a) (C b) (C g) (fwVecAS2L a b g))`.  The ring identity
`Work.MotV5.ASChart.kleinTwLinkComp2Free` (`ASCore`) with `p = pAS0L K`, `v = chart3 K`
(using `kleinQAS_pAS0L`, `pAS0L 0 = 1`, `chart3 K 0 = 0`, and `fwVecAS2L = kleinPAS (stereoAS …)`)
gives that vector as `-(GambAS2L a b g) • chart3 K`.
-/
theorem PsiL_bwVecAS2L {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (i : Fin 5) :
    Work.MotV5.ASChart.PsiL a b g (Work.MotV5.ASChart.bwVecAS2L a b g i)
      = Work.MotV5.ASChart.invFL a b g ^ 3 *
        algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Work.MotV5.ASChart.FdivAS2L a b g))
          (-(Work.MotV5.ASChart.GambAS2L a b g) * Work.MotK.chart3 K i) := by
  have hca : PsiL a b g (MvPolynomial.C a)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
          (MvPolynomial.C a) := by
    rw [PsiL_C, MvPolynomial.C_eq_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (FdivAS2L a b g)) a).symm
  have hcb : PsiL a b g (MvPolynomial.C b)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
          (MvPolynomial.C b) := by
    rw [PsiL_C, MvPolynomial.C_eq_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (FdivAS2L a b g)) b).symm
  have hcg : PsiL a b g (MvPolynomial.C g)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
          (MvPolynomial.C g) := by
    rw [PsiL_C, MvPolynomial.C_eq_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (FdivAS2L a b g)) g).symm
  have hP0 : (fun i => PsiL a b g (pAS0L K i))
      = fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
          (pAS0L K i) := by
    funext j
    fin_cases j <;> simp [pAS0L]
  have hRAS' : (fun i => PsiL a b g (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (tchartL K) i))
      = Work.MotAS.kleinRAS
          (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (MvPolynomial.C a))
          (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (MvPolynomial.C b))
          (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (MvPolynomial.C g))
          (fun j => invFL a b g * algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (FdivAS2L a b g)) (fwVecAS2L a b g j)) := by
    have hmap := Work.MotAS.KleinTwScalarAS_map_kleinRAS
      (PsiL a b g : MvPolynomial (Fin 3) K →+* Localization.Away (FdivAS2L a b g))
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchartL K)
    have hmap' : (fun i => PsiL a b g (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C g) (tchartL K) i))
        = Work.MotAS.kleinRAS (PsiL a b g (MvPolynomial.C a)) (PsiL a b g (MvPolynomial.C b))
            (PsiL a b g (MvPolynomial.C g)) (fun j => PsiL a b g (tchartL K j)) := hmap.symm
    rw [hmap', PsiL_tchart, hca, hcb, hcg]
  have hRAS : (fun i => PsiL a b g (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (tchartL K) i))
      = fun i => invFL a b g ^ 3 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (FdivAS2L a b g))
          (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (fwVecAS2L a b g) i) := by
    rw [hRAS', kleinRAS_smul_free]
    rw [Work.MotAS.KleinTwScalarAS_map_kleinRAS
      (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g)))
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (fwVecAS2L a b g)]
  have hA : (fun i => PsiL a b g (Work.MotK.kleinTwPi (pAS0L K)
        (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (tchartL K)) i))
      = Work.MotK.kleinTwPi (fun i => PsiL a b g (pAS0L K i))
          (fun i => PsiL a b g (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
            (MvPolynomial.C g) (tchartL K) i)) :=
    map_kleinTwPi_free (PsiL a b g : MvPolynomial (Fin 3) K →+*
      Localization.Away (FdivAS2L a b g))
      (pAS0L K) (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (tchartL K))
  have hTw : Work.MotK.kleinTwPi (pAS0L K)
        (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fwVecAS2L a b g))
      = fun i => -(GambAS2L a b g) * Work.MotK.chart3 K i :=
    kleinTwLinkComp2Free (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) h5
      (pAS0L K) (Work.MotK.chart3 K) (kleinQAS_pAS0L a b) rfl rfl
  have hfinal : (fun i => PsiL a b g (bwVecAS2L a b g i))
      = fun i => invFL a b g ^ 3 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (FdivAS2L a b g)) (-(GambAS2L a b g) * Work.MotK.chart3 K i) := by
    change (fun i => PsiL a b g (Work.MotK.kleinTwPi (pAS0L K)
        (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (tchartL K)) i))
      = fun i => invFL a b g ^ 3 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (FdivAS2L a b g)) (-(GambAS2L a b g) * Work.MotK.chart3 K i)
    rw [hA, hP0, hRAS, kleinTwPi_smul_free]
    have h2 : (fun i => Work.MotK.kleinTwPi (fun i => algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (FdivAS2L a b g)) (pAS0L K i))
          (fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
              (fwVecAS2L a b g) i)) i)
        = fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (Work.MotK.kleinTwPi (pAS0L K)
              (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (fwVecAS2L a b g)) i) :=
      funext fun k => congrFun (map_kleinTwPi_free (algebraMap (MvPolynomial (Fin 3) K)
        (Localization.Away (FdivAS2L a b g))) (pAS0L K)
        (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fwVecAS2L a b g))).symm k
    have h3 : (fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (Work.MotK.kleinTwPi (pAS0L K)
              (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (fwVecAS2L a b g)) i))
        = fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
            (-(GambAS2L a b g) * Work.MotK.chart3 K i) :=
      congrArg (fun v : Fin 5 → MvPolynomial (Fin 3) K =>
        fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g)) (v i))
        hTw
    exact congrArg (fun v : Fin 5 → Localization.Away (FdivAS2L a b g) =>
      fun i => invFL a b g ^ 3 * v i) (h2.trans h3)
  exact congrFun hfinal i

end Work.MotV5.ASChart
