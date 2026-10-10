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
Route.  `fwVecAS2L a b g = kleinPAS (C a) (C b) (C g) (stereoAS (C a) (C b) (pAS0L K) (chart3 K))`
(definitionally).  Push the `K`-algebra hom `PhiL a b g` through it with
`Work.MotAS.KleinTwScalarAS_map_kleinPAS`, `Work.MotV5.ASChart.map_stereoAS_free` and
`Work.MotV5.ASChart.map_kleinQAS_free` (`ASCore`); use `PhiL_C : PhiL (C c) = algebraMap _ _ c` and
`PhiL_chart3 : PhiL ∘ chart3 = invGL • (algebraMap ∘ bwVecAS2L)` (in `ASChartLocalDefs`).
Homogeneity `kleinStereoAS_smul_free` (degree 2) and `kleinPAS_smul_free` (degree 2, `ASCore`) give
`invGL^4` and leave `kleinPAS (C a) (C b) (C g) (stereoAS (C a) (C b) (pAS0L K) (bwVecAS2L a b g))`
at the vector level.  The ring identity `Work.MotV5.ASChart.kleinFwVecRingIdFree` (`ASCore`) with
`p = pAS0L K`, `w = tchartL K` — whose `hI2` input is the instance of
`Work.MotV5.ASChart.kleinPAS_kleinRAS_free` at `z = tchartL K`, and whose `hw` is `tchartL K 4 = 0`
— gives that vector as `fun i => cubAS2L a b g ^ 2 * sdualAS2L a b g * tchartL K i` (all by
definition).  Finish with `map_mul` of `algebraMap`.
-/
theorem PhiL_fwVecAS2L {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (i : Fin 5) :
    Work.MotV5.ASChart.PhiL a b g (Work.MotV5.ASChart.fwVecAS2L a b g i)
      = Work.MotV5.ASChart.invGL a b g ^ 4 *
        algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (Work.MotV5.ASChart.GdivAS2L a b g))
          (Work.MotV5.ASChart.cubAS2L a b g ^ 2 * Work.MotV5.ASChart.sdualAS2L a b g
            * Work.MotV5.ASChart.tchartL K i) := by
  -- Work with the *ring homomorphism* coercion of `PhiL`, so that the naturality lemmas (which are
  -- stated for `φ : A →+* B`) match syntactically.
  change (PhiL a b g : MvPolynomial (Fin 3) K →+* Localization.Away (GdivAS2L a b g))
      (Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K)) i) = _
  -- ### The three elementary substitutions along `PhiL`
  have hpp : (fun i => (PhiL a b g : MvPolynomial (Fin 3) K →+*
        Localization.Away (GdivAS2L a b g)) (pAS0L K i))
      = fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (pAS0L K i) := by
    funext i; fin_cases i <;> simp [pAS0L]
  have hC : ∀ c : K, (PhiL a b g : MvPolynomial (Fin 3) K →+*
        Localization.Away (GdivAS2L a b g)) (MvPolynomial.C c)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C c) := by
    intro c
    rw [show (PhiL a b g : MvPolynomial (Fin 3) K →+* Localization.Away (GdivAS2L a b g))
          (MvPolynomial.C c) = PhiL a b g (MvPolynomial.C c) from rfl]
    rw [PhiL_C, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (GdivAS2L a b g)) c, MvPolynomial.algebraMap_eq]
  have hc3 : (fun i => (PhiL a b g : MvPolynomial (Fin 3) K →+*
        Localization.Away (GdivAS2L a b g)) (Work.MotK.chart3 K i))
      = fun i => invGL a b g * algebraMap (MvPolynomial (Fin 3) K)
        (Localization.Away (GdivAS2L a b g)) (bwVecAS2L a b g i) := by
    rw [show (fun i => (PhiL a b g : MvPolynomial (Fin 3) K →+*
          Localization.Away (GdivAS2L a b g)) (Work.MotK.chart3 K i))
        = (fun i => PhiL a b g (Work.MotK.chart3 K i)) from rfl, PhiL_chart3]
  -- ### The push-forward of the stereographic vector
  have hpush : (fun j => (PhiL a b g : MvPolynomial (Fin 3) K →+*
        Localization.Away (GdivAS2L a b g))
        (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K) j))
      = fun j => invGL a b g ^ 2 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (GdivAS2L a b g))
          (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (bwVecAS2L a b g) j) := by
    have hmap := map_stereoAS_free (φ := (PhiL a b g : MvPolynomial (Fin 3) K →+*
        Localization.Away (GdivAS2L a b g))) (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K)
        (Work.MotK.chart3 K)
    rw [hmap]
    rw [hC a, hC b, hpp, hc3]
    rw [kleinStereoAS_smul_free
        (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C a))
        (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C b))
        (invGL a b g)
        (fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (pAS0L K i))
        (fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
          (bwVecAS2L a b g i))]
    rw [← map_stereoAS_free (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)))
          (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (bwVecAS2L a b g)]
  -- ### The composed ring identity, at `p = pAS0L K` and `w = tchartL K`
  have hI2 := Work.MotV5.ASChart.kleinPAS_kleinRAS_free (MvPolynomial.C a) (MvPolynomial.C b)
    (MvPolynomial.C g) (tchartL K) h5
  have hring := kleinFwVecRingIdFree (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (pAS0L K) (tchartL K) (kleinQAS_pAS0L a b) (by rfl) hI2
  -- ### The push-forward through `kleinPAS`
  have hnat := congrFun (Work.MotAS.KleinTwScalarAS_map_kleinPAS
    (φ := (PhiL a b g : MvPolynomial (Fin 3) K →+* Localization.Away (GdivAS2L a b g)))
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K))) i
  rw [← hnat]
  rw [hC a, hC b, hC g, hpush]
  -- ### Homogeneity: pull out `(invGL ^ 2) ^ 2 = invGL ^ 4`
  have hhom := congrFun (kleinPAS_smul_free
    (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C a))
    (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C b))
    (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C g))
    (invGL a b g ^ 2)
    (fun j => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (bwVecAS2L a b g) j))) i
  rw [hhom]
  -- ### Pull `algebraMap` back out of `kleinPAS`
  have hnat2 := congrFun (Work.MotAS.KleinTwScalarAS_map_kleinPAS
    (φ := algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)))
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (bwVecAS2L a b g))) i
  rw [hnat2]
  -- ### The ring identity, and the scalar `(invGL ^ 2) ^ 2 = invGL ^ 4`
  rw [show MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (bwVecAS2L a b g))
      = fun k => cubAS2L a b g ^ 2 * sdualAS2L a b g * tchartL K k from hring]
  simp only []
  rw [show (invGL a b g ^ 2) ^ 2 = invGL a b g ^ 4 from by ring]

end Work.MotV5.ASChart
