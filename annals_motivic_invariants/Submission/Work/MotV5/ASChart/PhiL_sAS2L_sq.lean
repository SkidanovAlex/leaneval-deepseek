import Mathlib
import Submission.Work.MotV5.ASChart.ASChartLocalDefs
import Submission.Work.MotV5.ASChart.ASCore
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.ASChart

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-
Route.  Put `y := stereoAS (C a) (C b) (pAS0L K) (chart3 K)`; then
`sAS2L a b g = kleinSecAS (C a) (C b) (C g) y` and `fwVecAS2L a b g = kleinPAS (C a) (C b) (C g) y`
(definitionally).  Use `map_pow` for `PhiL (sAS2L)^2 = PhiL (sAS2L^2)`, the link identity I3
`Work.MotAS.KleinTwI3AS` at `y` (`kleinSecDualAS (kleinPAS y) = kleinSecAS y ^ 2`) to rewrite the
argument as `kleinSecDualAS (C a) (C b) (C g) (fwVecAS2L a b g)`, and the naturality
`← Work.MotAS.KleinTwI3AS_map_kleinSecDualAS` to move `PhiL` inside.  The hypothesis `hfw` is the
vector form of `PhiL_fwVecAS2L`: after splitting the `algebraMap` of the product with `map_mul` it
says `PhiL ∘ fwVecAS2L = λ • (algebraMap ∘ tchartL)` with
`λ = invGL a b g ^ 4 * algebraMap _ _ (cubAS2L a b g ^ 2 * sdualAS2L a b g)`; use homogeneity
`Work.MotV5.ASChart.kleinSecDualAS_smul_free` (degree 5, `ASCore`), then naturality backwards
(`kleinSecDualAS (algebraMap ∘ tchartL) = algebraMap (sdualAS2L a b g)`, by definition of
`sdualAS2L` and `Work.MotAS.KleinTwI3AS_map_kleinSecDualAS`).
-/
theorem PhiL_sAS2L_sq {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hfw : (fun i => Work.MotV5.ASChart.PhiL a b g (Work.MotV5.ASChart.fwVecAS2L a b g i))
      = fun i => Work.MotV5.ASChart.invGL a b g ^ 4 *
          algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.GdivAS2L a b g))
            (Work.MotV5.ASChart.cubAS2L a b g ^ 2 * Work.MotV5.ASChart.sdualAS2L a b g
              * Work.MotV5.ASChart.tchartL K i)) :
    Work.MotV5.ASChart.PhiL a b g (Work.MotV5.ASChart.sAS2L a b g) ^ 2
      = (Work.MotV5.ASChart.invGL a b g ^ 4 *
          algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.GdivAS2L a b g))
            (Work.MotV5.ASChart.cubAS2L a b g ^ 2 * Work.MotV5.ASChart.sdualAS2L a b g)) ^ 5
        * algebraMap (MvPolynomial (Fin 3) K)
            (Localization.Away (Work.MotV5.ASChart.GdivAS2L a b g))
            (Work.MotV5.ASChart.sdualAS2L a b g) := by
  -- `PhiL (sAS2L)^2 = PhiL (sAS2L ^ 2)`.
  rw [← map_pow]
  -- The link identity I3 at `y = stereoAS (C a) (C b) (pAS0L K) (chart3 K)`:
  -- `sAS2L ^ 2 = kleinSecDualAS (fwVecAS2L)`.
  have hI3 : (sAS2L a b g) ^ 2
      = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (fwVecAS2L a b g) := by
    simp only [sAS2L, fwVecAS2L]
    exact (Work.MotAS.KleinTwI3AS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      _ h5).symm
  rw [hI3]
  -- Naturality of the dual secant quintic moves `PhiL` inside.
  have hnat : PhiL a b g (Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (fwVecAS2L a b g))
      = Work.MotAS.kleinSecDualAS (PhiL a b g (MvPolynomial.C a)) (PhiL a b g (MvPolynomial.C b))
          (PhiL a b g (MvPolynomial.C g)) (fun i => PhiL a b g (fwVecAS2L a b g i)) := by
    let Φ : MvPolynomial (Fin 3) K →+* Localization.Away (GdivAS2L a b g) :=
      (PhiL a b g).toRingHom
    have h := Work.MotAS.KleinTwI3AS_map_kleinSecDualAS Φ (MvPolynomial.C a)
      (MvPolynomial.C b) (MvPolynomial.C g) (fwVecAS2L a b g)
    exact h.symm
  rw [hnat, hfw]
  -- Split the `algebraMap` of the product and apply the homogeneity (degree `5`).
  have hvec : (fun i => invGL a b g ^ 4 * algebraMap (MvPolynomial (Fin 3) K)
        (Localization.Away (GdivAS2L a b g))
        (cubAS2L a b g ^ 2 * sdualAS2L a b g * tchartL K i))
      = fun i => (invGL a b g ^ 4 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (GdivAS2L a b g))
          (cubAS2L a b g ^ 2 * sdualAS2L a b g))
          * algebraMap (MvPolynomial (Fin 3) K)
              (Localization.Away (GdivAS2L a b g)) (tchartL K i) := by
    funext i
    rw [map_mul]
    first | refl_ring1 | ring
  rw [hvec, Work.MotV5.ASChart.kleinSecDualAS_smul_free]
  -- The coefficients: `PhiL (C c) = algebraMap (C c)`.
  have hcast : ∀ c : K, PhiL a b g (MvPolynomial.C c) = algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (GdivAS2L a b g)) (MvPolynomial.C c) := by
    intro c
    rw [PhiL_C]
    have h := IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (GdivAS2L a b g)) c
    rw [MvPolynomial.algebraMap_eq] at h
    exact h.symm
  -- Naturality backwards identifies the remaining dual secant with `sdualAS2L`.
  rw [hcast a, hcast b, hcast g,
    show sdualAS2L a b g = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (tchartL K) from rfl,
    ← Work.MotAS.KleinTwI3AS_map_kleinSecDualAS
      (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g)))
      (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchartL K)]

end Work.MotV5.ASChart
