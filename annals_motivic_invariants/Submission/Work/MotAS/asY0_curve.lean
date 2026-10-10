import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwProjAS
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotAS.asY0_curve` — the generic point of the twisted Klein curve lies on it

`asY0 D g j = asTwY D g j / asTwY D g 0` is the projective normalisation of the Lagrange
coordinates (`Submission/Work/MotAS/SdualAS2Defs.lean`), viewed in
`R = RatFunc ↥(twistFieldAS D g)`.

The homogeneous input is `asTwY_kleinPAS` below (the same statement as
`Work.MotAS.kleinPAS_asTwY` of `Submission/Work/MotAS/ASZChartPresentation.lean`, proved here so
that this file does not depend on it): `kleinPAS a b g (asTwY D g) = 0` in `Om D` under `D.Good` —
it is `asTransportP` applied to `D.Good.klein_eq` together with `asN_mulVec_injective`.  Each
`kleinPAS_k` is homogeneous of degree `2` in its argument (`Work.MotAS.kleinPAS_smul`), and `asY0`
is the image of `asTwY` under the scalar `(asTwY 0)⁻¹` — the identity
`kleinPAS (λ • y) = λ ^ 2 • kleinPAS y` needs no nonvanishing of `λ`.  Finally `kleinPAS` is
natural in the coefficient ring (`Work.MotAS.map_kleinPAS`), which pushes the identity first to
`↥(twistFieldAS D g)` (whose inclusion into `Om D` is injective) and then to
`RatFunc ↥(twistFieldAS D g)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open Work.MotV

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The Lagrange coordinates of the twisted Klein curve satisfy the twisted Pfaffians. -/
theorem asTwY_kleinPAS (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : RatFunc 𝕜) :
    Work.MotAS.kleinPAS (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
        (Work.MotAS.asTwY D g) = 0 := by
  have h5 : (5 : Work.MotV.Om D) = 0 := Work.MotAS.five_eq_zero_Om 𝕜 D
  set w : Work.MotV.Om D :=
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) with hw
  have hw' : w ^ 5 = w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g := by
    have h := congrArg (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D))
      (Work.MotV5.asRoot_spec (𝕜 := 𝕜) g)
    simp only [map_sub, map_pow] at h
    rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g] at h
    rw [hw]
    exact sub_eq_iff_eq_add'.mp h
  have hM : asM w = asMO D g := by
    ext i j
    rw [hw]
    simp only [asM, asMO, Matrix.of_apply, Matrix.map_apply, asOM, map_add, map_pow, map_natCast]
  have hmv : (fun i => ∑ j, asM w i j * Work.MotAS.asTwY D g j)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) := by
    funext i
    have h1 : (∑ j, asM w i j * Work.MotAS.asTwY D g j)
        = ((asMO D g).mulVec (Work.MotAS.asTwY D g)) i := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [congrFun (congrFun hM i) j]
    rw [h1, asMO_mulVec_asTwY]
    rfl
  have htr := Work.MotAS.asTransportP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
    (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g) w h5 hw'
    (Work.MotAS.asTwY D g)
  rw [hmv] at htr
  have hzero : Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜)) = 0 := by
    funext k
    exact hD.1.klein_eq (Work.MotV.Kb 𝕜) k
  rw [hzero] at htr
  refine Work.MotAS.asN_mulVec_injective h5 w ?_
  rw [← htr]
  simp

/-- Vanishing of `kleinPAS` descends along an injective ring homomorphism. -/
theorem kleinPAS_eq_zero_of_map_eq_zero {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (a b g : A) (y : Fin 5 → A)
    (h : ∀ k, Work.MotAS.kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) k = 0) :
    ∀ k, Work.MotAS.kleinPAS a b g y k = 0 := by
  intro k
  refine hφ ?_
  rw [map_kleinPAS_apply φ a b g y k, h k, map_zero]

theorem asY0_curve (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : RatFunc 𝕜) :
    ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.a)
        (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.b)
        (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D g)) g)
        (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D g)
          (RatFunc ↥(Work.MotAS.twistFieldAS D g)) (Work.MotAS.asY0 D g j)) k = 0 := by
  -- normalise by `asTwY 0` (homogeneity of degree `2`; no nonvanishing needed)
  have hnorm : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
        (fun j => (Work.MotAS.asY0 D g j : Work.MotV.Om D)) k = 0 := by
    intro k
    have heq : (fun j => (Work.MotAS.asY0 D g j : Work.MotV.Om D))
        = fun j => (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g j := by
      funext j
      show Work.MotAS.asTwY D g j / Work.MotAS.asTwY D g 0
        = (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g j
      rw [div_eq_mul_inv, mul_comm]
    have hraw : Work.MotAS.kleinPAS (algebraMap 𝕜 (Work.MotV.Om D) D.a)
        (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
        (Work.MotAS.asTwY D g) k = 0 := by
      simpa using congrFun (asTwY_kleinPAS D hD g) k
    have hsmul := congrFun (Work.MotAS.kleinPAS_smul (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
      ((Work.MotAS.asTwY D g 0)⁻¹) (Work.MotAS.asTwY D g)) k
    rw [heq, hsmul, hraw, mul_zero]
  -- descend to the twist field
  have hT : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
        (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g)
        (Work.MotAS.asY0 D g) k = 0 := by
    intro k
    have hinj : Function.Injective (algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)) :=
      fun x y h => Subtype.ext (by simpa using h)
    have hmap := map_kleinPAS_apply (algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D))
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g) (Work.MotAS.asY0 D g) k
    have tower_a : algebraMap 𝕜 (Work.MotV.Om D) D.a
        = algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a) := by
      rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.a,
        IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
          (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a),
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) D.a]
    have tower_b : algebraMap 𝕜 (Work.MotV.Om D) D.b
        = algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b) := by
      rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.b,
        IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
          (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b),
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) D.b]
    refine hinj ?_
    rw [map_zero, hmap, ← tower_a, ← tower_b,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
        (Work.MotV.Om D) g]
    exact hnorm k
  -- push to `RatFunc ↥(twistFieldAS D g)`
  intro k
  have hmap := map_kleinPAS_apply (algebraMap ↥(Work.MotAS.twistFieldAS D g)
      (RatFunc ↥(Work.MotAS.twistFieldAS D g))) (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
    (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
    (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g) (Work.MotAS.asY0 D g) k
  have hmap0 : Work.MotAS.kleinPAS
      (algebraMap ↥(Work.MotAS.twistFieldAS D g) (RatFunc ↥(Work.MotAS.twistFieldAS D g))
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a))
      (algebraMap ↥(Work.MotAS.twistFieldAS D g) (RatFunc ↥(Work.MotAS.twistFieldAS D g))
        (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b))
      (algebraMap ↥(Work.MotAS.twistFieldAS D g) (RatFunc ↥(Work.MotAS.twistFieldAS D g))
        (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g))
      (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) (Work.MotAS.asY0 D g j)) k = 0 := by
    rw [← hmap, hT k, map_zero]
  first
  | simpa only [IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.a,
      IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.b,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) g] using hmap0
  | simpa only [IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.a,
      IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D g)
        (RatFunc ↥(Work.MotAS.twistFieldAS D g)) D.b] using hmap0
  | exact hmap0

end Work.MotAS
