import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.ASZChartSetup
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.asY0_curve` — the generic point of the twisted Klein curve lies on it

The `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.asY0_curve`
(`Submission/Work/MotAS/asY0_curve.lean`): the projective Lagrange coordinates
`asY0 D g j = asTwY D g j / asTwY D g 0` of the Artin–Schreier twisted Klein curve satisfy the
twisted Pfaffians `kleinPAS`, in the fraction field `RatFunc ↥(twistFieldAS D g)` of the twist
field.

The homogeneous input is `asTwY_kleinPAS_gen` below (the `K`-generic form of
`Work.MotC5N3.kleinPAS_asTwY`): `kleinPAS a b g (asTwY D g) = 0` in `OmA K D` for `D.Good`.  Each
`kleinPAS_k` is homogeneous of degree `2` in its argument (`Work.MotAS.kleinPAS_smul`), and `asY0`
is the image of `asTwY` under the scalar `(asTwY 0)⁻¹` — the identity
`kleinPAS (λ • y) = λ ^ 2 • kleinPAS y` needs no nonvanishing of `λ`.  Finally `kleinPAS` is
natural in the coefficient ring (`Work.MotAS.map_kleinPAS_apply`), which pushes the identity first
to `↥(twistFieldAS D g)` (whose inclusion into `OmA K D` is injective) and then to
`RatFunc ↥(twistFieldAS D g)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotC5N3

/-- The residual characteristic of `𝕜` is `5` as soon as `K` is a `𝕜`-algebra field of
characteristic `5` (the algebra map is injective). -/
theorem charP_of_algebra_charP_lemma {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]
    [CharP K 5] : CharP 𝕜 5 :=
  RingHom.charP (algebraMap 𝕜 K) (algebraMap 𝕜 K).injective 5

variable {𝕜 : Type} [Field 𝕜]
variable {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- The five AS Pfaffians evaluated at the Lagrange coordinates `asTwY D g` vanish: this is the
transport `asTransportP` of the Klein relation `D.Good.klein_eq` along `x = asM w · y`. -/
theorem asTwY_kleinPAS_gen (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (g : K) :
    Work.MotAS.kleinPAS (algebraMap 𝕜 (OmA K D) D.a)
        (algebraMap 𝕜 (OmA K D) D.b)
        (algebraMap K (OmA K D) g) (asTwY D g) = 0 := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP_lemma (𝕜 := 𝕜) (K := K)
  have h5 : (5 : OmA K D) = 0 := five_eq_zero_OmA 𝕜 D
  set w : OmA K D :=
    algebraMap (KbA K) (OmA K D) (asRoot g) with hwdef
  have hw : w ^ 5 = w + algebraMap K (OmA K D) g := by
    rw [hwdef]
    have h := congrArg (algebraMap (KbA K) (OmA K D)) (asRoot_spec (K := K) g)
    simp only [map_sub, map_pow] at h
    rw [← IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) g] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hM : Work.MotAS.asM w = asMO D g := by
    ext i j
    rw [hwdef]
    simp only [Work.MotAS.asM, asMO, Matrix.of_apply, Matrix.map_apply, map_add, map_pow,
      map_natCast]
  have hmv : (fun i => ∑ j, Work.MotAS.asM w i j * asTwY D g j) = asKap D g := by
    funext i
    have h1 : (∑ j, Work.MotAS.asM w i j * asTwY D g j) = ((asMO D g).mulVec (asTwY D g)) i := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by
        rw [congrFun (congrFun hM i) j]
    rw [h1, asMO_mulVec_asTwY]
  have hzero : Work.MotK.kleinP (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (asKap D g) = 0 := by
    funext k
    exact hD.klein_eq (KbA K) k
  have htr := Work.MotAS.asTransportP (algebraMap 𝕜 (OmA K D) D.a)
    (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) w h5 hw (asTwY D g)
  rw [hmv] at htr
  rw [hzero] at htr
  refine Work.MotAS.asN_mulVec_injective h5 w ?_
  rw [← htr]
  simp

theorem asY0_curve (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    ∀ k : Fin 5, Work.MotAS.kleinPAS
        (algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.a)
        (algebraMap 𝕜 (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) D.b)
        (algebraMap K (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) g)
        (fun j => algebraMap ↥(Work.MotC5N3.twistFieldAS D g)
          (RatFunc ↥(Work.MotC5N3.twistFieldAS D g)) (Work.MotC5N3.asY0 D g j)) k = 0 := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP_lemma (𝕜 := 𝕜) (K := K)
  have hraw : Work.MotAS.kleinPAS (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) (asTwY D g) = 0 :=
    asTwY_kleinPAS_gen D hD.1 g
  -- normalise by `asTwY 0` (homogeneity of degree `2`; no nonvanishing needed)
  have hnorm : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap 𝕜 (OmA K D) D.a)
        (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g)
        (fun j => (Work.MotC5N3.asY0 D g j : OmA K D)) k = 0 := by
    intro k
    have heq : (fun j => (Work.MotC5N3.asY0 D g j : OmA K D))
        = fun j => (asTwY D g 0)⁻¹ * asTwY D g j := by
      funext j
      show asTwY D g j / asTwY D g 0 = (asTwY D g 0)⁻¹ * asTwY D g j
      rw [div_eq_mul_inv, mul_comm]
    have hrawk : Work.MotAS.kleinPAS (algebraMap 𝕜 (OmA K D) D.a)
        (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g) (asTwY D g) k = 0 := by
      simpa using congrFun hraw k
    have hsmul := congrFun (Work.MotAS.kleinPAS_smul (algebraMap 𝕜 (OmA K D) D.a)
      (algebraMap 𝕜 (OmA K D) D.b) (algebraMap K (OmA K D) g)
      ((asTwY D g 0)⁻¹) (asTwY D g)) k
    rw [heq, hsmul, hrawk, mul_zero]
  -- descend to the twist field
  have hT : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
        (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
        (algebraMap K ↥(twistFieldAS D g) g)
        (Work.MotC5N3.asY0 D g) k = 0 := by
    intro k
    have hinj : Function.Injective (algebraMap ↥(twistFieldAS D g) (OmA K D)) :=
      fun x y h => Subtype.ext (by simpa using h)
    have tower_a : algebraMap 𝕜 (OmA K D) D.a
        = algebraMap ↥(twistFieldAS D g) (OmA K D)
            (algebraMap 𝕜 ↥(twistFieldAS D g) D.a) := by
      calc algebraMap 𝕜 (OmA K D) D.a
          = algebraMap K (OmA K D) (algebraMap 𝕜 K D.a) :=
            IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.a
        _ = algebraMap ↥(twistFieldAS D g) (OmA K D)
              (algebraMap K ↥(twistFieldAS D g) (algebraMap 𝕜 K D.a)) :=
            IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D) _
        _ = algebraMap ↥(twistFieldAS D g) (OmA K D)
              (algebraMap 𝕜 ↥(twistFieldAS D g) D.a) :=
            congrArg (algebraMap ↥(twistFieldAS D g) (OmA K D))
              (IsScalarTower.algebraMap_apply 𝕜 K ↥(twistFieldAS D g) D.a).symm
    have tower_b : algebraMap 𝕜 (OmA K D) D.b
        = algebraMap ↥(twistFieldAS D g) (OmA K D)
            (algebraMap 𝕜 ↥(twistFieldAS D g) D.b) := by
      calc algebraMap 𝕜 (OmA K D) D.b
          = algebraMap K (OmA K D) (algebraMap 𝕜 K D.b) :=
            IsScalarTower.algebraMap_apply 𝕜 K (OmA K D) D.b
        _ = algebraMap ↥(twistFieldAS D g) (OmA K D)
              (algebraMap K ↥(twistFieldAS D g) (algebraMap 𝕜 K D.b)) :=
            IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D) _
        _ = algebraMap ↥(twistFieldAS D g) (OmA K D)
              (algebraMap 𝕜 ↥(twistFieldAS D g) D.b) :=
            congrArg (algebraMap ↥(twistFieldAS D g) (OmA K D))
              (IsScalarTower.algebraMap_apply 𝕜 K ↥(twistFieldAS D g) D.b).symm
    have tower_g : algebraMap K (OmA K D) g
        = algebraMap ↥(twistFieldAS D g) (OmA K D)
            (algebraMap K ↥(twistFieldAS D g) g) :=
      IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (OmA K D) g
    have hmap := Work.MotAS.map_kleinPAS_apply (algebraMap ↥(twistFieldAS D g) (OmA K D))
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
      (algebraMap K ↥(twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) k
    refine hinj ?_
    rw [map_zero, hmap, ← tower_a, ← tower_b, ← tower_g]
    exact hnorm k
  -- push to `RatFunc ↥(twistFieldAS D g)`
  intro k
  have hmap := Work.MotAS.map_kleinPAS_apply (algebraMap ↥(twistFieldAS D g)
      (RatFunc ↥(twistFieldAS D g))) (algebraMap 𝕜 ↥(twistFieldAS D g) D.a)
    (algebraMap 𝕜 ↥(twistFieldAS D g) D.b)
    (algebraMap K ↥(twistFieldAS D g) g) (Work.MotC5N3.asY0 D g) k
  rw [IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (RatFunc ↥(twistFieldAS D g)) D.a,
    IsScalarTower.algebraMap_apply 𝕜 ↥(twistFieldAS D g) (RatFunc ↥(twistFieldAS D g)) D.b,
    IsScalarTower.algebraMap_apply K ↥(twistFieldAS D g) (RatFunc ↥(twistFieldAS D g)) g,
    ← hmap, hT k, map_zero]

end Work.MotC5N3
