import Mathlib
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.ASChart2Units
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.KleinTwI2ASb
import Submission.Work.MotAS.KleinTwI4ASb
import Submission.Work.MotAS.KleinLinkUnitAS_free
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASChart2Idents` — the two ring identities of the corrected AS chart maps

These are the `AS` analogues of `MotK.TGen.KleinTwLinkComp2` (the composition `χ ∘ f`, i.e.
`π_p ∘ R^AS ∘ P^AS` on the chart) and of `MotK.TGen.FwVecRingId` (the composition `f ∘ χ`, i.e.
`P^AS ∘ Stereo^AS ∘ π_p ∘ R^AS` on the chart).  Unlike the split model, both are *short* here
because the two AS link identities

* `Work.MotAS.KleinTwScalarASv` : `R^AS (P^AS y) = s^AS(y) • y`  (w-free, **proved**),
* I2 (`Work.MotAS.KleinTwI2ASb`) : `P^AS (R^AS z) = s'^AS(z) • z`  (w-free),

reduce them to `kleinStereoAS_pi` / `kleinBilinAS_pi_eq` plus homogeneity; no big polynomial
certificate is involved.

The second identity is stated relative to I2 as an explicit hypothesis so that it can be reused
before/independently of the final w-free statement of I2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
namespace Work.MotAS

open MvPolynomial

/-! ## `π_p ∘ R^AS ∘ P^AS` on the chart -/

/-- **The composition `χ ∘ f` at the vector level.**  For `p` on the quadric with `p 0 = 1` and
`v` with `v 0 = 0`, the projection of `R^AS (P^AS (y^AS(v)))` is the scalar multiple
`-b(p,v)·s^AS(y^AS(v))` of `v`. -/
theorem KleinTwLinkComp2AS {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R)
    (p v : Fin 5 → R) (hp : kleinQAS a b p = 0) (hp0 : p 0 = 1) (hv0 : v 0 = 0) :
    Work.MotK.kleinTwPi p (kleinRAS a b g (kleinPAS a b g (kleinStereoAS a b p v)))
      = fun i => -(kleinBilinAS a b p v * kleinSecAS a b g (kleinStereoAS a b p v)) * v i := by
  have h1 : kleinRAS a b g (kleinPAS a b g (kleinStereoAS a b p v))
      = fun i => kleinSecAS a b g (kleinStereoAS a b p v) * kleinStereoAS a b p v i :=
    KleinTwScalarASv a b g (kleinStereoAS a b p v) h5
  rw [h1, kleinTwPi_smul]
  have h2 : Work.MotK.kleinTwPi p (kleinStereoAS a b p v)
      = fun i => -(kleinBilinAS a b p v) * v i := by
    funext i
    simp only [Work.MotK.kleinTwPi, kleinStereoAS, Pi.sub_apply, Pi.mul_apply, hp0, hv0,
      mul_one, mul_zero, sub_zero, sub_self]
    first | refl_ring1 | ring
  rw [h2]
  funext i
  first | refl_ring1 | ring

/-- **The composition `χ ∘ f` on the chart of the certificate**:
`π_{pAS0} (R^AS (P^AS (y^AS(chart3)))) = -(GambAS2) • chart3`. -/
theorem KleinTwLinkComp2AS_chart {K : Type*} [Field K]
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (a b g : K) :
    Work.MotK.kleinTwPi (pAS0 K) (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C g) (fwVecAS2 a b g))
      = fun i => -(GambAS2 a b g) * Work.MotK.chart3 K i := by
  have h := KleinTwLinkComp2AS h5 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (pAS0 K) (Work.MotK.chart3 K) (kleinQAS_pAS0 a b) rfl rfl
  have h2 : (fun i => -(GambAS2 a b g) * Work.MotK.chart3 K i)
      = fun i => -(kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
              (Work.MotK.chart3 K)
            * kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
                  (Work.MotK.chart3 K))) * Work.MotK.chart3 K i := by
    funext i
    simp only [GambAS2, kleinFhomAS]
  have hfw : fwVecAS2 a b g
      = kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)) :=
    rfl
  rw [h2, hfw]
  exact h

/-! ## `P^AS ∘ Stereo^AS ∘ π_p ∘ R^AS` on the chart -/

/-- **The composition `f ∘ χ` at the vector level.**  For `p` on the quadric and `w` in the target
hyperplane `{w 4 = 0}` (so that `R^AS w` lies on the quadric), the forward map at the projection of
`R^AS w` is the scalar multiple `b(p, R^AS w)^2 · s'^AS(w)` of `w`. -/
theorem FwVecRingIdAS {R : Type*} [CommRing R] (a b g : R) (p w : Fin 5 → R)
    (hp : kleinQAS a b p = 0) (hw : w 4 = 0)
    (hI2 : kleinPAS a b g (kleinRAS a b g w) = fun i => kleinSecDualAS a b g w * w i) :
    kleinPAS a b g (kleinStereoAS a b p (Work.MotK.kleinTwPi p (kleinRAS a b g w)))
      = fun i => (kleinBilinAS a b p (kleinRAS a b g w)) ^ 2 * kleinSecDualAS a b g w * w i := by
  have h4 := congrFun hI2 4
  rw [kleinPAS_four_eq_neg, hw, mul_zero] at h4
  have hq : kleinQAS a b (kleinRAS a b g w) = 0 := neg_eq_zero.mp h4
  have hst : kleinStereoAS a b p (Work.MotK.kleinTwPi p (kleinRAS a b g w))
      = fun i => -(kleinBilinAS a b p (kleinRAS a b g w)) * kleinRAS a b g w i := by
    rw [kleinStereoAS_pi a b p (kleinRAS a b g w) hp, hq]
    funext i
    first | refl_ring1 | ring
  rw [hst, kleinPAS_smul, hI2]
  funext i
  first | refl_ring1 | ring

/-- **The composition `f ∘ χ` on the chart of the certificate**:
`P^AS (y^AS(π_{pAS0} (R^AS (tchart)))) = cubAS2² · sdualAS2 • tchart`. -/
theorem FwVecRingIdAS_chart {K : Type*} [Field K]
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (a b g : K)
    (hI2 : kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = fun i => kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (tchart K) * tchart K i) :
    kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (bwVecAS2 a b g))
      = fun i => cubAS2 a b g ^ 2 * sdualAS2 a b g * tchart K i := by
  have hbw : bwVecAS2 a b g
      = Work.MotK.kleinTwPi (pAS0 K)
          (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K)) :=
    rfl
  rw [hbw]
  have h := FwVecRingIdAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (pAS0 K)
    (tchart K) (kleinQAS_pAS0 a b) rfl hI2
  rw [h]
  rw [show kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
        (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = cubAS2 a b g from rfl,
    show kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K)
      = sdualAS2 a b g from rfl]

/-! ## The two vector identities at the chart, with the link identities substituted -/

/-- **The source equation at `R^AS (tchart)`**:  on the quadric, `F^AS(p, R^AS z)` is the unit
multiple `-(cubAS2⁶ · sdualAS2³)` of the target equation.  (The AS form of
`MotK.kleinTwFhom_kleinTwR`.) -/
theorem KleinFhom_kleinRAS_chart {K : Type*} [Field K]
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (a b g : K) :
    kleinFhomAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (pAS0 K)
        (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = -(cubAS2 a b g ^ 6 * sdualAS2 a b g ^ 3) := by
  have hI2 := KleinTwI2ASb (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K) h5
  have hq : kleinQAS (MvPolynomial.C a) (MvPolynomial.C b)
      (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K)) = 0 := by
    have h4 := congrFun hI2 4
    rw [kleinPAS_four_eq_neg, tchart_four, mul_zero] at h4
    exact neg_eq_zero.mp h4
  have hst : kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
      (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = fun i => -(kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
            (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K)))
          * kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K) i := by
    funext i
    simp only [kleinStereoAS, hq, zero_mul, zero_sub]
    first | refl_ring1 | ring
  have hI4 : kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
      (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = sdualAS2 a b g ^ 3 :=
    KleinTwI4ASb (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K) h5 hI2
  rw [kleinFhomAS]
  rw [hst]
  rw [kleinSecAS_smul]
  rw [hI4]
  rw [show kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
        (kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchart K))
      = cubAS2 a b g from rfl]
  first | refl_ring1 | ring

/-- **The target equation at `P^AS (y^AS(chart3))`**:  the unit condition of the AS link at the
stereographic point `p = pAS0` and the source chart `chart3`, proved from the link identities I1
(`KleinTwScalarASv`) and I3 (`KleinTwI3AS`) and the stereographic polar identity. -/
theorem KleinGhom_fwVecAS_chart {K : Type*} [Field K]
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (a b g : K) :
    kleinGhomAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (pAS0 K)
        (fwVecAS2 a b g)
      = -(sAS2 a b g ^ 2 * linAS2 a b * GambAS2 a b g) := by
  have h := KleinLinkUnitAS_free h5 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (pAS0 K) (Work.MotK.chart3 K) (kleinQAS_pAS0 a b)
  have hfw : fwVecAS2 a b g
      = kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
            (Work.MotK.chart3 K)) := rfl
  rw [hfw, h]
  rw [show sAS2 a b g = kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K))
      from rfl,
    show linAS2 a b = kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K)
        (Work.MotK.chart3 K) from rfl,
    show GambAS2 a b g = kleinFhomAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (pAS0 K) (Work.MotK.chart3 K) from rfl]
  first | refl_ring1 | ring

end Work.MotAS
