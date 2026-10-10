import Mathlib
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.CensusAS2
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Geometric bricks of the AS Crauder–Katz chart

The AS (`Work.MotAS`) mirror of the geometric layer of `MotK/KleinTwLink.lean`, needed by the chart
isomorphism `MotAS.CensusAS2.chartIso`:

* `kleinStereoAS_pi_aux` / `kleinStereoAS_pi` — the inverse-stereographic identity: the
  stereographic parametrisation at the point `x - x₀·p` of the line through `p` and `x` is
  `q(x)p - b(p,x)x` (so `∝ x` for `x` on the quadric).  Note that `MotK.kleinTwPi p x = x - x₀·p`
  is the projection onto the source hyperplane `{v₀ = 0}` only when `p₀ = 1`; the identity itself
  needs no hypothesis on `p₀`;
* the homogeneity lemmas of the AS link data in the coordinate vector: the quadric and the polar
  form are quadratic, the Pfaffians `kleinPAS` are quadratic, the inverse map `kleinRAS` is cubic,
  the stereographic parametrisation is quadratic, and the two secant quintics are quintic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace Work.MotAS

/-! ## The inverse-stereographic identity -/

/-- The unconditional form: the stereographic parametrisation at `v = x - x₀ p` is
`q(x)p - b(p,x)x`, corrected by the `q(p)`-terms. -/
theorem kleinStereoAS_pi_aux {K : Type*} [CommRing K] (a b : K) (p x : Fin 5 → K) :
    kleinStereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i
          - kleinQAS a b p * (x 0) ^ 2 * p i + 2 * kleinQAS a b p * x 0 * x i := by
  funext i
  simp only [kleinStereoAS, kleinBilinAS, kleinQAS, Work.MotK.kleinTwPi, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply]
  refl_ring1

/-- **The inverse-stereographic identity.**  For `p` on the AS quadric (`kleinQAS p = 0`), the
stereographic parametrisation at the point `v = x - x₀ p` of the line through `p` and `x` is
`q(x)·p - b(p,x)·x`; in particular `y(x - x₀p) = -b(p,x)·x` for `x` on the quadric. -/
theorem kleinStereoAS_pi {K : Type*} [CommRing K] (a b : K) (p x : Fin 5 → K)
    (hp : kleinQAS a b p = 0) :
    kleinStereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i := by
  rw [kleinStereoAS_pi_aux, hp]
  funext i
  refl_ring1

/-! ## Homogeneity of the AS link data -/

/-- The AS quadric is homogeneous of degree `2`. -/
theorem kleinQAS_smul {K : Type*} [CommRing K] (a b c : K) (v : Fin 5 → K) :
    kleinQAS a b (fun i => c * v i) = c ^ 2 * kleinQAS a b v := by
  simp only [kleinQAS, Pi.mul_apply]
  refl_ring1

/-- The polar form is bilinear: linear in its second argument. -/
theorem kleinBilinAS_smul_right {K : Type*} [CommRing K] (a b c : K) (u v : Fin 5 → K) :
    kleinBilinAS a b u (fun i => c * v i) = c * kleinBilinAS a b u v := by
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS Pfaffian vector. -/
theorem kleinPAS0_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS0 a b g (fun i => c * v i) = c ^ 2 * kleinPAS0 a b g v := by
  simp only [kleinPAS0, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS Pfaffian vector. -/
theorem kleinPAS1_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS1 a b g (fun i => c * v i) = c ^ 2 * kleinPAS1 a b g v := by
  simp only [kleinPAS1, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS Pfaffian vector. -/
theorem kleinPAS2_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS2 a b g (fun i => c * v i) = c ^ 2 * kleinPAS2 a b g v := by
  simp only [kleinPAS2, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS Pfaffian vector. -/
theorem kleinPAS3_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS3 a b g (fun i => c * v i) = c ^ 2 * kleinPAS3 a b g v := by
  simp only [kleinPAS3, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS Pfaffian vector. -/
theorem kleinPAS4_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS4 a b g (fun i => c * v i) = c ^ 2 * kleinPAS4 a b g v := by
  simp only [kleinPAS4, Pi.mul_apply]
  refl_ring1

/-- The AS Pfaffians are homogeneous of degree `2`. -/
theorem kleinPAS_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinPAS a b g (fun i => c * v i) = fun i => c ^ 2 * kleinPAS a b g v i := by
  funext i
  fin_cases i
  · simpa [kleinPAS] using kleinPAS0_smul a b g c v
  · simpa [kleinPAS] using kleinPAS1_smul a b g c v
  · simpa [kleinPAS] using kleinPAS2_smul a b g c v
  · simpa [kleinPAS] using kleinPAS3_smul a b g c v
  · simpa [kleinPAS] using kleinPAS4_smul a b g c v

/-- Homogeneity of the components of the AS inverse quadro-cubic map. -/
theorem kleinRAS0_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS0 a b g (fun i => c * v i) = c ^ 3 * kleinRAS0 a b g v := by
  simp only [kleinRAS0, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS inverse quadro-cubic map. -/
theorem kleinRAS1_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS1 a b g (fun i => c * v i) = c ^ 3 * kleinRAS1 a b g v := by
  simp only [kleinRAS1, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS inverse quadro-cubic map. -/
theorem kleinRAS2_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS2 a b g (fun i => c * v i) = c ^ 3 * kleinRAS2 a b g v := by
  simp only [kleinRAS2, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS inverse quadro-cubic map. -/
theorem kleinRAS3_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS3 a b g (fun i => c * v i) = c ^ 3 * kleinRAS3 a b g v := by
  simp only [kleinRAS3, Pi.mul_apply]
  refl_ring1

/-- Homogeneity of the components of the AS inverse quadro-cubic map. -/
theorem kleinRAS4_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS4 a b g (fun i => c * v i) = c ^ 3 * kleinRAS4 a b g v := by
  simp only [kleinRAS4, Pi.mul_apply]
  refl_ring1

/-- The AS inverse quadro-cubic map is homogeneous of degree `3`. -/
theorem kleinRAS_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinRAS a b g (fun i => c * v i) = fun i => c ^ 3 * kleinRAS a b g v i := by
  funext i
  fin_cases i
  · simpa [kleinRAS] using kleinRAS0_smul a b g c v
  · simpa [kleinRAS] using kleinRAS1_smul a b g c v
  · simpa [kleinRAS] using kleinRAS2_smul a b g c v
  · simpa [kleinRAS] using kleinRAS3_smul a b g c v
  · simpa [kleinRAS] using kleinRAS4_smul a b g c v

/-- The stereographic parametrisation is homogeneous of degree `2`. -/
theorem kleinStereoAS_smul {K : Type*} [CommRing K] (a b c : K) (p v : Fin 5 → K) :
    kleinStereoAS a b p (fun i => c * v i) = fun i => c ^ 2 * kleinStereoAS a b p v i := by
  funext i
  simp only [kleinStereoAS, Pi.mul_apply, kleinQAS_smul, kleinBilinAS_smul_right]
  refl_ring1

/-- The AS target dual secant quintic is homogeneous of degree `5`. -/
theorem kleinSecDualAS_smul {K : Type*} [CommRing K] (a b g c : K) (v : Fin 5 → K) :
    kleinSecDualAS a b g (fun i => c * v i) = c ^ 5 * kleinSecDualAS a b g v := by
  simp only [kleinSecDualAS, Pi.mul_apply]
  refl_ring1

/-- The polar form at the projection: `b(p, x - x₀·p) = b(p,x) - x₀·b(p,p)`. -/
theorem kleinBilinAS_pi_aux {K : Type*} [CommRing K] (a b : K) (p x : Fin 5 → K) :
    kleinBilinAS a b p (Work.MotK.kleinTwPi p x)
      = kleinBilinAS a b p x - x 0 * kleinBilinAS a b p p := by
  simp only [kleinBilinAS, kleinQAS, Work.MotK.kleinTwPi, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply]
  refl_ring1

/-- The polar form of the quadric is `2 q`: `b(p,p) = 2 q(p)`. -/
theorem kleinBilinAS_self {K : Type*} [CommRing K] (a b : K) (p : Fin 5 → K) :
    kleinBilinAS a b p p = 2 * kleinQAS a b p := by
  have hp : p + p = fun i => (2 : K) * p i := by
    funext i
    simp only [Pi.add_apply]
    refl_ring1
  simp only [kleinBilinAS, hp, kleinQAS_smul]
  refl_ring1

/-- **`π_p` does not change the polar form at a point `p` of the quadric**:
`b(p, x - x₀·p) = b(p,x)` for `q(p) = 0`. -/
theorem kleinBilinAS_pi_eq {K : Type*} [CommRing K] (a b : K) (p x : Fin 5 → K)
    (hp : kleinQAS a b p = 0) :
    kleinBilinAS a b p (Work.MotK.kleinTwPi p x) = kleinBilinAS a b p x := by
  rw [kleinBilinAS_pi_aux, kleinBilinAS_self, hp]
  refl_ring1

/-- **`q^AS` at the inverse link map, from the AS link identity `I2`**: since
`kleinPAS 4 = -kleinQAS` and `P^AS(R^AS z) = s'^AS(z)·z`, the quadric vanishes on `R^AS z` exactly
where `z₄ = 0` (the target hyperplane). -/
theorem kleinQAS_kleinRAS_of_I2 {K : Type*} [CommRing K] (a b g : K) (z : Fin 5 → K)
    (hI2 : kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i) :
    kleinQAS a b (kleinRAS a b g z) = -(kleinSecDualAS a b g z * z 4) := by
  have h4 : kleinPAS a b g (kleinRAS a b g z) 4 = kleinSecDualAS a b g z * z 4 := congrFun hI2 4
  rw [kleinPAS_four_eq_neg] at h4
  linear_combination (norm := refl_ring1) -h4

/-- **`q^AS (R^AS z) = 0` on the target hyperplane** (`z₄ = 0`), the input of the target-side chart
identity: this is `kleinQAS_kleinRAS_of_I2` at `z₄ = 0`. -/
theorem kleinQAS_kleinRAS_of_zero {K : Type*} [CommRing K] (a b g : K) (z : Fin 5 → K)
    (hI2 : kleinPAS a b g (kleinRAS a b g z) = fun i => kleinSecDualAS a b g z * z i)
    (hz : z 4 = 0) : kleinQAS a b (kleinRAS a b g z) = 0 := by
  rw [kleinQAS_kleinRAS_of_I2 a b g z hI2, hz, mul_zero, neg_zero]

end Work.MotAS
