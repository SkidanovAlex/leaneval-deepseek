import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotV.Defs
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.CensusBridge.isFractionRing_adjoin_range_ratFunc
import Submission.Work.MotK.LinkCertDefs
import Submission.Work.MotK.ChartCompC
import Submission.Work.MotK.ChartAeval.fhatC_four_ne_zero
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.FwVec4Rational` — the quartic `f̂₄ = fwVec a b h 4` is a rational (junk) divisor

`fwVec a b h 4 = f̂₄` is the fourth component of the forward link map `f = kleinTwP ∘ kleinTwStereo`
of the `T`-twisted Crauder–Katz link on the affine chart `chart3 = ![0, x₀, x₁, x₂, 1]`, i.e. the
denominator of the affine coordinates `φ_j = f̂_{j+1}/f̂₄` of that map.  Geometrically
`{f̂₄ = 0}` is the preimage of the hyperplane at infinity `{w₄ = 0}` of the target chart under the
birational map `f`, hence a rational surface.

The parametrisation used here is the inverse link map `χ = π_p ∘ kleinTwR` restricted to the target
plane `{w₀ = 0, w₄ = 0}`; in the affine chart `w₃ = 1` of that plane (coordinates `u, v`) its
homogeneous coordinates are the cubic forms

  `χ₁ = a b² h (a - b h u² v)`,
  `χ₂ = a b h (a² h u² - a b h u³ - b² h u v² + b² v)`,
  `χ₃ = b h (a - b u) (a² u - b² v²)`,
  `χ₄ = -a² h v (a² u - b² v²)`,

so that the parametrisation of the surface is the rational map

  `(u,v) ↦ (χ₁/χ₄, χ₂/χ₄, χ₃/χ₄) =: (p₀, p₁, p₂)`.

The file proves that the substitution `θ : K[x₀,x₁,x₂] → K(u,v)`, `x_j ↦ p_j`, has kernel exactly
`(f̂₄)`, and reads off the result: `(f̂₄)` is a height-one prime whose residue field is
`K(u,v) = RatFunc (RatFunc K)`, i.e. the divisor is *junk* in the sense of the census.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K]

/-! ## The parametrisation of the surface `{f̂₄ = 0}` -/

/-- The first coordinate `χ₁` of the inverse link map on the plane `{w₀ = 0, w₄ = 0}`, in the
affine chart `w₃ = 1` (coordinates `u = X 0`, `v = X 1`). -/
def pl1 (a b h : K) : MvPolynomial (Fin 2) K :=
  C (a * b ^ 2 * h) * (C a - C (b * h) * X 0 ^ 2 * X 1)

/-- The second coordinate `χ₂`. -/
def pl2 (a b h : K) : MvPolynomial (Fin 2) K :=
  C (a * b * h) * (-(C (a ^ 2 * h) * X 0 ^ 2) + C (a * b * h) * X 0 ^ 3
    + C (b ^ 2 * h) * X 0 * X 1 ^ 2 - C (b ^ 2) * X 1)

/-- The third coordinate `χ₃`. -/
def pl3 (a b h : K) : MvPolynomial (Fin 2) K :=
  C (b * h) * (C a - C b * X 0) * (C (a ^ 2) * X 0 - C (b ^ 2) * X 1 ^ 2)

/-- The fourth coordinate `χ₄` (the denominator of the parametrisation). -/
def pl4 (a b h : K) : MvPolynomial (Fin 2) K :=
  (-(C (a ^ 2 * h) * X 1)) * (C (a ^ 2) * X 0 - C (b ^ 2) * X 1 ^ 2)

theorem pl4_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : pl4 a b h ≠ 0 := by
  have hA : ((-(C (a ^ 2 * h) * X (1 : Fin 2))) : MvPolynomial (Fin 2) K) ≠ 0 := by
    rw [neg_ne_zero]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 ha) hh))
      (MvPolynomial.X_ne_zero 1)
  have hB : ((C (a ^ 2) * X (0 : Fin 2) - C (b ^ 2) * X (1 : Fin 2) ^ 2 :
      MvPolynomial (Fin 2) K)) ≠ 0 := by
    intro hc
    have h := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : K) else 0)) hc
    simp only [map_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval_pow] at h
    simp at h
    exact ha h
  rw [pl4]
  intro hc
  exact mul_ne_zero hA hB hc

/-- **The parametrisation of `{f̂₄ = 0}`**: the three affine coordinates of the inverse link map
`χ = π_p ∘ kleinTwR` on the plane `{w₀ = 0, w₄ = 0}`, in the chart `w₃ = 1` of that plane. -/
def fwParam (a b h : K) : Fin 3 → FractionRing (MvPolynomial (Fin 2) K) :=
  ![algebraMap _ _ (pl1 a b h) * (algebraMap _ _ (pl4 a b h))⁻¹,
    algebraMap _ _ (pl2 a b h) * (algebraMap _ _ (pl4 a b h))⁻¹,
    algebraMap _ _ (pl3 a b h) * (algebraMap _ _ (pl4 a b h))⁻¹]

/-- **The presentation map of the divisor `{f̂₄ = 0}`**: substitution of the parametrisation
`(p₀,p₁,p₂)` into `K[x₀,x₁,x₂]`. -/
def fwTheta (a b h : K) :
    MvPolynomial (Fin 3) K →ₐ[K] FractionRing (MvPolynomial (Fin 2) K) :=
  MvPolynomial.aeval (fwParam a b h)

/-- The first coordinate function `u` on the parametrising plane. -/
def fwU (K : Type) [Field K] : FractionRing (MvPolynomial (Fin 2) K) :=
  algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 0)

/-- The second coordinate function `v` on the parametrising plane. -/
def fwV (K : Type) [Field K] : FractionRing (MvPolynomial (Fin 2) K) :=
  algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K)) (X 1)

end

end Work.MotK.TGen
