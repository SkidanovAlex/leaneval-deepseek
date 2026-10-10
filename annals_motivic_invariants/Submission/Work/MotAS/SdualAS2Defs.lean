import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.CensusASFalse
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.SdualAS2Defs` — the ruling data of the corrected AS target divisor

The **corrected** AS chart of the Crauder–Katz link (`Work.MotAS.CensusAS2`) has target chart
vector `tchart = (1, X₀, X₁, X₂, 0)`, i.e. the target hyperplane is `{z₄ = 0}`.  Its target ruling
quintic is `sdualAS2 a b g = kleinSecDualAS a b g (tchart)`.

The ruling lines of the surface `{sdualAS2 = 0}` are the analogue of those of the split
(`Work.MotK.RuleData`) and T-twisted (`Work.MotK.TwRule`) cases, but taken with the *invariant*
quadric `kleinQAS = -kleinPAS4` and the distinguished direction `e₄` (this is what makes the
ruling lines lie in `{z₄ = 0}`):

* `asTanQ a b c k = b_q(c, e_k)·e₄ − b_q(c, e₄)·e_k` (`q = kleinQAS`, `b_q = kleinBilinAS`);
* `asRuleQA = dP^AS_c(asTanQ(·,1))`, `asRuleQB = dP^AS_c(asTanQ(·,2))`, with `dP^AS = asPolarP`;
* `asRuleQW a b g c t = asRuleQA + t·asRuleQB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The tangent vector of the AS invariant quadric `kleinQAS` at `c` in the `k`-th direction, based
at the fourth coordinate vector: `b_q(c, e_k)·e₄ − b_q(c, e₄)·e_k`. -/
def asTanQ (a b : R) (c : Fin 5 → R) (k : Fin 5) : Fin 5 → R :=
  fun i => kleinBilinAS a b c (Work.MotK.kleinE k) * Work.MotK.kleinE 4 i
    - kleinBilinAS a b c (Work.MotK.kleinE 4) * Work.MotK.kleinE k i

/-- The first ruling vector `A(c) = dP^AS_c(asTanQ(·,1))` of the corrected chart. -/
def asRuleQA (a b g : R) (c : Fin 5 → R) : Fin 5 → R :=
  asPolarP a b g c (asTanQ a b c 1)

/-- The second ruling vector `B(c) = dP^AS_c(asTanQ(·,2))` of the corrected chart. -/
def asRuleQB (a b g : R) (c : Fin 5 → R) : Fin 5 → R :=
  asPolarP a b g c (asTanQ a b c 2)

/-- A point of the ruling line `ℓ_c` of the corrected chart: `A(c) + t·B(c)`. -/
def asRuleQW (a b g : R) (c : Fin 5 → R) (t : R) : Fin 5 → R :=
  fun i => asRuleQA a b g c i + t * asRuleQB a b g c i

/-- **Bilinearity of `kleinBilinAS`** in its last two arguments. -/
theorem kleinBilinAS_lin (a b : R) (c : Fin 5 → R) (x y : R) (u v : Fin 5 → R) :
    kleinBilinAS a b c (x • u + y • v)
      = x * kleinBilinAS a b c u + y * kleinBilinAS a b c v := by
  simp only [kleinBilinAS, Pi.add_apply, Pi.smul_apply, smul_eq_mul, kleinQAS]
  first | refl_ring1 | ring

/-- The tangent vector written as a linear combination of two basis vectors. -/
theorem asTanQ_eq (a b : R) (c : Fin 5 → R) (k : Fin 5) :
    asTanQ a b c k
      = kleinBilinAS a b c (Work.MotK.kleinE k) • Work.MotK.kleinE 4
        + (-(kleinBilinAS a b c (Work.MotK.kleinE 4))) • Work.MotK.kleinE k := by
  funext i
  simp only [asTanQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Work.MotK.kleinE,
    Pi.single_apply]
  first | refl_ring1 | ring

/-- The fourth component of `asPolarP c u` is `-b_q(c,u)`. -/
theorem asPolarP_four (a b g : R) (c u : Fin 5 → R) :
    asPolarP a b g c u 4 = -(kleinBilinAS a b c u) := by
  simp only [asPolarP, kleinBilinAS, Pi.sub_apply, kleinPAS_four_eq_neg]
  first | refl_ring1 | ring

/-- `b_q(c, asTanQ c k) = 0`: the tangent vector lies in the kernel of the polar form. -/
theorem kleinBilinAS_asTanQ (a b : R) (c : Fin 5 → R) (k : Fin 5) :
    kleinBilinAS a b c (asTanQ a b c k) = 0 := by
  rw [asTanQ_eq, kleinBilinAS_lin]
  first | refl_ring1 | ring

/-- **The ruling lines of the corrected chart lie in `{z₄ = 0}`.** -/
theorem asRuleQW_four (a b g : R) (c : Fin 5 → R) (t : R) : asRuleQW a b g c t 4 = 0 := by
  have hA : asRuleQA a b g c 4 = 0 := by
    rw [asRuleQA, asPolarP_four, kleinBilinAS_asTanQ, neg_zero]
  have hB : asRuleQB a b g c 4 = 0 := by
    rw [asRuleQB, asPolarP_four, kleinBilinAS_asTanQ, neg_zero]
  show asRuleQA a b g c 4 + t * asRuleQB a b g c 4 = 0
  rw [hA, hB, mul_zero, add_zero]

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The index map `Fin 3 → Fin 5`, `j ↦ j + 1`. -/
def asIdx (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

/-- **The generic point of the twisted Klein curve** as a point of `twistFieldAS D g`: the
projective point `(1, y₁/y₀, y₂/y₀, y₃/y₀, y₄/y₀)` of the AS Galois-coordinate Klein curve. -/
noncomputable def asY0 (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    Fin 5 → ↥(twistFieldAS D g) :=
  fun j => ⟨asTwY D g j / asTwY D g 0,
    IntermediateField.subset_adjoin (RatFunc 𝕜)
      (Set.range fun j => asTwY D g j / asTwY D g 0) (Set.mem_range_self j)⟩

/-- **The ruling parametrisation of the corrected AS target divisor**: the chart coordinates of the
ruling line `ℓ_c` over the generic curve point, with ruling parameter `t = RatFunc.X`. -/
noncomputable def asPhi2 (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    Fin 3 → RatFunc ↥(twistFieldAS D g) :=
  let R := RatFunc ↥(twistFieldAS D g)
  let c : Fin 5 → R := fun j => algebraMap ↥(twistFieldAS D g) R (asY0 D g j)
  let W : Fin 5 → R := asRuleQW (algebraMap 𝕜 R D.a) (algebraMap 𝕜 R D.b)
    (algebraMap (RatFunc 𝕜) R g) c (RatFunc.X : R)
  fun j => W (asIdx j) / W 0

/-- **The presentation of the corrected AS target divisor.** -/
noncomputable def asTheta2 (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    MvPolynomial (Fin 3) (RatFunc 𝕜) →ₐ[RatFunc 𝕜] RatFunc ↥(twistFieldAS D g) :=
  MvPolynomial.aeval (asPhi2 D g)

/-- The subalgebra of `RatFunc ↥(twistFieldAS D g)` generated by the chart coordinates. -/
noncomputable def asR2 (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    Subalgebra (RatFunc 𝕜) (RatFunc ↥(twistFieldAS D g)) :=
  Algebra.adjoin (RatFunc 𝕜) (Set.range (asPhi2 D g))

/-- The range of `asTheta2` is the subalgebra `asR2`. -/
theorem asTheta2_range (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    (asTheta2 D g).range = asR2 D g := by
  have h := MvPolynomial.aeval_range (R := RatFunc 𝕜)
    (S₁ := RatFunc ↥(twistFieldAS D g)) (σ := Fin 3) (asPhi2 D g)
  simpa only [asTheta2, asR2] using h

end Work.MotAS
