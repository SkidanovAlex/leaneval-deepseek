import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotC5N3.asPhi2_denom
import Submission.Work.MotC5N3.asRule_rank
import Submission.Work.MotC5N3.asRho_ne_zero
import Submission.Work.MotC5N3.Theta2Sdual
import Submission.Work.MotC5N3.asTheta2_fracTop_of

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.SdualChart` — the chart-2 presentation of the target AS divisor

The short assembly steps of the `sdualAS2` class clause, over an arbitrary `𝕜`-algebra field `K` of
characteristic `5`:

* `asPhi2_rho_ne_zero` — the ruling point `W / W 0` is not in the zero locus of the inverse
  quadro-cubic map `kleinRAS` (from the un-normalised form `asRho_ne_zero` and the degree-3
  homogeneity `kleinRAS_smul`);
* * `asTheta2_fracTop` — the fraction field of the chart algebra `asR2` is all of
  `RatFunc ↥(twistFieldAS D g)` (the unconditional form of `asTheta2_fracTop_of`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

variable {K : Type} [Field K] [CharP K 5]
variable {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]

/-- **The chart-2 rho input**: the inverse AS quadro-cubic map `kleinRAS` does not vanish at the
normalised ruling point `W / W 0 = (1, φ 0, φ 1, φ 2, 0)`, where `W = asW2 D g` and
`φ = asPhi2 D g`. -/
theorem asPhi2_rho_ne_zero (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotAS.kleinRAS (as2a D g) (as2b D g) (as2g D g)
      (fun j => asW2 D g j / asW2 D g 0) ≠ 0 := by
  obtain ⟨i, hi⟩ := asRho_ne_zero K D hD g
  have hW0 : asW2 D g 0 ≠ 0 := asPhi2_denom K D hD g
  have hdiv : (fun j => asW2 D g j / asW2 D g 0)
      = fun j => (asW2 D g 0)⁻¹ * asW2 D g j := by
    funext j
    rw [div_eq_mul_inv, mul_comm]
  rw [hdiv, Work.MotAS.kleinRAS_smul]
  intro hzero
  have h := congrFun hzero i
  simp only [Pi.zero_apply] at h
  exact hi ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 (inv_ne_zero hW0)))

/-- **The fraction field of the chart algebra `asR2` is all of `RatFunc ↥(twistFieldAS D g)`**: the
ruling parametrisation of the corrected AS chart generates the whole function field. -/
theorem asTheta2_fracTop (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Subfield.closure (Set.range (algebraMap ↥(asR2 D g)
      (RatFunc ↥(twistFieldAS D g)))) = ⊤ :=
  asTheta2_fracTop_of K D hD g (asPhi2_denom K D hD g) (asPhi2_rho_ne_zero D hD g)
    (asRule_rank K D hD g)

end Work.MotC5N3
