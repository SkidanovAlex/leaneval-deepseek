import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChiScaling
import Submission.Work.BoseB4.modeVec_re
import Submission.Work.BoseB4.realIP_thetaFun_eq_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_thetaFun_modeVec` — FS's `∫ χ_Λ e^{ikx} = ℓ³ χ̂(ℓk)`

The condensate matrix element of the localised plane wave against the sharp box
function:

  `⟨θ_Λ, e^{ikx} χ_Λ⟩ = ∫_{Λ(ℓ)} χ_Λ(x) cos(k·x) dx = ℓ³ χ̂(ℓk)`

(`Work.BoseB4.BoxChi`: `θ_Λ = 1_{Λ(ℓ)}`, `χ_Λ(x) = χ(x/ℓ)`, `χ̂` the cos-transform
of FS's Appendix).  This is the `ℓ⁻³⟨θ, e^{ikx}χ_Λ⟩ = χ̂(kℓ)` ingredient of FS
`def:projections` / `eq:Commutator_general` — the component of the localised plane
wave along the condensate, which is subtracted in `BoxData.qVec`.

The proof is the three-line assembly of the two halves of the box dictionary:

* `Work.BoseB4.realIP_thetaFun_eq_box` — `θ_Λ` against *any* function supported in
  the box is the integral of its real part (the `if x ∈ Λ then 1 else 0` drops out,
  and off the box the function vanishes);
* `Work.BoseB4.modeVec_re` — the real part of `e^{ik·x}χ_Λ` is `χ_Λ(x)·cos(k·x)`;
* `Work.BoseB4.BoxData.integral_chiLam_mul_cos` — FS's first box integral,
  `∫ χ_Λ cos(k·x) = ℓ³ χ̂(ℓk)` (`BoxChiScaling`).

The glue is `BoxData.modeVec_supp`: the localised plane wave vanishes off `Λ(ℓ)`
(it is `χ_Λ` times a nowhere-zero phase), which is what feeds the support
hypothesis of the first half.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace BoxData

variable (B : BoxData)

/-- The localised plane wave `e^{ik·x}χ_Λ` vanishes off the box `Λ(ℓ)`: it is
`χ_Λ` times the nowhere-zero phase `e^{ik·x}`. -/
lemma modeVec_supp {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) :
    Function.support (B.modeVec ℓ k) ⊆ B.boxL ℓ := by
  intro x hx
  apply B.chiLam_supp hℓ
  intro h0
  exact hx (by
    simp only [BoxData.modeVec_apply]
    rw [h0]
    simp)

end BoxData

/-- **FS's condensate matrix element of the localised plane wave.**
`⟨θ_Λ, e^{ik·x}χ_Λ⟩ = ℓ³ χ̂(ℓk)`: the `ℓ⁻³⟨θ, e^{ikx}χ_Λ⟩ = χ̂(kℓ)` identity
behind `def:projections` and `eq:Commutator_general`. -/
theorem realIP_thetaFun_modeVec (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    B.realIP (B.thetaFun ℓ) (B.modeVec ℓ k) = ℓ ^ 3 * B.hatChi (ℓ • k) := by
  rw [realIP_thetaFun_eq_box B (B.modeVec_supp hℓ k)]
  trans ∫ x, B.chiLam ℓ x * Real.cos (inner ℝ k x)
  · exact integral_congr_ae
      (Filter.Eventually.of_forall fun x => modeVec_re B ℓ k x)
  · exact B.integral_chiLam_mul_cos hℓ k

end Work.BoseB4
