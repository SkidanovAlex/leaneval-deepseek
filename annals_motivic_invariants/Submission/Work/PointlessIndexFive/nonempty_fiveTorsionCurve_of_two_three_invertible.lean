import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.nonempty_fiveTorsionPoint
import Submission.Work.Arithmetic.Aut_orderOf_dvd_of_short
import Submission.Work.PointlessIndexFive.order_aut_transport_variableChange
import Submission.Work.PointlessIndexFive.short_form_j_ne_hypotheses

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

/-- **Silverman, *AEC*, Proposition A.1.2 for an arbitrary Weierstrass model in characteristic
`≠ 2, 3`.**  If `W/𝕜` is elliptic with `j(W) ≠ 1728` and `2, 3` are invertible in `𝕜`, then
every automorphism of `W` has order dividing `2` or `6`.

Route: put `W` into short normal form `C₀ • W` with `C₀ = W.toShortNF` (possible because `2, 3`
are invertible), so that `C₀ • W` is the short model `⟨0, 0, 0, a₄, a₆⟩`; for a short model the
statement is `Work.Arithmetic.Aut_orderOf_dvd_of_short`, whose two hypotheses are supplied by
`Work.PointlessIndexFive.short_form_j_ne_hypotheses`; finally transport the result back along the
variable change with `Work.PointlessIndexFive.order_aut_transport_variableChange`. -/
lemma order_aut_of_j_ne {𝕜 : Type} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (W : WeierstrassCurve 𝕜) [W.IsElliptic] (hj : W.j ≠ 1728) :
    ∀ σ : Work.Arithmetic.Aut 𝕜 W, orderOf σ ∣ 2 ∨ orderOf σ ∣ 6 := by
  haveI : Invertible (2 : 𝕜) := invertibleOfNonzero h2
  haveI : Invertible (3 : 𝕜) := invertibleOfNonzero h3
  let C₀ : WeierstrassCurve.VariableChange 𝕜 := W.toShortNF
  haveI hshort : (C₀ • W).IsShortNF := W.toShortNF_spec
  haveI hEllC : (C₀ • W).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.variableChange_Δ]
    exact IsUnit.mul (Units.isUnit (C₀.u⁻¹ ^ 12)) W.isUnit_Δ
  have hjC : (C₀ • W).j ≠ 1728 := by
    rw [WeierstrassCurve.variableChange_j W C₀]; exact hj
  obtain ⟨hEll, hJ⟩ := short_form_j_ne_hypotheses (C₀ • W) h2 hjC
  let W' : WeierstrassCurve 𝕜 := ⟨0, 0, 0, (C₀ • W).a₄, (C₀ • W).a₆⟩
  have hC₀ : C₀ • W = W' := by
    ext <;> simp [W']
  refine order_aut_transport_variableChange C₀ hC₀ (fun τ => ?_)
  exact Work.Arithmetic.Aut_orderOf_dvd_of_short (C₀ • W).a₄ (C₀ • W).a₆ h2 h3 hEll hJ τ

/-- **Step (B) of the paper's proof, with the Silverman A.1.2 datum attached.**  Over an infinite
field in which `2` and `3` are invertible there is an elliptic curve with `j ≠ 1728`, a rational
point of exact order `5`, and every automorphism of order dividing `2` or `6`: a
`Work.TorsorExistence.FiveTorsionCurve`.

This closes the gap between the parent chapter's two ingredients
`nonempty_fiveTorsionPoint` (the Tate normal form `X₁(5)`, which supplies a `FiveTorsionPoint` but
*not* the `order_aut` field) and `nonempty_orderAutCurve` (a short model `y² = x³ + 1`, which has
`j = 0` but no rational `5`-torsion point): the `order_aut` field of `FiveTorsionCurve` is a
statement about *the same curve* as the `5`-torsion point, so neither ingredient alone supplies a
`FiveTorsionCurve`, and the `QuinticTwist` of the paper's construction cannot be assembled without
this lemma.  Route: take the Tate normal form with a good parameter (`Tate.exists_tate_param`,
`Tate.tate_five_smul`) and transport `Work.Arithmetic.Aut_orderOf_dvd_of_short` (Silverman, *AEC*,
A.1.2 for short models) along a `WeierstrassCurve.VariableChange` putting the Tate model into short
form (characteristic `≠ 2, 3`). -/
theorem nonempty_fiveTorsionCurve_of_two_three_invertible {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    [Infinite 𝕜] (h2 : (2 : 𝕜) ≠ 0) (h3 : (3 : 𝕜) ≠ 0) :
    Nonempty (Work.TorsorExistence.FiveTorsionCurve 𝕜) := by
  obtain ⟨D⟩ := Work.TorsorExistence.nonempty_fiveTorsionPoint (𝕜 := 𝕜)
  haveI : D.E.IsElliptic := D.isElliptic
  exact ⟨{ E := D.E, isElliptic := D.isElliptic, j_ne := D.j_ne, P := D.P,
           P_ne_zero := D.P_ne_zero, five_smul := D.five_smul,
           order_aut := order_aut_of_j_ne h2 h3 D.E D.j_ne }⟩

end Work.PointlessIndexFive
