import Mathlib
import Submission.Work.Mostow.hlDefsAccess
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cruxFixedPoint
import Submission.Work.Mostow.busemann_ne_zero_of_posDisp
import Submission.Work.Mostow.exists_second_bdFix

/-!
# Classification of fixed-point-free isometries of `ℍⁿ` (`ClassifyProp`)

`Work.Mostow.classifyProp`: every isometry `g` of `ℍⁿ` (`n ≥ 2`) without a fixed point in `ℍⁿ`
is either **parabolic** (infimal displacement `0`) or **loxodromic** (it fixes two distinct
boundary points `a ≠ b` and translates the horospheres at `a`: `busemann a (g • 0) ≠ 0`).

The proof splits on the infimum of the displacement function `u ↦ hdist u (g • u)`:

* if the infimum vanishes, `g` is parabolic by definition (`IsParabolic` is exactly
  "no interior fixed point + arbitrarily small displacement");
* otherwise the displacement is bounded below by some `δ > 0`, and then
  * `Work.Mostow.cruxFixedPoint` supplies a fixed boundary point `ξ` of `g`
    (`bd g ξ = ξ`, the limit of the Klein coordinates of an escaping orbit);
  * `Work.Mostow.busemann_ne_zero_of_posDisp` shows that `g` scales the horosphere levels at
    `ξ` (`busemann ξ (g • 0) ≠ 0`) — otherwise `g` would preserve the Busemann function and
    push the displacement to `0` (`Work.Mostow.deepCusp`);
  * `Work.Mostow.exists_second_bdFix` produces the second fixed boundary point `η ≠ ξ` from the
    eigenvalue analysis of the Lorentz lift `emat g`: the eigenvalue `λ ≠ 1` of `θ ξ` has a
    reciprocal `λ⁻¹`, whose eigenvector is null and therefore a multiple of `θ η`.

The pair `(ξ, η)` is then the loxodromic pair of `LoxPair g`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- **The loxodromic half of the classification.**  An isometry `g` of `ℍⁿ` (`n ≥ 2`) with no
fixed point in `ℍⁿ` and displacement bounded below by a positive constant is loxodromic: it
fixes two distinct boundary points and translates the horospheres at the first of them. -/
theorem loxPair_of_noFixed_posDisp (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u)
    (hpos : ∃ δ : ℝ, 0 < δ ∧ ∀ u : E n, δ ≤ hdist u (g • u)) :
    ∃ a b : E n, LoxPair g a b := by
  obtain ⟨ξ, hξS, hξfix⟩ := cruxFixedPoint n hn hA hI g hne hpos
  have hbus := busemann_ne_zero_of_posDisp n hn hA hI g hpos ξ hξS hξfix
  obtain ⟨η, hηS, hηξ, hηfix⟩ := exists_second_bdFix n hn hA g ξ hξS hξfix hbus
  exact ⟨ξ, η, hξS, hηS, fun h => hηξ h.symm, hξfix, hηfix, hbus⟩

theorem classifyProp (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ClassifyProp n := by
  intro g hne
  by_cases hP : ∀ ε : ℝ, 0 < ε → ∃ u : E n, hdist u (g • u) < ε
  · exact Or.inl ⟨hne, hP⟩
  · push Not at hP
    obtain ⟨ε, hε0, hε⟩ := hP
    exact Or.inr (loxPair_of_noFixed_posDisp hn hA hI g hne ⟨ε, hε0, hε⟩)

end

end Work.Mostow
