import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The values of the induced characters (Feit 1960, §3, displays (18) and (20))

Feit's computations (18) (the values of `η_i^* = Ind_H^G η_i`) and (20) (`‖Ind_Q^G ζ₁‖² = q + 1`)
are both driven by one geometric fact of the rank-one set-up: **an element of `Q ∖ 1` is
conjugate into `Q` only by elements of `H`** (equivalently, `{x : x y x⁻¹ ∈ Q} = H`).

Indeed, a non-identity `y ∈ Q` fixes only the base point `∞` of `Ω = G ⧸ H`
(`IsTIQ.Q_smul_eq_self`: `Q` acts freely on `Ω ∖ {∞}`), so `x y x⁻¹ ∈ Q ∖ 1` fixes only the point
`x · ∞`; but `x y x⁻¹` fixes `x · ∞` always, so `x · ∞ = ∞`, i.e. `x ∈ H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- In the split rank-one set-up, for `y ∈ Q ∖ 1` the conjugates of `y` lying in `Q` are exactly
the `H`-conjugates: `x * y * x⁻¹ ∈ Q` forces `x ∈ H`.  (This is the fact behind Feit's values
`(18)` and the norm computation `(20)`.) -/
theorem conj_mem_Q_iff {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {y : G} (hy : y ∈ Q) (hy1 : y ≠ 1) :
    ∀ x : G, x * y * x⁻¹ ∈ Q → x ∈ H := by
  intro x hx
  by_contra hxH
  have hx1 : x * y * x⁻¹ ≠ 1 := by
    intro h1
    have h2 : y = 1 := by
      have h3 := congrArg (fun z : G => x⁻¹ * z * x) h1
      simpa [mul_assoc] using h3
    exact hy1 h2
  have hω : x • IsTIQ.basePt H ≠ IsTIQ.basePt H := by
    rw [IsTIQ.smul_basePt]
    exact (IsTIQ.basePt_ne_iff H x).mpr hxH
  have hfix : (x * y * x⁻¹) • (x • IsTIQ.basePt H) = x • IsTIQ.basePt H := by
    rw [← mul_smul, show (x * y * x⁻¹) * x = x * y by group, mul_smul,
      IsTIQ.smul_basePt_of_mem H (h.le hy)]
  exact hx1 (IsTIQ.Q_smul_eq_self h hx hfix hω)

end Work.ZassenhausTwoGroup
