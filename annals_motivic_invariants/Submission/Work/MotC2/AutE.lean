import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.AutE_u_sq_eq_one
import Submission.Work.MotC2.AutE_char_two
import Submission.Work.MotC2.AutE_char_three
import Submission.Work.MotC2.AutE_char_ne_two_three

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotC2

/-
Route (Silverman, AEC, Prop. A.1.2).  Let `C = (u, r, s, t)` and `C • E = E`.  The coefficient
formulas `WeierstrassCurve.variableChange_a₁` … `variableChange_a₆` give the system
  `u⁻¹(a₁ + 2s) = a₁`, `u⁻²(a₂ - s a₁ + 3r - s²) = a₂`, `u⁻³(a₃ + r a₁ + 2t) = a₃`,
  `variableChange_a₄`, `variableChange_a₆`,
equivalently `(C • E).b₂ = E.b₂`, `(C • E).b₄ = E.b₄`, `(C • E).b₆ = E.b₆`, and
`c₄ = u⁻⁴ c₄`, `c₆ = u⁻⁶ c₆` (`variableChange_c₄`, `variableChange_c₆`).
Since `j = Δ'⁻¹ c₄³` with `j ≠ 0`, we get `c₄ ≠ 0` (`c₄ = 0` would give `j = 0`), hence
`u⁴ = 1`; similarly `j ≠ 1728` together with `1728 Δ = c₄³ - c₆²` gives `c₆ ≠ 0`, hence `u⁶ = 1`.
Case analysis on the characteristic:
* char ≠ 2, 3: `u⁴ = u⁶ = 1` gives `u² = 1`, and the system forces `r = s = t = 0`; then
  `C = 1` (if `u = 1`) or `C ≠ 1`, `C² = 1` (if `u = -1`; use `VariableChange.mul_def`).
* char 2: `j ≠ 0` forces `a₁ ≠ 0`; then `u = 1`, `r = 0`, `s ∈ {0, a₁}`, `t = s a₃`, and the
  third equation `t = s·a₃` plus `u = 1` gives `C² = 1` (`VariableChange.mul_def`).
* char 3: `j ≠ 0` forces `b₂ = a₁² + a₂ ≠ 0`; the system gives `u = ±1`, `r = s = 0`, `t ∈ {0, -a₃}`
  and `C² = 1`.
-/
theorem AutE (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (hj0 : E.j ≠ 0) (hj : E.j ≠ 1728) (C : WeierstrassCurve.VariableChange L) (hC : C • E = E) :
    C = 1 ∨ (C * C = 1 ∧ C ≠ 1) := by
  -- `C * C = 1` is the substantive claim; the disjunction is then formal.
  have hsq : C * C = 1 := by
    by_cases h2 : (2 : L) = 0
    · -- characteristic `2`
      haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h2
      refine AutE_char_two E ?_ C hC
      intro ha₁
      exact hj0 (WeierstrassCurve.j_eq_zero_of_char_two (W := E) ha₁)
    · by_cases h3 : (3 : L) = 0
      · -- characteristic `3`
        haveI : CharP L 3 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h3
        refine AutE_char_three E ?_ C (AutE_u_sq_eq_one E hj0 hj C hC) hC
        intro hb₂
        exact hj0 (WeierstrassCurve.j_eq_zero_of_char_three (W := E) hb₂)
      · -- characteristic neither `2` nor `3`
        exact AutE_char_ne_two_three h2 h3 E C (AutE_u_sq_eq_one E hj0 hj C hC) hC
  rcases eq_or_ne C 1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hsq, h⟩

end Work.MotC2
