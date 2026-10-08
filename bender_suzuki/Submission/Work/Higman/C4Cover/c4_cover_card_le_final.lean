/-
# The `C₄` cover bound `|C| ≤ |A| · |Ω₁(P)|` (assembly)

Combining the squaring dichotomy (`c4_sq_dichotomy`) with the two branch bounds
(`c4_cover_card_le_of_sq`, `c4_cover_card_le_of_ker`):

in the `C₄` setting, a `ξ`-invariant normal cover `C > A` minimal among the `ξ`-invariant normal
subgroups above `A` with `⁅C,C⁆ = A²` satisfies `|C| ≤ |A| · |Ω₁(P)| = q³`.

With the orbit counting `(q − 1) ∣ |C| − 1` (the involutions of `C` are the elements of
`Ω₁(P) ∖ {1}`) this yields `|C| = q³` and hence `|P| ≥ 2q³`: the `C₄` shape forces a proper
`ξ`-invariant normal subgroup of order exactly `q³`.
-/
import Mathlib
import Submission.Work.Higman.C4Cover.c4_cover_card_le
import Submission.Work.Higman.C4Cover.c4_cover_card_le_of_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.C4Cover

variable {P : Type} [Group P] [Finite P]

/-- **The `C₄` cover bound.**  In the `C₄` setting, a minimal `ξ`-invariant normal cover `C` of
`A` with `⁅C,C⁆ = A²` satisfies `|C| ≤ |A| · |Ω₁(P)|`. -/
theorem c4_cover_card_le (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    Nat.card ↥C ≤ Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥A := by
  rcases c4_sq_dichotomy h hAab hGs hNA htop hCn hCinv hAC hCA hcover hCd with hsq2 | hk
  · exact c4_cover_card_le_of_sq h hGs hsq htop hcard hCd hsq2
  · exact c4_cover_card_le_of_ker h hAab hGs hsq htop hcard hCn hAC hCd hk

end Work.Higman.C4Cover
