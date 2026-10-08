import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.RedAux

variable {P : Type} [Group P] [Finite P]

/-- **The class-two cover case of the `C₄` exclusion.**  A minimal `ξ`-invariant normal cover
`C > A` of `A` with `⁅C,C⁆ = C^(2) = A^(2) = Ω₁(P)` cannot exist.  This is the surviving
configuration of `Work.Higman.MSA.cover_sq_false` / `Work.Higman.NSM.c4DerivSqCase` /
`Work.Higman.H8.c4_sq_a2` / `Work.Higman.LayersAlt.cover_sq_sq_false`.

Known reductions (all axiom-clean, importable):

* `Work.Higman.MSA.centralizer_eq_self` gives `C_P(A) = A` as soon as `¬ (A ≤ Z(P))`
  (and `A ≤ Z(P)` leads to `A = A^(2)`, a contradiction with `hcard`/`htop`);
* `Work.Higman.H8.c4_sq_a2_card_quot` gives `|C/A| = |Ω₁(P)|`, hence `|C| = |Ω₁(P)|³`,
  once `⁅A,C⁆ = A^(2)` (which is forced, since `⁅A,C⁆ ≤ ⁅C,C⁆ = A^(2)`);
* `Work.Higman.H8.card_le_cube_of_sq_le_omega1` (Chevalley–Warning) bounds any `M` with
  `Ω₁(P) ≤ M`, `M^(2) ⊆ Ω₁(P)`, `⁅M,M⁆ ⊆ Ω₁(P)` by `|M| ≤ |Ω₁(P)|³`;
* `⁅C,P⁆` is `ξ`-invariant with `A^(2) ≤ ⁅C,P⁆ ≤ A`, so it is `A^(2)` or `A`.  In the case
  `⁅C,P⁆ = A^(2)` the whole configuration collapses (`_branch1` of
  `Submission/Work/Higman/cover_sq_false_clo.lean`), so only `⁅C,P⁆ = A` remains. -/
theorem class_two_cover_false {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hC2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2) :
    False := by
  sorry

end Work.Higman.RedAux
