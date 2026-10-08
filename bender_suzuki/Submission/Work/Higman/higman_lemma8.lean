import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.h8_hard

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Higman 1963, Lemma 8.**  Let `A` be a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`
and `C` a normal `ξ`-subgroup covering `A` (`C/A` a minimal normal `ξ`-section).  If `C' = A`
(and `C² ≤ A`, which follows from the covering condition), then `A` has exponent at most `2`.

The proof is a case split.  If `A = ⊥` the claim is trivial.  If `A ^ (2) = ⊥` then every element
of `A` is an involution and `A ≤ Ω₁(P)`.  Otherwise `A ≠ ⊥` and `A ^ (2) ≠ ⊥`, which is the hard
case of `Work.Higman.h8_hard`: there `C ^ (2) = C' = A`, `γᵢ(C) = A ^ (2 ^ (i-2))`, the layers
`C/A`, `A/A²`, `A²/A⁴`, `Ω₁(P)` are all of order `q = 2 ^ n` with `ξ` regular on each, the
squaring map `C/A → Ω₁(P)` is a quadratic map with polar form the commutator pairing, and the
bracket `C/A × Ω₁(P) → Ω₁(P)` is biadditive with `⌊x, s(x)⌋ = 0` and `⌊·,·⌋ ≠ 0`.  These are
exactly the hypotheses of `Work.Higman.HS.core_mul` (Higman's §4 Lemma 6 in multiplicative form),
which gives a contradiction. -/
theorem higman_lemma8 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) :
    ∀ a ∈ A, a * a = 1 := by
  rcases eq_or_ne A ⊥ with hA0 | hAne
  · subst hA0
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    simp
  · by_cases hA2 : Work.Higman.powSub A 2 = ⊥
    · intro a ha
      have h2 : a ^ 2 ∈ Work.Higman.powSub A 2 := Work.Higman.pow_mem_powSub ha
      rw [hA2, Subgroup.mem_bot] at h2
      simpa [pow_two] using h2
    · exact (h8_hard h hA hCn hCinv hAC hCA hcover hC2 hCd hAne hA2).elim

end Work.Higman
