import Submission.Work.Wire123.exists_cInv_ne_zero_of_transLink
import Submission.Work.Wire123.TransLinkWiring
import Submission.Work.Wire123.MinLink
import Submission.Work.Wire123.BareLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.TransLinkChallenge` — Theorem 1.2 (3) for `n ≥ 5` from the transport-free residual

The challenge-shaped wrappers of the sharpened reductions of `NOTES.md` §16:

* `Work.Wire123.theorem_1_2_3_of_transLink` — from `Work.Wire123.TransLink 𝕜` (the paper-shaped
  link data + (L2) + one birational map `𝔸⁵ ⇢ P`), for every `n ≥ 5`;
* `Work.Wire123.theorem_1_2_3_of_leanLink'` — from `Work.Wire123.LeanLink 𝕜` (the same, plus the
  redundant transport hypotheses of the delivered chain);
* `Work.Wire123.theorem_1_2_3_of_minLink` — from `Work.Wire123.MinLink 𝕜` (the sharpest residual of
  the area, `n = 5`, `Work.Wire123.MinLink.theorem_1_2_3`).

The `transLink` wrapper is what the comment block above `Submission.MotivicInvariants.theorem_1_2_3`
in `Submission.lean` refers to: the body of the challenge theorem becomes that single line as soon
as a term of the residual exists.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the transport-free residual.** -/
theorem theorem_1_2_3_of_transLink {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (D : TransLink 𝕜) : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n (exists_cInv_ne_zero_of_transLink hn 𝕜 D)

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from `Work.Wire123.LeanLink 𝕜`**: the same as
the pre-existing `Work.Wire123.theorem_1_2_3_of_leanLink`, now through the transport-free form. -/
theorem theorem_1_2_3_of_leanLink' {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (L : LeanLink 𝕜) : ¬ GenByPseudoRegularizable 𝕜 n :=
  theorem_1_2_3_of_transLink hn 𝕜 L.toTransLink

/-- **Theorem 1.2 (3) of the challenge at `n = 5`, from the sharpest residual.** -/
theorem theorem_1_2_3_of_minLink (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (D : MinLink 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 5 :=
  MinLink.not_gen_five D

end

end Work.Wire123
