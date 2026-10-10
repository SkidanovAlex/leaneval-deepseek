import Submission.Work.LLink.Count
import Submission.Work.LLink.Transport
import Submission.Work.LLink.QuadroCubic
import Submission.Work.LLink.Classes
import Submission.Work.LLink.not_resEquiv_of_ringEquiv
import Submission.Work.LLink.isPseudoIso_symm
import Submission.Work.LLink.cInv_eq_zero_of_isPseudoIso
import Submission.Work.LLink.exDiv_eq_singleton_iff
import Submission.Work.LLink.not_isIsoAt_of_mem_exDiv
import Submission.Work.LLink.cInv_eq_zero_of_exDiv_eq_empty
import Submission.Work.LLink.excCount_le_ncard_exDiv
import Submission.Work.LLink.excCount_eq_of_exDiv_eq
import Submission.Work.LLink.excCount_eq_zero_of_forall_not
import Submission.Work.LLink.cInv_eq_neg_symm
import Submission.Work.LLink.transport_symm

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.LLink` — Part B of `annals_motivic_invariants`: the L-link geometry area

Single entry point for the area.  `import Submission.Work.LLink.Main` brings in everything:
the counting layer, the affine transport, the Crauder–Katz residual and the four field-class
theorems.

## The four field-class results (`Submission/Work/LLink/Classes.lean`)

`Work.LLink.exists_cInv_ne_zero_numberField`,
`Work.LLink.exists_cInv_ne_zero_functionField_numberField`,
`Work.LLink.exists_cInv_ne_zero_functionField_finiteField`,
`Work.LLink.exists_cInv_ne_zero_functionField_algClosed`,

each of the form

```
(h : Work.Arithmetic.HasLLinkCurve 𝕜) → (hg : Work.LLink.CrauderKatzExists 𝕜) →
  ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 3),
    cInv 𝕜 z₀ φ ≠ 0
```

that is, **the named arithmetic input** of the sibling area `Submission/Work/Arithmetic`
(the paper's Lemma `lem:torsors`, consumed through `Work.Arithmetic.llink_tors_*`) **plus the
single geometric residual** `Work.LLink.CrauderKatzExists 𝕜` (Proposition `prop:elliptic`).
The companion `Work.LLink.not_gen_of_quadroCubic_*` do the one-line application of
`Work.Motivic.not_gen_of_cInv_ne_zero` giving `¬ GenByPseudoRegularizable 𝕜 3`.

## The residual and the computation

* `Work.LLink.CrauderKatzExists 𝕜` (`Submission/Work/LLink/QuadroCubic.lean`) — the geometric
  residual, `∀ X : GenOneCurve 𝕜, X.index = 5 → X.NotIsoJacSq → Nonempty (QuadroCubicLink 𝕜 X)`;
* `Work.LLink.QuadroCubicLink 𝕜 X` — the link data, whose fields are the individually named
  residuals (`exDiv_ψ`, `exDiv_ψ_symm`, `resEquiv_y`, `not_resEquiv_yx`, `cInv_ε`, `cInv_δ`);
* `Work.LLink.QuadroCubicLink.inv_ne_zero` — the main computation (`inv = 1`);
  `inv_eq_zero_of_resEquiv_yx` — its sharpness converse;
* the abstract L-link computation `Work.LLink.cInv_eq_one_of_exDiv_eq_singletons`,
  `Work.LLink.cInv_ne_zero_of_exDiv_eq_singletons`,
  `Work.LLink.cInv_eq_zero_of_exDiv_eq_singletons_of_resEquiv`,
  `Work.LLink.exists_cInv_ne_zero_of_link` (`Submission/Work/LLink/Count.lean`);
* the affine transport `Work.LLink.transport` / `Work.LLink.transportCr` /
  `Work.LLink.cInv_transport_eq` / `Work.LLink.cInv_transport_eq_of_eq_zero`
  (`Submission/Work/LLink/Transport.lean`);
* `Work.LLink.not_resEquiv_of_ringEquiv` and
  `Work.LLink.QuadroCubicLink.not_resEquiv_yx_of_functionFields` — the assembly point for the
  one-variable function-field step (see `NOTES.md` §6).

Every interface assumption, every weakening/strengthening relative to Lin–Shinder, and the
mapping between the paper's numbered statements and the named residuals is recorded in
`Submission/Work/LLink/NOTES.md`.
-/
