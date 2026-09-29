import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Kotani.Assembly
import Submission.Work.TMComp.Kotani.kotani_local
import Submission.Work.TMComp.Kotani.kotani_core_of_local

/-! Guidance from the project lead (the requester):

Component C8 (P_Kotani) of the Ten Martini formalisation. The FROZEN statement is Work.TMContract.P_Kotani (Submission/Work/TMContract/Components.lean; definitions in TMContract/Defs.lean; read TMContract/README.md). The proof route for C8 is in Submission/Work/TMPlan/ROUTE_LEAD.md (find the section for C8); the source is Avila–Jitomirskaya, The Ten Martini Problem (arXiv math/0503363), plus the references ROUTE_LEAD cites. Any other component's P_* that ROUTE_LEAD lists as an input for C8 may be taken as a HYPOTHESIS inside your proof only if P_Kotani's own statement takes it; otherwise prove what you need. Decompose into lemmas right away and dispatch them in parallel with request_lemma (request_review first if unsure a statement is true). Keep every build small; no hour-long files.
-/

/-!
# C8 — Kotani theory (`P_Kotani`, AJ Theorem 2.2)

The proof is assembled from the following modules (all in
`Submission/Work/TMComp/Kotani/`, see `NOTES.md` there for the mathematics):

* `mfun_props` — AJ Theorem 3.1: the `m`-function exists, is `ℍ`-valued, is holomorphic in `E`
  and continuous in `(E,x)` on `{0 < Im E}`, is 1-periodic in `x`, satisfies the invariance
  relation, and equals `amoM` on the upper half plane.  Built from the elementary contraction
  estimates `delta_estimates`, `backIterC_approxIt`, `approx_reg`.
* `two_ell`, `inv_N_le`, `L6_algebra`, `mfun_im_shift`, `Psi_bounds`, `EllDerivDefs`,
  `hasDerivAt_ell`, `ell_defect_le`, `ell_div_antitoneOn`, `cayley_defect` — the identities
  (M′), (L2), (L3), (L5), (L6) of the route, (K2), and the key unconditional bound (H′)
  (`ε ↦ ℓ(E₀+iε)/ε` is antitone).
* `kotani_local` — the extension of `E ↦ mfun α lam E x` across each `E₀ ∈ (a,b)`, with the
  reflection continuation below the axis and `ℍ`-valuedness (AJ Theorem 2.2, local form).
* `kotani_core_of_local` — glues the local continuations into `CoreStatement`.
* `Assembly` — `prove_Kotani_of_core` derives the frozen `P_Kotani` from `CoreStatement`.
-/

namespace Work.TMComp

open Work.TMContract

/-- **Kotani theory (AJ Theorem 2.2), component C8.** -/
theorem prove_Kotani : Work.TMContract.P_Kotani :=
  Work.TMComp.Kotani.prove_Kotani_of_core fun α lam a b hα h0 hab hL =>
    Work.TMComp.Kotani.kotani_core_of_local α lam a b hα h0 hab hL
      fun E₀ hE₀ x => Work.TMComp.Kotani.kotani_local α lam a b hα h0 hab hL E₀ hE₀ x

end Work.TMComp
