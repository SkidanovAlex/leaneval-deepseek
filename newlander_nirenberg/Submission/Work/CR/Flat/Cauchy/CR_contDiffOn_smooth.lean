import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger
import Submission.Work.CR.Flat.Holder.contDiffOn_holomorphic_of_step
import Submission.Work.CR.Flat.Cauchy.dCoord_contDiffOn_one_of_holomorphic

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set
open scoped ContDiff

/-- **Holomorphic functions are smooth (flat case).**  A `C¹` function on an open
`Ω ⊆ ℂⁿ` whose flat `∂̄`-derivatives vanish, `dbarCoord k f z = 0` for all `k` and
`z ∈ Ω`, is `C^∞` on `Ω`: each Wirtinger derivative `dCoord j f` is again
`C¹`-holomorphic (Cauchy integral formula in the `j`-th variable) and `f` is
reconstructed from its Wirtinger derivatives, so `C^k` bootstraps to `C^{k+1}`
for every `k`.

Note on the order: the conclusion is smoothness (`∞`, i.e. `∀ N, ContDiffOn ℝ N f Ω`),
*not* analyticity.  Only smoothness is reachable from the ingredients below, and it
is the form needed by the caller (a chart that is smooth, not merely `C^{k+1}` for a
fixed `k`).  Equivalent formulation via `contDiffOn_infty`:
`∀ N : ℕ, ContDiffOn ℝ (N : ℕ∞) f Ω`.

The ingredients are already proved in the workspace:
`Work.CR.Flat.Holder.contDiffOn_holomorphic_of_step` (the induction skeleton, taking
a `step` and an `upgrade`), `Work.CR.Flat.Cauchy.dCoord_contDiffOn_one_of_holomorphic`
(the `step`), and `Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger` (the `upgrade`). -/
theorem CR_contDiffOn_smooth {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ 1 f Ω)
    (h : ∀ k : Fin n, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord k f z = 0) :
    ContDiffOn ℝ ∞ f Ω := by
  rw [contDiffOn_infty]
  intro N
  exact Work.CR.Flat.Holder.contDiffOn_holomorphic_of_step
    (fun hΩ g hg hhol j => dCoord_contDiffOn_one_of_holomorphic hΩ hg hhol j)
    (fun hΩ h m hdiff hm h1 h2 =>
      Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger hΩ hdiff hm h1 h2)
    hΩ hf h N

end Work.CR.Flat.Cauchy
