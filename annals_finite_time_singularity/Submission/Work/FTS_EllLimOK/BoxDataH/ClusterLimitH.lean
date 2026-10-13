/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.ClusterLimitH` — the cluster limit of a `LimSeq4` under `HasPkgH`

`clusterLimitH_aux2` produces, along any subsequence, a strictly monotone reindexing `τ` and a
limit `Ψ` which is `BoxReg`, solves the elliptic law for the limit profile `f`
(`IsBslSolPos α f Ψ`), carries the two `ℋ⁰`-memberships, and is the pointwise limit of the values
on the open quadrant.  The uniqueness of the law (`UniqFatou.eqOn_of_same_law`) shows that the
limit does not depend on the subsequence, which upgrades the statement to the *full* sequence: for
every subsequence there is a further reindexing along which the values converge to the same `Ψ` —
exactly the hypothesis of `Filter.tendsto_of_subseq_tendsto`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_EllLimOK.HkMem_zero_diff
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxRegOfBoxUniform2
import Submission.Work.FTS_EllLimOK.BoxDataH.clusterLimitH_aux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The cluster limit under `HasPkgH`, in the form used by the box data**: a limit `Ψ` which is
`C²` on every closed box, solves the law of the limit profile, carries the two `ℋ⁰`-memberships,
and is the limit of the values along any sub-subsequence of the given `LimSeq4`. -/
theorem clusterLimitH {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Fn →ₗ[ℝ] Fn} (hE : Work.FTS_EllLimOK.HasPkgH α Ce E)
    {fn : ℕ → Fn} {f : Fn} (hL : Work.FTS_EllLimOK.LimSeq4 α fn f) :
    ∃ Ψ : Fn, Work.FTS_EllLimOK.BoxReg Ψ ∧
      Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      (∀ ns : ℕ → ℕ, Filter.Tendsto ns Filter.atTop Filter.atTop →
        ∃ τ : ℕ → ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
          Filter.Tendsto (fun m => E (fn (ns (τ m))) z θ) Filter.atTop (nhds (Ψ z θ))) := by
  obtain ⟨τ₀, -, Ψ₀, hbox₀, hsol₀, hHk₀, hHkc₀, -⟩ :=
    clusterLimitH_aux2 (E := E) hα hα1 hE hL Filter.tendsto_id
      (fun hU hconv => boxReg_of_boxUniform2 hU hconv)
  refine ⟨Ψ₀, hbox₀, hsol₀, hHk₀, hHkc₀, fun ns hns => ?_⟩
  obtain ⟨τ, -, Ψ', hbox', hsol', hHk', hHkc', hconv'⟩ :=
    clusterLimitH_aux2 (E := E) hα hα1 hE hL hns
      (fun hU hconv => boxReg_of_boxUniform2 hU hconv)
  have heq : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → Ψ' z θ = Ψ₀ z θ :=
    Work.FTS_EllLimOK.eqOn_of_same_law hα hsol' hsol₀ hbox' hbox₀ hHk' hHkc' hHk₀ hHkc₀
      (Work.FTS_EllLimOK.HkMem_zero_diff hHk' hHk₀ hbox' hbox₀)
  exact ⟨τ, fun z θ hzθ => by
    simpa only [heq z θ hzθ] using hconv' z θ hzθ⟩

end Work.FTS_EllLimOK.BoxDataH
