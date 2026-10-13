import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Compactness

/-- Uniform convergence on compact subsets of the fake-time slab (with the closed quadrant in
`(z,θ)`) implies pointwise convergence there: the singleton `{(z,θ,τ)}` is compact and contained in
the slab.

Intended proof: apply the hypothesis to `K = {p}`, and extract the pointwise limit from
`TendstoUniformlyOn` on a singleton (`tendstoUniformlyOn_singleton_iff_tendsto` in
`Mathlib/Topology/UniformSpace/UniformConvergence.lean`). -/
theorem convLocUnif_convPoint {G : ℕ → Work.FTS.Galerkin.Fam} {g : Work.FTS.Galerkin.Fam}
    (h : Work.FTS.Galerkin.ConvLocUnif G g) : Work.FTS.Galerkin.ConvPoint G g := by
  intro z hz θ hθ τ hτ
  -- the singleton `{(z,θ,τ)}` is compact and lies in the closed quadrant slab
  have hK : IsCompact ({((z, θ, τ) : ℝ × ℝ × ℝ)} : Set (ℝ × ℝ × ℝ)) := isCompact_singleton
  have hsub : ({((z, θ, τ) : ℝ × ℝ × ℝ)} : Set (ℝ × ℝ × ℝ)) ⊆
      {p | p.1 ∈ Work.Spaces.Iz ∧ p.2.1 ∈ Work.Spaces.Iθ ∧ 0 ≤ p.2.2} := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hz, hθ, hτ⟩
  -- uniform convergence on the singleton gives plain convergence at its point
  have h1 := h _ hK hsub
  have h2 := tendstoUniformlyOn_singleton_iff_tendsto.mp h1
  simpa using h2

end Work.FTS.Galerkin.Compactness
