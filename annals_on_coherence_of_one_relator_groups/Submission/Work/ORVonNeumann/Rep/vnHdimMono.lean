import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

/-- **Monotonicity of the von Neumann dimension.**  If `K ≤ L` are subspaces of `⊕ᵢ ℓ²(G)` with
orthogonal projections, then `hdim K ≤ hdim L`.  Proof: for each `i`,
`P_K (P_L x) = P_K x` (because `K ≤ L`), whence
`‖P_K x‖ = ‖P_K (P_L x)‖ ≤ ‖P_L x‖`, and both sides are non-negative, so squaring preserves
the inequality; summing over `i` gives the claim. -/
theorem vnHdimMono {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    {K L : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K ≤ L) :
    Work.ORVonNeumann.Rep.hdim K ≤ Work.ORVonNeumann.Rep.hdim L := by
  simp only [hdim]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := Submodule.starProjection_comp_starProjection_of_le (𝕜 := ℂ) (U := K) (V := L) h
  have h1 : K.starProjection (L.starProjection (hdelta (G := G) n i))
      = K.starProjection (hdelta (G := G) n i) := by
    have := congrArg (fun f => f (hdelta (G := G) n i)) hle
    simpa using this
  rw [← h1]
  exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le (K := K) _) 2

end Work.ORVonNeumann.Rep
