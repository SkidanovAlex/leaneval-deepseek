import Mathlib
import Submission.Work.Drive.Mono.Band.ae_finite_preimage

namespace Work.Drive.Mono

open scoped Topology

/-- **A compact zero set with everywhere invertible derivative is finite.**  Let
`Ω : ℝ × ℝ → ℝ × ℝ` be `C¹` on a compact set `K` and suppose that at every zero of `Ω` in `K` the
derivative `fderiv ℝ Ω x` is invertible.  Then `K ∩ Ω ⁻¹' {0}` is finite.

Proof: if `K ∩ Ω ⁻¹' {0}` were infinite, it would have an accumulation point `x₀ ∈ K` (compactness);
`Ω` is continuous there, so `Ω x₀ = 0`; the inverse function result (the workspace lemma
`Work.Drive.Mono.Band.injOn_of_isInvertible_fderiv`, in
`Submission.Work.Drive.Mono.Band.ae_finite_preimage`) makes `Ω` injective on a neighbourhood of
`x₀`, contradicting that infinitely many distinct points of the neighbourhood are mapped to `0`. -/
theorem finite_zeroSet_of_isInvertible_fderiv {Ω : ℝ × ℝ → ℝ × ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hΩ : ∀ x ∈ K, ContDiffAt ℝ 1 Ω x)
    (hinv : ∀ x ∈ K, Ω x = 0 → (fderiv ℝ Ω x).IsInvertible) :
    (K ∩ Ω ⁻¹' {0}).Finite := by
  set s : Set (ℝ × ℝ) := K ∩ Ω ⁻¹' {0} with hs
  by_contra hfin
  -- `s` is infinite, so by compactness of `K` it has an accumulation point `x₀ ∈ K`
  have hinf : s.Infinite := hfin
  obtain ⟨x₀, hx₀K, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK Set.inter_subset_left
  have hx₀cl : x₀ ∈ closure s :=
    mem_closure_iff_nhds.mpr (clusterPt_principal_iff.mp hacc.clusterPt)
  -- by continuity, `Ω x₀ = 0`
  have hΩx₀ : Ω x₀ = 0 := by
    by_contra hne
    have hcont : ContinuousAt Ω x₀ := (hΩ x₀ hx₀K).continuousAt
    have hmem : {x | Ω x ≠ 0} ∈ 𝓝 x₀ :=
      hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
    obtain ⟨z, hz⟩ := mem_closure_iff_nhds.mp hx₀cl _ hmem
    exact hz.1 hz.2.2
  -- the inverse function theorem makes `Ω` injective near `x₀`
  obtain ⟨U, hU, hUinj⟩ :=
    Band.injOn_of_isInvertible_fderiv (hΩ x₀ hx₀K) (hinv x₀ hx₀K hΩx₀)
  obtain ⟨z, ⟨hzU, hzs⟩, hzx⟩ := (accPt_iff_nhds.mp hacc) U hU
  exact hzx (hUinj hzU (mem_of_mem_nhds hU) (by rw [hzs.2, hΩx₀]))

end Work.Drive.Mono
