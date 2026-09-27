import Mathlib
import Submission.Work.EQ.FillDefs

namespace Work.EQ

open Filter Topology

/-- **Removable singularity for `fill` at a filled point.** If `f` is holomorphic off a finite set
`P` and locally bounded at every point of `P`, then the function `fill f P` (which replaces `f` at
`p ∈ P` by `limUnder (𝓝[≠] p) f`, and equals `f` off `P`) is complex differentiable at every point
of `P`. -/
theorem differentiableAt_fill_of_mem {f : ℂ → ℂ} {P : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f (↑P)ᶜ)
    (hbdd : ∀ p ∈ P, ∃ C : ℝ, ∀ᶠ z in nhdsWithin p {p}ᶜ, ‖f z‖ ≤ C)
    {p : ℂ} (hp : p ∈ P) : DifferentiableAt ℂ (fill f P) p := by
  -- A neighborhood of `p` meeting `P` only in `p`: the complement of `P.erase p`.
  have hcompl : (↑(P.erase p) : Set ℂ)ᶜ ∈ 𝓝 p := by
    refine IsOpen.mem_nhds (Finset.finite_toSet (P.erase p)).isClosed.isOpen_compl ?_
    simp
  -- `f` is holomorphic on the punctured part of that neighborhood.
  have hd : DifferentiableOn ℂ f ((↑(P.erase p) : Set ℂ)ᶜ \ {p}) := by
    refine hf.differentiableOn.mono ?_
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hz1 ⊢
    intro hzP
    exact hz1 (Finset.mem_erase.mpr ⟨by simpa using hz2, hzP⟩)
  -- Local boundedness makes `f z - f p` little-o of `(z - p)⁻¹` at `p`.
  have hlittle : (fun z => f z - f p) =o[𝓝[≠] p] fun z => (z - p)⁻¹ := by
    obtain ⟨C, hC⟩ := hbdd p hp
    refine Filter.IsBoundedUnder.isLittleO_sub_self_inv ?_
    refine ⟨C + ‖f p‖, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [hC] with z hz
    calc ‖f z - f p‖ ≤ ‖f z‖ + ‖f p‖ := norm_sub_le _ _
      _ ≤ C + ‖f p‖ := by linarith
  -- Riemann's removable singularity theorem for the version of `f` updated at `p`.
  have hupd : DifferentiableAt ℂ (Function.update f p (limUnder (𝓝[≠] p) f)) p :=
    (Complex.differentiableOn_update_limUnder_of_isLittleO hcompl hd hlittle).differentiableAt
      hcompl
  -- `fill f P` agrees with that update near `p`.
  have hev : fill f P =ᶠ[𝓝 p] Function.update f p (limUnder (𝓝[≠] p) f) := by
    filter_upwards [hcompl] with z hz
    by_cases hzp : z = p
    · subst hzp
      simp [fill_of_mem hp]
    · have hzP : z ∉ P := by
        intro hzm
        exact hz (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzp, hzm⟩))
      rw [Function.update_apply, fill_of_notMem hzP]
      simp [hzp]
  exact hupd.congr_of_eventuallyEq hev

end Work.EQ
