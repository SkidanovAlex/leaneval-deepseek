import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup

/-!
# PARAB0: elementary properties of the uniform parabolic basin

`MandelDim.ParabolicBasin f D` is the *uniform* basin: `z` belongs to it if some neighbourhood `U`
of `z` has all its iterates in `D` and the iterates converge to `0` uniformly on `U`.

This file proves the property the PARAB0 assembly needs: a basin point whose image is not
eventually constant (which holds in particular for every point in the attracting limb of a
parabolic germ, where `f' ≈ 1`) has its image again in the basin.  Openness of the basin under
`f` is what forbids the degenerate situation `f ≡ f z` near `z`; in that case the statement is
false (a constant map sends a basin point to a point whose neighbourhoods contain non-converging
points), which is why the hypothesis is needed.
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab

noncomputable section

/-- **Forward invariance of the uniform basin.**  If `f` is analytic at `z` and not eventually
constant there, and `z` is in the parabolic basin, then `f z` is again in the basin: the
neighbourhood `f '' U` of `f z` does the job. -/
theorem basin_forward {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hzan : AnalyticAt ℂ f z) (hnc : ¬ ∀ᶠ w in 𝓝 z, f w = f z)
    (hz : z ∈ MandelDim.ParabolicBasin f D) :
    f z ∈ MandelDim.ParabolicBasin f D := by
  obtain ⟨U, hU, hmap, hconv⟩ := hz
  have hle : 𝓝 (f z) ≤ map f (𝓝 z) :=
    (hzan.eventually_constant_or_nhds_le_map_nhds).resolve_left hnc
  have hW : f '' U ∈ 𝓝 (f z) := hle (image_mem_map hU)
  refine ⟨f '' U, hW, ?_, ?_⟩
  · intro n w hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← Function.iterate_succ_apply]
    exact hmap (n + 1) hu
  · -- uniform convergence on `f '' U` is the shift of uniform convergence on `U`
    rw [tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    have h2 : ∀ᶠ n in atTop, ∀ u ∈ U, dist (f^[n + 1] u) 0 < ε :=
      ((tendsto_add_atTop_nat 1).eventually (hconv ε hε)).mono
        (fun n hn u hu => by simpa using hn u hu)
    filter_upwards [h2] with n hn w hw
    obtain ⟨u, hu, rfl⟩ := hw
    rw [← Function.iterate_succ_apply]
    simpa [dist_comm] using hn u hu

end
end Work.Parab
