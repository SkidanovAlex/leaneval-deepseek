import Mathlib

/-!
# Removing a bounded singularity

If `g : ℂ → ℂ` is complex differentiable away from `0` and bounded on the punctured
unit disc, then `g` agrees away from `0` with an entire function `G`.

This is Riemann's removable singularity theorem in the form needed by the Fatou area:
the extension is built by redefining `g` at `0` as `limUnder (𝓝[≠] 0) g`, which is
complex differentiable by `Complex.differentiableOn_update_limUnder_of_bddAbove`.
-/

namespace Work.Fatou.Analysis

open Complex Metric Set Filter
open scoped Topology

/-- **Riemann removable singularity**, global form: a function holomorphic on `ℂ \ {0}`
and bounded on the punctured unit disc is the restriction of an entire function away from
the origin. -/
lemma existsEntireOfBddPunctured (g : ℂ → ℂ) (M : ℝ)
    (hd : DifferentiableOn ℂ g {w : ℂ | w ≠ 0})
    (hb : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < 1 → ‖g w‖ ≤ M) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ w : ℂ, w ≠ 0 → G w = g w := by
  refine ⟨Function.update g 0 (limUnder (𝓝[≠] 0) g), ?_, ?_⟩
  · intro z
    rcases eq_or_ne z 0 with rfl | hz
    · -- At the origin: use the removable singularity theorem on the punctured unit disc.
      have hbdd : BddAbove (norm ∘ g '' (ball (0 : ℂ) 1 \ {0})) := by
        refine ⟨max M 0, ?_⟩
        rintro y ⟨w, hw, rfl⟩
        simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, sub_zero, mem_singleton_iff] at hw
        exact le_trans (hb w (norm_pos_iff.mpr hw.2) hw.1) (le_max_left _ _)
      have hball : (ball (0 : ℂ) 1) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
      have hd' : DifferentiableOn ℂ g (ball (0 : ℂ) 1 \ {0}) :=
        hd.mono (fun w hw => hw.2)
      exact (Complex.differentiableOn_update_limUnder_of_bddAbove hball hd' hbdd).differentiableAt
        hball
    · -- Away from the origin, the update does not change `g` locally.
      have hmem : ({w : ℂ | w ≠ 0} : Set ℂ) ∈ 𝓝 z := isOpen_ne.mem_nhds hz
      have hev : Function.update g 0 (limUnder (𝓝[≠] 0) g) =ᶠ[𝓝 z] g :=
        Filter.mem_of_superset hmem (fun w hw => Function.update_of_ne hw _ _)
      exact DifferentiableAt.congr_of_eventuallyEq (hd.differentiableAt hmem) hev
  · intro w hw
    exact Function.update_of_ne hw _ _

end Work.Fatou.Analysis
