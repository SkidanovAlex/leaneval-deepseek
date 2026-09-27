import Mathlib
import Submission.Work.Kernel.GreenCover

namespace Work.Kernel

/-- **From a plateau at `a` to chart-wise `C¹` data.**

If `Ψ` is `C¹` in every chart away from `a`, is locally constant (equal to `c`) near `a`, and is
supported in `Ω`, then in every chart of the cover the representative `Ψ ∘ (chartAt ℂ (y k)).symm`
is `C¹` at every point of the chart source, and consequently `Ψ` is `ChartDiff` on `Ω` in every
chart of the cover.

The only point that needs care is `x = a`, where the hypothesis is replaced by the plateau: since
`(chartAt ℂ (E.y k)).symm` is continuous at `(chartAt ℂ (E.y k)) a`, the representative equals the
constant `c` near `(chartAt ℂ (E.y k)) a`. -/
theorem chartDiff_and_contDiffAt_of_plateau {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    {Ψ : X → ℝ} {c : ℝ}
    (hΨoff : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source, x ≠ a →
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hΨΩ : tsupport Ψ ⊆ Ω) (hconst : Ψ =ᶠ[nhds a] (fun _ => c)) :
    (∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) Ψ Ω) ∧
      (∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
        ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x)) := by
  classical
  have _hΨΩ := hΨΩ
  -- The `C¹`-statement in every chart at every point of its source.
  have hcont : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
    intro k x hx
    by_cases hxa : x = a
    · -- At `x = a` the function is constant near the point.
      rw [hxa] at hx ⊢
      -- an open neighbourhood of `a` on which `Ψ` is constantly `c`
      have hmem : {x : X | Ψ x = c} ∈ nhds a := hconst
      obtain ⟨t, ht_sub, ht_open, hat⟩ := mem_nhds_iff.mp hmem
      have hct : (chartAt ℂ (E.y k)) a ∈ (chartAt ℂ (E.y k)).target :=
        (chartAt ℂ (E.y k)).map_source hx
      have hta : t ∈ nhds ((chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) a)) := by
        rw [(chartAt ℂ (E.y k)).left_inv hx]
        exact ht_open.mem_nhds hat
      have hpre : (chartAt ℂ (E.y k)).symm ⁻¹' t ∈ nhds ((chartAt ℂ (E.y k)) a) :=
        ((chartAt ℂ (E.y k)).continuousAt_symm hct).preimage_mem_nhds hta
      have hev : (fun w : ℂ => Ψ ((chartAt ℂ (E.y k)).symm w))
          =ᶠ[nhds ((chartAt ℂ (E.y k)) a)] (fun _ => c) := by
        filter_upwards [hpre] with w hw
        exact ht_sub hw
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
    · exact hΨoff k x hx hxa
  refine ⟨fun k x hx => ?_, hcont⟩
  exact (hcont k x hx.2).differentiableAt_one

end Work.Kernel
