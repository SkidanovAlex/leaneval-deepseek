import Mathlib
import Submission.Work.RPV.V
import Submission.Work.RPB.B5.contDiffOn_uproj_comp

namespace Work.RPB.B5

open Work.RPV
open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-- Smoothness of the chart slice `t ↦ uproj (W τ t (ρh τ t σ))`.

For a fixed `τ ∈ [0,1]`, the map `p = (σ,t) ↦ uproj (W τ t (ρh τ t σ))` is `C¹` on the open
slab `(-κ,κ) × ℝ`: on that slab `ρh τ t σ` takes values in the open box `(-ρ₀,ρ₀)` where the
chart `W` is smooth, so the composite is the restriction of a smooth map.  Restricting further
to a line `t ↦ (σ,t)` with `σ ∈ (-(2δ),2δ) ⊆ (-κ,κ)` gives the claim. -/
theorem kappa_chartSlice_contDiff (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {κ : ℝ} (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : 2 * δ ≤ κ) (hδρ : 2 * δ ≤ ρ₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-(2 * δ)) (2 * δ),
      ContDiff ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) := by
  intro τ hτ σ hσ
  -- The `σ`-interval `(-(2δ), 2δ)` lies inside the chart's `σ`-interval `(-κ,κ)`.
  have hσκ : σ ∈ Set.Ioo (-κ) κ := by
    rw [Set.mem_Ioo] at hσ ⊢
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  -- The slab `(-κ,κ) × ℝ` in the variables `(σ,t)`.
  set T : Set (ℝ × ℝ) := Set.Ioo (-κ : ℝ) κ ×ˢ (Set.univ : Set ℝ) with hT
  -- The slice `(σ,t) ↦ ρh τ t σ` is smooth on `T`.
  have hρhst : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => ρh τ z.2 z.1) T := by
    rw [hT]
    refine hρh.comp ((by fun_prop : ContDiff ℝ 12
        (fun z : ℝ × ℝ => ((τ, (z.2, z.1)) : ℝ × (ℝ × ℝ)))).contDiffOn) ?_
    intro z hz
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioo, true_and] at hz ⊢
    exact ⟨hτ, hz.1⟩
  -- The map `Φ = (σ,t) ↦ (τ, t, ρh τ t σ)` is smooth on `T` and lands in the chart's box.
  have hΦcd : ContDiffOn ℝ 12
      (fun z : ℝ × ℝ => (((τ : ℝ), (z.2, ρh τ z.2 z.1)) : ℝ × (ℝ × ℝ))) T := by
    rw [hT]
    exact contDiffOn_const.prodMk
      ((contDiff_snd : ContDiff ℝ 12 (fun z : ℝ × ℝ => z.2)).contDiffOn.prodMk hρhst)
  have hmap : Set.MapsTo
      (fun z : ℝ × ℝ => (((τ : ℝ), (z.2, ρh τ z.2 z.1)) : ℝ × (ℝ × ℝ)))
      T (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    rw [hT]
    intro z hz
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioo, Set.mem_Icc, true_and] at hz ⊢
    exact ⟨hτ, hρhv τ hτ z.2 z.1 hz.1⟩
  -- Hence the chart variable `(σ,t) ↦ W τ t (ρh τ t σ)` and its `uproj` are smooth on `T`.
  have hWcd : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => W τ z.2 (ρh τ z.2 z.1)) T :=
    hW.comp hΦcd hmap
  have hGcd : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => Work.RPV.uproj (W τ z.2 (ρh τ z.2 z.1))) T :=
    contDiff_uproj.contDiffOn.comp (hWcd.of_le (by norm_num)) (fun z _ => Set.mem_univ _)
  -- Restrict to the line `t ↦ (σ,t)`, which stays inside `T`.
  have hline : ContDiffOn ℝ 1 (fun t : ℝ => ((σ, t) : ℝ × ℝ)) (Set.univ : Set ℝ) :=
    (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => ((σ, t) : ℝ × ℝ))).contDiffOn
  have hmap2 : Set.MapsTo (fun t : ℝ => ((σ, t) : ℝ × ℝ)) (Set.univ : Set ℝ) T := by
    rw [hT]
    exact fun t _ => ⟨hσκ, trivial⟩
  have hslice : ContDiffOn ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) Set.univ :=
    hGcd.comp hline hmap2
  rwa [contDiffOn_univ] at hslice

end

end Work.RPB.B5
