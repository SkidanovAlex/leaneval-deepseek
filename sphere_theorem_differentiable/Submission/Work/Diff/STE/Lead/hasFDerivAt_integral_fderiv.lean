import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiation under the integral sign for a parametrised interval integral

This file proves that if `(σ, y) ↦ H σ y` and `(σ, y) ↦ fderiv ℝ (H σ) y` are jointly continuous on
`[0, τ) × Ω` (with `Ω` open and each slice `H σ` smooth on `Ω`), then for `t₀, s ∈ [0, τ)` the map
`y ↦ ∫ σ in t₀..s, H σ y` is differentiable at every `y ∈ Ω` with derivative
`∫ σ in t₀..s, fderiv ℝ (H σ) y`.

The proof is the standard one: pick a closed ball `B ⊆ Ω` around `y`, bound `‖fderiv ℝ (H σ) x‖`
uniformly on the compact set `[min t₀ s, max t₀ s] × B` by a constant `C` (continuity of the
derivative on a compact set, which is where properness of the model space enters), and apply
Mathlib's `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` with the constant
dominating function `C`.
-/

open MeasureTheory Filter Set

open scoped Interval Topology

namespace Work.Diff.STE.Lead

/-- **Differentiation under the integral sign** for a family of functions `(H σ)` on an open set
`Ω` of a proper normed `ℝ`-space, uniformly in `σ ∈ [0, τ)`: if `(σ, y) ↦ H σ y` and
`(σ, y) ↦ fderiv ℝ (H σ) y` are jointly continuous and every slice `H σ` is smooth on `Ω`, then
`y ↦ ∫ σ in t₀..s, H σ y` has derivative `∫ σ in t₀..s, fderiv ℝ (H σ) y` at every `y ∈ Ω`. -/
theorem hasFDerivAt_integral_fderiv_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E]
    {τ : ℝ} {Ω : Set E} (hΩ : IsOpen Ω)
    (H : ℝ → E → ℂ)
    (hsm : ∀ σ ∈ Set.Ico (0 : ℝ) τ, ContDiffOn ℝ (⊤ : ℕ∞) (H σ) Ω)
    (hc : ContinuousOn (fun p : ℝ × E => H p.1 p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (hd : ContinuousOn (fun p : ℝ × E => fderiv ℝ (H p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    {t₀ s : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) τ) (hs : s ∈ Set.Ico (0 : ℝ) τ)
    {y : E} (hy : y ∈ Ω) :
    HasFDerivAt (fun y' : E => ∫ σ in t₀..s, H σ y')
      (∫ σ in t₀..s, fderiv ℝ (H σ) y) y := by
  -- A closed ball around `y` contained in `Ω`.
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.mp hΩ y hy
  have hB_sub : Metric.closedBall y (ρ / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρΩ
  have hB_nhds : Metric.closedBall y (ρ / 2) ∈ 𝓝 y := Metric.closedBall_mem_nhds y (by linarith)
  -- Both endpoints lie in `[0, τ)`, hence so does the whole unordered interval between them.
  have huIcc_sub : Set.uIcc t₀ s ⊆ Set.Ico (0 : ℝ) τ := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans ht₀.1 h1, lt_of_le_of_lt h2 hs.2⟩
    · exact ⟨le_trans hs.1 h1, lt_of_le_of_lt h2 ht₀.2⟩
  -- Continuity of the slices.
  have hslice : ∀ x ∈ Ω, ContinuousOn (fun t : ℝ => H t x) (Set.uIcc t₀ s) := by
    intro x hx
    exact hc.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨huIcc_sub ht, hx⟩)
  have hdslice : ContinuousOn (fun t : ℝ => fderiv ℝ (H t) y) (Set.uIcc t₀ s) :=
    hd.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨huIcc_sub ht, hy⟩)
  -- Uniform bound of the derivative on the compact set `uIcc t₀ s × B`.
  have hK : IsCompact (Set.uIcc t₀ s ×ˢ Metric.closedBall y (ρ / 2)) :=
    isCompact_uIcc.prod (isCompact_closedBall y (ρ / 2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hd.mono (Set.prod_mono huIcc_sub hB_sub))
  -- Differentiate under the integral sign, with the constant dominating function `max C 0`.
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (E := ℂ) (H := E) (F := fun x t => H t x) (F' := fun x t => fderiv ℝ (H t) x)
    (x₀ := y) (s := Metric.closedBall y (ρ / 2)) (a := t₀) (b := s) (bound := fun _ => max C 0)
    hB_nhds ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hy] with x hx
    exact ((hslice x hx).mono Set.uIoc_subset_uIcc).aestronglyMeasurable (μ := volume)
      measurableSet_uIoc
  · exact (hslice y hy).intervalIntegrable
  · exact (hdslice.mono Set.uIoc_subset_uIcc).aestronglyMeasurable (μ := volume) measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht x hx =>
      (hC (t, x) ⟨Set.uIoc_subset_uIcc ht, hx⟩).trans (le_max_left _ _)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht x hx =>
      (((hsm t (huIcc_sub (Set.uIoc_subset_uIcc ht))).differentiableOn (by norm_num)).differentiableAt
        (hΩ.mem_nhds (hB_sub hx))).hasFDerivAt

theorem hasFDerivAt_integral_fderiv {n : ℕ} {τ : ℝ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (H : ℝ → (Fin n → ℝ) → ℂ)
    (hsm : ∀ σ ∈ Set.Ico (0 : ℝ) τ, ContDiffOn ℝ (⊤ : ℕ∞) (H σ) Ω)
    (hc : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => H p.1 p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (hd : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (H p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    {t₀ s : ℝ} (ht₀ : t₀ ∈ Set.Ico (0 : ℝ) τ) (hs : s ∈ Set.Ico (0 : ℝ) τ)
    {y : Fin n → ℝ} (hy : y ∈ Ω) :
    HasFDerivAt (fun y' : Fin n → ℝ => ∫ σ in t₀..s, H σ y')
      (∫ σ in t₀..s, fderiv ℝ (H σ) y) y :=
  hasFDerivAt_integral_fderiv_gen hΩ H hsm hc hd ht₀ hs hy

end Work.Diff.STE.Lead
