import Mathlib

/-!
# Extending a bounded analytic function across a discrete set (Riemann, global form)

Let `Ω ⊆ ℂ` be open, `F ⊆ ℂ` a closed discrete subset of `Ω` (every point of `F` has a ball
meeting `F` only in that point, and every point of `Ω \ F` has a ball avoiding `F`), and let
`ψ : ℂ → ℂ` be analytic at every point of `Ω \ F` with `‖ψ z‖ ≤ 1` there.  Then `ψ` agrees on
`Ω \ F` with a function `Ψ` analytic on all of `Ω`.

The extension is the Riemann extension: at a point `z ∈ F` we take the value
`limUnder (𝓝[≠] z) ψ'`, where `ψ'` is `ψ` inside `Ω` and `0` outside (so that the values of the
arbitrary function `ψ` at points of `F` and outside `Ω` do not pollute the limit).  On the
punctured ball of `hFdisc` the function `ψ'` is holomorphic and bounded, so
`Complex.differentiableOn_update_limUnder_of_bddAbove` makes the updated function holomorphic
there.
-/

open Filter
open scoped Topology

namespace Work.Horn.HB

theorem exists_analytic_extension_of_bounded {Ω F : Set ℂ} (hΩ : IsOpen Ω)
    (hFdisc : ∀ z ∈ F, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ Ω ∧ Metric.ball z ρ ∩ F = {z})
    (hFcl : ∀ z ∈ Ω, z ∉ F → ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ Ω \ F)
    {ψ : ℂ → ℂ} (hψ : ∀ z ∈ Ω \ F, AnalyticAt ℂ ψ z)
    (hbdd : ∀ z ∈ Ω \ F, ‖ψ z‖ ≤ 1) :
    ∃ Ψ : ℂ → ℂ, (∀ z ∈ Ω, AnalyticAt ℂ Ψ z) ∧ Set.EqOn Ψ ψ (Ω \ F) := by
  classical
  -- Every point of `Ω \ F` has a ball avoiding `F`, i.e. `Ω \ F` is open.
  have hOpen : IsOpen (Ω \ F) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ρ, hρ, hball⟩ := hFcl z hz.1 hz.2
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hρ) hball
  -- Redefine `ψ` to vanish outside `Ω`, so that the limits at points of `F` only see `Ω \ F`.
  set ψ' : ℂ → ℂ := fun w => if w ∈ Ω then ψ w else 0 with hψ'def
  have hψ'_eq : ∀ w ∈ Ω, ψ' w = ψ w := by
    intro w hw
    simp only [hψ'def]
    exact ite_eq_left hw
  have hψ'_an : ∀ w ∈ Ω \ F, AnalyticAt ℂ ψ' w := by
    intro w hw
    have heq : ψ' =ᶠ[𝓝 w] ψ :=
      Filter.eventually_of_mem (hOpen.mem_nhds hw) (fun x hx => hψ'_eq x hx.1)
    exact (hψ w hw).congr heq.symm
  have hψ'_bdd : ∀ w ∈ Ω \ F, ‖ψ' w‖ ≤ 1 := by
    intro w hw
    rw [hψ'_eq w hw.1]
    exact hbdd w hw
  -- The candidate extension.
  set Ψ : ℂ → ℂ := fun w =>
    if w ∈ Ω ∧ w ∈ F then (𝓝[≠] w).limUnder ψ' else ψ' w with hΨdef
  have hΨ_off : ∀ w ∈ Ω \ F, Ψ w = ψ' w := by
    intro w hw
    simp only [hΨdef]
    exact ite_eq_right (fun h => hw.2 h.2)
  -- Analyticity at the points of `F`.
  have hΨ_on : ∀ z ∈ Ω ∩ F, AnalyticAt ℂ Ψ z := by
    intro z hz
    obtain ⟨hzΩ, hzF⟩ := hz
    obtain ⟨ρ, hρ, hballΩ, hballF⟩ := hFdisc z hzF
    -- the punctured ball is contained in `Ω \ F`
    have hsub : Metric.ball z ρ \ {z} ⊆ Ω \ F := by
      rintro w ⟨hw, hwz⟩
      refine ⟨hballΩ hw, fun hwF => hwz ?_⟩
      have hmem : w ∈ Metric.ball z ρ ∩ F := ⟨hw, hwF⟩
      rwa [hballF] at hmem
    have hanNhd : AnalyticOnNhd ℂ ψ' (Ω \ F) := hψ'_an
    have hdiffOn : DifferentiableOn ℂ ψ' (Metric.ball z ρ \ {z}) :=
      hanNhd.differentiableOn.mono hsub
    have hbddOn : BddAbove (norm ∘ ψ' '' (Metric.ball z ρ \ {z})) := by
      refine ⟨1, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact hψ'_bdd w (hsub hw)
    have hupd : DifferentiableOn ℂ
        (Function.update ψ' z ((𝓝[≠] z).limUnder ψ')) (Metric.ball z ρ) :=
      Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds z hρ) hdiffOn
        hbddOn
    have hAnUpd : AnalyticAt ℂ (Function.update ψ' z ((𝓝[≠] z).limUnder ψ')) z :=
      ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr hupd) z
        (Metric.mem_ball_self hρ)
    -- on the ball, `Ψ` is the updated function
    have heq : Function.update ψ' z ((𝓝[≠] z).limUnder ψ') =ᶠ[𝓝 z] Ψ := by
      refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hρ) ?_
      intro w hw
      rcases eq_or_ne w z with rfl | hne
      · rw [Function.update_self]
        simp only [hΨdef]
        exact (ite_eq_left ⟨hzΩ, hzF⟩).symm
      · rw [Function.update_of_ne hne]
        simp only [hΨdef]
        exact (ite_eq_right (fun h => hne (by
          have hmem : w ∈ Metric.ball z ρ ∩ F := ⟨hw, h.2⟩
          rwa [hballF] at hmem))).symm
    exact hAnUpd.congr heq
  refine ⟨Ψ, ?_, ?_⟩
  · intro z hz
    by_cases hzF : z ∈ F
    · exact hΨ_on z ⟨hz, hzF⟩
    · exact (hψ'_an z ⟨hz, hzF⟩).congr
        (Filter.eventually_of_mem (hOpen.mem_nhds ⟨hz, hzF⟩)
          (fun w hw => (hΨ_off w hw).symm))
  · intro z hz
    rw [hΨ_off z hz, hψ'_eq z hz.1]

end Work.Horn.HB
