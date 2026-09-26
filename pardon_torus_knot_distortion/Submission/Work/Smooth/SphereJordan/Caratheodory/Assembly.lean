import Mathlib

/-!
# From an injective continuous extension to the homeomorphism of the closures

Last step of the "Carathéodory" route to `Work.Smooth.SphereJordan.caratheodory_jordan`
(see `NOTES.md` in this directory): once the boundary curve `γ` of a Jordan domain `Ω` has been
extended to a *continuous injection* `Φ` of the closed disc whose image on the open disc is `Ω`,
the target `Nonempty (closure Ω ≃ₜ closedBall 0 1)` follows, because `Φ` is then a continuous
bijection from the compact `𝔻̄` onto the Hausdorff `Ω̄`.

The hypothesis `Φ '' 𝔻 = Ω` is exactly what the boundary-correspondence argument produces.
-/

noncomputable section

open Set Metric Filter

open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-- **The target follows from a continuous injective extension of the boundary curve to the closed
disc whose image on the open disc is `Ω`.** -/
theorem homeo_of_injective_extension {Ω : Set ℂ} {Φ : ℂ → ℂ}
    (hΦc : ContinuousOn Φ (Metric.closedBall (0 : ℂ) 1))
    (hΦinj : Set.InjOn Φ (Metric.closedBall (0 : ℂ) 1))
    (hΦimage : Φ '' Metric.ball (0 : ℂ) 1 = Ω) :
    Nonempty (closure Ω ≃ₜ Metric.closedBall (0 : ℂ) 1) := by
  have hΩmem : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ∈ Ω := fun z hz => by
    have h1 : Φ z ∈ Φ '' Metric.ball (0 : ℂ) 1 := ⟨z, hz, rfl⟩
    rwa [hΦimage] at h1
  have hclosed : Φ '' Metric.closedBall (0 : ℂ) 1 = closure Ω := by
    have hsub : Φ '' Metric.closedBall (0 : ℂ) 1 ⊆ closure Ω := by
      rintro _ ⟨z, hz, rfl⟩
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with h | h
      · exact subset_closure (hΩmem z (by rwa [Metric.mem_ball]))
      · -- `z` is on the sphere: approach it from inside along the radius
        have hnorm : ‖z‖ = 1 := by rw [dist_eq_norm] at h; simpa using h
        have hlt : ∀ n : ℕ, (1 - 1 / ((n : ℝ) + 1) : ℝ) < 1 := by
          intro n
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        have hle : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          intro n
          rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
          linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
        have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := fun n => by linarith [hle n]
        have hseq_ball : ∀ n : ℕ, ((1 - 1 / ((n : ℝ) + 1) : ℝ)) • z ∈ Metric.ball (0 : ℂ) 1 := by
          intro n
          rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn n),
            hnorm, mul_one]
          exact hlt n
        have hseq_tend : Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 1) : ℝ)) • z) atTop (𝓝 z) := by
          have h1 : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
            have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
              simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
            simpa using tendsto_const_nhds.sub h0
          have h2 := h1.smul (tendsto_const_nhds (x := z))
          rwa [one_smul] at h2
        have hseq_in : ∀ᶠ n : ℕ in atTop,
            ((1 - 1 / ((n : ℝ) + 1) : ℝ)) • z ∈ Metric.closedBall (0 : ℂ) 1 :=
          Eventually.of_forall fun n => Metric.ball_subset_closedBall (hseq_ball n)
        have hlimΦ : Tendsto (fun n : ℕ => Φ (((1 - 1 / ((n : ℝ) + 1) : ℝ)) • z)) atTop
            (𝓝 (Φ z)) := by
          refine Tendsto.comp ?_ (tendsto_inf.mpr ⟨hseq_tend, tendsto_principal.mpr hseq_in⟩)
          exact hΦc.continuousWithinAt hz
        exact isClosed_closure.mem_of_tendsto hlimΦ
          (Eventually.of_forall fun n => subset_closure (hΩmem _ (hseq_ball n)))
    refine Subset.antisymm hsub ?_
    have hΩsub : Ω ⊆ Φ '' Metric.closedBall (0 : ℂ) 1 := by
      intro w hw
      obtain ⟨z, hz, hze⟩ :=
        (show w ∈ Φ '' Metric.ball (0 : ℂ) 1 from by rw [hΦimage]; exact hw)
      exact ⟨z, Metric.ball_subset_closedBall hz, hze⟩
    exact closure_minimal hΩsub ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hΦc).isClosed
  have hmem : ∀ z : (Metric.closedBall (0 : ℂ) 1 : Set ℂ), Φ z ∈ closure Ω := fun z => by
    have h1 : Φ z ∈ Φ '' Metric.closedBall (0 : ℂ) 1 := ⟨z, z.2, rfl⟩
    rwa [hclosed] at h1
  let F : (Metric.closedBall (0 : ℂ) 1 : Set ℂ) → closure Ω := fun z => ⟨Φ z, hmem z⟩
  have hFinj : Function.Injective F := by
    intro z w hzw
    refine Subtype.ext (hΦinj z.2 w.2 ?_)
    exact congrArg Subtype.val hzw
  have hFsurj : Function.Surjective F := by
    intro y
    have hy : (y : ℂ) ∈ Φ '' Metric.closedBall (0 : ℂ) 1 := by
      rw [hclosed]; exact y.2
    obtain ⟨z, hz, hze⟩ := hy
    exact ⟨⟨z, hz⟩, Subtype.ext hze⟩
  have hFcont : Continuous F := by
    have h1 : Continuous (fun z : (Metric.closedBall (0 : ℂ) 1 : Set ℂ) => Φ (z : ℂ)) :=
      continuousOn_iff_continuous_domRestrict.mp hΦc
    exact h1.subtype_mk hmem
  rcases (show Nonempty ((Metric.closedBall (0 : ℂ) 1 : Set ℂ) ≃ₜ closure Ω) from
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFcont⟩)
    with ⟨e⟩
  exact ⟨e.symm⟩

end Work.Smooth.SphereJordan.Caratheodory
