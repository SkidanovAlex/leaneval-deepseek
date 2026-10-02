/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.robust_of_greenOpen` — the robustness **(I2)** of the leak disc

`Work.PARIMPL.LeakData.robust` (the field (I2) of §1.4 of
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md`) is *derived* here from the NAKANE input
`Work.PARIMPL.GreenEscapeOpen`, the joint continuity of the Green function `(c, z) ↦ G_c z` of
the family `T_c`.

## The mathematics

Let `D = closedBall (x* − j₀) r₀` be the leak disc and `Ψ` the repelling coordinate.  On `D`
the composite `Ψ` is continuous, so `Ψ '' D` is compact; it is nonempty because `r₀ > 0`.  For
`w ∈ Ψ '' D`, say `w = Ψ z` with `z ∈ D`, the deepness hypothesis `hdeep` gives
`G_{c₀} w > 0`, and `GreenEscapeOpen` yields a radius `δ w > 0` with

  `∀ c' ∈ ball c₀ (δ w), ∀ z' ∈ ball w (δ w), 0 < G_{c'} z'`.

The balls `ball w (δ w / 3)` cover the compact set `Ψ '' D`, so the third of the radii can be
replaced by a finite subcover with centres `w i` (`i ∈ t`).  The uniform radius

  `ρ = min_{i ∈ t} δ i / 3 > 0`

then does the job: if `c ∈ ball c₀ ρ` and `y` is within `ρ` of `Ψ z` for some `z ∈ D`, choose
`i ∈ t` with `Ψ z ∈ ball w i (δ i / 3)`; then

  `c ∈ ball c₀ (δ i)`  — since `dist c c₀ < ρ ≤ δ i / 3 < δ i`, and
  `y ∈ ball w i (δ i)`  — since `dist y w i ≤ ρ + δ i / 3 ≤ 2 δ i / 3 < δ i`,

so `G_c y > 0`, and by `Work.PARIMPL.notMem_K_of_green_pos` the point `y` does not lie in the
filled Julia set `K_c`.  ∎

The "third" is what makes the second radius bound *strict*: with the same radius `δ i` on both
sides one only gets `dist y (w i) ≤ δ i`.
-/
import Mathlib
import Submission.Work.PARIMPL.Leak

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL

open Classical Filter Set Metric
open scoped Topology

/-- **The robustness (I2) of the leak disc**, derived from the NAKANE input
`Work.PARIMPL.GreenEscapeOpen`: if the leak disc `closedBall (x* − j₀) r₀` is *deep* in the
escaping region at `c₀` (every point of `Ψ '' closedBall (x* − j₀) r₀` has positive Green
function), then there is a radius `ρ > 0` such that for every parameter `c` within `ρ` of `c₀`,
every point within `ρ` of `Ψ '' closedBall (x* − j₀) r₀` lies outside the filled Julia set
`K_c`.

This is exactly the field `Work.PARIMPL.LeakData.robust`. -/
theorem robust_of_greenOpen {c₀ : ℂ}
    {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (hG : Work.PARIMPL.GreenEscapeOpen)
    {xstar : ℝ} {j₀ : ℤ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdeep : ∀ z ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀,
      0 < Work.Bottcher.green c₀ (Ψ z)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀, dist y (Ψ z) ≤ ρ) →
        y ∉ Work.EL.K c := by
  -- the leak disc, and its image under `Ψ`
  let D : Set ℂ := Metric.closedBall (((xstar - (j₀ : ℝ)) : ℝ) : ℂ) r₀
  have hDcpt : IsCompact D := isCompact_closedBall _ _
  have hDne : D.Nonempty := ⟨_, Metric.mem_closedBall_self (le_of_lt hr₀)⟩
  have hKD : IsCompact (Ψ '' D) := hDcpt.image hΨ
  have hKDne : (Ψ '' D).Nonempty := hDne.image Ψ
  -- the escaping region of the family is open around each point of `Ψ '' D` at `c₀`
  have hex : ∀ w : ↥(Ψ '' D), ∃ δ : ℝ, 0 < δ ∧
      ∀ c' ∈ Metric.ball c₀ δ, ∀ z' ∈ Metric.ball (w : ℂ) δ,
        0 < Work.Bottcher.green c' z' := by
    rintro w
    obtain ⟨z, hz, hzw⟩ := w.property
    rw [← hzw]
    exact hG c₀ (Ψ z) (hdeep z hz)
  choose δ hδpos hδ using hex
  -- the thirds of these radii cover the compact set `Ψ '' D`
  have hcover : (Ψ '' D) ⊆ ⋃ w : ↥(Ψ '' D), Metric.ball (w : ℂ) (δ w / 3) := by
    intro w hw
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    have := hδpos ⟨w, hw⟩
    linarith
  obtain ⟨t, ht⟩ := hKD.elim_finite_subcover
      (fun w : ↥(Ψ '' D) => Metric.ball (w : ℂ) (δ w / 3))
      (fun _ => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨w, hw⟩ := hKDne
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (ht hw)
    exact ⟨i, hi⟩
  -- the uniform radius
  refine ⟨t.inf' htne (fun i => δ i / 3), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro i _
    have := hδpos i
    linarith
  · intro c hc y hz
    obtain ⟨z, hzD, hzy⟩ := hz
    have hzKD : Ψ z ∈ Ψ '' D := ⟨z, hzD, rfl⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hzKD)
    have hρle : t.inf' htne (fun i => δ i / 3) ≤ δ i / 3 := Finset.inf'_le _ hi
    have hδi : 0 < δ i := hδpos i
    have hcball : c ∈ Metric.ball c₀ (δ i) := by
      rw [Metric.mem_ball] at hc ⊢
      linarith
    have hyball : y ∈ Metric.ball (i : ℂ) (δ i) := by
      have htri : dist y ((i : ℂ)) ≤ dist y (Ψ z) + dist (Ψ z) (i : ℂ) :=
        dist_triangle _ _ _
      rw [Metric.mem_ball] at hzi ⊢
      linarith
    exact notMem_K_of_green_pos (hδ i c hcball y hyball)

end Work.PARIMPL
