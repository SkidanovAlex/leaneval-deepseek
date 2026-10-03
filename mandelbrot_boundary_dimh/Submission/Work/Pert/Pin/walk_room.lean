import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup
import Submission.Work.Pert.Ksub2.phi_norm_le_of_far_re_le

/-!
# `Work.Pert.Pin.walk_room`

Room around the `φ₀`-image of the "walk region" of a §4.1-datum `d = ParabData f₀ D₀`:

  `∃ R₀ > 0, ∀ q, q.re ≤ 3 → y₁ ≤ |q.im| → closedBall (φ₀ q) R₀ ⊆ D₀`.

The region `{Re q ≤ 3, |Im q| ≥ y₁}` is unbounded in two directions (`Re q → -∞` and
`|Im q| → ∞`), so compactness alone cannot give a uniform radius: one also needs control at
infinity.  Both ingredients are in the datum.

* Far out, `φ₀` is uniformly small in the half-plane `Re u ≤ 3`
  (`Work.Pert.Ksub2.phi_norm_le_of_far_re_le`, whose content is the asymptotic expansion field
  `ParabData.φ_asymp` on the repelling sector together with the elementary fact that
  `{Re u ≤ 3} \ QLeft ξ₀` is bounded).  Hence for `‖u‖ ≥ R'` the image `φ₀ u` lies in a fixed ball
  about `0` contained in `D₀`.
* The remaining core `{Re u ≤ 3, |Im u| ≥ y₁, ‖u‖ ≤ R'}` is compact and every one of its points
  has `|Im| ≥ y₁ > η₀`, so `ParabData.ends_sub` puts `u ∈ Dφ₀` and `φ₀ u` in the parabolic basin
  of `0`; the basin is contained in `D₀` (the `n = 0` case of its defining neighbourhood
  condition).  So its image is a compact subset of the open set `D₀`, hence has room.

Adding the two pieces gives a compact set `S ⊆ D₀` containing the whole image; a compact subset of
an open set has positive distance to the complement, and that distance is the required `R₀`.
-/

namespace Work.Pert.Pin

open MandelDim Set Metric
open scoped Topology

theorem walk_room {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {y₁ : ℝ} (hy₁ : d.η₀ < y₁) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ M : ℝ, 0 < M → ∀ q : ℂ,
      -M - 1 ≤ q.re → q.re ≤ 3 → y₁ ≤ |q.im| → Metric.closedBall (d.φ q) R₀ ⊆ D₀ := by
  have hDopen : IsOpen D₀ := hd.1
  have h0 : (0 : ℂ) ∈ D₀ := hd.2.1
  -- the parabolic basin of `0` is contained in `D₀` (the `n = 0` case of the definition)
  have hbasin : MandelDim.ParabolicBasin f₀ D₀ ⊆ D₀ := by
    rintro z ⟨U, hU, hmap, -⟩
    exact hmap 0 (mem_of_mem_nhds hU)
  -- every point of the region is in the maximal domain `Dφ₀` and maps into `D₀`
  have hreg : ∀ u : ℂ, y₁ ≤ |u.im| → u ∈ d.Dφ ∧ d.φ u ∈ D₀ := by
    intro u hu
    obtain ⟨hDφ, hbas⟩ := d.ends_sub u (lt_of_lt_of_le hy₁ hu)
    exact ⟨hDφ, hbasin hbas⟩
  -- room around `0` inside the open set `D₀`
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds h0)
  set c : ℝ := r / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcball : Metric.closedBall (0 : ℂ) c ⊆ D₀ :=
    subset_trans (Metric.closedBall_subset_ball (by rw [hcdef]; linarith)) hrsub
  -- `φ₀` is uniformly small far out in the half-plane `Re u ≤ 3`
  obtain ⟨R', hR'pos, hfar⟩ :=
    Work.Pert.Ksub2.phi_norm_le_of_far_re_le d (B := 3) hcpos
  -- the bounded core of the region, `{Re u ≤ 3, |Im u| ≥ y₁, ‖u‖ ≤ R'}`
  set K : Set ℂ := {u : ℂ | u.re ≤ 3} ∩ {u : ℂ | y₁ ≤ |u.im|} ∩ Metric.closedBall (0 : ℂ) R'
    with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R') ?_ ?_
    · exact ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))).inter
        Metric.isClosed_closedBall
    · intro u hu; exact hu.2
  have hKDφ : K ⊆ d.Dφ := fun u hu => (hreg u hu.1.2).1
  -- the image of the core is compact and lies in `D₀`
  have hImc : IsCompact (d.φ '' K) :=
    hKc.image_of_continuousOn ((d.φ_holo.continuousOn).mono hKDφ)
  have hImD : d.φ '' K ⊆ D₀ := by
    rintro z ⟨u, hu, rfl⟩
    exact (hreg u hu.1.2).2
  -- the whole region is mapped into `S = φ₀ '' K ∪ closedBall 0 c`
  set S : Set ℂ := d.φ '' K ∪ Metric.closedBall (0 : ℂ) c with hSdef
  have hSc : IsCompact S := by
    rw [hSdef]; exact hImc.union (isCompact_closedBall (0 : ℂ) c)
  have hSD : S ⊆ D₀ := by
    rw [hSdef]; exact Set.union_subset hImD hcball
  -- a compact set inside an open set has room
  obtain ⟨δ, hδpos, hδsub⟩ := hSc.exists_cthickening_subset_open hDopen hSD
  refine ⟨δ, hδpos, ?_⟩
  intro M _hM q _hre1 hre2 him
  have hmem : d.φ q ∈ S := by
    rw [hSdef]
    by_cases h : ‖q‖ ≤ R'
    · left
      exact ⟨q, ⟨⟨hre2, him⟩, by rw [Metric.mem_closedBall, dist_zero_right]; exact h⟩, rfl⟩
    · right
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hfar q hre2 (le_of_lt (not_le.mp h))
  exact subset_trans (Metric.closedBall_subset_cthickening hmem δ) hδsub

end Work.Pert.Pin
