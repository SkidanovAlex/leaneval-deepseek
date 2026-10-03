import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.lift_section
import Submission.Work.L62.section_unique
import Submission.Work.L62.section_Bl

/-!
# A holomorphic section of `ĥ_β = d.E - β` over a fixed ball, uniformly in `β ∈ Λ`

Given `𝓕₀`-data `d` and the horn data `hd` (so that `d.E : hd.Bl → ℂ` is a covering map over the
complement of the critical class `hd.v + ℤ`, `HornData.cov_l`, and is surjective, `HornData.surj_l`),
a compact `Λ` of parameters and a ball `ball ζ₀ ρ₀` whose `β`-translates stay `2ρ₀` away from the
critical class (`havoid`), we produce

* one compact `K ⊆ hd.Bl`, and
* for every `β ∈ Λ` a holomorphic section `σ` of `ĥ_β` over the whole ball `ball ζ₀ ρ₀`
  (`d.E (σ y) = y + β`), with `σ (ball ζ₀ ρ₀) ⊆ K`.

## Proof

The section over `ball ζ₀ ρ` exists for every `β ∈ Λ` by `Work.L62.lift_section`: `ĥ_β` is a covering
map over the *enlarged* ball `ball ζ₀ r` (`r = 3ρ₀/2 < 2ρ₀`, so `havoid` keeps it off `v + ℤ - β`),
and the enlarged ball is simply connected and contains a preimage of `ζ₀` by `HornData.surj_l`.

The point of the lemma is the *uniform* compact box.  If `σ` is a section over `ball ζ₀ r`, then for
every `β'` with `‖β' - β‖ < ρ₀/4` the translated map `y ↦ σ (y + β' - β)` is a section of `ĥ_{β'}`
over `ball ζ₀ ρ₀` (since `y + β' - β ∈ ball ζ₀ r`), and its image is contained in
`σ '' closedBall ζ₀ (5ρ₀/4)`, which is compact and contained in `hd.Bl`.  So each `β ∈ Λ` has a
*neighbourhood* of parameters admitting a section with image in a fixed compact box; since `Λ` is
compact, finitely many of those boxes suffice, and their union is `K`.
-/

namespace Work.L62HD

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

theorem section_over_ball_in_compact {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {ζ₀ : ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {Λ : Set ℂ} (hΛ : IsCompact Λ)
    (havoid : ∀ β ∈ Λ, ∀ k : ℤ, 2 * ρ₀ < ‖ζ₀ + β - (hd.v + (k : ℂ))‖) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ hd.Bl ∧
      ∀ β ∈ Λ, ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζ₀ ρ₀) ∧
        (∀ y ∈ Metric.ball ζ₀ ρ₀, σ y ∈ hd.Bl ∧ d.E (σ y) = y + β) ∧
        (∀ y ∈ Metric.ball ζ₀ ρ₀, σ y ∈ K) := by
  classical
  -- `d.E` is holomorphic on the lower horn
  have hsubE : hd.Bl ⊆ d.DE := fun w hw => hd.sub (Or.inr hw)
  have hEdiff : DifferentiableOn ℂ d.E hd.Bl :=
    d.Φ_holo.comp (d.φ_holo.mono (fun w hw => (hsubE hw).1)) (fun w hw => (hsubE hw).2)
  -- the two auxiliary radii `ρ₀ < r₂ < r < 2ρ₀`
  set r : ℝ := 3 * ρ₀ / 2 with hrdef
  set r₂ : ℝ := 5 * ρ₀ / 4 with hr₂def
  have hρ₄ : 0 < ρ₀ / 4 := by linarith
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hr₂lt : r₂ < r := by rw [hrdef, hr₂def]; linarith
  have hmem : ζ₀ ∈ Metric.ball ζ₀ r := by simp [Metric.mem_ball, hrpos]
  -- (A) the enlarged ball avoids the critical class `hd.v + ℤ - β` of `ĥ_β`
  have havoid' : ∀ β ∈ Λ, ∀ y ∈ Metric.ball ζ₀ r, ∀ k : ℤ, y + β ≠ hd.v + (k : ℂ) := by
    intro β hβ y hy k hc
    have h1 : ‖y - ζ₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    have h2 : ‖ζ₀ + β - (hd.v + (k : ℂ))‖ = ‖y - ζ₀‖ := by
      have h3 : ζ₀ + β - (hd.v + (k : ℂ)) = ζ₀ - y := by rw [← hc]; ring
      rw [h3, norm_sub_rev]
    have h4 := havoid β hβ k
    rw [h2] at h4
    rw [hrdef] at h1
    linarith
  -- (C) for every `β ∈ Λ`, a holomorphic section of `ĥ_β` over the enlarged ball
  have hsec : ∀ β ∈ Λ, ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζ₀ r) ∧
      (∀ y ∈ Metric.ball ζ₀ r, σ y ∈ hd.Bl ∧ d.E (σ y) - β = y) := by
    intro β hβ
    have hcontr : ContractibleSpace ↥(Metric.ball ζ₀ r) :=
      (convex_ball ζ₀ r).contractibleSpace ⟨ζ₀, hmem⟩
    have hYsc : SimplyConnectedSpace ↥(Metric.ball ζ₀ r) :=
      @SimplyConnectedSpace.ofContractible ↥(Metric.ball ζ₀ r) _ hcontr
    obtain ⟨x₀, hx₀mem, hx₀⟩ := hd.surj_l (ζ₀ + β)
    have hp : DifferentiableOn ℂ (fun z : ℂ => d.E z - β) hd.Bl := hEdiff.sub_const β
    have hpx : (fun z : ℂ => d.E z - β) x₀ = ζ₀ := by
      show d.E x₀ - β = ζ₀
      rw [hx₀]; ring
    obtain ⟨σ, hσdiff, -, hσsec⟩ :=
      Work.L62.lift_section (X := hd.Bl) hd.Bl_open (p := fun z : ℂ => d.E z - β) hp
        (Y := Metric.ball ζ₀ r) Metric.isOpen_ball hYsc
        ((hd.cov_l.homeomorph_comp (Homeomorph.subRight β)).mono
          (fun y hy k => havoid' β hβ y hy k)) hmem hx₀mem hpx
    exact ⟨σ, hσdiff, hσsec⟩
  -- (D) each `β ∈ Λ` has a neighbourhood of parameters with a section inside a fixed box
  have hbox : ∀ β ∈ Λ, ∃ Kb : Set ℂ, IsCompact Kb ∧ Kb ⊆ hd.Bl ∧
      ∀ β' ∈ Λ, ‖β' - β‖ < ρ₀ / 4 → ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball ζ₀ ρ₀) ∧
        (∀ y ∈ Metric.ball ζ₀ ρ₀, σ y ∈ hd.Bl ∧ d.E (σ y) = y + β') ∧
        (∀ y ∈ Metric.ball ζ₀ ρ₀, σ y ∈ Kb) := by
    intro β hβ
    obtain ⟨σ, hσdiff, hσsec⟩ := hsec β hβ
    refine ⟨σ '' Metric.closedBall ζ₀ r₂, ?_, ?_, ?_⟩
    · exact (isCompact_closedBall ζ₀ r₂).image_of_continuousOn
        (hσdiff.mono (Metric.closedBall_subset_ball hr₂lt)).continuousOn
    · rintro x ⟨y, hy, rfl⟩
      exact (hσsec y (Metric.closedBall_subset_ball hr₂lt hy)).1
    · intro β' hβ' hlt
      -- the translate `y ↦ y + (β' - β)` sends `ball ζ₀ ρ₀` into `ball ζ₀ r`
      have htrans : ∀ y : ℂ, y ∈ Metric.ball ζ₀ ρ₀ → y + (β' - β) ∈ Metric.ball ζ₀ r := by
        intro y hy
        rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
        have h1 : ‖y + (β' - β) - ζ₀‖ ≤ ‖y - ζ₀‖ + ‖β' - β‖ := by
          have h2 : y + (β' - β) - ζ₀ = (y - ζ₀) + (β' - β) := by ring
          rw [h2]; exact norm_add_le _ _
        have h3 : ‖y - ζ₀‖ + ‖β' - β‖ < r₂ := by
          have h4 : ‖y - ζ₀‖ + ‖β' - β‖ < ρ₀ + ρ₀ / 4 := add_lt_add hy hlt
          linarith [h4, hr₂def]
        linarith [h1, h3, hr₂lt]
      refine ⟨fun y => σ (y + (β' - β)), ?_, ?_, ?_⟩
      · exact hσdiff.comp (differentiableOn_id.add_const (β' - β)) htrans
      · intro y hy
        obtain ⟨hmem', hsec'⟩ := hσsec (y + (β' - β)) (htrans y hy)
        refine ⟨hmem', ?_⟩
        have h5 : d.E (σ (y + (β' - β))) = y + (β' - β) + β := sub_eq_iff_eq_add.mp hsec'
        rw [h5]; ring
      · intro y hy
        have hy'' : y + (β' - β) ∈ Metric.closedBall ζ₀ r₂ := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have h1 : ‖y + (β' - β) - ζ₀‖ ≤ ‖y - ζ₀‖ + ‖β' - β‖ := by
            have h2 : y + (β' - β) - ζ₀ = (y - ζ₀) + (β' - β) := by ring
            rw [h2]; exact norm_add_le _ _
          have hyb : ‖y - ζ₀‖ ≤ ρ₀ := by
            rw [Metric.mem_ball, dist_eq_norm] at hy
            exact le_of_lt hy
          have hltb : ‖β' - β‖ ≤ ρ₀ / 4 := le_of_lt hlt
          calc ‖y + (β' - β) - ζ₀‖ ≤ ‖y - ζ₀‖ + ‖β' - β‖ := h1
            _ ≤ ρ₀ + ρ₀ / 4 := add_le_add hyb hltb
            _ = r₂ := by rw [hr₂def]; ring
        exact ⟨y + (β' - β), hy'', rfl⟩
  -- (E) finitely many boxes suffice
  have hcoverΛ : Λ ⊆ ⋃ β : ↥Λ, Metric.ball (β : ℂ) (ρ₀ / 4) := by
    intro β hβ
    exact Set.mem_iUnion.mpr ⟨⟨β, hβ⟩, by rw [Metric.mem_ball]; simpa using hρ₄⟩
  obtain ⟨F, hFcov⟩ := hΛ.elim_finite_subcover (fun β : ↥Λ => Metric.ball (β : ℂ) (ρ₀ / 4))
      (fun _ => Metric.isOpen_ball) hcoverΛ
  choose Kb hKbc hKbs hKbp using fun β : ↥Λ => hbox β β.2
  refine ⟨⋃ β ∈ (F : Set ↥Λ), Kb β, ?_, ?_, ?_⟩
  · exact F.finite_toSet.isCompact_biUnion (fun β _ => hKbc β)
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨β, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨_, hx⟩ := hx
    exact hKbs β hx
  · intro β hβ
    have hb := hFcov hβ
    rw [Set.mem_iUnion] at hb
    obtain ⟨β₀, hb⟩ := hb
    rw [Set.mem_iUnion] at hb
    obtain ⟨hβ₀F, hb⟩ := hb
    have hlt : ‖β - (β₀ : ℂ)‖ < ρ₀ / 4 := by
      rw [Metric.mem_ball, dist_eq_norm] at hb
      exact hb
    obtain ⟨σ, hσd, hσs, hσK⟩ := hKbp β₀ β hβ hlt
    exact ⟨σ, hσd, hσs, fun y hy => Set.mem_biUnion hβ₀F (hσK y hy)⟩

end

end Work.L62HD
