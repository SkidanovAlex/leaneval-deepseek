import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.Prelim

/-!
# `Work.Pert.pert2v2.HdiffRow.EfQpAux` — local `Qp`-membership helpers for the floor extension

The floor extension `EfFloor Φm Φp Q` uses the value `Φp (invOn Φm Q u)` at the canonical
(`⌊Re⌋`) representative `u = w - ⌊Re w⌋` of `w`.  When `Φp` is only known to be holomorphic on a
*second* open set `Qp ⊆ ℂ` (the gate of the partner coordinate), differentiability of
`w ↦ EfFloor Φm Φp Q w - w` at `w₀` only needs `Φp` differentiable at the *single* point
`invOn Φm Q u` — and this point is in `Qp` as soon as the gate points of the band lie in `Qp`.

This file supplies the three local ingredients:

* `seedP_differentiableAt_of_invOn_mem`: the seed value `seedP τ Φ Q = τ ∘ invOn Φ Q` is
  differentiable at `w ∈ Φ '' Q` as soon as `τ` is differentiable at `invOn Φ Q w`
  (the pointwise form of `Work.Pert.seedP_holo`);
* `eventually_invOn_mem_of_mem`: the chosen preimage of the gate image near `Φ ζ` can be pushed
  into any neighbourhood of `ζ` (continuity of `invOn` *within* the gate image);
* `exists_ball_germ_data`: combining the two, a ball around a gate value `u` on which
  `invOn Φ Q` maps both `z` and `z + 1` into `Qp` — the exact hypothesis shape needed by the
  identity-theorem germ argument for the level-one relation of `EfFloor`.
-/

namespace Work.Pert.pert2v2.HdiffRow

open Complex Set Filter
open scoped Topology

noncomputable section

/-- **Pointwise differentiability of the seed value.**  If `w = Φ ζ` is a gate value and `τ` is
differentiable at the chosen preimage `invOn Φ Q w` (which lies in the open `Qp` in the intended
application), then `seedP τ Φ Q = τ ∘ invOn Φ Q` is differentiable at `w`.  This is
`Work.Pert.seedP_holo` with the global hypothesis `DifferentiableOn ℂ τ Q` weakened to a single
point: the local inverse `g` of `Φ` at `ζ` is analytic and `invOn Φ Q =ᶠ g` on `Φ '' Q`. -/
theorem seedP_differentiableAt_of_invOn_mem {Φ τ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    {w : ℂ} (hw : w ∈ Φ '' Q) (hτ : DifferentiableAt ℂ τ (Work.Pert.invOn Φ Q w)) :
    DifferentiableAt ℂ (Work.Pert.seedP τ Φ Q) w := by
  obtain ⟨ζ₀, hζ₀, rfl⟩ := hw
  have hζ₀inv : Work.Pert.invOn Φ Q (Φ ζ₀) = ζ₀ :=
    Work.Pert.invOn_eq hinj ⟨ζ₀, hζ₀, rfl⟩ hζ₀ rfl
  obtain ⟨g, hga, hg0, hge⟩ :=
    Work.Pert.invOn_eventuallyEq_localInverse hQ hΦ hinj hζ₀ (hder ζ₀ hζ₀)
  have hVopen : IsOpen (Φ '' Q) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨ζ, hζ, rfl⟩
    exact Work.Pert.pert2v2.EfFloorDiffV2.mem_nhds_image_of_deriv_ne_zero hQ hΦ hζ (hder ζ hζ)
  have hmem : Φ '' Q ∈ 𝓝 (Φ ζ₀) := hVopen.mem_nhds ⟨ζ₀, hζ₀, rfl⟩
  have hev : Work.Pert.seedP τ Φ Q =ᶠ[𝓝 (Φ ζ₀)] (fun w => τ (g w)) := by
    filter_upwards [hge, hmem] with w hgw hwQ
    simp only [Work.Pert.seedP]
    rw [hgw hwQ]
  have hτ' : DifferentiableAt ℂ τ (g (Φ ζ₀)) := by
    have : g (Φ ζ₀) = Work.Pert.invOn Φ Q (Φ ζ₀) := by rw [hg0, hζ₀inv]
    rw [this]; exact hτ
  have hcomp : DifferentiableAt ℂ (fun w => τ (g w)) (Φ ζ₀) := by
    simpa [Function.comp_def] using hτ'.comp (Φ ζ₀) hga.differentiableAt
  exact hcomp.congr_of_eventuallyEq hev

/-- **The chosen preimage near a gate value can be pushed into any neighbourhood of the
preimage.**  `invOn Φ Q` is continuous *within* `Φ '' Q` (it agrees there, near `Φ ζ`, with the
analytic local inverse of `Φ` at `ζ`), so for an open `V ∋ ζ` the points `w ∈ Φ '' Q` close to
`Φ ζ` have `invOn Φ Q w ∈ V`. -/
theorem eventually_invOn_mem_of_mem {Φ : ℂ → ℂ} {Q V : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hV : IsOpen V) {ζ : ℂ} (hζ : ζ ∈ Q) (hζV : ζ ∈ V) :
    ∀ᶠ w in 𝓝 (Φ ζ), w ∈ Φ '' Q → Work.Pert.invOn Φ Q w ∈ V := by
  obtain ⟨g, hga, hg0, hge⟩ := Work.Pert.invOn_eventuallyEq_localInverse hQ hΦ hinj hζ (hder ζ hζ)
  have hcont : ContinuousAt g (Φ ζ) := hga.continuousAt
  have hmemV : V ∈ 𝓝 (g (Φ ζ)) := by rw [hg0]; exact hV.mem_nhds hζV
  have hev : ∀ᶠ w in 𝓝 (Φ ζ), g w ∈ V := hcont.eventually hmemV
  filter_upwards [hev, hge] with w hgw hge' hwQ
  rw [hge' hwQ]; exact hgw

/-- **The ball on which the germ argument lives.**  Let `u` and `u + 1` be gate values whose chosen
preimages `ς = invOn Φ Q u` and `ς₁ = invOn Φ Q (u + 1)` lie in the open set `Qp`.  Then there is
`r > 0` such that on `ball u r`:

* `z` and `z + 1` are gate values, and
* the chosen preimages of `z` and of `z + 1` lie in `Qp`.

This is exactly the hypothesis shape needed to know that
`z ↦ seedP Φp Φm Q z` and `z ↦ seedP Φp Φm Q (z+1)` are holomorphic on `ball u r` when `Φp` is
holomorphic on `Qp` (`seedP_differentiableAt_of_invOn_mem`). -/
theorem exists_ball_germ_data {Φ : ℂ → ℂ} {Q Qp : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hQpopen : IsOpen Qp) {u : ℂ}
    (hu : u ∈ Φ '' Q) (hu1 : u + 1 ∈ Φ '' Q)
    (h0 : Work.Pert.invOn Φ Q u ∈ Qp) (h1 : Work.Pert.invOn Φ Q (u + 1) ∈ Qp) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball u r ⊆ Φ '' Q ∧
      (∀ z ∈ Metric.ball u r, z + 1 ∈ Φ '' Q) ∧
      (∀ z ∈ Metric.ball u r, Work.Pert.invOn Φ Q z ∈ Qp) ∧
      (∀ z ∈ Metric.ball u r, Work.Pert.invOn Φ Q (z + 1) ∈ Qp) := by
  have hVopen : IsOpen (Φ '' Q) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨ζ, hζ, rfl⟩
    exact Work.Pert.pert2v2.EfFloorDiffV2.mem_nhds_image_of_deriv_ne_zero hQ hΦ hζ (hder ζ hζ)
  set U : Set ℂ := (Φ '' Q) ∩ {z : ℂ | z + 1 ∈ Φ '' Q} with hU
  have hUopen : IsOpen U := hVopen.inter (hVopen.preimage (continuous_id.add continuous_const))
  have huU : u ∈ U := by rw [hU]; exact ⟨hu, by simpa using hu1⟩
  have hUmem : U ∈ 𝓝 u := hUopen.mem_nhds huU
  have hE0 : ∀ᶠ w in 𝓝 u, w ∈ Φ '' Q → Work.Pert.invOn Φ Q w ∈ Qp := by
    have h := eventually_invOn_mem_of_mem hQ hΦ hinj hder hQpopen (Work.Pert.invOn_mem hu) h0
    rwa [Work.Pert.invOn_spec hu] at h
  have hE1 : ∀ᶠ z in 𝓝 u, z + 1 ∈ Φ '' Q → Work.Pert.invOn Φ Q (z + 1) ∈ Qp := by
    have h := eventually_invOn_mem_of_mem hQ hΦ hinj hder hQpopen
      (Work.Pert.invOn_mem hu1) h1
    rw [Work.Pert.invOn_spec hu1] at h
    exact (continuousAt_id.add_const (1 : ℂ)).eventually h
  obtain ⟨r1, hr1, hb1⟩ := Metric.mem_nhds_iff.mp hUmem
  obtain ⟨r2, hr2, hb2⟩ := Metric.mem_nhds_iff.mp hE0
  obtain ⟨r3, hr3, hb3⟩ := Metric.mem_nhds_iff.mp hE1
  refine ⟨min r1 (min r2 r3), lt_min hr1 (lt_min hr2 hr3), ?_, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans
      (Set.Subset.trans hb1 Set.inter_subset_left)
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans
      (Set.Subset.trans hb1 Set.inter_subset_right)
  · intro z hz
    exact hb2 (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hz)
      ((Metric.ball_subset_ball (min_le_left _ _)).trans
        (Set.Subset.trans hb1 Set.inter_subset_left) hz)
  · intro z hz
    exact hb3 (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hz)
      ((Metric.ball_subset_ball (min_le_left _ _)).trans
        (Set.Subset.trans hb1 Set.inter_subset_right) hz)

end

end Work.Pert.pert2v2.HdiffRow
