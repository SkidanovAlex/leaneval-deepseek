import Mathlib
import Submission.Work.Pert.V5.Basics

/-!
# `Work.Pert.V5.deriv_sub_one_le_of_margin`

The pointwise (single-point) form of the "deviation bound from a margin" tool of
`NOTES_session23.md` §5: if the gate margin `min (mgA Ξ α w) (mgB Ξ w)` at a gate point `w` is at
least `κ` and `κ / √2 ≥ Rde`, then `hDE` (Shishikura's Lemma A.2.4(i),
`‖Φ' - 1/v‖ ≤ C₂/R` for `R ≥ Rde` and `ball z R ⊆ Qm`) applied on the ball of radius `R := κ/√2`
around `w` gives

  `‖deriv Φm w - 1 / v w‖ ≤ C₂ √2 / κ`   and   `‖1 / v w - 1‖ ≤ 1/31`,

whence `‖deriv Φm w - 1‖ ≤ C₂ √2 / κ + 1/31`.

The two ingredients are exactly the ones used by `Work.Pert.deriv_Phi_close_on_gate`:

* `Work.Pert.V5.ball_in_gate`: `ball w (min (mgA) (mgB) / √2) ⊆ Qm`, and `κ/√2 ≤ min / √2`, so
  every ball of radius `κ/√2` around `w` lies in the gate (`Rde ≤ κ/√2` is `hκRde`);
* `Work.Pert.V5.inv_sub_one_le_of_close` with `‖v z - 1‖ = ‖F z - (z + 1)‖ ≤ 1/32` from the
  near-translation hypothesis `hNT`.

No differentiability or injectivity hypothesis is needed: the displacement map `v = F - id`, its
near-translation bound and the Abel relation on the ball all come from `hNT` and `hΦm`.
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

theorem deriv_sub_one_le_of_margin {Ξ rr M Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {w : ℂ}
    {κ : ℝ}
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hDE : ∀ (Φ v : ℂ → ℂ) (z : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z R) → Set.InjOn Φ (Metric.ball z R) →
      DifferentiableOn ℂ v (Metric.ball z R) → (∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4) →
      (∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1) →
      ‖deriv Φ z - 1 / v z‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hw : w ∈ Work.Pert.Qm Ξ α) (hκ : 0 < κ) (hκRde : Rde ≤ κ / Real.sqrt 2)
    (hmargin : κ ≤ min (Work.Pert.V5.mgA Ξ α w) (Work.Pert.V5.mgB Ξ w)) :
    ‖deriv Φm w - 1‖ ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 := by
  -- the pointwise near-translation bound of `hNT`, in the shape used for `v = F - id`
  have hclose : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32 :=
    fun z hz => (hNT.1.2 z hz).1
  -- the displacement map `v = F - id` of the near-translation `F`
  set v : ℂ → ℂ := fun z => Work.Pert.liftF u σ α z - z with hv
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- the ball of radius `κ/√2` around `w` lies in the gate
  have hball : Metric.ball w (κ / Real.sqrt 2) ⊆ Work.Pert.Qm Ξ α :=
    subset_trans (Metric.ball_subset_ball (div_le_div_of_nonneg_right hmargin (le_of_lt hsq)))
      (Work.Pert.V5.ball_in_gate hw)
  have hvdiff : DifferentiableOn ℂ v (Metric.ball w (κ / Real.sqrt 2)) := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ => Work.Pert.liftF u σ α z - z)
        (Metric.ball w (κ / Real.sqrt 2)) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa only [hv] using h1
  have hvnear : ∀ z ∈ Metric.ball w (κ / Real.sqrt 2), ‖v z - 1‖ < 1 / 4 := by
    intro z hz
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hball hz
    have hb : ‖v z - 1‖ ≤ 1 / 32 := by
      have he : v z - 1 = Work.Pert.liftF u σ α z - (z + 1) := by simp only [hv]; ring
      rw [he]; exact hclose z hzQ
    linarith
  have habel : ∀ z ∈ Metric.ball w (κ / Real.sqrt 2),
      z + v z ∈ Metric.ball w (κ / Real.sqrt 2) → Φm (z + v z) = Φm z + 1 := by
    intro z hz hzv
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hball hz
    have he : z + v z = Work.Pert.liftF u σ α z := by simp only [hv]; ring
    have hFQ : Work.Pert.liftF u σ α z ∈ Work.Pert.Qm Ξ α := by rw [← he]; exact hball hzv
    have h := hΦm.2.2 z hzQ hFQ
    rwa [he]
  -- Shishikura's derivative estimate on the ball of radius `κ/√2`
  have hb := hDE Φm v w (κ / Real.sqrt 2) hκRde (hΦm.1.mono hball) (hΦm.2.1.mono hball)
    hvdiff hvnear habel
  have hdiv : C₂ / (κ / Real.sqrt 2) = C₂ * Real.sqrt 2 / κ := by rw [div_div_eq_mul_div]
  -- `‖1/(F w - w) - 1‖ ≤ 1/31`
  have hvinv : ‖1 / v w - 1‖ ≤ 1 / 31 := by
    refine Work.Pert.V5.inv_sub_one_le_of_close ?_
    have he : v w - 1 = Work.Pert.liftF u σ α w - (w + 1) := by simp only [hv]; ring
    rw [he]; exact hclose w hw
  have htri : ‖deriv Φm w - 1‖ ≤ ‖deriv Φm w - 1 / v w‖ + ‖1 / v w - 1‖ := by
    have he : deriv Φm w - 1 = (deriv Φm w - 1 / v w) + (1 / v w - 1) := by ring
    rw [he]; exact norm_add_le _ _
  calc ‖deriv Φm w - 1‖ ≤ ‖deriv Φm w - 1 / v w‖ + ‖1 / v w - 1‖ := htri
    _ ≤ C₂ * Real.sqrt 2 / κ + 1 / 31 := by
        refine add_le_add ?_ hvinv
        rw [← hdiv]; exact hb

end

end Work.Pert.V5
