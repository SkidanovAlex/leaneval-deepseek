import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs

namespace Work.Pert.PinAux

open MandelDim Complex Metric

set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.Pert.PinAux.good_deriv_bound`

The derivative of a Fatou coordinate of a near-translation, on the part of the gate where the
clearance `minmarg Ξ α w / √2` is at least `Rde`.

The proof applies Lemma A.2.4(i) (here the hypothesis `hDEest`) at `w` with the *vector field*
`v = F - id` of the near-translation and the ball `ball w (minmarg / √2)`:

* `ball w (minmarg / √2) ⊆ Qm Ξ α` (`ball_subset_Qm_of_minmarg`), so `Φ` is differentiable and
  injective there and the Abel equation `Φ (z + v z) = Φ z + 1` holds;
* `‖v z - 1‖ = ‖F z - (z + 1)‖ ≤ 1/32 < 1/4` on the gate (`NearTranslationOn`).

This gives `‖deriv Φ w - 1 / (F w - w)‖ ≤ C₂ / (minmarg / √2) = C₂ √2 / minmarg`.  It remains to
compare `1 / (F w - w)` with `1`, for which the *sharp* deviation hypothesis `hsh` at the single
point `w` is used: `t := ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c` (as well as `t ≤ 1/32`), and then

  `‖1 / (F w - w) - 1‖ ≤ t / (1 - t) ≤ c / (1 - c) + 4 K / ‖w‖`

by elementary arithmetic (`goodDev_norm_inv`, `goodDev_arith`).
-/

/-- Elementary arithmetic behind the estimate of `1 / (F w - w) - 1`: if `t ≤ c + x` with
`0 ≤ t ≤ 1/32`, `0 ≤ c ≤ 1/256` and `0 ≤ x`, then `t / (1 - t) ≤ c / (1 - c) + 4 x`.

The point is that `(1 - c)(1 - t) ≥ (255/256)(31/32) ≥ 1/4`, hence `t ≤ c + 4 x (1-c)(1-t)`,
which after clearing denominators is exactly the claim. -/
lemma goodDev_arith {t c x : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 32) (hx : 0 ≤ x) (h : t ≤ c + x) :
    t / (1 - t) ≤ c / (1 - c) + 4 * x := by
  have h1t : 0 < 1 - t := by linarith
  have h1c : 0 < 1 - c := by linarith
  have hprod : 1 ≤ 4 * (1 - c) * (1 - t) := by nlinarith [hc, ht, hc0, ht0]
  have hkey : t ≤ c + 4 * x * (1 - c) * (1 - t) := by nlinarith [hx, hprod, h]
  rw [div_le_iff₀ h1t]
  have hR : c / (1 - c) + 4 * x = (c + 4 * x * (1 - c)) / (1 - c) := by
    field_simp
  rw [hR, div_mul_eq_mul_div, le_div_iff₀ h1c]
  nlinarith [hkey]

/-- Comparison of `1 / u` with `1` when `u` is `1 + O(t)`: with `t = ‖1 - u‖ ≤ 1/32`,
`‖1 / u - 1‖ ≤ t / (1 - t)`. -/
lemma goodDev_norm_inv {u : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : ‖1 - u‖ ≤ t)
    (ht32 : t ≤ 1 / 32) :
    ‖1 / u - 1‖ ≤ t / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have htu : 1 - t ≤ ‖u‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖1 - u‖ + ‖u‖ := by
      calc ‖(1 : ℂ)‖ = ‖(1 - u) + u‖ := by congr 1; ring
        _ ≤ ‖1 - u‖ + ‖u‖ := norm_add_le _ _
    rw [norm_one] at h1
    linarith
  have hne : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at htu
    linarith
  rw [div_sub_one hne, norm_div]
  exact div_le_div₀ ht0 ht h1t htu

theorem good_deriv_bound {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c Rde C₂ K : ℝ}
    (hRdepos : 0 < Rde) (hC₂pos : 0 < C₂) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 256) (hK : 0 < K)
    (hDEest : ∀ (Φ' v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z₀ R) → Set.InjOn Φ' (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hsh : ∀ w ∈ Work.Pert.Qm Ξ α, ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c) :
    ∀ w : ℂ, w ∈ Work.Pert.Qm Ξ α → Real.sqrt 2 * Rde ≤ Work.Pert.PinAux.minmarg Ξ α w →
      ‖deriv Φ w - 1‖ ≤ C₂ * Real.sqrt 2 / Work.Pert.PinAux.minmarg Ξ α w
        + c / (1 - c) + 4 * K / ‖w‖ := by
  intro w hw hmin
  have hmmpos : 0 < minmarg Ξ α w := mem_Qm_iff_minmarg_pos.mp hw
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set R : ℝ := minmarg Ξ α w / Real.sqrt 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hball : Metric.ball w R ⊆ Work.Pert.Qm Ξ α :=
    ball_subset_Qm_of_minmarg (le_of_lt hmmpos)
  have hRge : Rde ≤ R := by
    rw [hRdef, le_div_iff₀ hs2]
    calc Rde * Real.sqrt 2 = Real.sqrt 2 * Rde := by ring
      _ ≤ minmarg Ξ α w := hmin
  -- The vector field `v = F - id` of the near-translation.
  set v : ℂ → ℂ := fun z => F z - z with hv
  have hvdiff : DifferentiableOn ℂ v (Metric.ball w R) := by
    have h1 : DifferentiableOn ℂ (fun z : ℂ => F z - z) (Metric.ball w R) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa [hv] using h1
  have hvnear : ∀ z ∈ Metric.ball w R, ‖v z - 1‖ < 1 / 4 := by
    intro z hz
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hball hz
    have hb : ‖v z - 1‖ ≤ 1 / 32 := by
      have heq : v z - 1 = F z - (z + 1) := by simp only [hv]; ring
      rw [heq]; exact (hNT.1.2 z hzQ).1
    linarith
  have habel : ∀ z ∈ Metric.ball w R, z + v z ∈ Metric.ball w R → Φ (z + v z) = Φ z + 1 := by
    intro z hz hzv
    have hzQ : z ∈ Work.Pert.Qm Ξ α := hball hz
    have heq : z + v z = F z := by simp only [hv]; ring
    have hFQ : F z ∈ Work.Pert.Qm Ξ α := by rw [← heq]; exact hball hzv
    have h := hΦ.2.2 z hzQ hFQ
    rwa [heq]
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball w R) := hΦ.1.mono hball
  have hΦinj : Set.InjOn Φ (Metric.ball w R) := hΦ.2.1.mono hball
  -- Lemma A.2.4(i) at `w`.
  have hDE := hDEest Φ v w R hRge hΦdiff hΦinj hvdiff hvnear habel
  have hDE' : ‖deriv Φ w - 1 / v w‖ ≤ C₂ * Real.sqrt 2 / minmarg Ξ α w := by
    refine le_trans hDE ?_
    rw [hRdef, div_div_eq_mul_div]
  -- The deviation of `F` from the translation `w ↦ w + 1` enters only at the point `w`.
  have hdev : ‖F w - (w + 1)‖ ≤ K / ‖w‖ + c := hsh w hw
  have hdev32 : ‖F w - (w + 1)‖ ≤ 1 / 32 := (hNT.1.2 w hw).1
  have hx : 0 ≤ K / ‖w‖ := div_nonneg (le_of_lt hK) (norm_nonneg w)
  have hvinv : ‖1 / v w - 1‖ ≤ c / (1 - c) + 4 * K / ‖w‖ := by
    have htne : 1 - v w = -(F w - (w + 1)) := by simp only [hv]; ring
    have ht : ‖1 - v w‖ = ‖F w - (w + 1)‖ := by rw [htne, norm_neg]
    have h132 : ‖1 - v w‖ ≤ 1 / 32 := by rw [ht]; exact hdev32
    have h1 : ‖1 / v w - 1‖ ≤ ‖1 - v w‖ / (1 - ‖1 - v w‖) :=
      goodDev_norm_inv (norm_nonneg _) le_rfl h132
    have h2 : ‖1 - v w‖ / (1 - ‖1 - v w‖) ≤ c / (1 - c) + 4 * K / ‖w‖ := by
      have h3 := goodDev_arith hc0 hc (norm_nonneg _) h132 hx
        (by rw [ht]; linarith [hdev])
      have h4 : 4 * (K / ‖w‖) = 4 * K / ‖w‖ := by ring
      linarith [h3, h4]
    linarith
  have htri : ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w - 1 / v w‖ + ‖1 / v w - 1‖ := by
    have he : deriv Φ w - 1 = (deriv Φ w - 1 / v w) + (1 / v w - 1) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [hDE', htri, hvinv]

end

end Work.Pert.PinAux
