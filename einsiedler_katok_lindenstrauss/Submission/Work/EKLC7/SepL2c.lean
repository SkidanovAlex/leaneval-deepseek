import Mathlib
import Submission.Work.EKLC7.Defs

namespace Work.EKLC7

open MeasureTheory

/-- The essential content of `SepL2c` at a point `z` of the support where `Ψ` is strictly
positive: a compactly supported continuous bump `b` with `0 ≤ b ≤ 1`, `b z = 1` and
`Ψ ≥ 0` on the support of `b` produces the nonnegative function `b * Ψ`, whose integral
vanishes by hypothesis; hence `b * Ψ = 0` almost everywhere, so (`b * Ψ` being continuous)
the open set `{b * Ψ ≠ 0}` is null and therefore disjoint from the support of `β`,
contradicting `b z * Ψ z > 0`. -/
private lemma pos_case
    {β : MeasureTheory.Measure (ℝ × ℝ)} [MeasureTheory.IsFiniteMeasureOnCompacts β]
    {Ψ : ℝ × ℝ → ℝ} (hΨ : Continuous Ψ)
    (hβ : ∀ F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ, ∫ z, F z * Ψ z ∂β = 0)
    {z : ℝ × ℝ} (hz : z ∈ β.support) (hpos : 0 < Ψ z) : False := by
  -- `Ψ` is positive on a ball around `z`
  have hmem : {w : ℝ × ℝ | 0 < Ψ w} ∈ nhds z := by
    have h : Ψ ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds z :=
      hΨ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    exact h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
  -- a smooth bump at `z` supported in that ball
  let b : ContDiffBump z := ⟨δ / 4, δ / 2, by linarith, by linarith⟩
  have hb_out : b.rOut = δ / 2 := rfl
  have hb_one : b z = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_self]
    exact b.rIn_pos.le
  have hb_supp : ∀ w, b w ≠ 0 → 0 < Ψ w := by
    intro w hw
    have h1 : w ∈ Metric.ball z b.rOut := by
      rw [← b.support_eq]
      exact Function.mem_support.mpr hw
    have h2 : dist w z < b.rOut := Metric.mem_ball.mp h1
    have h3 : dist w z < δ := by rw [hb_out] at h2; linarith
    exact hδ (Metric.mem_ball.mpr h3)
  -- package the bump as a compactly supported continuous map
  let h : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ :=
    ⟨⟨b, b.continuous⟩, b.hasCompactSupport⟩
  have hh_one : h z = 1 := hb_one
  have hnonneg : ∀ w, 0 ≤ h w * Ψ w := by
    intro w
    by_cases hw : h w = 0
    · rw [hw, zero_mul]
    · exact mul_nonneg b.nonneg (le_of_lt (hb_supp w hw))
  have hcont : Continuous (fun w => h w * Ψ w) := (map_continuous h).mul hΨ
  have hcs : HasCompactSupport (fun w => h w * Ψ w) :=
    (CompactlySupportedContinuousMap.hasCompactSupport h).mul_right (f' := Ψ)
  have hint : Integrable (fun w => h w * Ψ w) β :=
    hcont.integrable_of_hasCompactSupport hcs
  have hzero : ∫ w, h w * Ψ w ∂β = 0 := hβ h
  have hae : (fun w => h w * Ψ w) =ᵐ[β] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hzero
  have hnull : β {w : ℝ × ℝ | h w * Ψ w ≠ 0} = 0 :=
    (ae_iff (μ := β) (p := fun w => (fun w => h w * Ψ w) w = 0)).mp hae
  have hopen : IsOpen {w : ℝ × ℝ | h w * Ψ w ≠ 0} :=
    hcont.isOpen_preimage _ isOpen_compl_singleton
  have hzmem : z ∈ {w : ℝ × ℝ | h w * Ψ w ≠ 0} := by
    change h z * Ψ z ≠ 0
    rw [hh_one, one_mul]
    exact ne_of_gt hpos
  exact (Measure.subset_compl_support_of_isOpen hopen hnull) hzmem hz

theorem SepL2c :
    ∀ (β : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasureOnCompacts β]
      (Ψ : ℝ × ℝ → ℝ), Continuous Ψ →
      (∀ F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ,
        ∫ z, F z * Ψ z ∂β = 0) →
      ∀ z ∈ β.support, Ψ z = 0 := by
  intro β hβfin Ψ hΨ hβ z hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine pos_case hΨ.neg (fun F => ?_) hz (neg_pos.mpr hlt)
    have h := hβ F
    simp only [Pi.neg_apply, mul_neg]
    rw [integral_neg, h, neg_zero]
  · exact pos_case hΨ hβ hz hgt

end Work.EKLC7
