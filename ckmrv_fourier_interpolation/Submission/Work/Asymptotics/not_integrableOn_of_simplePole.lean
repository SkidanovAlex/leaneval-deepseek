import Mathlib
import Submission.Work.Asymptotics.Basic

open MeasureTheory Filter Topology Asymptotics Set

namespace Work.Asymptotics

/-- A function with a non-removable *simple pole* at a point `t₀ > 0` is not integrable on
`(0,∞)`: this is the mechanism by which the naive integral defining the CKMRV transform
degenerates when a pole of `z ↦ K(τ,z)` lies on the contour `{it : t > 0}`. -/
theorem not_integrableOn_of_simplePole {f g : ℝ → ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀) {c : ℂ}
    (hc : c ≠ 0) (hg : ∃ M : ℝ, Filter.Eventually (fun t => ‖g t‖ ≤ M) (nhds t₀))
    (hf : Filter.Eventually (fun t => f t = c / ((t : ℂ) - t₀) + g t) (nhds t₀)) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  intro hfint
  obtain ⟨M, hMe⟩ := hg
  have hcomb : ∀ᶠ t in 𝓝 t₀, ‖g t‖ ≤ M ∧ f t = c / ((t : ℂ) - t₀) + g t := hMe.and hf
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcomb
  have hnormc : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set N : ℝ := |M| + 1 with hNdef
  have hNpos : 0 < N := by positivity
  have hMN : M ≤ N := by have := le_abs_self M; linarith
  have hsub_norm : ∀ x : ℝ, ‖(x : ℂ) - (t₀ : ℂ)‖ = |x - t₀| := by
    intro x
    rw [← Complex.ofReal_sub, ← Real.sqrt_sq (norm_nonneg (((x - t₀ : ℝ) : ℂ))),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
  have hbigO : (fun x : ℝ => (x - t₀)⁻¹) =O[𝓝[≠] t₀] f := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 / ‖c‖, ?_⟩
    set η := min ε (‖c‖ / (2 * N)) with hηdef
    have hηpos : 0 < η := lt_min hεpos (div_pos hnormc (by positivity))
    have hηleε : η ≤ ε := min_le_left _ _
    have hηle : η ≤ ‖c‖ / (2 * N) := min_le_right _ _
    have hball : ∀ᶠ x in 𝓝[≠] t₀, x ∈ Metric.ball t₀ η :=
      (show ∀ᶠ x in 𝓝 t₀, x ∈ Metric.ball t₀ η from Metric.ball_mem_nhds t₀ hηpos).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hball, self_mem_nhdsWithin] with x hxball hxne
    have hxne' : x ≠ t₀ := hxne
    have hxd : dist x t₀ < η := hxball
    have hxε : x ∈ Metric.ball t₀ ε := Metric.ball_subset_ball hηleε hxball
    obtain ⟨hgx, hfx⟩ := hε hxε
    have habs : 0 < |x - t₀| := abs_pos.mpr (sub_ne_zero.mpr hxne')
    have hlow : ‖c‖ / |x - t₀| - M ≤ ‖f x‖ := by
      have hn : ‖c / ((x : ℂ) - (t₀ : ℂ))‖ = ‖c‖ / |x - t₀| := by
        rw [norm_div, hsub_norm x]
      calc ‖c‖ / |x - t₀| - M
          = ‖c / ((x : ℂ) - (t₀ : ℂ))‖ - M := by rw [hn]
        _ ≤ ‖c / ((x : ℂ) - (t₀ : ℂ))‖ - ‖g x‖ := by linarith
        _ ≤ ‖c / ((x : ℂ) - (t₀ : ℂ)) + g x‖ := by
              simpa using norm_sub_norm_le (c / ((x : ℂ) - (t₀ : ℂ))) (-(g x))
        _ = ‖f x‖ := by rw [← hfx]
    have hmiddle : ‖c‖ / (2 * |x - t₀|) ≤ ‖c‖ / |x - t₀| - M := by
      have hdist : |x - t₀| < η := by rw [← Real.dist_eq]; exact hxd
      have hρ : |x - t₀| < ‖c‖ / (2 * N) := lt_of_lt_of_le hdist hηle
      have hpos2 : (0:ℝ) < 2 * |x - t₀| := by positivity
      have hpos3 : (0:ℝ) < 2 * N := by positivity
      have h3 : 2 * N * |x - t₀| < ‖c‖ := by
        have := (lt_div_iff₀ hpos3).mp hρ
        nlinarith [this]
      have h4 : N < ‖c‖ / (2 * |x - t₀|) := by
        rw [lt_div_iff₀ hpos2]
        nlinarith [h3]
      have h2 : M ≤ ‖c‖ / (2 * |x - t₀|) := by linarith
      have hid : ‖c‖ / |x - t₀| = 2 * (‖c‖ / (2 * |x - t₀|)) := by
        field_simp
      linarith [hid, h2]
    have hkey : ‖c‖ / (2 * |x - t₀|) ≤ ‖f x‖ := le_trans hmiddle hlow
    have hgoal : |x - t₀|⁻¹ ≤ (2 / ‖c‖) * ‖f x‖ := by
      have heq : (2 / ‖c‖) * (‖c‖ / (2 * |x - t₀|)) = |x - t₀|⁻¹ := by
        field_simp
      calc |x - t₀|⁻¹ = (2 / ‖c‖) * (‖c‖ / (2 * |x - t₀|)) := heq.symm
        _ ≤ (2 / ‖c‖) * ‖f x‖ := by
            apply mul_le_mul_of_nonneg_left hkey
            positivity
    rw [Real.norm_eq_abs, abs_inv]
    exact hgoal
  have hne : t₀ - t₀ / 2 ≠ t₀ + t₀ / 2 := by
    apply ne_of_lt; linarith
  have hmem : t₀ ∈ uIcc (t₀ - t₀ / 2) (t₀ + t₀ / 2) := by
    rw [Set.mem_uIcc]; left; constructor <;> linarith
  have hnotint := not_intervalIntegrable_of_sub_inv_isBigO_punctured hbigO hne hmem
  apply hnotint
  rw [intervalIntegrable_iff]
  refine hfint.mono_set (fun x hx => ?_)
  rw [uIoc_of_le (by linarith : t₀ - t₀ / 2 ≤ t₀ + t₀ / 2)] at hx
  simp only [Set.mem_Ioi]
  nlinarith [hx.1, ht₀]

end Work.Asymptotics
