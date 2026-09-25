import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.NN.Core.CzBfar.volume_ball_le
import Submission.Work.NN.Core.CzBfar.integrable_bmDzKernel_mul_translate

namespace Work.NN.Core.CzBfar

open MeasureTheory Set

/-- Far-field Hölder bound for the singular integral: if `F` is `α`-Hölder with constant `K` and
vanishes off the sup-norm ball of radius `r`, and the translated support windows of `z` and `z'`
stay outside the Euclidean ball of radius `3r`, then the difference of the two singular integrals
is bounded by `C K ‖z - z'‖^α`.

Both integrands are supported in the sup-norm balls of radius `r` around `-z` and `-z'`, where the
kernel is bounded by `n/(3r)^{2n}`; on the union of the two balls the Hölder bound gives the
difference estimate, and the total volume is `≤ 2 C r^{2n}` (`volume_ball_le`). -/
theorem far_diff_bound {n : ℕ} (hn : 0 < n) (i l : Fin n) {r : ℝ} (hr : 0 < r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin n → ℂ) → ℂ) (K : ℝ) (z z' : Fin n → ℂ),
      0 ≤ K → (∀ x y, ‖F x - F y‖ ≤ K * ‖x - y‖ ^ α) →
      (∀ x, r ≤ ‖x‖ → F x = 0) →
      (∀ x, ‖z + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x) →
      (∀ x, ‖z' + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x) →
      ‖(∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x))
        - ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z' + x)‖
        ≤ C * K * ‖z - z'‖ ^ α := by
  classical
  obtain ⟨Cvol, hCvolpos, hCvol⟩ := volume_ball_le hn
  refine ⟨2 * Cvol * ((n : ℝ) / 3 ^ (2 * n)), by positivity, ?_⟩
  intro F K z z' hK hholder hsupp hgeo hgeo'
  have hFc : Continuous F := Work.CR.Flat.Cauchy.BmDzCzAux.continuous_of_holder hα0 hK hholder
  have hint : MeasureTheory.Integrable
      (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)) :=
    integrable_bmDzKernel_mul_translate hn i l hr hFc hsupp hgeo
  have hint' : MeasureTheory.Integrable
      (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z' + x)) :=
    integrable_bmDzKernel_mul_translate hn i l hr hFc hsupp hgeo'
  have heq : (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x))
      - (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z' + x))
      = ∫ x : Fin n → ℂ,
          Work.CR.Flat.Cauchy.bmDzKernel i l x * (F (z + x) - F (z' + x)) := by
    rw [← MeasureTheory.integral_sub hint hint']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  rw [heq]
  set g : (Fin n → ℂ) → ℂ :=
    fun x => Work.CR.Flat.Cauchy.bmDzKernel i l x * (F (z + x) - F (z' + x)) with hgdef
  set T : Set (Fin n → ℂ) := {x | ‖z + x‖ < r} ∪ {x | ‖z' + x‖ < r} with hTdef
  have hTsub : T ⊆ Metric.ball (-z) r ∪ Metric.ball (-z') r := by
    intro x hx
    rw [hTdef] at hx
    rcases hx with hx | hx
    · left
      simpa only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm, sub_neg_eq_add,
        add_comm x z] using hx
    · right
      simpa only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm, sub_neg_eq_add,
        add_comm x z'] using hx
  have hTfin : volume T < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono hTsub) ?_
    refine lt_of_le_of_lt (MeasureTheory.measure_union_le _ _) ?_
    exact ENNReal.add_lt_top.mpr
      ⟨MeasureTheory.measure_ball_lt_top, MeasureTheory.measure_ball_lt_top⟩
  have hg0 : ∀ x, x ∉ T → g x = 0 := by
    intro x hx
    have h1 : r ≤ ‖z + x‖ := by
      refine le_of_not_gt (fun h => hx ?_)
      rw [hTdef]; exact Or.inl h
    have h2 : r ≤ ‖z' + x‖ := by
      refine le_of_not_gt (fun h => hx ?_)
      rw [hTdef]; exact Or.inr h
    simp [hgdef, hsupp (z + x) h1, hsupp (z' + x) h2]
  have hpt : ∀ x ∈ T, ‖g x‖
      ≤ (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α) := by
    intro x hx
    have h3r : 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x := by
      rw [hTdef] at hx
      rcases hx with hx | hx
      · exact hgeo x hx
      · exact hgeo' x hx
    have hxne : x ≠ 0 := by
      intro h0
      rw [h0] at h3r
      simp only [Work.CR.Flat.Cauchy.eucNorm_zero] at h3r
      linarith
    have hker := Work.CR.Flat.Cauchy.BmDzCzAux.norm_bmDzKernel_le i l hxne
    have hden : (3 * r) ^ (2 * n) ≤ Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n) :=
      pow_le_pow_left₀ (by linarith) h3r _
    have hdenpos : 0 < (3 * r) ^ (2 * n) := pow_pos (by linarith) _
    have h1 : (n : ℝ) / Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n)
        ≤ (n : ℝ) / (3 * r) ^ (2 * n) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg n) hdenpos hden
    have h2 : (n : ℝ) / (3 * r) ^ (2 * n) = (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) := by
      rw [mul_pow]
      field_simp
    have hd : ‖F (z + x) - F (z' + x)‖ ≤ K * ‖z - z'‖ ^ α := by
      have h := hholder (z + x) (z' + x)
      rwa [show (z + x) - (z' + x) = z - z' from by abel] at h
    have hKP : 0 ≤ K * ‖z - z'‖ ^ α :=
      mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) α)
    calc ‖g x‖ = ‖Work.CR.Flat.Cauchy.bmDzKernel i l x‖ * ‖F (z + x) - F (z' + x)‖ := by
          simp only [hgdef, norm_mul]
      _ ≤ ((n : ℝ) / Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n)) * (K * ‖z - z'‖ ^ α) :=
          mul_le_mul hker hd (norm_nonneg _)
            (div_nonneg (Nat.cast_nonneg n) (pow_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x) _))
      _ ≤ ((n : ℝ) / (3 * r) ^ (2 * n)) * (K * ‖z - z'‖ ^ α) :=
          mul_le_mul_of_nonneg_right h1 hKP
      _ = (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α) := by rw [h2]
  have hvolT : (volume T).toReal ≤ 2 * (Cvol * r ^ (2 * n)) := by
    have h1 : volume T
        ≤ volume (Metric.ball (-z) r) + volume (Metric.ball (-z') r) :=
      le_trans (MeasureTheory.measure_mono hTsub) (MeasureTheory.measure_union_le _ _)
    have h2 : volume (Metric.ball (-z) r) + volume (Metric.ball (-z') r) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ne_of_lt MeasureTheory.measure_ball_lt_top, ne_of_lt MeasureTheory.measure_ball_lt_top⟩
    calc (volume T).toReal
        ≤ (volume (Metric.ball (-z) r) + volume (Metric.ball (-z') r)).toReal :=
          ENNReal.toReal_mono h2 h1
      _ ≤ (volume (Metric.ball (-z) r)).toReal + (volume (Metric.ball (-z') r)).toReal :=
          ENNReal.toReal_add_le
      _ ≤ Cvol * r ^ (2 * n) + Cvol * r ^ (2 * n) :=
          add_le_add (hCvol (-z) r hr) (hCvol (-z') r hr)
      _ = 2 * (Cvol * r ^ (2 * n)) := by ring
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
  have hmain : ‖∫ x in T, g x‖
      ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α)) * (volume T).toReal :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hTfin hpt
  have hnum : ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α))
        * (2 * (Cvol * r ^ (2 * n)))
      = 2 * Cvol * ((n : ℝ) / 3 ^ (2 * n)) * K * ‖z - z'‖ ^ α := by
    field_simp
  calc ‖∫ x in T, g x‖
      ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α)) * (volume T).toReal :=
        hmain
    _ ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * (K * ‖z - z'‖ ^ α))
          * (2 * (Cvol * r ^ (2 * n))) :=
        mul_le_mul_of_nonneg_left hvolT (by positivity)
    _ = 2 * Cvol * ((n : ℝ) / 3 ^ (2 * n)) * K * ‖z - z'‖ ^ α := hnum

end Work.NN.Core.CzBfar
