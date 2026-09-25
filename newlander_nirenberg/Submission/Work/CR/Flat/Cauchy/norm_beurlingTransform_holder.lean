import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_le
import Submission.Work.CR.Flat.Cauchy.CZaux

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

set_option maxHeartbeats 1000000

namespace HolderAux

/-- Sub-additivity of `x ↦ x ^ α` for `0 < α ≤ 1`. -/
private theorem rpow_add_le_add_rpow {x y α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : (x + y) ^ α ≤ x ^ α + y ^ α := by
  have hsubY : ∀ {z : ℝ}, 0 < z → z ^ (α - 1) = z ^ α * z⁻¹ := by
    intro z hz
    rw [Real.rpow_sub hz α 1, div_eq_mul_inv, Real.rpow_one]
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst hx0
    rw [zero_add, Real.zero_rpow (ne_of_gt hα0), zero_add]
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · subst hy0
    rw [add_zero, Real.zero_rpow (ne_of_gt hα0), add_zero]
  rcases le_or_gt x y with hxy | hxy
  · have h1 : (1 + x / y) ^ α ≤ 1 + x / y := by
      have hle : (1 : ℝ) ≤ 1 + x / y := by linarith [div_nonneg hx hy]
      have h := Real.rpow_le_rpow_of_exponent_le hle hα1
      rwa [Real.rpow_one] at h
    have heq : y * (1 + x / y) = x + y := by
      rw [mul_add, mul_one, mul_comm y (x / y), div_mul_cancel₀ x (ne_of_gt hypos)]; ring
    calc (x + y) ^ α = (y * (1 + x / y)) ^ α := by rw [heq]
      _ = y ^ α * (1 + x / y) ^ α := Real.mul_rpow (le_of_lt hypos) (by linarith [div_nonneg hx hy])
      _ ≤ y ^ α * (1 + x / y) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hy α)
      _ ≤ y ^ α + x ^ α := by
          rw [mul_add, mul_one]
          have hy1 : y ^ α * (x / y) = x * y ^ (α - 1) := by
            rw [div_eq_mul_inv, ← mul_assoc, mul_comm (y ^ α) x, mul_assoc, ← hsubY hypos]
          rw [hy1]
          have h5 : y ^ (α - 1) ≤ x ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hxpos hxy (by linarith)
          have h6 : x * y ^ (α - 1) ≤ x ^ α := by
            calc x * y ^ (α - 1) ≤ x * x ^ (α - 1) := mul_le_mul_of_nonneg_left h5 hx
              _ = x ^ α := by
                  nth_rewrite 1 [← Real.rpow_one x]
                  rw [← Real.rpow_add hxpos, show (1 : ℝ) + (α - 1) = α from by ring]
          linarith
      _ = x ^ α + y ^ α := by ring
  · have h1 : (1 + y / x) ^ α ≤ 1 + y / x := by
      have hle : (1 : ℝ) ≤ 1 + y / x := by linarith [div_nonneg hy hx]
      have h := Real.rpow_le_rpow_of_exponent_le hle hα1
      rwa [Real.rpow_one] at h
    have heq : x * (1 + y / x) = x + y := by
      rw [mul_add, mul_one, mul_comm x (y / x), div_mul_cancel₀ y (ne_of_gt hxpos)]
    calc (x + y) ^ α = (x * (1 + y / x)) ^ α := by rw [heq]
      _ = x ^ α * (1 + y / x) ^ α := Real.mul_rpow (le_of_lt hxpos) (by linarith [div_nonneg hy hx])
      _ ≤ x ^ α * (1 + y / x) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx α)
      _ ≤ x ^ α + y ^ α := by
          rw [mul_add, mul_one]
          have hx1 : x ^ α * (y / x) = y * x ^ (α - 1) := by
            rw [div_eq_mul_inv, ← mul_assoc, mul_comm (x ^ α) y, mul_assoc, ← hsubY hxpos]
          rw [hx1]
          have h5 : x ^ (α - 1) ≤ y ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hypos hxy.le (by linarith)
          have h6 : y * x ^ (α - 1) ≤ y ^ α := by
            calc y * x ^ (α - 1) ≤ y * y ^ (α - 1) := mul_le_mul_of_nonneg_left h5 hy
              _ = y ^ α := by
                  nth_rewrite 1 [← Real.rpow_one y]
                  rw [← Real.rpow_add hypos, show (1 : ℝ) + (α - 1) = α from by ring]
          linarith
      _ = x ^ α + y ^ α := by ring

/-- `a ^ α - b ^ α ≤ (a - b) ^ α` for `0 ≤ b ≤ a`, `0 < α ≤ 1`. -/
private theorem rpow_sub_le_sub_rpow {a b α : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : a ^ α - b ^ α ≤ (a - b) ^ α := by
  have h0 : 0 ≤ a - b := by linarith
  have h := rpow_add_le_add_rpow hb h0 hα0 hα1
  rw [show b + (a - b) = a from by ring] at h
  linarith


/-- Crescent ("domain mismatch") estimate for the Beurling kernel. -/
theorem crescent_bound_holder {ρ α C δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ4 : δ ≤ ρ / 4) {z z' : ℂ} (hzz' : ‖z - z'‖ = δ) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    ‖(∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
          (f u - f z') * ((u - z')⁻¹ ^ 2))
        - (∫ u in (fun x : ℂ => x + z') '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
          (f u - f z') * ((u - z')⁻¹ ^ 2))‖
      ≤ C * (2 * Real.pi * (4 ^ α + 2 ^ α) / α) * δ ^ α := by
  have hρ : 0 < ρ := by linarith
  have hcont : Continuous f := continuous_of_holder hα hC hf
  set A : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hA
  set Az : Set ℂ := (fun x : ℂ => x + z) '' A with hAz
  set Az' : Set ℂ := (fun x : ℂ => x + z') '' A with hAz'
  set g : ℂ → ℂ := fun u => (f u - f z') * ((u - z')⁻¹ ^ 2) with hg
  set D : Set ℂ := Az \ Az' ∪ Az' \ Az with hD
  have hAm : MeasurableSet A := by rw [hA]; measurability
  have hAzm : MeasurableSet Az := by
    rw [hAz]
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image' hAm
  have hAz'm : MeasurableSet Az' := by
    rw [hAz']
    exact (Homeomorph.addRight z').measurableEmbedding.measurableSet_image' hAm
  have hDm : MeasurableSet D := by
    rw [hD]; exact (hAzm.diff hAz'm).union (hAz'm.diff hAzm)
  have hgm : Measurable g := by rw [hg]; fun_prop
  have hpt : ∀ u : ℂ, ‖g u‖ ≤ C * ‖u - z'‖ ^ (α - 2) := by
    intro u
    rw [hg, norm_mul]
    by_cases hu : u = z'
    · subst hu
      simp [Real.zero_rpow (by linarith : α - 2 ≠ 0)]
    · have hx : 0 < ‖u - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu)
      have hnorm : ‖((u - z')⁻¹) ^ 2‖ = ‖u - z'‖ ^ (-2 : ℝ) := by
        rw [norm_pow, norm_inv, inv_pow, ← Real.rpow_natCast ‖u - z'‖ 2]
        exact (Real.rpow_neg (norm_nonneg _) 2).symm
      rw [hnorm]
      calc ‖f u - f z'‖ * ‖u - z'‖ ^ (-2 : ℝ)
          ≤ (C * ‖u - z'‖ ^ α) * ‖u - z'‖ ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right (hf u z') (Real.rpow_nonneg (norm_nonneg _) _)
        _ = C * ‖u - z'‖ ^ (α - 2) := by
            rw [show C * ‖u - z'‖ ^ α * ‖u - z'‖ ^ (-2 : ℝ)
                  = C * (‖u - z'‖ ^ α * ‖u - z'‖ ^ (-2 : ℝ)) from by ring,
              ← Real.rpow_add hx, show α + (-2) = α - 2 from by ring]
  have hAzfin : volume Az < ⊤ := by
    apply CZaux.volume_lt_top_of_subset_ball (c := z) (R := ρ)
    rintro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_right] using ha.2
  have hAz'fin : volume Az' < ⊤ := by
    apply CZaux.volume_lt_top_of_subset_ball (c := z') (R := ρ)
    rintro u hu
    rw [hAz', Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_right] using ha.2
  have hbound_Az : ∀ u ∈ Az, ‖g u‖ ≤ C * δ ^ (α - 2) := by
    intro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have hge : δ ≤ ‖(a + z) - z'‖ := by
      have h1 := abs_norm_sub_norm_le a (z' - z)
      rw [show a - (z' - z) = (a + z) - z' from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h1
      have h2 : ‖a‖ - δ ≤ ‖(a + z) - z'‖ := le_trans (le_abs_self _) h1
      linarith [ha.1]
    calc ‖g (a + z)‖ ≤ C * ‖(a + z) - z'‖ ^ (α - 2) := hpt (a + z)
      _ ≤ C * δ ^ (α - 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hge (by linarith)) hC
  have hbound_Az' : ∀ u ∈ Az', ‖g u‖ ≤ C * δ ^ (α - 2) := by
    intro u hu
    rw [hAz', Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have hge : δ ≤ ‖(a + z') - z'‖ := by rw [add_sub_cancel_right]; linarith [ha.1]
    calc ‖g (a + z')‖ ≤ C * ‖(a + z') - z'‖ ^ (α - 2) := hpt (a + z')
      _ ≤ C * δ ^ (α - 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hge (by linarith)) hC
  have hIAz : IntegrableOn g Az :=
    CZaux.integrableOn_of_norm_le_const hAzfin hAzm hgm.aestronglyMeasurable hbound_Az
  have hIAz' : IntegrableOn g Az' :=
    CZaux.integrableOn_of_norm_le_const hAz'fin hAz'm hgm.aestronglyMeasurable hbound_Az'
  have hDfin : volume D < ⊤ := by
    apply CZaux.volume_lt_top_of_subset_ball (c := z) (R := ρ + δ)
    intro u hu
    rw [hD, Set.mem_union, Set.mem_diff, Set.mem_diff] at hu
    rw [Metric.mem_ball, dist_eq_norm]
    rcases hu with ⟨hu1, _⟩ | ⟨hu1, _⟩
    · rw [hAz, Set.mem_image] at hu1; obtain ⟨a, ha, hae⟩ := hu1
      rw [hA] at ha
      calc ‖u - z‖ = ‖a‖ := by rw [← hae]; simp
        _ < ρ := ha.2
        _ ≤ ρ + δ := by linarith
    · rw [hAz', Set.mem_image] at hu1; obtain ⟨a, ha, hae⟩ := hu1
      rw [hA] at ha
      calc ‖u - z‖ = ‖a + (z' - z)‖ := by rw [← hae]; congr 1; ring
        _ ≤ ‖a‖ + ‖z' - z‖ := norm_add_le _ _
        _ < ρ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]; linarith [ha.2]
  have hbound_D : ∀ u ∈ D, ‖g u‖ ≤ C * δ ^ (α - 2) := by
    intro u hu
    rw [hD, Set.mem_union, Set.mem_diff, Set.mem_diff] at hu
    rcases hu with ⟨hu1, _⟩ | ⟨hu1, _⟩
    · exact hbound_Az u hu1
    · exact hbound_Az' u hu1
  have hIgD : IntegrableOn g D :=
    CZaux.integrableOn_of_norm_le_const hDfin hDm hgm.aestronglyMeasurable hbound_D
  have hID : IntegrableOn (fun u : ℂ => ‖g u‖) D := hIgD.norm
  have hstep1 : ‖(∫ u in Az, g u) - (∫ u in Az', g u)‖ ≤ ∫ u in D, ‖g u‖ := by
    have key : (∫ u in Az, g u) - (∫ u in Az', g u)
        = ∫ u, (Az.indicator g u - Az'.indicator g u) := by
      have h1 : (∫ u in Az, g u) = ∫ u, Az.indicator g u := (integral_indicator hAzm (f := g)).symm
      have h2 : (∫ u in Az', g u) = ∫ u, Az'.indicator g u := (integral_indicator hAz'm (f := g)).symm
      rw [h1, h2]
      exact (integral_sub (hIAz.integrable_indicator hAzm) (hIAz'.integrable_indicator hAz'm)).symm
    rw [key]
    calc ‖∫ u, (Az.indicator g u - Az'.indicator g u)‖
        ≤ ∫ u, ‖Az.indicator g u - Az'.indicator g u‖ := norm_integral_le_integral_norm _
      _ = ∫ u, D.indicator (fun u => ‖g u‖) u := by
          apply integral_congr_ae
          filter_upwards with u
          by_cases hu : u ∈ Az
          · by_cases hu' : u ∈ Az'
            · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu',
                Set.indicator_of_notMem (by rw [hD]; simp [hu, hu'])]
              simp
            · rw [Set.indicator_of_mem hu, Set.indicator_of_notMem hu',
                Set.indicator_of_mem (by rw [hD]; exact Or.inl ⟨hu, hu'⟩)]
              simp
          · by_cases hu' : u ∈ Az'
            · rw [Set.indicator_of_notMem hu, Set.indicator_of_mem hu',
                Set.indicator_of_mem (by rw [hD]; exact Or.inr ⟨hu', hu⟩)]
              simp
            · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu',
                Set.indicator_of_notMem (by rw [hD]; simp [hu, hu'])]
              simp
      _ = ∫ u in D, ‖g u‖ := integral_indicator hDm
  have hnear : ∫ u in D ∩ Metric.ball z' (4 * δ), ‖g u‖ ≤ C * (2 * Real.pi * (4 * δ) ^ α / α) := by
    have hT : ∫ u in D ∩ Metric.ball z' (4 * δ), ‖g u‖
        = ∫ w in (fun u : ℂ => u - z') '' (D ∩ Metric.ball z' (4 * δ)), ‖g (w + z')‖ := by
      have h := CZaux.setIntegral_translate z' (fun u : ℂ => ‖g u‖)
        ((fun u : ℂ => u - z') '' (D ∩ Metric.ball z' (4 * δ)))
      rw [show (fun x : ℂ => x + z') '' ((fun u : ℂ => u - z') '' (D ∩ Metric.ball z' (4 * δ)))
            = D ∩ Metric.ball z' (4 * δ) from by rw [Set.image_image]; simp] at h
      exact h.symm
    rw [hT]
    set E : Set ℂ := (fun u : ℂ => u - z') '' (D ∩ Metric.ball z' (4 * δ)) with hE
    have hEsub : E ⊆ Metric.ball 0 (4 * δ) := by
      rintro w ⟨u, hu, rfl⟩
      rw [Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm] at hu
      rw [Metric.mem_ball, dist_zero_right]
      simpa only [sub_zero] using hu.2
    have hEm : MeasurableSet E := by
      rw [hE]
      exact (Homeomorph.subRight z').measurableEmbedding.measurableSet_image'
        (hDm.inter measurableSet_ball)
    have hptE : ∀ w : ℂ, ‖g (w + z')‖ ≤ C * ‖w‖ ^ (α - 2) := by
      intro w; simpa [add_sub_cancel_right] using hpt (w + z')
    have hIntBall : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2)) (Metric.ball 0 (4 * δ)) :=
      MeasureTheory.Integrable.const_mul
        (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := 4 * δ) (s := α - 2) (by linarith)) C
    have hIntE : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2)) E :=
      MeasureTheory.IntegrableOn.mono_set hIntBall hEsub
    have hIntgE : IntegrableOn (fun w : ℂ => ‖g (w + z')‖) E :=
      hIntE.mono' ((hgm.comp (measurable_id.add_const z')).norm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun w => by
          simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hptE w))
    calc ∫ w in E, ‖g (w + z')‖ ≤ ∫ w in E, C * ‖w‖ ^ (α - 2) :=
          MeasureTheory.setIntegral_mono_on hIntgE hIntE hEm (fun w _ => hptE w)
      _ ≤ ∫ w in Metric.ball 0 (4 * δ), C * ‖w‖ ^ (α - 2) :=
          MeasureTheory.setIntegral_mono_set hIntBall (Filter.Eventually.of_forall (fun w => by positivity))
            (Filter.Eventually.of_forall (fun w hw => hEsub hw))
      _ = C * (2 * Real.pi * (4 * δ) ^ α / α) := by
          rw [MeasureTheory.integral_const_mul,
            Work.CR.Flat.Cauchy.integral_norm_rpow_ball (by linarith) (by linarith),
            show α - 2 + 2 = α from by ring]
  have hfar : ∫ u in D \ Metric.ball z' (4 * δ), ‖g u‖ ≤ C * (2 * Real.pi * (2 * δ) ^ α / α) := by
    have hT : ∫ u in D \ Metric.ball z' (4 * δ), ‖g u‖
        = ∫ w in (fun u : ℂ => u - z') '' (D \ Metric.ball z' (4 * δ)), ‖g (w + z')‖ := by
      have h := CZaux.setIntegral_translate z' (fun u : ℂ => ‖g u‖)
        ((fun u : ℂ => u - z') '' (D \ Metric.ball z' (4 * δ)))
      rw [show (fun x : ℂ => x + z') '' ((fun u : ℂ => u - z') '' (D \ Metric.ball z' (4 * δ)))
            = D \ Metric.ball z' (4 * δ) from by rw [Set.image_image]; simp] at h
      exact h.symm
    rw [hT]
    set E : Set ℂ := (fun u : ℂ => u - z') '' (D \ Metric.ball z' (4 * δ)) with hE
    have hEsub : E ⊆ {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ + δ} := by
      rintro w ⟨u, hu, rfl⟩
      rw [Set.mem_diff, hD, Set.mem_union, Set.mem_diff, Set.mem_diff] at hu
      obtain ⟨hdisj, hu4⟩ := hu
      have hge4 : 4 * δ ≤ ‖u - z'‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hu4
      show ρ - δ ≤ ‖u - z'‖ ∧ ‖u - z'‖ < ρ + δ
      rcases hdisj with ⟨huAz, huAz'⟩ | ⟨huAz', huAz⟩
      · rw [hAz, Set.mem_image] at huAz
        obtain ⟨a, ha, hae⟩ := huAz
        rw [hA] at ha
        have hsub : u = a + z := hae.symm
        have hnot : ¬ (2 * δ ≤ ‖u - z'‖ ∧ ‖u - z'‖ < ρ) := by
          intro hh
          exact huAz' (by rw [hAz', Set.mem_image]; exact ⟨u - z', by rw [hA]; exact hh, by ring⟩)
        have hgeρ : ρ ≤ ‖u - z'‖ := not_lt.mp (by intro hh; exact hnot ⟨by linarith, hh⟩)
        have hupper : ‖u - z'‖ < ρ + δ := by
          rw [hsub]
          calc ‖(a + z) - z'‖ = ‖a - (z' - z)‖ := by congr 1; ring
            _ ≤ ‖a‖ + ‖z' - z‖ := norm_sub_le _ _
            _ = ‖a‖ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]
            _ < ρ + δ := by linarith [ha.2]
        exact ⟨by linarith, hupper⟩
      · rw [hAz', Set.mem_image] at huAz'
        obtain ⟨a, ha, hae⟩ := huAz'
        rw [hA] at ha
        have hsub : u = a + z' := hae.symm
        have hnot : ¬ (2 * δ ≤ ‖u - z‖ ∧ ‖u - z‖ < ρ) := by
          intro hh
          exact huAz (by rw [hAz, Set.mem_image]; exact ⟨u - z, by rw [hA]; exact hh, by ring⟩)
        have hzz : (u - z) - (z' - z) = u - z' := by ring
        have hzz2 : (u - z') - (z - z') = u - z := by ring
        have h2 : 2 * δ ≤ ‖u - z‖ := by
          have h1 := abs_norm_sub_norm_le (u - z') (z - z')
          rw [hzz2, hzz'] at h1
          have h2' : ‖u - z'‖ - δ ≤ ‖u - z‖ := le_trans (le_abs_self _) h1
          linarith
        have hgeρ : ρ ≤ ‖u - z‖ := not_lt.mp (by intro hh; exact hnot ⟨h2, hh⟩)
        have hlow : ρ - δ ≤ ‖u - z'‖ := by
          have h1 := abs_norm_sub_norm_le (u - z) (z' - z)
          rw [hzz, show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h1
          have h2' : ‖u - z‖ - δ ≤ ‖u - z'‖ := le_trans (le_abs_self _) h1
          linarith
        have hup : ‖u - z'‖ < ρ := by rw [hsub, add_sub_cancel_right]; exact ha.2
        exact ⟨hlow, by linarith⟩
    have hEm : MeasurableSet E := by
      rw [hE]
      exact (Homeomorph.subRight z').measurableEmbedding.measurableSet_image'
        (hDm.diff measurableSet_ball)
    have hptE : ∀ w : ℂ, ‖g (w + z')‖ ≤ C * ‖w‖ ^ (α - 2) := by
      intro w; simpa [add_sub_cancel_right] using hpt (w + z')
    have hAnnsub : {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ + δ} ⊆ Metric.ball 0 (ρ + δ) := by
      intro w hw; rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hw.2 (by linarith)
    have hIntAnn : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2))
        {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ + δ} :=
      MeasureTheory.IntegrableOn.mono_set
        (MeasureTheory.Integrable.const_mul
          (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ + δ) (s := α - 2) (by linarith)) C)
        hAnnsub
    have hIntE : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2)) E :=
      MeasureTheory.IntegrableOn.mono_set hIntAnn hEsub
    have hIntgE : IntegrableOn (fun w : ℂ => ‖g (w + z')‖) E :=
      hIntE.mono' ((hgm.comp (measurable_id.add_const z')).norm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun w => by
          simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hptE w))
    calc ∫ w in E, ‖g (w + z')‖ ≤ ∫ w in E, C * ‖w‖ ^ (α - 2) :=
          MeasureTheory.setIntegral_mono_on hIntgE hIntE hEm (fun w _ => hptE w)
      _ ≤ ∫ w in {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ + δ}, C * ‖w‖ ^ (α - 2) :=
          MeasureTheory.setIntegral_mono_set hIntAnn (Filter.Eventually.of_forall (fun w => by positivity))
            (Filter.Eventually.of_forall (fun w hw => hEsub hw))
      _ = C * (2 * Real.pi * ((ρ + δ) ^ α - (ρ - δ) ^ α) / α) := by
          rw [MeasureTheory.integral_const_mul,
            CZaux.integral_norm_rpow_annulus (by linarith) (by linarith) (by linarith : α - 2 ≠ -2),
            show α - 2 + 2 = α from by ring]
      _ ≤ C * (2 * Real.pi * (2 * δ) ^ α / α) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply div_le_div_of_nonneg_right _ hα.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h := rpow_sub_le_sub_rpow (b := ρ - δ) (a := ρ + δ) (α := α)
            (by linarith) (by linarith) hα hα1.le
          rw [show (ρ + δ) - (ρ - δ) = 2 * δ from by ring] at h
          exact h
  have hsplit : ∫ u in D, ‖g u‖
      = (∫ u in D ∩ Metric.ball z' (4 * δ), ‖g u‖) + (∫ u in D \ Metric.ball z' (4 * δ), ‖g u‖) := by
    have hDeq : D = (D ∩ Metric.ball z' (4 * δ)) ∪ (D \ Metric.ball z' (4 * δ)) := by
      ext u; constructor
      · intro hu
        by_cases h : u ∈ Metric.ball z' (4 * δ)
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    conv_lhs => rw [hDeq]
    exact MeasureTheory.setIntegral_union (s := D ∩ Metric.ball z' (4 * δ))
      (t := D \ Metric.ball z' (4 * δ))
      (by rw [Set.disjoint_left]; intro u hu hu'; exact hu'.2 hu.2)
      (hDm.diff measurableSet_ball)
      (hID.mono_set Set.inter_subset_left) (hID.mono_set Set.diff_subset)
  calc ‖(∫ u in Az, g u) - (∫ u in Az', g u)‖
      ≤ ∫ u in D, ‖g u‖ := hstep1
    _ = (∫ u in D ∩ Metric.ball z' (4 * δ), ‖g u‖) + (∫ u in D \ Metric.ball z' (4 * δ), ‖g u‖) := hsplit
    _ ≤ C * (2 * Real.pi * (4 * δ) ^ α / α) + C * (2 * Real.pi * (2 * δ) ^ α / α) :=
        add_le_add hnear hfar
    _ = C * (2 * Real.pi * (4 ^ α + 2 ^ α) / α) * δ ^ α := by
        rw [show (4 * δ) ^ α = 4 ^ α * δ ^ α from by rw [Real.mul_rpow (by norm_num) (le_of_lt hδ)],
          show (2 * δ) ^ α = 2 ^ α * δ ^ α from by rw [Real.mul_rpow (by norm_num) (le_of_lt hδ)]]
        ring_nf

/-- The Beurling-transform difference as one absolutely convergent integral. -/
theorem beurling_sub_eq {ρ α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) (z z' : ℂ) :
    beurlingTransform ρ f z - beurlingTransform ρ f z'
      = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ,
          ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2 := by
  have hIntz : IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w ^ 2) (Metric.ball 0 ρ) :=
    CZaux.integrableOn_beurlingIntegrand hα hK hf z
  have hIntz' : IntegrableOn (fun w : ℂ => (f (z' + w) - f z') / w ^ 2) (Metric.ball 0 ρ) :=
    CZaux.integrableOn_beurlingIntegrand hα hK hf z'
  have hdiff : (∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w ^ 2)
        - (∫ w in Metric.ball 0 ρ, (f (z' + w) - f z') / w ^ 2)
      = ∫ w in Metric.ball 0 ρ, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2 := by
    rw [← integral_sub hIntz hIntz']
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    ring
  have hSf : beurlingTransform ρ f z - beurlingTransform ρ f z'
      = -((Real.pi : ℂ))⁻¹ * ((∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w ^ 2)
          - (∫ w in Metric.ball 0 ρ, (f (z' + w) - f z') / w ^ 2)) := by
    simp only [beurlingTransform]; ring
  rw [hSf, hdiff]

/-- Decomposition of the outer (far-field) integral into a genuine kernel-difference
integral plus a difference of two integrals over the two translated annuli (the
"crescent").  This is the algebraic heart of the Calderón--Zygmund estimate. -/
theorem outer_decomp {ρ α K δ : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hδ : 0 < δ) (h2δρ : 2 * δ ≤ ρ)
    {z z' : ℂ} (hzz' : ‖z - z'‖ = δ) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) :
    (∫ w in {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
        ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
      = (∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
            (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
        + ((∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2))
          - (∫ u in (fun x : ℂ => x + z') '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2))) := by
  set A : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hA
  set Az : Set ℂ := (fun x : ℂ => x + z) '' A with hAz
  set Az' : Set ℂ := (fun x : ℂ => x + z') '' A with hAz'
  have hcont : Continuous f := continuous_of_holder hα hK hf
  have hρ : 0 < ρ := by linarith
  have hAm : MeasurableSet A := by rw [hA]; measurability
  have hAzm : MeasurableSet Az := by
    rw [hAz]; exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image' hAm
  have hAz'm : MeasurableSet Az' := by
    rw [hAz']; exact (Homeomorph.addRight z').measurableEmbedding.measurableSet_image' hAm
  have hAfin : volume A < ⊤ := by
    apply CZaux.volume_lt_top_of_subset_ball (c := 0) (R := ρ)
    intro w hw; rw [hA] at hw; rw [Metric.mem_ball, dist_zero_right]; exact hw.2
  have hAzfin : volume Az < ⊤ := by
    apply CZaux.volume_lt_top_of_subset_ball (c := z) (R := ρ)
    rintro u hu; rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha; rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_right] using ha.2
  -- bounds
  have hM1a : ∀ w ∈ A, ‖(f (z + w) - f (z' + w)) / w ^ 2‖ ≤ K * δ ^ α / (2 * δ) ^ 2 := by
    intro w hw
    rw [hA] at hw
    have hnum : ‖f (z + w) - f (z' + w)‖ ≤ K * δ ^ α := by
      have h := hf (z + w) (z' + w)
      rw [show (z + w) - (z' + w) = -(z' - z) from by ring] at h
      have hδ' : ‖-(z' - z)‖ = δ := by rw [norm_neg, norm_sub_rev, hzz']
      rwa [hδ'] at h
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hnum (by positivity) (by nlinarith [hw.1, hδ])
  have hM1b : ∀ w ∈ A, ‖(f z - f z') / w ^ 2‖ ≤ K * δ ^ α / (2 * δ) ^ 2 := by
    intro w hw
    rw [hA] at hw
    have hnum : ‖f z - f z'‖ ≤ K * δ ^ α := by
      have h := hf z z'; rwa [hzz'] at h
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hnum (by positivity) (by nlinarith [hw.1, hδ])
  have hM3a : ∀ u ∈ Az, ‖(f u - f z') / (u - z) ^ 2‖ ≤ K * (ρ + δ) ^ α / (2 * δ) ^ 2 := by
    intro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have huz : (2 * δ) ≤ ‖(a + z) - z‖ := by rw [add_sub_cancel_right]; exact ha.1
    have hnum : ‖f (a + z) - f z'‖ ≤ K * (ρ + δ) ^ α := by
      refine le_trans (hf (a + z) z') (mul_le_mul_of_nonneg_left ?_ hK)
      apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
      calc ‖(a + z) - z'‖ = ‖a - (z' - z)‖ := by congr 1; ring
        _ ≤ ‖a‖ + ‖z' - z‖ := norm_sub_le _ _
        _ ≤ ρ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]; linarith [ha.2]
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hnum (by positivity) (by nlinarith [huz, hδ])
  have hM3b : ∀ u ∈ Az, ‖(f (u + (z' - z)) - f z') / (u - z) ^ 2‖ ≤ K * (ρ + δ) ^ α / (2 * δ) ^ 2 := by
    intro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have huz : (2 * δ) ≤ ‖(a + z) - z‖ := by rw [add_sub_cancel_right]; exact ha.1
    have hnum : ‖f ((a + z) + (z' - z)) - f z'‖ ≤ K * (ρ + δ) ^ α := by
      refine le_trans (hf ((a + z) + (z' - z)) z') (mul_le_mul_of_nonneg_left ?_ hK)
      apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
      rw [show (a + z) + (z' - z) - z' = a from by ring]
      linarith [ha.2, hδ]
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hnum (by positivity) (by nlinarith [huz, hδ])
  have hM4a : ∀ u ∈ Az, ‖(f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
      ≤ K * (ρ + δ) ^ α * ((2 * δ)⁻¹ ^ 2 + δ⁻¹ ^ 2) := by
    intro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have hnum : ‖f (a + z) - f z'‖ ≤ K * (ρ + δ) ^ α := by
      refine le_trans (hf (a + z) z') (mul_le_mul_of_nonneg_left ?_ hK)
      apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
      calc ‖(a + z) - z'‖ = ‖a - (z' - z)‖ := by congr 1; ring
        _ ≤ ‖a‖ + ‖z' - z‖ := norm_sub_le _ _
        _ ≤ ρ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]; linarith [ha.2]
    have hge : δ ≤ ‖(a + z) - z'‖ := by
      have h1 := abs_norm_sub_norm_le a (z' - z)
      rw [show a - (z' - z) = (a + z) - z' from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h1
      have h2 : ‖a‖ - δ ≤ ‖(a + z) - z'‖ := le_trans (le_abs_self _) h1
      linarith [ha.1]
    have h1 : ‖((a + z) - z)⁻¹ ^ 2‖ ≤ (2 * δ)⁻¹ ^ 2 := by
      rw [norm_pow, norm_inv, add_sub_cancel_right]
      rw [show (‖a‖⁻¹) ^ 2 = (‖a‖ ^ 2)⁻¹ from by rw [inv_pow]]
      rw [show ((2 * δ)⁻¹) ^ 2 = ((2 * δ) ^ 2)⁻¹ from by rw [inv_pow]]
      exact inv_anti₀ (by positivity) (by nlinarith [ha.1, hδ])
    have h2 : ‖((a + z) - z')⁻¹ ^ 2‖ ≤ δ⁻¹ ^ 2 := by
      rw [norm_pow, norm_inv]
      rw [show (‖(a + z) - z'‖⁻¹) ^ 2 = (‖(a + z) - z'‖ ^ 2)⁻¹ from by rw [inv_pow]]
      rw [show (δ⁻¹) ^ 2 = (δ ^ 2)⁻¹ from by rw [inv_pow]]
      exact inv_anti₀ (by positivity) (by nlinarith [hge, hδ])
    rw [norm_mul]
    calc ‖f (a + z) - f z'‖ * ‖((a + z) - z)⁻¹ ^ 2 - ((a + z) - z')⁻¹ ^ 2‖
        ≤ K * (ρ + δ) ^ α * (‖((a + z) - z)⁻¹ ^ 2‖ + ‖((a + z) - z')⁻¹ ^ 2‖) :=
          mul_le_mul hnum (norm_sub_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ K * (ρ + δ) ^ α * ((2 * δ)⁻¹ ^ 2 + δ⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  have hM4b : ∀ u ∈ Az, ‖(f u - f z') * ((u - z')⁻¹ ^ 2)‖ ≤ K * (ρ + δ) ^ α * δ⁻¹ ^ 2 := by
    intro u hu
    rw [hAz, Set.mem_image] at hu; obtain ⟨a, ha, rfl⟩ := hu
    rw [hA] at ha
    have hnum : ‖f (a + z) - f z'‖ ≤ K * (ρ + δ) ^ α := by
      refine le_trans (hf (a + z) z') (mul_le_mul_of_nonneg_left ?_ hK)
      apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
      calc ‖(a + z) - z'‖ = ‖a - (z' - z)‖ := by congr 1; ring
        _ ≤ ‖a‖ + ‖z' - z‖ := norm_sub_le _ _
        _ ≤ ρ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]; linarith [ha.2]
    have hge : δ ≤ ‖(a + z) - z'‖ := by
      have h1 := abs_norm_sub_norm_le a (z' - z)
      rw [show a - (z' - z) = (a + z) - z' from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h1
      have h2 : ‖a‖ - δ ≤ ‖(a + z) - z'‖ := le_trans (le_abs_self _) h1
      linarith [ha.1]
    have h2 : ‖((a + z) - z')⁻¹ ^ 2‖ ≤ δ⁻¹ ^ 2 := by
      rw [norm_pow, norm_inv]
      rw [show (‖(a + z) - z'‖⁻¹) ^ 2 = (‖(a + z) - z'‖ ^ 2)⁻¹ from by rw [inv_pow]]
      rw [show (δ⁻¹) ^ 2 = (δ ^ 2)⁻¹ from by rw [inv_pow]]
      exact inv_anti₀ (by positivity) (by nlinarith [hge, hδ])
    rw [norm_mul]
    exact mul_le_mul hnum h2 (norm_nonneg _) (by positivity)
  -- measurability
  have hmI1a : Measurable (fun w : ℂ => (f (z + w) - f (z' + w)) / w ^ 2) := by fun_prop
  have hmI1b : Measurable (fun w : ℂ => (f z - f z') / w ^ 2) := by fun_prop
  have hmI3a : Measurable (fun u : ℂ => (f u - f z') / (u - z) ^ 2) := by fun_prop
  have hmI3b : Measurable (fun u : ℂ => (f (u + (z' - z)) - f z') / (u - z) ^ 2) := by fun_prop
  have hmI4a : Measurable (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)) := by fun_prop
  have hmI4b : Measurable (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2)) := by fun_prop
  -- integrability
  have hI1a : IntegrableOn (fun w : ℂ => (f (z + w) - f (z' + w)) / w ^ 2) A :=
    CZaux.integrableOn_of_norm_le_const hAfin hAm hmI1a.aestronglyMeasurable hM1a
  have hI1b : IntegrableOn (fun w : ℂ => (f z - f z') / w ^ 2) A :=
    CZaux.integrableOn_of_norm_le_const hAfin hAm hmI1b.aestronglyMeasurable hM1b
  have hI3a : IntegrableOn (fun u : ℂ => (f u - f z') / (u - z) ^ 2) Az :=
    CZaux.integrableOn_of_norm_le_const hAzfin hAzm hmI3a.aestronglyMeasurable hM3a
  have hI3b : IntegrableOn (fun u : ℂ => (f (u + (z' - z)) - f z') / (u - z) ^ 2) Az :=
    CZaux.integrableOn_of_norm_le_const hAzfin hAzm hmI3b.aestronglyMeasurable hM3b
  have hI4a : IntegrableOn (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)) Az :=
    CZaux.integrableOn_of_norm_le_const hAzfin hAzm hmI4a.aestronglyMeasurable hM4a
  have hI4b : IntegrableOn (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2)) Az :=
    CZaux.integrableOn_of_norm_le_const hAzfin hAzm hmI4b.aestronglyMeasurable hM4b
  -- step 1
  have hstep1 : (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
      = ∫ w in A, (f (z + w) - f (z' + w)) / w ^ 2 := by
    rw [show (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
          = ∫ w in A, ((f (z + w) - f (z' + w)) / w ^ 2 - (f z - f z') / w ^ 2) from
        setIntegral_congr_fun hAm (fun w _ => by ring)]
    rw [integral_sub hI1a hI1b]
    have hzero : (∫ w in A, (f z - f z') / w ^ 2) = 0 := by
      rw [show (fun w : ℂ => (f z - f z') / w ^ 2) = (fun w : ℂ => (f z - f z') * (w⁻¹ ^ 2)) from
        by funext w; rw [div_eq_mul_inv, inv_pow]]
      rw [integral_const_mul]
      rw [show (∫ w in A, w⁻¹ ^ 2) = 0 from by rw [hA]; exact CZaux.integral_inv_sq_annulus (2 * δ) ρ]
      ring
    rw [hzero, sub_zero]
  -- step 2
  have hstep2 : (∫ w in A, (f (z + w) - f (z' + w)) / w ^ 2)
      = ∫ u in Az, (f u - f (u + (z' - z))) / (u - z) ^ 2 := by
    have h := CZaux.setIntegral_translate z (fun u : ℂ => (f u - f (u + (z' - z))) / (u - z) ^ 2) A
    rw [← hAz] at h
    rw [show (∫ w in A, (f (z + w) - f (z' + w)) / w ^ 2)
          = ∫ w in A, (fun u : ℂ => (f u - f (u + (z' - z))) / (u - z) ^ 2) (w + z) from
        setIntegral_congr_fun hAm (fun w _ => by
          show (f (z + w) - f (z' + w)) / w ^ 2
              = (f (w + z) - f ((w + z) + (z' - z))) / ((w + z) - z) ^ 2
          rw [add_sub_cancel_right, show w + z + (z' - z) = z' + w from by ring,
            show w + z = z + w from by ring])]
    exact h
  -- step 3
  have hstep3 : (∫ u in Az, (f u - f (u + (z' - z))) / (u - z) ^ 2)
      = (∫ u in Az, (f u - f z') / (u - z) ^ 2)
        - (∫ u in Az, (f (u + (z' - z)) - f z') / (u - z) ^ 2) := by
    rw [show (∫ u in Az, (f u - f (u + (z' - z))) / (u - z) ^ 2)
          = ∫ u in Az, ((f u - f z') / (u - z) ^ 2 - (f (u + (z' - z)) - f z') / (u - z) ^ 2) from
        setIntegral_congr_fun hAzm (fun u _ => by ring)]
    rw [integral_sub hI3a hI3b]
  -- step 4
  have hstep4 : (∫ u in Az, (f u - f z') / (u - z) ^ 2)
      = (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
        + (∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2)) := by
    rw [show (∫ u in Az, (f u - f z') / (u - z) ^ 2)
          = ∫ u in Az, ((f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)
              + (f u - f z') * ((u - z')⁻¹ ^ 2)) from
        setIntegral_congr_fun hAzm (fun u _ => by rw [div_eq_mul_inv, inv_pow]; ring)]
    rw [integral_add hI4a hI4b]
  -- step 5
  have hstep5 : (∫ u in Az, (f (u + (z' - z)) - f z') / (u - z) ^ 2)
      = ∫ v in Az', (f v - f z') * ((v - z')⁻¹ ^ 2) := by
    have h := CZaux.setIntegral_translate (z' - z) (fun v : ℂ => (f v - f z') * ((v - z')⁻¹ ^ 2)) Az
    have himg : (fun x : ℂ => x + (z' - z)) '' Az = Az' := by
      rw [hAz, hAz', Set.image_image]; congr 1; funext x; ring
    rw [himg] at h
    rw [show (∫ u in Az, (f (u + (z' - z)) - f z') / (u - z) ^ 2)
          = ∫ u in Az, (fun v : ℂ => (f v - f z') * ((v - z')⁻¹ ^ 2)) (u + (z' - z)) from
        setIntegral_congr_fun hAzm (fun u _ => by
          show (f (u + (z' - z)) - f z') / (u - z) ^ 2
              = (f (u + (z' - z)) - f z') * (((u + (z' - z)) - z')⁻¹ ^ 2)
          rw [show u + (z' - z) - z' = u - z from by ring, div_eq_mul_inv, inv_pow])]
    exact h
  calc (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
      = ∫ w in A, (f (z + w) - f (z' + w)) / w ^ 2 := hstep1
    _ = ∫ u in Az, (f u - f (u + (z' - z))) / (u - z) ^ 2 := hstep2
    _ = (∫ u in Az, (f u - f z') / (u - z) ^ 2)
        - (∫ u in Az, (f (u + (z' - z)) - f z') / (u - z) ^ 2) := hstep3
    _ = ((∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
          + (∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2)))
        - (∫ v in Az', (f v - f z') * ((v - z')⁻¹ ^ 2)) := by rw [hstep4, hstep5]
    _ = (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
          + ((∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2))
            - (∫ v in Az', (f v - f z') * ((v - z')⁻¹ ^ 2))) := by ring


/-- Bound for the outer region integral, combining the kernel-difference far-field
estimate with the crescent (domain-mismatch) estimate. -/
theorem outer_bound {ρ α K δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hδ4 : δ ≤ ρ / 4) {z z' : ℂ} (hzz' : ‖z - z'‖ = δ) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) :
    ‖∫ w in {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
        ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2‖
      ≤ (24 * Real.pi * K * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
          + K * (2 * Real.pi * (4 ^ α + 2 ^ α) / α)) * δ ^ α := by
  have h2δρ : 2 * δ ≤ ρ := by linarith
  rw [outer_decomp hα hK hδ h2δρ hzz' hf]
  have hfar := CZaux.far_kernelDiff_bound hα hα1 hK hδ h2δρ hzz'
    (φ := fun u : ℂ => f u - f z') (fun u => hf u z')
  have hcres := crescent_bound_holder hα hα1 hK hδ hδ4 hzz' hf
  calc ‖(∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
            (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
        + ((∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2))
          - (∫ u in (fun x : ℂ => x + z') '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2)))‖
      ≤ ‖∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
            (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
        + ‖(∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2))
          - (∫ u in (fun x : ℂ => x + z') '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
              (f u - f z') * ((u - z')⁻¹ ^ 2))‖ := norm_add_le _ _
    _ ≤ 24 * Real.pi * K * (3 / 2) ^ α * 2 ^ (α - 1) * δ ^ α / (1 - α)
        + K * (2 * Real.pi * (4 ^ α + 2 ^ α) / α) * δ ^ α := add_le_add hfar hcres
    _ = (24 * Real.pi * K * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
          + K * (2 * Real.pi * (4 ^ α + 2 ^ α) / α)) * δ ^ α := by ring


end HolderAux


theorem norm_beurlingTransform_holder {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (C' : ℝ), 0 ≤ C' → ∀ {f : ℂ → ℂ},
      (∀ x y : ℂ, ‖f x - f y‖ ≤ C' * ‖x - y‖ ^ α) → SupportedInBall (ρ / 2) f →
      ∀ z ∈ Metric.ball (0 : ℂ) (ρ / 2), ∀ z' ∈ Metric.ball (0 : ℂ) (ρ / 2),
        ‖beurlingTransform ρ f z - beurlingTransform ρ f z'‖ ≤ C * C' * ‖z - z'‖ ^ α := by
  set AC : ℝ := 4 * Real.pi * 2 ^ α / α + 24 * Real.pi * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
      + 2 * Real.pi * (4 ^ α + 2 ^ α) / α with hAC
  have hACpos : 0 ≤ AC := by rw [hAC]; positivity
  refine ⟨max (Real.pi⁻¹ * AC) (4 * 4 ^ α / α), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 4 * 4 ^ α / α := by positivity
    exact lt_of_lt_of_le h1 (le_max_right _ _)
  · intro K hK f hf hsupp z hz z' hz'
    have hzr : ‖z‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz'r : ‖z'‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz'
    by_cases hzz : z = z'
    · subst hzz
      simp [Real.zero_rpow (ne_of_gt hα)]
    · have hδpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
      set δ := ‖z - z'‖ with hδ
      have hδp : 0 < δ := hδpos
      have hzz' : ‖z - z'‖ = δ := hδ
      set N : ℂ → ℂ := fun w => (f (z + w) - f z) - (f (z' + w) - f z') with hN
      have hN_bound : ∀ w : ℂ, ‖N w‖ ≤ 2 * K * ‖w‖ ^ α := by
        intro w
        have ha : ‖f (z + w) - f z‖ ≤ K * ‖w‖ ^ α := by
          have h := hf (z + w) z; rwa [add_sub_cancel_left] at h
        have hb : ‖f (z' + w) - f z'‖ ≤ K * ‖w‖ ^ α := by
          have h := hf (z' + w) z'; rwa [add_sub_cancel_left] at h
        calc ‖N w‖ = ‖(f (z + w) - f z) - (f (z' + w) - f z')‖ := by rw [hN]
          _ ≤ ‖f (z + w) - f z‖ + ‖f (z' + w) - f z'‖ := norm_sub_le _ _
          _ ≤ K * ‖w‖ ^ α + K * ‖w‖ ^ α := add_le_add ha hb
          _ = 2 * K * ‖w‖ ^ α := by ring
      by_cases hδ4 : δ ≤ ρ / 4
      · -- ===== CASE A =====
        have h2δρ : 2 * δ ≤ ρ := by linarith
        have h2δlt : 2 * δ < ρ := by linarith
        set S1 : Set ℂ := Metric.ball (0:ℂ) ρ ∩ Metric.ball (0:ℂ) (2*δ) with hS1
        set Areg : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAreg
        have hS1m : MeasurableSet S1 := by rw [hS1]; exact measurableSet_ball.inter measurableSet_ball
        have hAregm : MeasurableSet Areg := by rw [hAreg]; measurability
        have hS1_ball : S1 ⊆ Metric.ball (0:ℂ) ρ := by rw [hS1]; exact inter_subset_left
        have hAreg_ball : Areg ⊆ Metric.ball (0:ℂ) ρ := by
          intro w hw; rw [hAreg] at hw; rw [Metric.mem_ball, dist_zero_right]; exact hw.2
        have hIntN_ball : IntegrableOn (fun w : ℂ => N w / w ^ 2) (Metric.ball (0:ℂ) ρ) := by
          have h1 := CZaux.integrableOn_beurlingIntegrand (ρ := ρ) hα hK hf z
          have h2 := CZaux.integrableOn_beurlingIntegrand (ρ := ρ) hα hK hf z'
          refine (h1.sub h2).congr_fun ?_ measurableSet_ball
          intro w _
          show (f (z + w) - f z) / w ^ 2 - (f (z' + w) - f z') / w ^ 2 = N w / w ^ 2
          rw [hN]; ring
        have hIntS1 : IntegrableOn (fun w : ℂ => N w / w ^ 2) S1 := hIntN_ball.mono_set hS1_ball
        have hIntAreg : IntegrableOn (fun w : ℂ => N w / w ^ 2) Areg :=
          hIntN_ball.mono_set hAreg_ball
        have hball_eq : Metric.ball (0:ℂ) ρ = S1 ∪ Areg := by
          ext w; simp only [hS1, hAreg, Metric.mem_ball, dist_zero_right, Set.mem_union,
            Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro hw
            rcases lt_or_ge (‖w‖) (2*δ) with h | h
            · exact Or.inl ⟨hw, h⟩
            · exact Or.inr ⟨h, hw⟩
          · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact h1
            · exact h2
        have hdisj : Disjoint S1 Areg := by
          rw [Set.disjoint_left]
          intro w hw1 hw2
          rw [hS1] at hw1; rw [hAreg] at hw2
          simp only [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] at hw1 hw2
          linarith [hw1.2, hw2.1]
        have hsplit : ∫ w in Metric.ball (0:ℂ) ρ, N w / w ^ 2
            = (∫ w in S1, N w / w ^ 2) + (∫ w in Areg, N w / w ^ 2) := by
          rw [hball_eq]
          exact MeasureTheory.setIntegral_union (s := S1) (t := Areg) hdisj hAregm hIntS1 hIntAreg
        have hinner : ‖∫ w in S1, N w / w ^ 2‖ ≤ 2 * K * (2 * Real.pi * (2*δ) ^ α / α) := by
          rw [hS1]; exact CZaux.inner_bound hα hα1 hK hδp hN_bound
        have houter : ‖∫ w in Areg, N w / w ^ 2‖
            ≤ (24 * Real.pi * K * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
                + K * (2 * Real.pi * (4 ^ α + 2 ^ α) / α)) * δ ^ α := by
          rw [hAreg]
          exact HolderAux.outer_bound hα hα1 hK hδp hδ4 hzz' hf
        have hmain : ‖∫ w in Metric.ball (0:ℂ) ρ, N w / w ^ 2‖ ≤ K * AC * δ ^ α := by
          rw [hsplit]
          calc ‖(∫ w in S1, N w / w ^ 2) + (∫ w in Areg, N w / w ^ 2)‖
              ≤ ‖∫ w in S1, N w / w ^ 2‖ + ‖∫ w in Areg, N w / w ^ 2‖ := norm_add_le _ _
            _ ≤ 2 * K * (2 * Real.pi * (2*δ) ^ α / α)
                + (24 * Real.pi * K * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
                    + K * (2 * Real.pi * (4 ^ α + 2 ^ α) / α)) * δ ^ α := add_le_add hinner houter
            _ = K * AC * δ ^ α := by
                rw [show (2*δ) ^ α = 2^α * δ^α from by
                  rw [Real.mul_rpow (by norm_num) (le_of_lt hδp)]]
                rw [hAC]; ring
        have hSf : beurlingTransform ρ f z - beurlingTransform ρ f z'
            = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0:ℂ) ρ, N w / w ^ 2 := by
          rw [HolderAux.beurling_sub_eq hα hK hf z z']
        rw [hSf, norm_mul, norm_neg]
        have hpi : ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ := by
          rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        rw [hpi]
        calc Real.pi⁻¹ * ‖∫ w in Metric.ball (0:ℂ) ρ, N w / w ^ 2‖
            ≤ Real.pi⁻¹ * (K * AC * δ ^ α) := mul_le_mul_of_nonneg_left hmain (by positivity)
          _ = (Real.pi⁻¹ * AC) * K * δ ^ α := by ring
          _ ≤ max (Real.pi⁻¹ * AC) (4 * 4 ^ α / α) * K * δ ^ α :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hK) (Real.rpow_nonneg hδp.le α)
      · -- ===== CASE B =====
        push_neg at hδ4
        have hδge : ρ / 4 ≤ δ := le_of_lt hδ4
        have h1 : ‖beurlingTransform ρ f z‖ ≤ 2 * K * ρ ^ α / α :=
          norm_beurlingTransform_le hα hK hf (by linarith [hzr])
        have h2 : ‖beurlingTransform ρ f z'‖ ≤ 2 * K * ρ ^ α / α :=
          norm_beurlingTransform_le hα hK hf (by linarith [hz'r])
        have hbd : ‖beurlingTransform ρ f z - beurlingTransform ρ f z'‖ ≤ 4 * K * ρ ^ α / α := by
          calc _ ≤ ‖beurlingTransform ρ f z‖ + ‖beurlingTransform ρ f z'‖ := norm_sub_le _ _
            _ ≤ 2*K*ρ^α/α + 2*K*ρ^α/α := add_le_add h1 h2
            _ = 4*K*ρ^α/α := by ring
        have hpow : ρ^α / 4^α ≤ δ^α := by
          rw [← Real.div_rpow hρ.le (by norm_num : (0:ℝ) ≤ 4)]
          exact Real.rpow_le_rpow (by positivity) hδge hα.le
        have hfac : 4 * K * 4 ^ α / α * (ρ^α / 4^α) = 4 * K * ρ ^ α / α := by
          have h4α : (4:ℝ)^α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) α)
          rw [div_mul_div_comm]
          rw [show (4 * K * 4 ^ α) * ρ^α = (4 * K * ρ^α) * 4^α from by ring]
          rw [mul_div_mul_right _ _ h4α]
        have hKδ : 4 * K * ρ ^ α / α ≤ max (Real.pi⁻¹ * AC) (4 * 4 ^ α / α) * K * δ ^ α := by
          have hA4 : 4 * 4 ^ α / α ≤ max (Real.pi⁻¹ * AC) (4 * 4 ^ α / α) := le_max_right _ _
          have h4 : (0:ℝ) ≤ 4 * K * 4 ^ α / α := by positivity
          calc 4 * K * ρ ^ α / α = 4 * K * 4 ^ α / α * (ρ^α / 4^α) := hfac.symm
            _ ≤ 4 * K * 4 ^ α / α * δ^α := mul_le_mul_of_nonneg_left hpow h4
            _ ≤ max (Real.pi⁻¹ * AC) (4 * 4 ^ α / α) * K * δ ^ α := by
                rw [show 4 * K * 4 ^ α / α * δ^α = (4 * 4 ^ α / α) * K * δ ^ α from by ring]
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (le_max_right _ _) hK) (Real.rpow_nonneg hδp.le α)
        linarith [hbd, hKδ]

end Work.CR.Flat.Cauchy
