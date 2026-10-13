import Mathlib.Analysis.SpecialFunctions.NonIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

open MeasureTheory Set Filter
open scoped Topology

/-- **The limit at `0⁺` of `t ↦ c t * t ^ q` can only be `0`.**  If `F t = c t * t ^ q` for all
`t > 0`, if `t ↦ c t * t ^ (q - 1)` is integrable on `(0,1)`, and if `F` has a limit `C` at `0⁺`,
then `C = 0`.

Route: suppose `C ≠ 0`.  Then `|F t| ≥ |C|/2` for all `t` in some `(0,ε)` (`nhdsGT_basis`), and
`|c t * t ^ (q-1)| = |F t| / t ≥ |C| / (2 * t)` there.  For `0 < a < ε`,
`∫ x in a..ε, 1/x = Real.log (ε/a) → ∞` as `a → 0⁺` (`integral_one_div_of_pos` plus
`Real.tendsto_log_nhdsGT_zero`), while these interval integrals stay below
`∫⁻ x in Set.Ioo 0 1, ‖c x * x ^ (q-1)‖ < ∞` (`MeasureTheory.lintegral_mono_set`). -/
theorem tendsto_limit_eq_zero_of_rpow {q C : ℝ} {c F : ℝ → ℝ}
    (hF : ∀ t : ℝ, 0 < t → F t = c t * t ^ q)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ (q - 1)) (Set.Ioo 0 1))
    (hC : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds C)) :
    C = 0 := by
  -- Strategy: `g t = c t * t ^ (q - 1)` equals `F t / t` on `(0,∞)`.  If `C ≠ 0` then
  -- `‖g t‖ ≥ (|C|/2) * t⁻¹` on a small interval `(0,b)`, so monotone comparison makes
  -- `t ↦ (|C|/2) * t⁻¹` (hence `t ↦ t⁻¹`) integrable there — contradicting the fact that
  -- `t ↦ t⁻¹` is not integrable on any interval containing `0`.
  by_contra hne
  let g : ℝ → ℝ := fun t => c t * t ^ (q - 1)
  -- `g t = F t / t` for `t > 0`
  have hg_eq : ∀ t : ℝ, 0 < t → g t = F t / t := by
    intro t ht
    have h1 : t ^ (q - 1) = t ^ q / t := by rw [Real.rpow_sub ht q 1, Real.rpow_one]
    show c t * t ^ (q - 1) = F t / t
    rw [h1, hF t ht]
    ring
  -- eventually near `0⁺`, `|F t| ≥ |C|/2`
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), |C| / 2 ≤ |F t| := by
    have hball : Metric.ball C (|C| / 2) ∈ nhds C :=
      Metric.ball_mem_nhds C (by have h := abs_pos.mpr hne; linarith)
    filter_upwards [hC.eventually hball] with t ht
    rw [Real.dist_eq] at ht
    have h2 : |C| - |F t| ≤ |C - F t| := abs_sub_abs_le_abs_sub C (F t)
    have h3 : |C - F t| < |C| / 2 := by rw [abs_sub_comm]; exact ht
    linarith
  obtain ⟨ε, hεpos, hε⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.mp hev
  -- a small interval `(0,b)` contained in `(0,ε) ∩ (0,1)`
  let b : ℝ := min ε 1 / 2
  have hb_pos : 0 < b := by
    have h : 0 < min ε 1 := lt_min hεpos one_pos
    show 0 < min ε 1 / 2
    linarith
  have hbε : b < ε := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    show min ε 1 / 2 < ε
    linarith
  have hb1 : b ≤ 1 := by
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    show min ε 1 / 2 ≤ 1
    linarith
  -- the pointwise lower bound `(|C|/2) * t⁻¹ ≤ ‖g t‖` on `(0,b)`
  have hpt : ∀ t ∈ Set.Ioo 0 b, ‖|C| / 2 * t⁻¹‖ ≤ ‖g t‖ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hFt : |C| / 2 ≤ |F t| := hε ⟨ht.1, lt_trans ht.2 hbε⟩
    have hgt : ‖g t‖ = |F t| / t := by
      rw [hg_eq t ht0, norm_div, Real.norm_of_nonneg ht0.le, Real.norm_eq_abs]
    have hleft : ‖|C| / 2 * t⁻¹‖ = |C| / 2 * t⁻¹ := Real.norm_of_nonneg (by positivity)
    rw [hgt, hleft, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hFt (inv_nonneg.mpr ht0.le)
  have hgb : MeasureTheory.IntegrableOn g (Set.Ioo 0 b) :=
    h0.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hb1⟩)
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |C| / 2 * t⁻¹)
      (volume.restrict (Set.Ioo 0 b)) := by
    have hcont : ContinuousOn (fun t : ℝ => |C| / 2 * t⁻¹) (Set.Ioo 0 b) :=
      continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => ne_of_gt hx.1))
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  -- monotone comparison: `(|C|/2) * t⁻¹` is integrable on `(0,b)`
  have hint1 : MeasureTheory.IntegrableOn (fun t : ℝ => |C| / 2 * t⁻¹) (Set.Ioo 0 b) :=
    hgb.norm.mono' hmeas ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hpt))
  -- hence so is `t ↦ t⁻¹`
  have hinv1 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (|C| / 2)⁻¹ * (|C| / 2 * t⁻¹)) (Set.Ioo 0 b) :=
    Integrable.const_mul hint1 (|C| / 2)⁻¹
  have hinv : MeasureTheory.IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioo 0 b) :=
    hinv1.congr_fun
      (fun t ht => by
        show (|C| / 2)⁻¹ * (|C| / 2 * t⁻¹) = t⁻¹
        rw [← mul_assoc, inv_mul_cancel₀ (by have h := abs_pos.mpr hne; linarith), one_mul])
      measurableSet_Ioo
  -- but `t ↦ t⁻¹` is not integrable on any interval containing `0`
  have hnot : ¬ MeasureTheory.IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioo 0 b) := by
    intro h
    have hII : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hb_pos.le).2 h
    rcases (intervalIntegrable_inv_iff (a := 0) (b := b)).1 hII with h' | h'
    · exact hb_pos.ne' h'.symm
    · exact h' (by rw [Set.uIcc_of_le hb_pos.le]; exact ⟨le_refl 0, hb_pos.le⟩)
  exact hnot hinv

end Work.FTS.ClassCHon.Zpz
