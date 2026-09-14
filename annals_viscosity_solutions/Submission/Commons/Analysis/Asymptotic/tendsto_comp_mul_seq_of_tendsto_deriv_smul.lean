import Mathlib

namespace Commons.Analysis.Asymptotic

open Filter Set MeasureTheory
open scoped Topology

/-- Variable-coefficient mean value inequality with a `1/t` bound: if `f` is differentiable on
`(0, ε)` with `‖t • f' t‖ ≤ δ` there, then for `0 < a ≤ b < ε` one has
`‖f b - f a‖ ≤ δ * (b - a) / a`. -/
theorem norm_sub_le_of_hasDerivAt_of_norm_le_inv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {a b δ ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbε : b < ε)
    (hf : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (f' t) t)
    (hbd : ∀ t ∈ Set.Ioo (0:ℝ) ε, ‖t • f' t‖ ≤ δ) :
    ‖f b - f a‖ ≤ δ * (b - a) / a := by
  have key : ∀ x ∈ Set.Icc a b, ‖f x - f a‖ ≤ (δ / a) * (x - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (a := a) (b := b)
      (C := δ / a) (fun x hx =>
        (hf x ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hbε⟩).hasDerivWithinAt)
      (fun x hx => by
        have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
        have hxε : x ∈ Set.Ioo (0:ℝ) ε := ⟨hxpos, lt_trans hx.2 hbε⟩
        have hb := hbd x hxε
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos] at hb
        have hle : a * ‖f' x‖ ≤ δ :=
          le_trans (mul_le_mul_of_nonneg_right hx.1 (norm_nonneg _)) hb
        rw [le_div_iff₀ ha]
        simpa [mul_comm] using hle)
  calc ‖f b - f a‖ ≤ (δ / a) * (b - a) := key b (right_mem_Icc.mpr hab)
    _ = δ * (b - a) / a := by ring

theorem tendsto_comp_mul_seq_of_tendsto_deriv_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hdiff : ∀ u ∈ Set.Ioo (0:ℝ) ε, HasDerivAt f (deriv f u) u)
    (hder : Filter.Tendsto (fun u : ℝ => u • deriv f u) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    {lam : ℕ → ℝ} (hlam : Filter.Tendsto lam Filter.atTop (nhdsWithin (0:ℝ) (Set.Ioi 0)))
    {s : F} (hs : Filter.Tendsto (fun n => f (lam n)) Filter.atTop (nhds s)) :
    ∀ t ∈ Set.Ioc (0:ℝ) T, Filter.Tendsto (fun n => f (lam n * t)) Filter.atTop (nhds s) := by
  intro t ht
  rw [Set.mem_Ioc] at ht
  obtain ⟨ht0, htT⟩ := ht
  have hlam' := tendsto_nhdsWithin_iff.mp hlam
  have hlam_ten : Tendsto lam atTop (nhds 0) := hlam'.1
  have hlam_pos : ∀ᶠ n in atTop, (0:ℝ) < lam n := by
    filter_upwards [hlam'.2] with n hn using hn
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hder_extract : ∀ δ' > 0, ∃ η0 > 0, ∀ u, 0 < u → u < η0 → ‖u • deriv f u‖ ≤ δ' := by
    intro δ' hδ'
    obtain ⟨η0, hη0pos, hη0⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hder) δ' hδ'
    refine ⟨η0, hη0pos, fun u hu0 huη => ?_⟩
    have hdist : dist u 0 < η0 := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu0]; exact huη
    have h2 := hη0 (Set.mem_Ioi.mpr hu0) hdist
    rw [dist_eq_norm, sub_zero] at h2
    exact le_of_lt h2
  rcases lt_or_ge t 1 with ht1 | h1t
  · -- Case `t < 1`
    have ht_le : t ≤ 1 := le_of_lt ht1
    have hδ'pos : 0 < δ * t / (2 * (t + 1)) := by positivity
    obtain ⟨η0, hη0pos, hη0⟩ := hder_extract (δ * t / (2 * (t + 1))) hδ'pos
    set ε' := min ε η0 with hε'def
    have hε'pos : 0 < ε' := lt_min hε hη0pos
    have hdiff' : ∀ u ∈ Set.Ioo (0:ℝ) ε', HasDerivAt f (deriv f u) u :=
      fun u hu => hdiff u ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
    have hbd' : ∀ u ∈ Set.Ioo (0:ℝ) ε', ‖u • deriv f u‖ ≤ δ * t / (2 * (t + 1)) :=
      fun u hu => hη0 u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    have hEv0 : ∀ᶠ n in atTop, (0:ℝ) < lam n ∧ lam n < ε' := by
      have h2 : ∀ᶠ n in atTop, lam n < ε' :=
        (tendsto_order.mp hlam_ten).2 ε' hε'pos
      filter_upwards [hlam_pos, h2] with n h1 h2 using ⟨h1, h2⟩
    have hEv1 : ∀ᶠ n in atTop, dist (f (lam n)) s < δ / 2 :=
      (Metric.tendsto_nhds.mp hs) (δ / 2) (by linarith)
    filter_upwards [hEv0, hEv1] with n hn hn1
    obtain ⟨hn_pos, hn_lt⟩ := hn
    have ha : 0 < lam n * t := mul_pos hn_pos ht0
    have hab : lam n * t ≤ lam n := by
      have := mul_le_mul_of_nonneg_left ht_le (le_of_lt hn_pos)
      simpa using this
    have hkey := norm_sub_le_of_hasDerivAt_of_norm_le_inv (f := f) (f' := fun u => deriv f u)
      (a := lam n * t) (b := lam n) (δ := δ * t / (2 * (t + 1))) (ε := ε')
      ha hab hn_lt hdiff' hbd'
    have hb1 : ‖f (lam n * t) - f (lam n)‖ ≤ (δ * t / (2 * (t + 1))) * (1 - t) / t := by
      calc ‖f (lam n * t) - f (lam n)‖ = ‖f (lam n) - f (lam n * t)‖ := norm_sub_rev _ _
        _ ≤ (δ * t / (2 * (t + 1))) * (lam n - lam n * t) / (lam n * t) := hkey
        _ = (δ * t / (2 * (t + 1))) * (1 - t) / t := by
            field_simp [ne_of_gt hn_pos, ne_of_gt ht0]
    have hb2 : (δ * t / (2 * (t + 1))) * (1 - t) / t < δ / 2 := by
      have heq : (δ * t / (2 * (t + 1))) * (1 - t) / t = δ * (1 - t) / (2 * (t + 1)) := by
        field_simp [ne_of_gt ht0]
      rw [heq]
      rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (t + 1)) (by norm_num : (0:ℝ) < 2)]
      nlinarith [ht0, hδ]
    have hclose : ‖f (lam n) - s‖ < δ / 2 := by rw [dist_eq_norm] at hn1; exact hn1
    rw [dist_eq_norm]
    have hsplit : f (lam n * t) - s = (f (lam n * t) - f (lam n)) + (f (lam n) - s) := by abel
    rw [hsplit]
    calc ‖(f (lam n * t) - f (lam n)) + (f (lam n) - s)‖
        ≤ ‖f (lam n * t) - f (lam n)‖ + ‖f (lam n) - s‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add (lt_of_le_of_lt hb1 hb2) hclose
      _ = δ := by ring
  · -- Case `1 ≤ t`
    have hδ'pos : 0 < δ / (2 * (T + 1)) := by positivity
    obtain ⟨η0, hη0pos, hη0⟩ := hder_extract (δ / (2 * (T + 1))) hδ'pos
    set ε' := min ε η0 with hε'def
    have hε'pos : 0 < ε' := lt_min hε hη0pos
    have hdiff' : ∀ u ∈ Set.Ioo (0:ℝ) ε', HasDerivAt f (deriv f u) u :=
      fun u hu => hdiff u ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
    have hbd' : ∀ u ∈ Set.Ioo (0:ℝ) ε', ‖u • deriv f u‖ ≤ δ / (2 * (T + 1)) :=
      fun u hu => hη0 u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    have hQpos : 0 < ε' / t := div_pos hε'pos ht0
    have hEv0 : ∀ᶠ n in atTop, (0:ℝ) < lam n ∧ lam n < ε' / t := by
      have h2 : ∀ᶠ n in atTop, lam n < ε' / t :=
        (tendsto_order.mp hlam_ten).2 (ε' / t) hQpos
      filter_upwards [hlam_pos, h2] with n h1 h2 using ⟨h1, h2⟩
    have hEv1 : ∀ᶠ n in atTop, dist (f (lam n)) s < δ / 2 :=
      (Metric.tendsto_nhds.mp hs) (δ / 2) (by linarith)
    filter_upwards [hEv0, hEv1] with n hn hn1
    obtain ⟨hn_pos, hn_lt⟩ := hn
    have hab : lam n ≤ lam n * t := by
      have := mul_le_mul_of_nonneg_left h1t (le_of_lt hn_pos)
      simpa using this
    have hbt : lam n * t < ε' := by
      have := mul_lt_mul_of_pos_right hn_lt ht0
      rwa [div_mul_cancel₀ _ (ne_of_gt ht0)] at this
    have hkey := norm_sub_le_of_hasDerivAt_of_norm_le_inv (f := f) (f' := fun u => deriv f u)
      (a := lam n) (b := lam n * t) (δ := δ / (2 * (T + 1))) (ε := ε')
      hn_pos hab hbt hdiff' hbd'
    have hb1 : ‖f (lam n * t) - f (lam n)‖ ≤ (δ / (2 * (T + 1))) * (t - 1) := by
      calc ‖f (lam n * t) - f (lam n)‖
          ≤ (δ / (2 * (T + 1))) * (lam n * t - lam n) / lam n := hkey
        _ = (δ / (2 * (T + 1))) * (t - 1) := by
            field_simp [ne_of_gt hn_pos]
    have hb2 : (δ / (2 * (T + 1))) * (t - 1) < δ / 2 := by
      have ht1' : t - 1 ≤ T := by linarith
      have hstep1 : (δ / (2 * (T + 1))) * (t - 1) ≤ (δ / (2 * (T + 1))) * T :=
        mul_le_mul_of_nonneg_left ht1' (by positivity)
      have hstep2 : (δ / (2 * (T + 1))) * T < δ / 2 := by
        rw [div_mul_eq_mul_div]
        rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (T + 1)) (by norm_num : (0:ℝ) < 2)]
        nlinarith [hT, hδ]
      linarith
    have hclose : ‖f (lam n) - s‖ < δ / 2 := by rw [dist_eq_norm] at hn1; exact hn1
    rw [dist_eq_norm]
    have hsplit : f (lam n * t) - s = (f (lam n * t) - f (lam n)) + (f (lam n) - s) := by abel
    rw [hsplit]
    calc ‖(f (lam n * t) - f (lam n)) + (f (lam n) - s)‖
        ≤ ‖f (lam n * t) - f (lam n)‖ + ‖f (lam n) - s‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add (lt_of_le_of_lt hb1 hb2) hclose
      _ = δ := by ring

end Commons.Analysis.Asymptotic
