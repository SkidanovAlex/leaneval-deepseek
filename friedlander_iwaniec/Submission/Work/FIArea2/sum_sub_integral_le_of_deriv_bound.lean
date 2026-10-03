import Mathlib

namespace Work.FIArea2

open MeasureTheory Set

/-- Pointwise comparison: if `φ` is differentiable on `[a, b]` with `|φ'| ≤ ψ` there,
and `ψ` is interval integrable on `[a, b]`, then `|φ x - φ a| ≤ ∫_a^b ψ` for every
`x ∈ [a, b]`. -/
lemma abs_sub_le_integral_of_deriv_bound_aux {φ ψ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ φ x)
    (hbound : ∀ x ∈ Set.Icc a b, |deriv φ x| ≤ ψ x)
    (hψ : IntervalIntegrable ψ volume a b) :
    ∀ x ∈ Set.Icc a b, |φ x - φ a| ≤ ∫ y in a..b, ψ y := by
  intro x hx
  have hax : a ≤ x := hx.1
  have hxb : x ≤ b := hx.2
  have hsub : Set.uIcc a x ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hax, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl hxb
  have hψax : IntervalIntegrable ψ volume a x := hψ.mono_set hsub
  have hderivint : IntervalIntegrable (deriv φ) volume a x := by
    refine IntervalIntegrable.mono_fun' hψax (measurable_deriv φ).aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hax]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => ?_
    show ‖deriv φ y‖ ≤ ψ y
    rw [Real.norm_eq_abs]
    exact hbound y ⟨le_of_lt hy.1, le_trans hy.2 hxb⟩
  have hFTC : ∫ y in a..x, deriv φ y = φ x - φ a := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro y hy
      rw [Set.uIcc_of_le hax] at hy
      exact hdiff y ⟨hy.1, le_trans hy.2 hxb⟩
    · exact hderivint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] ψ :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun y hy =>
      le_trans (abs_nonneg _) (hbound y ⟨le_of_lt hy.1, hy.2⟩)
  calc |φ x - φ a|
      = |∫ y in a..x, deriv φ y| := by rw [hFTC]
    _ ≤ ∫ y in a..x, |deriv φ y| := intervalIntegral.abs_integral_le_integral_abs hax
    _ ≤ ∫ y in a..x, ψ y := by
        refine intervalIntegral.integral_mono_on hax hderivint.abs hψax fun y hy => ?_
        exact hbound y ⟨hy.1, le_trans hy.2 hxb⟩
    _ ≤ ∫ y in a..b, ψ y :=
        intervalIntegral.integral_mono_interval le_rfl hax hxb hnonneg hψ

theorem sum_sub_integral_le_of_deriv_bound {φ ψ : ℝ → ℝ} {L U : ℕ} (hLU : L ≤ U)
    (hdiff : ∀ x ∈ Set.Icc (L : ℝ) ((U : ℝ) + 1), DifferentiableAt ℝ φ x)
    (hbound : ∀ x ∈ Set.Icc (L : ℝ) ((U : ℝ) + 1), |deriv φ x| ≤ ψ x)
    (hψint : ∀ k ∈ Finset.Ico L (U + 1), IntervalIntegrable ψ volume (k : ℝ) ((k : ℝ) + 1)) :
    |(∑ k ∈ Finset.Ico L (U + 1), φ (k : ℝ)) - ∫ x in (L : ℝ)..((U : ℝ) + 1), φ x|
      ≤ ∫ x in (L : ℝ)..((U : ℝ) + 1), ψ x := by
  have hl1 : (L : ℝ) ≤ (U : ℝ) + 1 := by
    have h : (L : ℝ) ≤ (U : ℝ) := by exact_mod_cast hLU
    linarith
  have hφcont : ContinuousOn φ (Set.Icc (L : ℝ) ((U : ℝ) + 1)) :=
    fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hintφ : ∀ k ∈ Finset.Ico L (U + 1),
      IntervalIntegrable φ volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k hk
    obtain ⟨hkL, hkU⟩ := Finset.mem_Ico.mp hk
    have hkU' : k ≤ U := by omega
    have hstep : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hsub : Set.uIcc (k : ℝ) ((k : ℝ) + 1) ⊆ Set.Icc (L : ℝ) ((U : ℝ) + 1) := by
      rw [Set.uIcc_of_le hstep]
      exact Set.Icc_subset_Icc (by exact_mod_cast hkL) (by
        have : (k : ℝ) ≤ (U : ℝ) := by exact_mod_cast hkU'
        linarith)
    exact (hφcont.mono hsub).intervalIntegrable
  have hφsum : (∑ k ∈ Finset.Ico L (U + 1), ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x)
      = ∫ x in (L : ℝ)..((U : ℝ) + 1), φ x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := φ)
      (a := fun k : ℕ => (k : ℝ)) (by omega : L ≤ U + 1)
      (fun k hk => by
        have hk' : k ∈ Finset.Ico L (U + 1) := by simpa [Finset.coe_Ico] using hk
        simpa using hintφ k hk')
    simpa using h
  have hψsum : (∑ k ∈ Finset.Ico L (U + 1), ∫ x in (k : ℝ)..((k : ℝ) + 1), ψ x)
      = ∫ x in (L : ℝ)..((U : ℝ) + 1), ψ x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume) (f := ψ)
      (a := fun k : ℕ => (k : ℝ)) (by omega : L ≤ U + 1)
      (fun k hk => by
        have hk' : k ∈ Finset.Ico L (U + 1) := by simpa [Finset.coe_Ico] using hk
        simpa using hψint k hk')
    simpa using h
  have hterm : ∀ k ∈ Finset.Ico L (U + 1),
      |φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x|
        ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), ψ x := by
    intro k hk
    obtain ⟨hkL, hkU⟩ := Finset.mem_Ico.mp hk
    have hkU' : k ≤ U := by omega
    have hkLr : (L : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkL
    have hkr : (k : ℝ) ≤ (U : ℝ) := by exact_mod_cast hkU'
    have hstep : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hsub : Set.Icc (k : ℝ) ((k : ℝ) + 1) ⊆ Set.Icc (L : ℝ) ((U : ℝ) + 1) := by
      intro y hy
      exact ⟨le_trans hkLr hy.1, le_trans hy.2 (by linarith)⟩
    have hK : ∀ y ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
        |φ (k : ℝ) - φ y| ≤ ∫ z in (k : ℝ)..((k : ℝ) + 1), ψ z := by
      intro y hy
      have h := abs_sub_le_integral_of_deriv_bound_aux hstep
        (fun y hy => hdiff y (hsub hy)) (fun y hy => hbound y (hsub hy)) (hψint k hk) y hy
      simpa [abs_sub_comm] using h
    have hD : φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x
        = ∫ x in (k : ℝ)..((k : ℝ) + 1), (φ (k : ℝ) - φ x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hintφ k hk),
        intervalIntegral.integral_const]
      simp
    have hcont_k : ContinuousOn φ (Set.uIcc (k : ℝ) ((k : ℝ) + 1)) :=
      hφcont.mono (by rw [Set.uIcc_of_le hstep]; exact hsub)
    have hint_abs : IntervalIntegrable (fun y => |φ (k : ℝ) - φ y|) volume
        (k : ℝ) ((k : ℝ) + 1) :=
      ((continuousOn_const.sub hcont_k).abs).intervalIntegrable
    calc |φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x|
        = |∫ x in (k : ℝ)..((k : ℝ) + 1), (φ (k : ℝ) - φ x)| := by rw [hD]
      _ ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), |φ (k : ℝ) - φ x| :=
            intervalIntegral.abs_integral_le_integral_abs hstep
      _ ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), (∫ z in (k : ℝ)..((k : ℝ) + 1), ψ z) :=
            intervalIntegral.integral_mono_on hstep hint_abs intervalIntegrable_const
              fun y hy => hK y hy
      _ = ∫ x in (k : ℝ)..((k : ℝ) + 1), ψ x := by
            rw [intervalIntegral.integral_const]; simp
  calc |(∑ k ∈ Finset.Ico L (U + 1), φ (k : ℝ)) - ∫ x in (L : ℝ)..((U : ℝ) + 1), φ x|
      = |∑ k ∈ Finset.Ico L (U + 1),
          (φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x)| := by
        rw [← hφsum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.Ico L (U + 1),
          |φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x| :=
        Finset.abs_sum_le_sum_abs
          (fun k : ℕ => φ (k : ℝ) - ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x)
          (Finset.Ico L (U + 1))
    _ ≤ ∑ k ∈ Finset.Ico L (U + 1), ∫ x in (k : ℝ)..((k : ℝ) + 1), ψ x :=
        Finset.sum_le_sum hterm
    _ = ∫ x in (L : ℝ)..((U : ℝ) + 1), ψ x := hψsum

end Work.FIArea2
