import Submission.Work.WilG1.OneDim.thin_ev

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 10. No interval of oscillation -/

theorem no_interval_oscR {g : ℝ → ℝ} {q u v : ℝ} (huv : u < v)
    (hcont : ∀ x ∈ Set.Ioo u v, ContinuousAt g x)
    (hsub : Set.Ioo u v ⊆ oscR g q) : False := by
  obtain ⟨s, hs1, hs2⟩ := exists_between huv
  obtain ⟨t, ht1, ht2⟩ := exists_between hs2
  set F : ℝ → ℝ := fun y => g y - q * y with hF
  have hcontF : ContinuousOn F (Set.Icc s t) := by
    intro y hy
    have hy' : y ∈ Set.Ioo u v := ⟨lt_of_lt_of_le hs1 hy.1, lt_of_le_of_lt hy.2 ht2⟩
    exact ((hcont y hy').sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  obtain ⟨m, hmI, hmmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s, le_rfl, ht1.le⟩ hcontF
  obtain ⟨m', hm'I, hm'min⟩ := isCompact_Icc.exists_isMinOn ⟨s, le_rfl, ht1.le⟩ hcontF
  have hmosc : m ∈ oscR g q :=
    hsub ⟨lt_of_lt_of_le hs1 hmI.1, lt_of_le_of_lt hmI.2 ht2⟩
  have hm'osc : m' ∈ oscR g q :=
    hsub ⟨lt_of_lt_of_le hs1 hm'I.1, lt_of_le_of_lt hm'I.2 ht2⟩
  have hm_eq : m = t := by
    by_contra hne
    have hmlt : m < t := lt_of_le_of_ne hmI.2 hne
    obtain ⟨y, hy1, hy2, hy3⟩ := hmosc.1 (t - m) (by linarith)
    have hyI : y ∈ Set.Icc s t := ⟨by linarith [hmI.1], by linarith⟩
    have hyF : F m < F y := by
      have h' := (lt_dq_iff hy1).mp hy3
      simp only [hF]; linarith
    have hle : F y ≤ F m := hmmax hyI
    linarith
  have hm'_eq : m' = t := by
    by_contra hne
    have hm'lt : m' < t := lt_of_le_of_ne hm'I.2 hne
    obtain ⟨y, hy1, hy2, hy3⟩ := hm'osc.2 (t - m') (by linarith)
    have hyI : y ∈ Set.Icc s t := ⟨by linarith [hm'I.1], by linarith⟩
    have hyF : F y < F m' := by
      have h' := (dq_lt_iff hy1).mp hy3
      simp only [hF]; linarith
    have hle : F m' ≤ F y := hm'min hyI
    linarith
  have hconst : ∀ y ∈ Set.Icc s t, F y = F t := by
    intro y hy
    have h1 : F y ≤ F t := by simpa [hm_eq] using hmmax hy
    have h2 : F t ≤ F y := by simpa [hm'_eq] using hm'min hy
    linarith
  obtain ⟨y, hy1, hy2, hy3⟩ := (hsub ⟨hs1, hs2⟩).2 (t - s) (by linarith)
  have hyI : y ∈ Set.Icc s t := ⟨by linarith [hy1], by linarith⟩
  have hyF : F y < F s := by
    have h' := (dq_lt_iff hy1).mp hy3
    simp only [hF]; linarith
  have h1 := hconst y hyI
  have h2 := hconst s ⟨le_rfl, ht1.le⟩
  linarith

theorem no_interval_oscL {g : ℝ → ℝ} {q u v : ℝ} (huv : u < v)
    (hcont : ∀ x ∈ Set.Ioo u v, ContinuousAt g x)
    (hsub : Set.Ioo u v ⊆ oscL g q) : False := by
  obtain ⟨s, hs1, hs2⟩ := exists_between huv
  obtain ⟨t, ht1, ht2⟩ := exists_between hs2
  set F : ℝ → ℝ := fun y => g y - q * y with hF
  have hcontF : ContinuousOn F (Set.Icc s t) := by
    intro y hy
    have hy' : y ∈ Set.Ioo u v := ⟨lt_of_lt_of_le hs1 hy.1, lt_of_le_of_lt hy.2 ht2⟩
    exact ((hcont y hy').sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
  obtain ⟨m, hmI, hmmax⟩ := isCompact_Icc.exists_isMaxOn ⟨s, le_rfl, ht1.le⟩ hcontF
  obtain ⟨m', hm'I, hm'min⟩ := isCompact_Icc.exists_isMinOn ⟨s, le_rfl, ht1.le⟩ hcontF
  have hmosc : m ∈ oscL g q :=
    hsub ⟨lt_of_lt_of_le hs1 hmI.1, lt_of_le_of_lt hmI.2 ht2⟩
  have hm'osc : m' ∈ oscL g q :=
    hsub ⟨lt_of_lt_of_le hs1 hm'I.1, lt_of_le_of_lt hm'I.2 ht2⟩
  have hm_eq : m = s := by
    by_contra hne
    have hslt : s < m := lt_of_le_of_ne hmI.1 (fun h => hne h.symm)
    obtain ⟨y, hy1, hy2, hy3⟩ := hmosc.2 (m - s) (by linarith)
    have hyI : y ∈ Set.Icc s t := ⟨by linarith, by linarith [hmI.2]⟩
    have hyF : F m < F y := by
      have h' := (dq_lt_iff_of_lt hy2).mp hy3
      simp only [hF]; linarith
    have hle : F y ≤ F m := hmmax hyI
    linarith
  have hm'_eq : m' = s := by
    by_contra hne
    have hslt : s < m' := lt_of_le_of_ne hm'I.1 (fun h => hne h.symm)
    obtain ⟨y, hy1, hy2, hy3⟩ := hm'osc.1 (m' - s) (by linarith)
    have hyI : y ∈ Set.Icc s t := ⟨by linarith, by linarith [hm'I.2]⟩
    have hyF : F y < F m' := by
      have h' := (lt_dq_iff_of_lt hy2).mp hy3
      simp only [hF]; linarith
    have hle : F m' ≤ F y := hm'min hyI
    linarith
  have hconst : ∀ y ∈ Set.Icc s t, F y = F s := by
    intro y hy
    have h1 : F y ≤ F s := by simpa [hm_eq] using hmmax hy
    have h2 : F s ≤ F y := by simpa [hm'_eq] using hm'min hy
    linarith
  obtain ⟨y, hy1, hy2, hy3⟩ := (hsub ⟨by linarith, ht2⟩).1 (t - s) (by linarith)
  have hyI : y ∈ Set.Icc s t := ⟨by linarith [hy1], le_of_lt hy2⟩
  have hyF : F y < F t := by
    have h' := (lt_dq_iff_of_lt hy2).mp hy3
    simp only [hF]; linarith
  have h1 := hconst y hyI
  have h2 := hconst t ⟨ht1.le, le_rfl⟩
  linarith

end Work.WilG1.OneDim
