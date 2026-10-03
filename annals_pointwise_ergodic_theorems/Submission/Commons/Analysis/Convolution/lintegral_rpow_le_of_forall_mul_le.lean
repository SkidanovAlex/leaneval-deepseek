import Mathlib
import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite

namespace Commons.Analysis.Convolution

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

open Commons.Analysis.Integral

/-- For `a : ℝ≥0∞`, the truncations `a ⊓ n` (`n : ℕ`) have supremum `a`. -/
lemma iSup_inf_natCast (a : ℝ≥0∞) : (⨆ n : ℕ, a ⊓ (n : ℝ≥0∞)) = a := by
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro n; exact inf_le_left
  · intro w hw
    have hwtop : w < ⊤ := lt_of_lt_of_le hw le_top
    obtain ⟨n, hn⟩ := (iSup_eq_top.mp ENNReal.iSup_natCast) w hwtop
    exact ⟨n, lt_inf_iff.mpr ⟨hw, hn⟩⟩

/-- The integral of a constant against a restricted measure. -/
lemma lintegral_const_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (c : ℝ≥0∞) : ∫⁻ _ in s, c ∂μ = c * μ s := by
  rw [lintegral_const]
  congr 1
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- Auxiliary finite-measure truncation bound: for a fixed finite-measure set `spanningSets μ k`
and truncation level `n`, the `q`-norm of the truncation `min (F x) n` is bounded by `C`. -/
theorem lintegral_rpow_le_of_forall_mul_le_aux {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {q : ℝ} (hq : 1 < q) {F : α → ℝ≥0∞} (hF : AEMeasurable F μ)
    {C : ℝ≥0∞}
    (h : ∀ g : α → ℝ≥0∞, AEMeasurable g μ →
      ∫⁻ x, F x * g x ∂μ ≤ C * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q))
    (k n : ℕ) :
    (∫⁻ x in spanningSets μ k, (min (F x) (n:ℝ≥0∞)) ^ q ∂μ) ^ (1 / q) ≤ C := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hc1 : 0 < q - 1 := by linarith
  have hpq : 0 < q / (q - 1) := div_pos hq0 hc1
  have hs : 0 < (q - 1) / q := div_pos hc1 hq0
  have hp : 0 < 1 / q := div_pos one_pos hq0
  set E : Set α := spanningSets μ k with hEdef
  have hE : MeasurableSet E := measurableSet_spanningSets μ k
  set u : α → ℝ≥0∞ := fun x => F x ⊓ (n : ℝ≥0∞) with hudef
  have hu : AEMeasurable u μ := hF.inf aemeasurable_const
  have huu : AEMeasurable (fun x => (u x) ^ (q-1)) μ := by
    have h := hu.pow (aemeasurable_const : AEMeasurable (fun _ : α => q - 1) μ)
    simpa using h
  have hidx : (q - 1) * (q / (q - 1)) = q := by
    field_simp
  set A : ℝ≥0∞ := ∫⁻ x in E, (u x) ^ q ∂μ with hAdef
  set A' : ℝ≥0∞ := ∫⁻ x in E, F x * (u x)^(q-1) ∂μ with hA'def
  have hmul : ∫⁻ x, F x * (E.indicator (fun x => (u x)^(q-1))) x ∂μ = A' := by
    have h1 : (fun x => F x * (E.indicator (fun x => (u x)^(q-1))) x)
        = E.indicator (fun x => F x * (u x)^(q-1)) := by
      funext x
      exact (Set.indicator_mul_right E F (fun x => (u x)^(q-1))).symm
    rw [h1, lintegral_indicator hE, hA'def]
  have hpow : ∫⁻ x, (E.indicator (fun x => (u x)^(q-1))) x ^ (q / (q - 1)) ∂μ = A := by
    have h1 : (fun x => (E.indicator (fun x => (u x)^(q-1))) x ^ (q / (q - 1)))
        = E.indicator (fun x => (u x)^q) := by
      funext x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← ENNReal.rpow_mul, hidx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
            ENNReal.zero_rpow_of_pos hpq]
    rw [h1, lintegral_indicator hE, hAdef]
  have hA'bound : A' ≤ C * A ^ ((q-1)/q) := by
    have h1 := h (E.indicator (fun x => (u x)^(q-1))) (huu.indicator hE)
    rw [hmul, hpow] at h1
    exact h1
  have hAA' : A ≤ A' := by
    rw [hAdef, hA'def]
    apply lintegral_mono
    intro x
    have hutop : u x ≠ ⊤ := by
      rw [hudef]
      exact ne_of_lt (lt_of_le_of_lt inf_le_right (ENNReal.natCast_lt_top n))
    calc (u x)^q = (u x)^(q-1) * (u x) := rpow_pred_mul hutop hq
      _ ≤ (u x)^(q-1) * F x := by
          gcongr
          rw [hudef]; exact inf_le_left
      _ = F x * (u x)^(q-1) := mul_comm _ _
  have hbound : A ≤ C * A ^ ((q-1)/q) := le_trans hAA' hA'bound
  have hAfin : A < ⊤ := by
    have h1 : A ≤ ∫⁻ x in E, (n:ℝ≥0∞)^q ∂μ := by
      rw [hAdef]
      apply lintegral_mono
      intro x
      exact ENNReal.rpow_le_rpow inf_le_right hq0.le
    have h2 : ∫⁻ x in E, (n:ℝ≥0∞)^q ∂μ < ⊤ := by
      rw [lintegral_const_restrict]
      exact ENNReal.mul_lt_top
        ((ENNReal.rpow_lt_top_iff_of_pos hq0).mpr (ENNReal.natCast_lt_top n))
        (measure_spanningSets_lt_top μ k)
    exact lt_of_le_of_lt h1 h2
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp]
    exact zero_le
  · have hAtop : A ≠ ⊤ := ne_of_lt hAfin
    have hsplit : A ^ (1/q) * A ^ ((q-1)/q) = A := by
      rw [← ENNReal.rpow_add (1/q) ((q-1)/q) hA0 hAtop]
      rw [show 1/q + (q-1)/q = 1 by rw [← add_div]; field_simp; ring, ENNReal.rpow_one]
    have hcc : A ^ ((q-1)/q) ≠ 0 :=
      (ENNReal.rpow_pos (lt_of_le_of_ne (zero_le) (Ne.symm hA0)) hAtop).ne'
    have hct : A ^ ((q-1)/q) ≠ ⊤ :=
      ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos hs).mpr hAfin)
    have hle : A ^ (1/q) * A ^ ((q-1)/q) ≤ C * A ^ ((q-1)/q) := by
      rw [hsplit]; exact hbound
    exact (ENNReal.mul_le_mul_iff_left hcc hct).mp hle

theorem lintegral_rpow_le_of_forall_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {q : ℝ} (hq : 1 < q) {F : α → ℝ≥0∞} (hF : AEMeasurable F μ)
    {C : ℝ≥0∞}
    (h : ∀ g : α → ℝ≥0∞, AEMeasurable g μ →
      ∫⁻ x, F x * g x ∂μ ≤ C * (∫⁻ x, g x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q)) :
    (∫⁻ x, F x ^ q ∂μ) ^ (1 / q) ≤ C := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hp : 0 < 1 / q := div_pos one_pos hq0
  set f : ℕ → α → ℝ≥0∞ :=
    fun m x => (spanningSets μ m).indicator (fun x => (min (F x) (m:ℝ≥0∞)) ^ q) x with hfdef
  have hAEM : ∀ m, AEMeasurable (f m) μ := by
    intro m
    exact ((hF.inf (aemeasurable_const : AEMeasurable (fun _ : α => (m:ℝ≥0∞)) μ)).pow
      (aemeasurable_const : AEMeasurable (fun _ : α => q) μ)).indicator
      (measurableSet_spanningSets μ m)
  have hmono : ∀ᵐ x ∂μ, Monotone (fun m : ℕ => f m x) := by
    apply Filter.Eventually.of_forall
    intro x m m' hmm'
    simp only [hfdef]
    by_cases hx : x ∈ spanningSets μ m
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (monotone_spanningSets μ hmm' hx)]
      exact ENNReal.rpow_le_rpow (inf_le_inf_left _ (Nat.cast_le.mpr hmm')) hq0.le
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hsup : ∀ x, (⨆ m, f m x) = F x ^ q := by
    intro x
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro m
      simp only [hfdef]
      by_cases hx : x ∈ spanningSets μ m
      · rw [Set.indicator_of_mem hx]
        exact ENNReal.rpow_le_rpow inf_le_left hq0.le
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    · intro w hw
      obtain ⟨k, hk⟩ : ∃ k, x ∈ spanningSets μ k := by
        have : x ∈ ⋃ k, spanningSets μ k := by
          rw [iUnion_spanningSets]; exact mem_univ x
        exact Set.mem_iUnion.mp this
      have hsupn : (⨆ n : ℕ, (min (F x) (n:ℝ≥0∞))^q) = F x ^ q := by
        rw [← Commons.Analysis.Integral.ENNReal.iSup_rpow
              (f := fun n : ℕ => min (F x) (n:ℝ≥0∞)) hq0, iSup_inf_natCast]
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp (by rw [hsupn]; exact hw)
      refine ⟨max k n, ?_⟩
      have hxm : x ∈ spanningSets μ (max k n) := monotone_spanningSets μ (le_max_left k n) hk
      simp only [hfdef]
      rw [Set.indicator_of_mem hxm]
      refine lt_of_lt_of_le hn (ENNReal.rpow_le_rpow ?_ hq0.le)
      exact inf_le_inf_left _ (Nat.cast_le.mpr (le_max_right k n))
  have hconv : ∫⁻ x, F x ^ q ∂μ = ⨆ m, ∫⁻ x, f m x ∂μ := by
    rw [← funext hsup]
    exact lintegral_iSup' hAEM hmono
  have hcore : ∀ m, (∫⁻ x, f m x ∂μ) ^ (1 / q) ≤ C := by
    intro m
    have hfm : ∫⁻ x, f m x ∂μ
        = ∫⁻ x in spanningSets μ m, (min (F x) (m:ℝ≥0∞)) ^ q ∂μ := by
      simp only [hfdef]
      exact lintegral_indicator (measurableSet_spanningSets μ m) _
    rw [hfm]
    exact lintegral_rpow_le_of_forall_mul_le_aux hq hF h m m
  rw [hconv, Commons.Analysis.Integral.ENNReal.iSup_rpow hp]
  exact iSup_le hcore

end Commons.Analysis.Convolution
