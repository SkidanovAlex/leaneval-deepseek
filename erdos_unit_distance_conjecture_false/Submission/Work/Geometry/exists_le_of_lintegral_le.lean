import Mathlib

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise ENNReal

/-- Auxiliary: a set that is null for the restricted measure `μ.restrict s` has null
intersection with `s`. -/
theorem measure_inter_eq_zero_of_restrict_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s Z : Set α) (hZ : μ.restrict s Z = 0) : μ (Z ∩ s) = 0 := by
  obtain ⟨W, hZW, hWm, hW0⟩ := exists_measurable_superset_of_null hZ
  refine measure_mono_null (Set.inter_subset_inter hZW (subset_refl s)) ?_
  rw [← Measure.restrict_apply hWm]
  exact hW0

/-- Auxiliary: if two a.e.-measurable functions satisfy `f a ≤ g a` on all of `s`, then
`f ≤ g` almost everywhere for the restricted measure `μ.restrict s`. -/
theorem ae_le_restrict_of_forall_mem_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) {f g : α → ENNReal}
    (hf : AEMeasurable f (μ.restrict s)) (hg : AEMeasurable g (μ.restrict s))
    (h : ∀ a ∈ s, f a ≤ g a) : f ≤ᵐ[μ.restrict s] g := by
  set f' := hf.mk f with hf'def
  set g' := hg.mk g with hg'def
  have hf'm : Measurable f' := hf.measurable_mk
  have hg'm : Measurable g' := hg.measurable_mk
  have hff' : f =ᵐ[μ.restrict s] f' := hf.ae_eq_mk
  have hgg' : g =ᵐ[μ.restrict s] g' := hg.ae_eq_mk
  have hNf : μ.restrict s {a | ¬ f a = f' a} = 0 := ae_iff.mp hff'
  have hNg : μ.restrict s {a | ¬ g a = g' a} = 0 := ae_iff.mp hgg'
  have hU : MeasurableSet {a | g' a < f' a} := measurableSet_lt hg'm hf'm
  have hU0 : μ.restrict s {a | g' a < f' a} = 0 := by
    rw [Measure.restrict_apply hU]
    refine measure_mono_null ?_
      (measure_inter_eq_zero_of_restrict_eq_zero μ s _ (measure_union_null hNf hNg))
    rintro a ⟨hga, has⟩
    change g' a < f' a at hga
    refine ⟨?_, has⟩
    by_cases h1 : f a = f' a
    · by_cases h2 : g a = g' a
      · exfalso
        have hlt : g a < f a := by rw [← h2, ← h1] at hga; exact hga
        exact absurd (h a has) (not_le.mpr hlt)
      · exact Or.inr h2
    · exact Or.inl h1
  refine ae_iff.mpr ?_
  refine measure_mono_null
    (t := ({a | ¬ f a = f' a} ∪ {a | ¬ g a = g' a}) ∪ {a | g' a < f' a}) ?_ ?_
  · intro a ha
    change ¬ f a ≤ g a at ha
    by_cases h1 : f a = f' a
    · by_cases h2 : g a = g' a
      · exact Or.inr (by change g' a < f' a; rw [← h2, ← h1]; exact not_le.mp ha)
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  · refine le_antisymm ?_ zero_le
    calc μ.restrict s ({a | ¬ f a = f' a} ∪ {a | ¬ g a = g' a} ∪ {a | g' a < f' a})
        ≤ μ.restrict s ({a | ¬ f a = f' a} ∪ {a | ¬ g a = g' a}) + μ.restrict s {a | g' a < f' a} :=
          measure_union_le _ _
      _ = 0 := by rw [measure_union_null hNf hNg, hU0, add_zero]

theorem exists_le_of_lintegral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (n e : α → ℕ) (C : ℝ) (hC : 0 ≤ C) (K₀ : ℕ)
    (hn : AEMeasurable (fun a => (n a : ENNReal)) (μ.restrict s))
    (he : AEMeasurable (fun a => (e a : ENNReal)) (μ.restrict s))
    (hnK : ∀ a ∈ s, n a ≤ K₀) (heK : ∀ a ∈ s, e a ≤ n a * n a)
    (hpos : 0 < ∫⁻ a in s, (n a : ENNReal) ∂μ)
    (hfin : ∫⁻ a in s, (n a : ENNReal) ∂μ < ∞)
    (hint : ENNReal.ofReal C * (∫⁻ a in s, (n a : ENNReal) ∂μ) ≤ ∫⁻ a in s, (e a : ENNReal) ∂μ) :
    ∃ a ∈ s, 1 ≤ n a ∧ C * (n a : ℝ) ≤ (e a : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  -- pointwise bound on `s`
  have hpt : ∀ a ∈ s, (e a : ENNReal) ≤ ENNReal.ofReal C * (n a : ENNReal) := by
    intro a ha
    rcases Nat.eq_zero_or_pos (n a) with h0 | hposa
    · have he0 : e a = 0 := by
        have hh := heK a ha
        rw [h0] at hh
        simpa using hh
      simp [he0, h0]
    · have hge1 : 1 ≤ n a := by omega
      have hlt : (e a : ℝ) < C * (n a : ℝ) := hcon a ha hge1
      have hposC : 0 < C * (n a : ℝ) := (Nat.cast_nonneg (e a)).trans_lt hlt
      calc (e a : ENNReal) = ENNReal.ofReal (e a : ℝ) := (ENNReal.ofReal_natCast (e a)).symm
        _ ≤ ENNReal.ofReal (C * (n a : ℝ)) := ENNReal.ofReal_le_ofReal hlt.le
        _ = ENNReal.ofReal C * (n a : ENNReal) := by
              rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_natCast]
  have hle_ae : (fun a => (e a : ENNReal)) ≤ᵐ[μ.restrict s]
      (fun a => ENNReal.ofReal C * (n a : ENNReal)) :=
    ae_le_restrict_of_forall_mem_le μ s he (hn.const_mul (ENNReal.ofReal C)) hpt
  have hbdd : (fun a => (e a : ENNReal)) ≤ᵐ[μ.restrict s]
      (fun a => (K₀ : ENNReal) * (n a : ENNReal)) :=
    ae_le_restrict_of_forall_mem_le μ s he (hn.const_mul (K₀ : ENNReal)) fun a ha => by
      calc (e a : ENNReal) ≤ ((n a * n a : ℕ) : ENNReal) := by exact_mod_cast heK a ha
        _ ≤ ((K₀ * n a : ℕ) : ENNReal) := by exact_mod_cast Nat.mul_le_mul_right (n a) (hnK a ha)
        _ = (K₀ : ENNReal) * (n a : ENNReal) := by rw [Nat.cast_mul]
  have he_ne_top : ∫⁻ a, (e a : ENNReal) ∂(μ.restrict s) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbdd)
    rw [lintegral_const_mul'' (K₀ : ENNReal) hn]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top K₀) (ne_of_lt hfin)
  -- the set where the pointwise bound is strict has positive (restricted) measure
  have hlt_null : μ.restrict s {a | (e a : ENNReal) < ENNReal.ofReal C * (n a : ENNReal)} ≠ 0 := by
    intro hz0
    have h1 : μ.restrict s {a | ENNReal.ofReal C * (n a : ENNReal) < (e a : ENNReal)} = 0 := by
      have hh := ae_iff.mp hle_ae
      simpa only [not_le] using hh
    have hNE : μ.restrict s ({a | (e a : ENNReal) < ENNReal.ofReal C * (n a : ENNReal)} ∪
        {a | ENNReal.ofReal C * (n a : ENNReal) < (e a : ENNReal)}) = 0 :=
      measure_union_null hz0 h1
    have hNE' : μ.restrict s {a | (e a : ENNReal) ≠ ENNReal.ofReal C * (n a : ENNReal)} = 0 :=
      measure_mono_null (fun a ha => lt_or_gt_of_ne ha) hNE
    have hNE'' : μ ({a | (e a : ENNReal) ≠ ENNReal.ofReal C * (n a : ENNReal)} ∩ s) = 0 :=
      measure_inter_eq_zero_of_restrict_eq_zero μ s _ hNE'
    set F' := hn.mk (fun a => (n a : ENNReal)) with hF'def
    have hF'm : Measurable F' := hn.measurable_mk
    have hFF' : (fun a => (n a : ENNReal)) =ᵐ[μ.restrict s] F' := hn.ae_eq_mk
    have hNF : μ ({a | ¬ (n a : ENNReal) = F' a} ∩ s) = 0 :=
      measure_inter_eq_zero_of_restrict_eq_zero μ s _ (ae_iff.mp hFF')
    have hcover : {a | ¬ F' a = 0} ∩ s ⊆ ({a | ¬ (n a : ENNReal) = F' a} ∩ s) ∪
        ({a | (e a : ENNReal) ≠ ENNReal.ofReal C * (n a : ENNReal)} ∩ s) := by
      rintro a ⟨haF', has⟩
      by_cases hcase : (n a : ENNReal) = F' a
      · right
        refine ⟨?_, has⟩
        have hn0 : n a ≠ 0 := by
          intro h0
          exact haF' (by rw [← hcase, h0]; simp)
        have hge1 : 1 ≤ n a := by omega
        have hlt : (e a : ℝ) < C * (n a : ℝ) := hcon a has hge1
        have hposC : 0 < C * (n a : ℝ) := (Nat.cast_nonneg (e a)).trans_lt hlt
        have hstrict : (e a : ENNReal) < ENNReal.ofReal C * (n a : ENNReal) := by
          calc (e a : ENNReal) = ENNReal.ofReal (e a : ℝ) := (ENNReal.ofReal_natCast (e a)).symm
            _ < ENNReal.ofReal (C * (n a : ℝ)) := (ENNReal.ofReal_lt_ofReal_iff hposC).mpr hlt
            _ = ENNReal.ofReal C * (n a : ENNReal) := by
                  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_natCast]
        exact hstrict.ne
      · left
        exact ⟨hcase, has⟩
    have hF'0 : μ ({a | ¬ F' a = 0} ∩ s) = 0 :=
      measure_mono_null hcover (measure_union_null hNF hNE'')
    have hF'null : μ.restrict s {a | ¬ F' a = 0} = 0 := by
      rw [Measure.restrict_apply]
      · exact hF'0
      · convert (hF'm (measurableSet_singleton (0 : ENNReal))).compl using 1
        ext a
        simp [eq_comm]
    have hzero : ∫⁻ a, (n a : ENNReal) ∂(μ.restrict s) = 0 := by
      rw [lintegral_congr_ae hFF', lintegral_eq_zero_iff hF'm]
      exact ae_iff.mpr hF'null
    exact absurd (by simpa using hzero) (ne_of_gt hpos)
  have hfreq : ∃ᵐ a ∂μ.restrict s, (e a : ENNReal) ≠ ENNReal.ofReal C * (n a : ENNReal) := by
    rw [frequently_ae_iff]
    exact fun hz => hlt_null (measure_mono_null (fun a ha => ha.ne) hz)
  -- strict monotonicity contradicts the hypothesis
  have hstrict := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
      (f := fun a => (e a : ENNReal)) (g := fun a => ENNReal.ofReal C * (n a : ENNReal))
      (hn.const_mul (ENNReal.ofReal C)) he_ne_top hle_ae hfreq
  rw [lintegral_const_mul'' (ENNReal.ofReal C) hn] at hstrict
  exact absurd (lt_of_le_of_lt hint hstrict) (lt_irrefl _)

end Work.Geometry
