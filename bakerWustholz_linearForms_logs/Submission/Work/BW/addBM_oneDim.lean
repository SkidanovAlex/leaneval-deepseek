import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set Pointwise
open scoped ENNReal

/-- Lebesgue measure scales by a nonnegative factor. -/
lemma volume_smul_set {c : ℝ} (hc : 0 ≤ c) (A : Set ℝ) :
    volume (c • A) = ENNReal.ofReal c * volume A := by
  rcases hc.eq_or_lt with rfl | hcpos
  · rw [ENNReal.ofReal_zero, zero_mul]
    have hsub : (0 : ℝ) • A ⊆ ({(0 : ℝ)} : Set ℝ) := by
      intro x hx
      rw [Set.mem_smul_set] at hx
      obtain ⟨a, _ha, hax⟩ := hx
      rw [← hax, Set.mem_singleton_iff, smul_eq_mul, zero_mul]
    refine le_antisymm ?_ bot_le
    calc volume ((0 : ℝ) • A) ≤ volume ({(0 : ℝ)} : Set ℝ) := measure_mono hsub
      _ = 0 := by simp
  · have hset : c • A = (fun x : ℝ => x * c⁻¹) ⁻¹' A := by
      ext x
      simp only [Set.mem_smul_set, Set.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [smul_eq_mul]
        convert ha using 1
        field_simp
      · intro hx
        exact ⟨x * c⁻¹, hx, by rw [smul_eq_mul]; field_simp⟩
    rw [hset, Real.volume_preimage_mul_right (inv_ne_zero hcpos.ne') A, inv_inv,
      abs_of_pos hcpos]

/-- Translation invariance, right. -/
lemma volume_add_singleton (K : Set ℝ) (v : ℝ) : volume (K + {v}) = volume K := by
  rw [Set.add_singleton]
  have h := MeasureTheory.measure_preimage_add_right volume v ((fun x : ℝ => x + v) '' K)
  rw [Set.preimage_image_eq K (fun a b hab => by simpa using hab)] at h
  exact h.symm

/-- Translation invariance, left. -/
lemma volume_singleton_add (u : ℝ) (L : Set ℝ) : volume ({u} + L) = volume L := by
  rw [Set.singleton_add]
  have h := MeasureTheory.measure_preimage_add volume u ((fun x : ℝ => u + x) '' L)
  rw [Set.preimage_image_eq L (fun a b hab => by simpa using hab)] at h
  exact h.symm

/-- 1-dimensional Brunn--Minkowski for compact sets. -/
lemma volume_add_ge_of_isCompact {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  obtain ⟨u, hu, humax⟩ := IsCompact.exists_isMaxOn hK hKne continuousOn_id
  obtain ⟨v, hv, hvmin⟩ := IsCompact.exists_isMinOn hL hLne continuousOn_id
  have hBmeas : MeasurableSet ({u} + L) := by
    rw [Set.singleton_add]
    exact (hL.image (by fun_prop : Continuous (fun x : ℝ => u + x))).measurableSet
  have hinter : (K + {v}) ∩ ({u} + L) ⊆ {u + v} := by
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_add] at hx1 hx2
    obtain ⟨k, hk, w, hw, hkw⟩ := hx1
    obtain ⟨p, hp, l, hl, hpl⟩ := hx2
    simp only [Set.mem_singleton_iff] at hw hp
    rw [hw] at hkw
    rw [hp] at hpl
    rw [Set.mem_singleton_iff]
    have h1 : x ≤ u + v := by rw [← hkw]; exact add_le_add (humax hk) le_rfl
    have h2 : u + v ≤ x := by rw [← hpl]; exact add_le_add le_rfl (hvmin hl)
    exact le_antisymm h1 h2
  have h0 : volume ((K + {v}) ∩ ({u} + L)) = 0 :=
    measure_mono_null hinter (by simp)
  have hunion : volume ((K + {v}) ∪ ({u} + L)) = volume (K + {v}) + volume ({u} + L) := by
    have h := measure_union_add_inter (μ := volume) (K + {v}) hBmeas
    rw [h0, add_zero] at h
    exact h
  calc volume K + volume L
      = volume (K + {v}) + volume ({u} + L) := by rw [volume_add_singleton, volume_singleton_add]
    _ = volume ((K + {v}) ∪ ({u} + L)) := hunion.symm
    _ ≤ volume (K + L) := by
        refine measure_mono ?_
        exact union_subset
          (Set.add_subset_add (Subset.refl K) (Set.singleton_subset_iff.mpr hv))
          (Set.add_subset_add (Set.singleton_subset_iff.mpr hu) (Subset.refl L))

/-- 1-dimensional Brunn--Minkowski for measurable sets. -/
lemma volume_add_ge {A B : Set ℝ} (hAm : MeasurableSet A) (hAne : A.Nonempty)
    (hBm : MeasurableSet B) (hBne : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  rcases eq_or_ne (volume A) 0 with hA0 | hAz
  · obtain ⟨a0, ha0⟩ := hAne
    have hsub : ({a0} : Set ℝ) + B ⊆ A + B :=
      Set.add_subset_add (Set.singleton_subset_iff.mpr ha0) (Subset.refl B)
    calc volume A + volume B = volume B := by rw [hA0, zero_add]
      _ = volume (({a0} : Set ℝ) + B) := (volume_singleton_add a0 B).symm
      _ ≤ volume (A + B) := measure_mono hsub
  rcases eq_or_ne (volume B) 0 with hB0 | hBz
  · obtain ⟨b0, hb0⟩ := hBne
    have hsub : A + {b0} ⊆ A + B :=
      Set.add_subset_add (Subset.refl A) (Set.singleton_subset_iff.mpr hb0)
    calc volume A + volume B = volume A := by rw [hB0, add_zero]
      _ = volume (A + {b0}) := (volume_add_singleton A b0).symm
      _ ≤ volume (A + B) := measure_mono hsub
  refine le_of_forall_lt fun d hd => ?_
  obtain ⟨p, hp, q, hq, hpq⟩ := ENNReal.exists_lt_add_of_lt_add hd hAz hBz
  obtain ⟨K, hKA, hKc, hKp⟩ := hAm.exists_lt_isCompact hp
  obtain ⟨L, hLB, hLc, hLq⟩ := hBm.exists_lt_isCompact hq
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with h0 | h
    · rw [h0, measure_empty] at hKp
      exact absurd hKp (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ p by positivity))
    · exact h
  have hLne : L.Nonempty := by
    rcases L.eq_empty_or_nonempty with h0 | h
    · rw [h0, measure_empty] at hLq
      exact absurd hLq (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ q by positivity))
    · exact h
  have h1 : d < volume K + volume L := lt_trans hpq (ENNReal.add_lt_add hKp hLq)
  have h2 : volume K + volume L ≤ volume (A + B) :=
    le_trans (volume_add_ge_of_isCompact hKc hLc hKne hLne)
      (measure_mono (Set.add_subset_add hKA hLB))
  exact lt_of_lt_of_le h1 h2

/-- Scalar multiples of measurable nonempty sets are measurable. -/
lemma measurableSet_smul_set {c : ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hAne : A.Nonempty) :
    MeasurableSet (c • A) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hz : (0 : ℝ) • A = {0} := by
      ext x
      rw [Set.mem_smul_set, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, _ha, rfl⟩
        rw [smul_eq_mul, zero_mul]
      · intro hx
        obtain ⟨a, ha⟩ := hAne
        exact ⟨a, ha, by rw [smul_eq_mul, zero_mul, hx]⟩
    rw [hz]
    exact measurableSet_singleton 0
  · have hset : c • A = (fun x : ℝ => x * c⁻¹) ⁻¹' A := by
      ext x
      simp only [Set.mem_smul_set, Set.mem_preimage]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [smul_eq_mul]
        convert ha using 1
        field_simp
      · intro hx
        exact ⟨x * c⁻¹, hx, by rw [smul_eq_mul]; field_simp⟩
    rw [hset]
    exact hA.preimage (by fun_prop : Measurable (fun x : ℝ => x * c⁻¹))

theorem addBM_oneDim {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    volume (lam • A + (1 - lam) • B) ≥ ENNReal.ofReal lam * volume A + ENNReal.ofReal (1 - lam) * volume B := by
  have h1' : 0 ≤ 1 - lam := sub_nonneg.mpr h1
  have hneA : (lam • A).Nonempty := by
    rw [← Set.image_smul]
    exact hA.image (fun x => lam • x)
  have hneB : ((1 - lam) • B).Nonempty := by
    rw [← Set.image_smul]
    exact hB.image (fun x => (1 - lam) • x)
  have hcore := volume_add_ge (measurableSet_smul_set hAm hA) hneA
    (measurableSet_smul_set hBm hB) hneB
  rw [volume_smul_set h0, volume_smul_set h1'] at hcore
  exact hcore

end Work.BW
