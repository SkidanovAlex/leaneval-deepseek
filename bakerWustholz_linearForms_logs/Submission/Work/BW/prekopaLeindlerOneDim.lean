import Mathlib
import Submission.Work.BW.addBM_oneDim
import Submission.Work.BW.layerCakeENNRealLe
import Submission.Work.BW.ennrealGeomMeanLeArithMean
import Submission.Work.BW.addBMnullMeasurable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set Pointwise
open scoped ENNReal

/-! ## Prékopa–Leindler in one dimension -/

/-! ### Order-theoretic helpers for `essSup` -/

lemma essSup_le_of_ae_le {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ᵐ x ∂volume, f x ≤ c) :
    essSup f volume ≤ c := by
  rw [essSup_eq_sInf]
  apply sInf_le
  change volume {x | c < f x} = 0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h] with x hx
  exact not_lt.mpr hx

lemma ne_empty_of_lt_essSup {f : ℝ → ℝ≥0∞} {u : ℝ≥0∞} (h : u < essSup f volume) :
    {x | u ≤ f x}.Nonempty := by
  by_contra hc
  have hlt : ∀ x, f x < u := by
    intro x
    by_contra hx
    exact hc ⟨x, not_lt.mp hx⟩
  exact absurd
    (lt_of_lt_of_le h (essSup_le_of_ae_le (Filter.Eventually.of_forall (fun x => (hlt x).le))))
    (lt_irrefl _)

lemma ae_le_one_of_essSup_eq_one {f : ℝ → ℝ≥0∞} (hf : essSup f volume = 1) :
    ∀ᵐ x ∂volume, f x ≤ 1 := by
  have h := ENNReal.ae_le_essSup (f := f) (μ := volume)
  rwa [hf] at h

lemma antitone_volume_level (f : ℝ → ℝ≥0∞) :
    Antitone (fun w : ℝ => volume {x | ENNReal.ofReal w ≤ f x}) := by
  intro w1 w2 h12
  apply measure_mono
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact le_trans (ENNReal.ofReal_le_ofReal h12) hx

lemma lintegral_Ioi_eq_Ioo_zero {G : ℝ → ℝ≥0∞} (hG : ∀ w, 1 < w → G w = 0) :
    ∫⁻ w in Set.Ioi 0, G w = ∫⁻ w in Set.Ioo 0 1, G w := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (by simp : volume ({1} : Set ℝ) = 0)] with w hw
  rw [Set.mem_singleton_iff] at hw
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h0 : 0 < w
  · by_cases h1 : w < 1
    · rw [if_pos (show w ∈ Set.Ioi 0 from h0), if_pos (show w ∈ Set.Ioo 0 1 from ⟨h0, h1⟩)]
    · have h1' : 1 < w := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hw)
      rw [if_pos (show w ∈ Set.Ioi 0 from h0),
        if_neg (show w ∉ Set.Ioo 0 1 from by simp [h1]), hG w h1']
  · rw [if_neg (show w ∉ Set.Ioi 0 from by simpa using h0),
      if_neg (show w ∉ Set.Ioo 0 1 from by simp [h0])]

/-! ### A real-arithmetic helper -/

lemma exists_rpow_mul_ge (K : ℝ) {l d : ℝ} (hl : 0 < l) (hd : 0 < d) :
    ∃ a : ℝ, 0 < a ∧ K ≤ a ^ l * d := by
  by_cases hK : K ≤ 0
  · exact ⟨1, one_pos, le_trans hK (by positivity)⟩
  · push_neg at hK
    have hKd : 0 < K / d := div_pos hK hd
    refine ⟨(K / d) ^ l⁻¹ + 1, by positivity, ?_⟩
    have hpow : ((K / d) ^ l⁻¹) ^ l = K / d := by
      rw [← Real.rpow_mul hKd.le, inv_mul_cancel₀ hl.ne', Real.rpow_one]
    have hle : (K / d) ^ l⁻¹ ≤ (K / d) ^ l⁻¹ + 1 := le_add_of_nonneg_right zero_le_one
    calc K = (K / d) * d := by rw [div_mul_cancel₀ _ hd.ne']
      _ = ((K / d) ^ l⁻¹) ^ l * d := by rw [hpow]
      _ ≤ ((K / d) ^ l⁻¹ + 1) ^ l * d :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hle hl.le) hd.le

/-! ### The level-set inclusion -/

lemma level_subset {f g m : ℝ → ℝ≥0∞} {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, m (lam * x + (1 - lam) * y) ≥ f x ^ lam * g y ^ (1 - lam))
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    lam • {x | ENNReal.ofReal u ≤ f x} + (1 - lam) • {y | ENNReal.ofReal v ≤ g y}
      ⊆ {z | ENNReal.ofReal (u ^ lam * v ^ (1 - lam)) ≤ m z} := by
  intro z hz
  rw [Set.mem_add] at hz
  obtain ⟨a, ha, b, hb, hab⟩ := hz
  rw [Set.mem_smul_set] at ha hb
  obtain ⟨x, hx, hxa⟩ := ha
  obtain ⟨y, hy, hyb⟩ := hb
  rw [Set.mem_setOf_eq] at hx hy ⊢
  rw [← hxa, ← hyb, smul_eq_mul, smul_eq_mul] at hab
  rw [← hab]
  have hx' : ENNReal.ofReal u ^ lam ≤ f x ^ lam := ENNReal.rpow_le_rpow hx h0.le
  have hy' : ENNReal.ofReal v ^ (1 - lam) ≤ g y ^ (1 - lam) :=
    ENNReal.rpow_le_rpow hy (by linarith)
  rw [ENNReal.ofReal_rpow_of_nonneg hu.le h0.le] at hx'
  rw [ENNReal.ofReal_rpow_of_nonneg hv.le (by linarith : (0 : ℝ) ≤ 1 - lam)] at hy'
  calc ENNReal.ofReal (u ^ lam * v ^ (1 - lam))
      = ENNReal.ofReal (u ^ lam) * ENNReal.ofReal (v ^ (1 - lam)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)
    _ ≤ f x ^ lam * g y ^ (1 - lam) := mul_le_mul' hx' hy'
    _ ≤ m (lam * x + (1 - lam) * y) := h x y

/-! ### The normalized core -/

theorem coreNormalized {f g m : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) (hm : AEMeasurable m volume) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, m (lam * x + (1 - lam) * y) ≥ f x ^ lam * g y ^ (1 - lam))
    (hf1 : essSup f volume = 1) (hg1 : essSup g volume = 1) :
    ∫⁻ x, m x ≥ (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) := by
  have hlayf : ∫⁻ w in Set.Ioi 0, volume {x | ENNReal.ofReal w ≤ f x} = ∫⁻ x, f x :=
    (layerCakeENNRealLe volume f hf).symm
  have hlayg : ∫⁻ w in Set.Ioi 0, volume {x | ENNReal.ofReal w ≤ g x} = ∫⁻ x, g x :=
    (layerCakeENNRealLe volume g hg).symm
  have hlaym : ∫⁻ w in Set.Ioi 0, volume {z | ENNReal.ofReal w ≤ m z} = ∫⁻ z, m z :=
    (layerCakeENNRealLe volume m hm).symm
  have hnullf : volume {x | (1 : ℝ≥0∞) < f x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_le_one_of_essSup_eq_one hf1] with x hx
    exact not_lt.mpr hx
  have hnullg : volume {x | (1 : ℝ≥0∞) < g x} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_le_one_of_essSup_eq_one hg1] with x hx
    exact not_lt.mpr hx
  have hAzero : ∀ w, 1 < w → volume {x | ENNReal.ofReal w ≤ f x} = 0 := by
    intro w hw
    apply measure_mono_null _ hnullf
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le (ENNReal.one_lt_ofReal.mpr hw) hx
  have hBzero : ∀ w, 1 < w → volume {x | ENNReal.ofReal w ≤ g x} = 0 := by
    intro w hw
    apply measure_mono_null _ hnullg
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le (ENNReal.one_lt_ofReal.mpr hw) hx
  have hAvol : ∫⁻ w in Set.Ioo 0 1, volume {x | ENNReal.ofReal w ≤ f x} = ∫⁻ x, f x := by
    rw [← lintegral_Ioi_eq_Ioo_zero hAzero, hlayf]
  have hBvol : ∫⁻ w in Set.Ioo 0 1, volume {x | ENNReal.ofReal w ≤ g x} = ∫⁻ x, g x := by
    rw [← lintegral_Ioi_eq_Ioo_zero hBzero, hlayg]
  have hCvol : ∫⁻ w in Set.Ioo 0 1, volume {z | ENNReal.ofReal w ≤ m z} ≤ ∫⁻ z, m z :=
    le_trans (lintegral_mono_set Set.Ioo_subset_Ioi_self) hlaym.le
  have hkey : ∀ w ∈ Set.Ioo 0 1,
      volume {z | ENNReal.ofReal w ≤ m z} ≥
        ENNReal.ofReal lam * volume {x | ENNReal.ofReal w ≤ f x}
          + ENNReal.ofReal (1 - lam) * volume {y | ENNReal.ofReal w ≤ g y} := by
    intro w hw
    have hww : w ^ lam * w ^ (1 - lam) = w := by
      rw [← Real.rpow_add hw.1, show lam + (1 - lam) = 1 by ring, Real.rpow_one]
    have hset : {z | ENNReal.ofReal (w ^ lam * w ^ (1 - lam)) ≤ m z}
        = {z | ENNReal.ofReal w ≤ m z} := by rw [hww]
    have hsub := (level_subset h0 h1 h hw.1 hw.1)
    rw [hset] at hsub
    refine le_trans (addBMnullMeasurable ?_ ?_ ?_ ?_ h0.le h1.le) (measure_mono hsub)
    · exact hf.nullMeasurableSet_preimage measurableSet_Ici
    · exact hg.nullMeasurableSet_preimage measurableSet_Ici
    · exact ne_empty_of_lt_essSup (by rw [hf1]; exact ENNReal.ofReal_lt_one.mpr hw.2)
    · exact ne_empty_of_lt_essSup (by rw [hg1]; exact ENNReal.ofReal_lt_one.mpr hw.2)
  have hIntC : ∫⁻ w in Set.Ioo 0 1,
        ENNReal.ofReal lam * volume {x | ENNReal.ofReal w ≤ f x}
          + ENNReal.ofReal (1 - lam) * volume {y | ENNReal.ofReal w ≤ g y}
      ≤ ∫⁻ w in Set.Ioo 0 1, volume {z | ENNReal.ofReal w ≤ m z} := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with w hw
    exact hkey w hw
  have hsplit : ∫⁻ w in Set.Ioo 0 1,
        (ENNReal.ofReal lam * volume {x | ENNReal.ofReal w ≤ f x}
          + ENNReal.ofReal (1 - lam) * volume {y | ENNReal.ofReal w ≤ g y})
      = ENNReal.ofReal lam * (∫⁻ x, f x) + ENNReal.ofReal (1 - lam) * (∫⁻ x, g x) := by
    rw [lintegral_add_left']
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hAvol, hBvol]
    · exact (measurable_const.mul
        (Antitone.measurable (antitone_volume_level f))).aemeasurable
  calc ∫⁻ x, m x ≥ ∫⁻ w in Set.Ioo 0 1, volume {z | ENNReal.ofReal w ≤ m z} := hCvol
    _ ≥ ∫⁻ w in Set.Ioo 0 1,
          (ENNReal.ofReal lam * volume {x | ENNReal.ofReal w ≤ f x}
            + ENNReal.ofReal (1 - lam) * volume {y | ENNReal.ofReal w ≤ g y}) := hIntC
    _ = ENNReal.ofReal lam * (∫⁻ x, f x) + ENNReal.ofReal (1 - lam) * (∫⁻ x, g x) := hsplit
    _ ≥ (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) :=
        ennrealGeomMeanLeArithMean h0.le h1.le _ _

/-! ### Normalization to `essSup = 1` -/

lemma essSup_const_mul_eq_one {f : ℝ → ℝ≥0∞} {M : ℝ≥0∞} (hM0 : M ≠ 0) (hMt : M ≠ ⊤)
    (h : essSup f volume = M) : essSup (fun x => M⁻¹ * f x) volume = 1 := by
  rw [ENNReal.essSup_const_mul, h, ENNReal.inv_mul_cancel hM0 hMt]

lemma ennorm_unwind {a b P Q : ℝ≥0∞} (hP0 : P ≠ 0) (hPt : P ≠ ⊤) (hQ0 : Q ≠ 0)
    (hQt : Q ≠ ⊤) :
    (P * Q) * ((P⁻¹ * a) * (Q⁻¹ * b)) = a * b := by
  rw [show (P * Q) * ((P⁻¹ * a) * (Q⁻¹ * b)) = (P * P⁻¹) * (Q * Q⁻¹) * (a * b)
        from by ac_rfl,
    ENNReal.mul_inv_cancel hP0 hPt, ENNReal.mul_inv_cancel hQ0 hQt]
  simp

private lemma finiteCase {f g m : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hm : AEMeasurable m volume) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, m (lam * x + (1 - lam) * y) ≥ f x ^ lam * g y ^ (1 - lam))
    (hfpos : 0 < ∫⁻ x, f x) (hgpos : 0 < ∫⁻ x, g x)
    (hft : essSup f volume ≠ ⊤) (hgt : essSup g volume ≠ ⊤) :
    ∫⁻ x, m x ≥ (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) := by
  set M := essSup f volume with hMdef
  set N := essSup g volume with hNdef
  have hM0 : M ≠ 0 := by
    intro hM
    have h0' : essSup f volume = 0 := by rw [← hMdef]; exact hM
    have hf0 : f =ᵐ[volume] 0 := ENNReal.essSup_eq_zero_iff.mp h0'
    have hz : ∫⁻ x, f x = 0 := by rw [lintegral_congr_ae hf0]; simp
    exact hfpos.ne' hz
  have hN0 : N ≠ 0 := by
    intro hM
    have h0' : essSup g volume = 0 := by rw [← hNdef]; exact hM
    have hg0 : g =ᵐ[volume] 0 := ENNReal.essSup_eq_zero_iff.mp h0'
    have hz : ∫⁻ x, g x = 0 := by rw [lintegral_congr_ae hg0]; simp
    exact hgpos.ne' hz
  set c := M ^ lam * N ^ (1 - lam) with hcdef
  have hMpow0 : M ^ lam ≠ 0 :=
    (ENNReal.rpow_pos_of_nonneg (bot_lt_iff_ne_bot.mpr hM0) h0.le).ne'
  have hMpowt : M ^ lam ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h0.le hft
  have hNpow0 : N ^ (1 - lam) ≠ 0 :=
    (ENNReal.rpow_pos_of_nonneg (bot_lt_iff_ne_bot.mpr hN0) (by linarith)).ne'
  have hNpowt : N ^ (1 - lam) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hgt
  have hc0 : c ≠ 0 := mul_ne_zero hMpow0 hNpow0
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top hMpowt hNpowt
  have h' : ∀ x y, (fun z => c⁻¹ * m z) (lam * x + (1 - lam) * y)
      ≥ (fun x => M⁻¹ * f x) x ^ lam * (fun y => N⁻¹ * g y) y ^ (1 - lam) := by
    intro x y
    have hEq : (M⁻¹ * f x) ^ lam * (N⁻¹ * g y) ^ (1 - lam)
        = c⁻¹ * (f x ^ lam * g y ^ (1 - lam)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ h0.le, ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
        ENNReal.inv_rpow, ENNReal.inv_rpow, hcdef,
        ENNReal.mul_inv (Or.inl hMpow0) (Or.inl hMpowt)]
      ac_rfl
    exact le_trans (le_of_eq hEq) (mul_le_mul' le_rfl (h x y))
  have hcore := coreNormalized (hf.const_mul M⁻¹) (hg.const_mul N⁻¹) (hm.const_mul c⁻¹)
    h0 h1 h' (essSup_const_mul_eq_one hM0 hft hMdef) (essSup_const_mul_eq_one hN0 hgt hNdef)
  have hIf : ∫⁻ x, (fun x => M⁻¹ * f x) x = M⁻¹ * ∫⁻ x, f x :=
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hM0)
  have hIg : ∫⁻ x, (fun x => N⁻¹ * g x) x = N⁻¹ * ∫⁻ x, g x :=
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hN0)
  have hIc : ∫⁻ x, (fun z => c⁻¹ * m z) x = c⁻¹ * ∫⁻ x, m x :=
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)
  rw [hIf, hIg, hIc] at hcore
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0.le, ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
    ENNReal.inv_rpow, ENNReal.inv_rpow] at hcore
  have hceq : ∫⁻ x, m x = c * (c⁻¹ * ∫⁻ x, m x) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
  have hmul : c * (((M ^ lam)⁻¹ * (∫⁻ x, f x) ^ lam) * ((N ^ (1 - lam))⁻¹ * (∫⁻ x, g x) ^ (1 - lam)))
      = (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) :=
    ennorm_unwind hMpow0 hMpowt hNpow0 hNpowt
  calc ∫⁻ x, m x = c * (c⁻¹ * ∫⁻ x, m x) := hceq
    _ ≥ c * (((M ^ lam)⁻¹ * (∫⁻ x, f x) ^ lam) * ((N ^ (1 - lam))⁻¹ * (∫⁻ x, g x) ^ (1 - lam))) :=
        mul_le_mul' le_rfl hcore
    _ = (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) := hmul

/-! ### The degenerate case `essSup = ⊤` -/

lemma exists_pos_measure_level {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g volume)
    (h : 0 < ∫⁻ x, g x) :
    ∃ b : ℝ, 0 < b ∧ 0 < volume {x | ENNReal.ofReal b ≤ g x} := by
  by_contra hc
  push_neg at hc
  have hc' : ∀ b, 0 < b → volume {x | ENNReal.ofReal b ≤ g x} = 0 := by
    intro b hb
    exact le_antisymm (hc b hb) (zero_le)
  have h2 : (∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t ≤ g x}) = 0 := by
    change ∫⁻ t, volume {x | ENNReal.ofReal t ≤ g x} ∂(volume.restrict (Set.Ioi 0)) = 0
    rw [lintegral_eq_zero_iff' (Antitone.measurable (antitone_volume_level g)).aemeasurable]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hc' t ht
  have hz : ∫⁻ x, g x = 0 := by rw [layerCakeENNRealLe volume g hg, h2]
  exact h.ne' hz

lemma const_mul_measure_le_lintegral {m : ℝ → ℝ≥0∞} (hm : AEMeasurable m volume) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal t * volume {z | ENNReal.ofReal t ≤ m z} ≤ ∫⁻ z, m z := by
  rw [layerCakeENNRealLe volume m hm]
  have hbase : ENNReal.ofReal t * volume {z | ENNReal.ofReal t ≤ m z}
      = ∫⁻ s in Set.Ioc 0 t, volume {z | ENNReal.ofReal t ≤ m z} := by
    rw [MeasureTheory.setLIntegral_const (Set.Ioc 0 t) (volume {z | ENNReal.ofReal t ≤ m z})]
    rw [Real.volume_Ioc, sub_zero, mul_comm]
  rw [hbase]
  calc ∫⁻ s in Set.Ioc 0 t, volume {z | ENNReal.ofReal t ≤ m z}
      ≤ ∫⁻ s in Set.Ioc 0 t, volume {z | ENNReal.ofReal s ≤ m z} := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
        apply measure_mono
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        exact le_trans (ENNReal.ofReal_le_ofReal hs.2) hz
    _ ≤ ∫⁻ s in Set.Ioi 0, volume {z | ENNReal.ofReal s ≤ m z} :=
        lintegral_mono_set Set.Ioc_subset_Ioi_self

lemma topCaseAux {p q m : ℝ → ℝ≥0∞} (hp : AEMeasurable p volume) (hq : AEMeasurable q volume)
    (hm : AEMeasurable m volume) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, m (lam * x + (1 - lam) * y) ≥ p x ^ lam * q y ^ (1 - lam))
    (hptop : essSup p volume = ⊤) (hqpos : 0 < ∫⁻ y, q y) :
    ∫⁻ z, m z = ⊤ := by
  obtain ⟨b, hb0, hbvol⟩ := exists_pos_measure_level hq hqpos
  set B : Set ℝ := {y | ENNReal.ofReal b ≤ q y} with hBdef
  obtain ⟨δ, hδ0, hδD⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ volume B := by
    by_cases hD : volume B = ⊤
    · exact ⟨1, one_pos, by rw [hD]; exact le_top⟩
    · exact ⟨(volume B).toReal, ENNReal.toReal_pos hbvol.ne' hD,
        le_of_eq (ENNReal.ofReal_toReal hD)⟩
  refine le_antisymm le_top ?_
  refine le_of_forall_lt ?_
  intro c hc
  obtain ⟨a, ha0, ha⟩ := exists_rpow_mul_ge ((c.toReal + 1) / ((1 - lam) * δ))
    (d := b ^ (1 - lam)) h0 (by positivity)
  have hne : ({x | ENNReal.ofReal a ≤ p x} : Set ℝ).Nonempty := by
    refine ne_empty_of_lt_essSup ?_
    rw [hptop]; exact ENNReal.ofReal_lt_top
  obtain ⟨x0, hx0⟩ := hne
  have hsub := level_subset h0 h1 h ha0 hb0
  have h2 : lam • ({x0} : Set ℝ) + (1 - lam) • B
      ⊆ {z | ENNReal.ofReal (a ^ lam * b ^ (1 - lam)) ≤ m z} := by
    intro z hz
    refine hsub ?_
    rw [Set.mem_add] at hz ⊢
    obtain ⟨s, hs, t, ht, hst⟩ := hz
    refine ⟨s, ?_, t, ht, hst⟩
    rw [Set.mem_smul_set] at hs ⊢
    obtain ⟨x, hx, hxs⟩ := hs
    rw [Set.mem_singleton_iff] at hx
    exact ⟨x0, hx0, by rw [← hx, hxs]⟩
  have hvol : volume (lam • ({x0} : Set ℝ) + (1 - lam) • B)
      = ENNReal.ofReal (1 - lam) * volume B := by
    rw [show lam • ({x0} : Set ℝ) = {lam * x0} from by
        ext x
        simp only [Set.mem_smul_set, Set.mem_singleton_iff, smul_eq_mul]
        constructor
        · rintro ⟨y, rfl, hy⟩; exact hy.symm
        · intro hx; exact ⟨x0, rfl, hx.symm⟩,
      volume_singleton_add, volume_smul_set (by linarith)]
  have hge : ENNReal.ofReal (a ^ lam * b ^ (1 - lam))
        * ENNReal.ofReal ((1 - lam) * δ) ≤ ∫⁻ z, m z := by
    calc ENNReal.ofReal (a ^ lam * b ^ (1 - lam)) * ENNReal.ofReal ((1 - lam) * δ)
        ≤ ENNReal.ofReal (a ^ lam * b ^ (1 - lam)) * (ENNReal.ofReal (1 - lam) * volume B) := by
          apply mul_le_mul' le_rfl
          rw [ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 1 - lam)]
          exact mul_le_mul' le_rfl hδD
      _ = ENNReal.ofReal (a ^ lam * b ^ (1 - lam))
            * volume (lam • ({x0} : Set ℝ) + (1 - lam) • B) := by rw [hvol]
      _ ≤ ENNReal.ofReal (a ^ lam * b ^ (1 - lam))
            * volume {z | ENNReal.ofReal (a ^ lam * b ^ (1 - lam)) ≤ m z} :=
          mul_le_mul' le_rfl (measure_mono h2)
      _ ≤ ∫⁻ z, m z := const_mul_measure_le_lintegral hm (by positivity)
  refine lt_of_lt_of_le ?_ hge
  rw [show ENNReal.ofReal (a ^ lam * b ^ (1 - lam)) * ENNReal.ofReal ((1 - lam) * δ)
      = ENNReal.ofReal ((a ^ lam * b ^ (1 - lam)) * ((1 - lam) * δ)) from
      (ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ a ^ lam * b ^ (1 - lam))).symm]
  rw [← ENNReal.ofReal_toReal hc.ne]
  rw [ENNReal.ofReal_lt_ofReal_iff']
  refine ⟨?_, by positivity⟩
  calc c.toReal < c.toReal + 1 := lt_add_one _
    _ ≤ (a ^ lam * b ^ (1 - lam)) * ((1 - lam) * δ) := by
        rw [← div_mul_cancel₀ (c.toReal + 1) (by positivity : ((1 - lam) * δ) ≠ 0)]
        exact mul_le_mul_of_nonneg_right ha (by positivity)

/-! ### The theorem -/

theorem prekopaLeindlerOneDim (f g m : ℝ → ℝ≥0∞)
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) (hm : AEMeasurable m volume)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, m (lam * x + (1 - lam) * y) ≥ f x ^ lam * g y ^ (1 - lam)) :
    ∫⁻ x, m x ≥ (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) := by
  by_cases hf0 : ∫⁻ x, f x = 0
  · rw [hf0, ENNReal.zero_rpow_of_pos h0, zero_mul]
    exact zero_le
  by_cases hg0 : ∫⁻ x, g x = 0
  · rw [hg0, ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < 1 - lam), mul_zero]
    exact zero_le
  have hfpos : 0 < ∫⁻ x, f x := lt_of_le_of_ne' (zero_le) hf0
  have hgpos : 0 < ∫⁻ x, g x := lt_of_le_of_ne' (zero_le) hg0
  by_cases hft : essSup f volume = ⊤
  · have htop := topCaseAux hf hg hm lam h0 h1 h hft hgpos
    rw [htop]; exact le_top
  by_cases hgt : essSup g volume = ⊤
  · have h' : ∀ x y, m ((1 - lam) * x + (1 - (1 - lam)) * y)
        ≥ g x ^ (1 - lam) * f y ^ (1 - (1 - lam)) := by
      intro x y
      have hxy := h y x
      rw [show (1 - lam) * x + (1 - (1 - lam)) * y = lam * y + (1 - lam) * x by ring,
        show (1 : ℝ) - (1 - lam) = lam by ring]
      exact le_trans (le_of_eq (mul_comm _ _)) hxy
    have htop := topCaseAux hg hf hm (1 - lam) (by linarith) (by linarith) h' hgt hfpos
    rw [htop]; exact le_top
  · exact finiteCase hf hg hm h0 h1 h hfpos hgpos hft hgt

end Work.BW
