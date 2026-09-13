import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.Convex

open MeasureTheory Set Filter
open scoped Pointwise

/-- Scaling of Lebesgue measure on `ℝ` under the map `x ↦ c * x`. -/
lemma volume_image_mul (c : ℝ) (s : Set ℝ) :
    volume (Set.image (fun x => c * x) s) = ENNReal.ofReal |c| * volume s := by
  rcases eq_or_ne c 0 with rfl | hc
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · simp [Set.Nonempty.image_const hs]
  · have himg : Set.image (fun x => c * x) s = (fun y => c⁻¹ * y) ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [inv_mul_cancel_left₀ hc]
      · intro hy
        exact ⟨c⁻¹ * y, hy, by rw [mul_inv_cancel_left₀ hc]⟩
    rw [himg, Real.volume_preimage_mul_left (inv_ne_zero hc), inv_inv]

/-- Translation invariance of Lebesgue measure on `ℝ`. -/
lemma volume_image_add (c : ℝ) (s : Set ℝ) :
    volume (Set.image (fun x => x + c) s) = volume s := by
  have himg : Set.image (fun x => x + c) s = (fun y => y + (-c)) ⁻¹' s := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + (-c), hy, by ring⟩
  rw [himg, measure_preimage_add_right]

/-- The one-dimensional Brunn-Minkowski inequality, for nonempty compact sets. -/
lemma bm_compact (K K' : Set ℝ) (hK : IsCompact K) (hK' : IsCompact K') (hKne : K.Nonempty)
    (hK'ne : K'.Nonempty) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume K' ≤
      volume (Set.image2 (fun x y => a * x + b * y) K K') := by
  obtain ⟨s, hsK, hsmax⟩ := hK.exists_isMaxOn hKne continuousOn_id
  obtain ⟨t, htK', htmin⟩ := hK'.exists_isMinOn hK'ne continuousOn_id
  set K0 : Set ℝ := Set.image (fun x => x + (-s)) K with hK0def
  set K1 : Set ℝ := Set.image (fun y => y + (-t)) K' with hK1def
  have hK0_vol : volume K0 = volume K := volume_image_add (-s) K
  have hK1_vol : volume K1 = volume K' := volume_image_add (-t) K'
  have hK0_sub : K0 ⊆ Iic 0 := by
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_Iic]
    have := hsmax hx
    simpa using this
  have hK1_sub : K1 ⊆ Ici 0 := by
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_Ici]
    have := htmin hx
    simpa using this
  have hK0_0 : (0 : ℝ) ∈ K0 := ⟨s, hsK, by ring⟩
  have hK1_0 : (0 : ℝ) ∈ K1 := ⟨t, htK', by ring⟩
  set A : Set ℝ := Set.image (fun x => a * x) K0 with hAdef
  set B : Set ℝ := Set.image (fun y => b * y) K1 with hBdef
  have hA_sub : A ⊆ Iic 0 := by
    rintro z ⟨x, hx, rfl⟩
    simp only [Set.mem_Iic]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le (hK0_sub hx)
  have hB_sub : B ⊆ Ici 0 := by
    rintro z ⟨x, hx, rfl⟩
    simp only [Set.mem_Ici]
    exact mul_nonneg hb.le (hK1_sub hx)
  have hK0c : IsCompact K0 := hK.image (continuous_id.add continuous_const)
  have hK1c : IsCompact K1 := hK'.image (continuous_id.add continuous_const)
  have hA_meas : MeasurableSet A := (hK0c.image (continuous_const.mul continuous_id)).measurableSet
  have hB_meas : MeasurableSet B := (hK1c.image (continuous_const.mul continuous_id)).measurableSet
  have hdisj : AEDisjoint volume A B := by
    refine measure_mono_null ?_ (by simp : volume ({(0:ℝ)} : Set ℝ) = 0)
    intro z hz
    simp only [Set.mem_singleton_iff]
    exact le_antisymm (hA_sub hz.1) (hB_sub hz.2)
  have hA_vol : volume A = ENNReal.ofReal a * volume K0 := by
    rw [hAdef, volume_image_mul, abs_of_pos ha]
  have hB_vol : volume B = ENNReal.ofReal b * volume K1 := by
    rw [hBdef, volume_image_mul, abs_of_pos hb]
  have hunion_sub : A ∪ B ⊆ Set.image2 (fun x y => a * x + b * y) K0 K1 := by
    rintro z (hz | hz)
    · rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hx, 0, hK1_0, by ring⟩
    · rcases hz with ⟨y, hy, rfl⟩
      exact ⟨0, hK0_0, y, hy, by ring⟩
  have hvol_eq : volume (Set.image2 (fun x y => a * x + b * y) K K') =
      volume (Set.image2 (fun x y => a * x + b * y) K0 K1) := by
    have hset : Set.image2 (fun x y => a * x + b * y) K K' =
        Set.image (fun z => z + (a * s + b * t))
          (Set.image2 (fun x y => a * x + b * y) K0 K1) := by
      rw [hK0def, hK1def]
      ext z
      simp only [Set.mem_image2, Set.mem_image]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨a * (x + -s) + b * (y + -t), ⟨x + -s, ⟨x, hx, rfl⟩, y + -t, ⟨y, hy, rfl⟩, rfl⟩,
          by ring⟩
      · rintro ⟨w, ⟨x0, ⟨x, hx, rfl⟩, y0, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
        exact ⟨x, hx, y, hy, by ring⟩
    rw [hset, volume_image_add]
  calc ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume K'
      = ENNReal.ofReal a * volume K0 + ENNReal.ofReal b * volume K1 := by rw [hK0_vol, hK1_vol]
    _ = volume A + volume B := by rw [hA_vol, hB_vol]
    _ = volume (A ∪ B) := (measure_union₀ hB_meas.nullMeasurableSet hdisj).symm
    _ ≤ volume (Set.image2 (fun x y => a * x + b * y) K0 K1) := measure_mono hunion_sub
    _ = volume (Set.image2 (fun x y => a * x + b * y) K K') := hvol_eq.symm


/-- Inner approximation of a measurable nonempty set of finite measure by a nonempty compact set,
up to `ε` in measure. -/
lemma exists_compact_subset_measureReal_close (A : Set ℝ) (hA : MeasurableSet A)
    (hAne : A.Nonempty) (hfin : volume A ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ K ⊆ A, IsCompact K ∧ K.Nonempty ∧ volume.real A - ε ≤ volume.real K := by
  by_cases hle : volume.real A ≤ ε
  · obtain ⟨x, hx⟩ := hAne
    have hx0 : volume.real ({x} : Set ℝ) = 0 := by simp [measureReal_def]
    refine ⟨{x}, ?_, isCompact_singleton, ⟨x, rfl⟩, ?_⟩
    · rintro y rfl; exact hx
    · rw [hx0]; linarith
  · have hlt : ε < volume.real A := not_le.mp hle
    have hlt' : ε < (volume A).toReal := by simpa only [measureReal_def] using hlt
    have hnum : (0 : ℝ) < (volume A).toReal := lt_trans hε hlt'
    have hr : ENNReal.ofReal ((volume A).toReal - ε) < volume A := by
      have h2 : ENNReal.ofReal ((volume A).toReal - ε) < ENNReal.ofReal ((volume A).toReal) :=
        (ENNReal.ofReal_lt_ofReal_iff hnum).mpr (by linarith)
      rwa [ENNReal.ofReal_toReal hfin] at h2
    obtain ⟨K, hKA, hKc, hKr⟩ := hA.exists_lt_isCompact_of_ne_top hfin hr
    refine ⟨K, hKA, hKc, ?_, ?_⟩
    · by_contra hKemp
      rw [Set.not_nonempty_iff_eq_empty] at hKemp
      rw [hKemp, measure_empty] at hKr
      simp at hKr
    · have hKtop : volume K ≠ ⊤ := hKc.measure_lt_top.ne
      have h1 : (ENNReal.ofReal ((volume A).toReal - ε)).toReal < (volume K).toReal :=
        (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hKtop).mpr hKr
      rw [ENNReal.toReal_ofReal (by linarith)] at h1
      simpa only [measureReal_def] using le_of_lt h1

/-- The one-dimensional Brunn-Minkowski inequality in "real measure" form, for nonempty sets. -/
lemma bm_nullMeasurable (A B C : Set ℝ) (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hCfin : volume C ≠ ⊤) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hsub : Set.image2 (fun x y => a * x + b * y) A B ⊆ C) :
    a * volume.real A + b * volume.real B ≤ volume.real C := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨x0, hx0⟩ := hAne
  obtain ⟨A', hA'sub, hA'meas, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  have hA''sub : insert x0 A' ⊆ A := by
    intro y hy
    rcases hy with rfl | hy
    · exact hx0
    · exact hA'sub hy
  have hA''meas : MeasurableSet (insert x0 A') := hA'meas.insert x0
  have hA''ne : (insert x0 A').Nonempty := ⟨x0, Set.mem_insert _ _⟩
  have hA'vol : volume A' = volume A := measure_congr hA'ae
  have hA''vol : volume (insert x0 A') = volume A := le_antisymm (measure_mono hA''sub)
    (by rw [← hA'vol]; exact measure_mono (Set.subset_insert _ _))
  have hA''real : volume.real (insert x0 A') = volume.real A := by
    simp only [measureReal_def, hA''vol]
  obtain ⟨K, hKsub, hKc, hKne, hKclose⟩ :=
    exists_compact_subset_measureReal_close (insert x0 A') hA''meas hA''ne (by rw [hA''vol]; exact hAfin) ε hε
  obtain ⟨y0, hy0⟩ := hBne
  obtain ⟨B', hB'sub, hB'meas, hB'ae⟩ := hB.exists_measurable_subset_ae_eq
  have hB''sub : insert y0 B' ⊆ B := by
    intro y hy
    rcases hy with rfl | hy
    · exact hy0
    · exact hB'sub hy
  have hB''meas : MeasurableSet (insert y0 B') := hB'meas.insert y0
  have hB''ne : (insert y0 B').Nonempty := ⟨y0, Set.mem_insert _ _⟩
  have hB'vol : volume B' = volume B := measure_congr hB'ae
  have hB''vol : volume (insert y0 B') = volume B := le_antisymm (measure_mono hB''sub)
    (by rw [← hB'vol]; exact measure_mono (Set.subset_insert _ _))
  have hB''real : volume.real (insert y0 B') = volume.real B := by
    simp only [measureReal_def, hB''vol]
  obtain ⟨K', hK'sub, hK'c, hK'ne, hK'close⟩ :=
    exists_compact_subset_measureReal_close (insert y0 B') hB''meas hB''ne (by rw [hB''vol]; exact hBfin) ε hε
  have hKsubA : K ⊆ A := fun y hy => hA''sub (hKsub hy)
  have hK'subB : K' ⊆ B := fun y hy => hB''sub (hK'sub hy)
  have himg2c : IsCompact (Set.image2 (fun x y => a * x + b * y) K K') := by
    have hset : Set.image2 (fun x y => a * x + b * y) K K' =
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) '' (K ×ˢ K') := by
      ext z
      simp only [Set.mem_image2, Set.mem_image, Set.mem_prod, Prod.exists, exists_and_left,
        exists_prop]
      tauto
    rw [hset]
    exact (hKc.prod hK'c).image (by fun_prop)
  have hbm := bm_compact K K' hKc hK'c hKne hK'ne a b ha hb hab
  have hbm_real : a * volume.real K + b * volume.real K' ≤
      volume.real (Set.image2 (fun x y => a * x + b * y) K K') := by
    have hKtop : volume K ≠ ⊤ := hKc.measure_lt_top.ne
    have hK'top : volume K' ≠ ⊤ := hK'c.measure_lt_top.ne
    have h1 : (ENNReal.ofReal a * volume K + ENNReal.ofReal b * volume K').toReal ≤
        (volume (Set.image2 (fun x y => a * x + b * y) K K')).toReal :=
      ENNReal.toReal_mono himg2c.measure_lt_top.ne hbm
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK'top),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
      ENNReal.toReal_ofReal hb.le] at h1
    simpa only [measureReal_def] using h1
  have himg2sub : Set.image2 (fun x y => a * x + b * y) K K' ⊆ C := by
    rw [Set.image2_subset_iff] at hsub ⊢
    exact fun x hx y hy => hsub x (hKsubA hx) y (hK'subB hy)
  have hle2 : volume.real (Set.image2 (fun x y => a * x + b * y) K K') ≤ volume.real C :=
    measureReal_mono himg2sub hCfin
  have hle3 : volume.real A - ε ≤ volume.real K := by
    rw [← hA''real]; exact hKclose
  have hle4 : volume.real B - ε ≤ volume.real K' := by
    rw [← hB''real]; exact hK'close
  have hAK : a * volume.real A ≤ a * (volume.real K + ε) := by
    nlinarith [hle3, ha]
  have hBK : b * volume.real B ≤ b * (volume.real K' + ε) := by
    nlinarith [hle4, hb]
  have hfinal : a * volume.real A + b * volume.real B ≤ volume.real C + ε := by
    have : a * volume.real K + b * volume.real K' ≤ volume.real C := le_trans hbm_real hle2
    nlinarith [hAK, hBK, this, ha.le, hb.le, hab]
  linarith


/-- Prékopa-Leindler in one dimension, normalized so that `sup f = sup g = 1` and `f, g ≤ 1`. -/
theorem one_dim_normalized (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfmax : sSup (range f) = 1) (hgmax : sSup (range g) = 1)
    (hfg : ∀ x y, h ((1 - lam) * x + lam * y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x := by
  have hα0 : (0 : ℝ) < 1 - lam := by linarith
  have hβ0 : (0 : ℝ) < lam := hl0
  have hFnn : 0 ≤ ∫ x, f x := integral_nonneg hfn
  have hGnn : 0 ≤ ∫ x, g x := integral_nonneg hgn
  have hHnn : 0 ≤ ∫ x, h x := integral_nonneg hhn
  -- Layer cake identities (in `ℝ≥0∞`).
  have hF : ∫⁻ t in Ioi (0:ℝ), volume {x | t < f x} = ENNReal.ofReal (∫ x, f x) := by
    rw [← lintegral_eq_lintegral_meas_lt volume (ae_of_all _ hfn) hf.aemeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hfn) hf.aestronglyMeasurable]
    exact (ENNReal.ofReal_toReal (Integrable.lintegral_lt_top hf).ne).symm
  have hG : ∫⁻ t in Ioi (0:ℝ), volume {y | t < g y} = ENNReal.ofReal (∫ x, g x) := by
    rw [← lintegral_eq_lintegral_meas_lt volume (ae_of_all _ hgn) hg.aemeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgn) hg.aestronglyMeasurable]
    exact (ENNReal.ofReal_toReal (Integrable.lintegral_lt_top hg).ne).symm
  have hH : ∫⁻ t in Ioi (0:ℝ), volume {z | t < h z} = ENNReal.ofReal (∫ x, h x) := by
    rw [← lintegral_eq_lintegral_meas_lt volume (ae_of_all _ hhn) hh.aemeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hhn) hh.aestronglyMeasurable]
    exact (ENNReal.ofReal_toReal (Integrable.lintegral_lt_top hh).ne).symm
  -- Pointwise inequality for every `t > 0`.
  have hpoint : ∀ t ∈ Ioi (0:ℝ),
      ENNReal.ofReal (1 - lam) * volume {x | t < f x} + ENNReal.ofReal lam * volume {y | t < g y}
        ≤ volume {z | t < h z} := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    rcases lt_or_ge t 1 with ht1 | ht1
    · have hAne : {x | t < f x}.Nonempty := by
        obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup (range_nonempty f) (by rw [hfmax]; exact ht1)
        rw [Set.mem_range] at ha
        obtain ⟨x, rfl⟩ := ha
        exact ⟨x, hlt⟩
      have hBne : {y | t < g y}.Nonempty := by
        obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup (range_nonempty g) (by rw [hgmax]; exact ht1)
        rw [Set.mem_range] at ha
        obtain ⟨x, rfl⟩ := ha
        exact ⟨x, hlt⟩
      have hAmeas : NullMeasurableSet {x | t < f x} volume :=
        nullMeasurableSet_lt aemeasurable_const hf.aemeasurable
      have hBmeas : NullMeasurableSet {y | t < g y} volume :=
        nullMeasurableSet_lt aemeasurable_const hg.aemeasurable
      have hAfin : volume {x | t < f x} ≠ ⊤ := by
        refine ne_top_of_le_ne_top (hf.measure_ge_lt_top ht0).ne (measure_mono ?_)
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact le_of_lt hx
      have hBfin : volume {y | t < g y} ≠ ⊤ := by
        refine ne_top_of_le_ne_top (hg.measure_ge_lt_top ht0).ne (measure_mono ?_)
        intro y hy
        simp only [Set.mem_ofPred_eq] at hy ⊢
        exact le_of_lt hy
      have hCfin : volume {z | t < h z} ≠ ⊤ := by
        refine ne_top_of_le_ne_top (hh.measure_ge_lt_top ht0).ne (measure_mono ?_)
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        exact le_of_lt hz
      have hsub : Set.image2 (fun x y => (1 - lam) * x + lam * y) {x | t < f x} {y | t < g y}
          ⊆ {z | t < h z} := by
        rintro z ⟨x, hx, y, hy, rfl⟩
        have h1 : t ^ (1 - lam) < f x ^ (1 - lam) := Real.rpow_lt_rpow ht0.le hx hα0
        have h2 : t ^ lam < g y ^ lam := Real.rpow_lt_rpow ht0.le hy hβ0
        have hfx0 : 0 ≤ f x := le_of_lt (lt_trans ht0 hx)
        have htlam : 0 < t ^ lam := Real.rpow_pos_of_pos ht0 lam
        have h3 : t ^ (1 - lam) * t ^ lam < f x ^ (1 - lam) * g y ^ lam :=
          mul_lt_mul h1 h2.le htlam (Real.rpow_nonneg hfx0 (1 - lam))
        have ht_eq : t ^ (1 - lam) * t ^ lam = t := by
          rw [← Real.rpow_add ht0, show (1 - lam) + lam = 1 by ring, Real.rpow_one]
        rw [ht_eq] at h3
        exact lt_of_lt_of_le h3 (hfg x y)
      have hbm := bm_nullMeasurable _ _ _ hAmeas hBmeas hAne hBne hAfin hBfin hCfin
        (1 - lam) lam hα0 hβ0 (by ring) hsub
      have hAeq : volume {x | t < f x} = ENNReal.ofReal (volume.real {x | t < f x}) :=
        (ENNReal.ofReal_toReal hAfin).symm
      have hBeq : volume {y | t < g y} = ENNReal.ofReal (volume.real {y | t < g y}) :=
        (ENNReal.ofReal_toReal hBfin).symm
      have hCeq : volume {z | t < h z} = ENNReal.ofReal (volume.real {z | t < h z}) :=
        (ENNReal.ofReal_toReal hCfin).symm
      rw [hAeq, hBeq, hCeq, ← ENNReal.ofReal_mul hα0.le, ← ENNReal.ofReal_mul hβ0.le,
        ← ENNReal.ofReal_add (mul_nonneg hα0.le (measureReal_nonneg (μ := volume)))
          (mul_nonneg hβ0.le (measureReal_nonneg (μ := volume)))]
      exact ENNReal.ofReal_le_ofReal hbm
    · have hA0 : volume {x | t < f x} = 0 := by
        have hempty : {x | t < f x} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact not_lt.mpr (le_trans (hf1 x) ht1)
        rw [hempty, measure_empty]
      have hB0 : volume {y | t < g y} = 0 := by
        have hempty : {y | t < g y} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact not_lt.mpr (le_trans (hg1 x) ht1)
        rw [hempty, measure_empty]
      rw [hA0, hB0]
      simp
  -- Measurability of the level-set-measure functions.
  have hFm : Measurable (fun t : ℝ => volume {x | t < f x}) :=
    Antitone.measurable fun a b hab => measure_mono fun x hx => lt_of_le_of_lt hab hx
  have hGm : Measurable (fun t : ℝ => volume {y | t < g y}) :=
    Antitone.measurable fun a b hab => measure_mono fun y hy => lt_of_le_of_lt hab hy
  have hHm : Measurable (fun t : ℝ => volume {z | t < h z}) :=
    Antitone.measurable fun a b hab => measure_mono fun z hz => lt_of_le_of_lt hab hz
  have hkey : ENNReal.ofReal (1 - lam) * ENNReal.ofReal (∫ x, f x)
      + ENNReal.ofReal lam * ENNReal.ofReal (∫ x, g x) ≤ ENNReal.ofReal (∫ x, h x) := by
    rw [← hF, ← hG, ← hH]
    calc ENNReal.ofReal (1 - lam) * (∫⁻ t in Ioi (0:ℝ), volume {x | t < f x})
          + ENNReal.ofReal lam * (∫⁻ t in Ioi (0:ℝ), volume {y | t < g y})
        = ∫⁻ t in Ioi (0:ℝ), (ENNReal.ofReal (1 - lam) * volume {x | t < f x}
            + ENNReal.ofReal lam * volume {y | t < g y}) := by
          rw [← lintegral_const_mul _ hFm, ← lintegral_const_mul _ hGm,
            ← lintegral_add_left (hFm.const_mul _)]
      _ ≤ ∫⁻ t in Ioi (0:ℝ), volume {z | t < h z} := setLIntegral_mono hHm hpoint
  have hmain : (1 - lam) * (∫ x, f x) + lam * (∫ x, g x) ≤ ∫ x, h x := by
    have hconv : ENNReal.ofReal ((1 - lam) * (∫ x, f x) + lam * (∫ x, g x))
        ≤ ENNReal.ofReal (∫ x, h x) := by
      rw [ENNReal.ofReal_add (mul_nonneg hα0.le hFnn) (mul_nonneg hβ0.le hGnn),
        ENNReal.ofReal_mul hα0.le, ENNReal.ofReal_mul hβ0.le]
      exact hkey
    exact (ENNReal.ofReal_le_ofReal_iff hHnn).mp hconv
  calc (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam
      ≤ (1 - lam) * (∫ x, f x) + lam * (∫ x, g x) :=
        Real.geom_mean_le_arith_mean2_weighted hα0.le hβ0.le hFnn hGnn (by ring)
    _ ≤ ∫ x, h x := hmain

/-- If `f` has positive supremum, then the supremum of `x ↦ f x / sup f` is `1`. -/
private lemma csSup_div_self (f : ℝ → ℝ) (hbdd : BddAbove (Set.range f))
    (ha : 0 < sSup (Set.range f)) :
    sSup (Set.range (fun x => f x / sSup (Set.range f))) = 1 := by
  set a := sSup (Set.range f)
  have ha' : 0 < a := ha
  have hle : ∀ x, f x / a ≤ 1 := by
    intro x
    rw [div_le_one ha']
    exact le_csSup hbdd (Set.mem_range_self x)
  have hbdd' : BddAbove (Set.range (fun x => f x / a)) :=
    ⟨1, by rintro y ⟨x, rfl⟩; exact hle x⟩
  have hne : (Set.range (fun x => f x / a)).Nonempty := ⟨f 0 / a, Set.mem_range_self 0⟩
  refine le_antisymm (csSup_le hne (by rintro y ⟨x, rfl⟩; exact hle x)) ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hcon
  have hta : t * a < a := by nlinarith
  obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup (range_nonempty f) hta
  obtain ⟨x, rfl⟩ := hy
  have hx' : t < f x / a := (lt_div_iff₀ ha').mpr hxy
  have h2 : f x / a ≤ sSup (Set.range (fun x => f x / a)) :=
    le_csSup hbdd' (Set.mem_range_self x)
  linarith

/-- Prékopa-Leindler in one dimension for `f`, `g` bounded above. -/
private theorem one_dim_bounded (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hfbdd : BddAbove (Set.range f)) (hgbdd : BddAbove (Set.range g))
    (hfg : ∀ x y, h ((1 - lam) * x + lam * y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x := by
  have ha0 : 0 ≤ sSup (Set.range f) :=
    le_trans (hfn 0) (le_csSup hfbdd (Set.mem_range_self 0))
  have hb0 : 0 ≤ sSup (Set.range g) :=
    le_trans (hgn 0) (le_csSup hgbdd (Set.mem_range_self 0))
  rcases eq_or_lt_of_le ha0 with ha | ha
  · have hf0 : ∫ x, f x = 0 := by
      have hzero : f = fun _ => 0 := by
        funext x
        exact le_antisymm (ha ▸ le_csSup hfbdd (Set.mem_range_self x)) (hfn x)
      rw [hzero]; simp
    rw [hf0, Real.zero_rpow (by linarith : (1:ℝ) - lam ≠ 0), zero_mul]
    exact integral_nonneg hhn
  rcases eq_or_lt_of_le hb0 with hb | hb
  · have hg0 : ∫ x, g x = 0 := by
      have hzero : g = fun _ => 0 := by
        funext x
        exact le_antisymm (hb ▸ le_csSup hgbdd (Set.mem_range_self x)) (hgn x)
      rw [hzero]; simp
    rw [hg0, Real.zero_rpow (by linarith : lam ≠ 0), mul_zero]
    exact integral_nonneg hhn
  · set a : ℝ := sSup (Set.range f) with hadef
    set b : ℝ := sSup (Set.range g) with hbdef
    set c : ℝ := a ^ (1 - lam) * b ^ lam with hcdef
    set F : ℝ → ℝ := fun x => f x / a with hFdef
    set G : ℝ → ℝ := fun x => g x / b with hGdef
    set H : ℝ → ℝ := fun x => h x / c with hHdef
    have ha_pos : 0 < a := ha
    have hb_pos : 0 < b := hb
    have hc_pos : 0 < c := mul_pos (Real.rpow_pos_of_pos ha_pos _) (Real.rpow_pos_of_pos hb_pos _)
    have hFnn : ∀ x, 0 ≤ F x := fun x => div_nonneg (hfn x) ha_pos.le
    have hGnn : ∀ x, 0 ≤ G x := fun x => div_nonneg (hgn x) hb_pos.le
    have hHnn : ∀ x, 0 ≤ H x := fun x => div_nonneg (hhn x) hc_pos.le
    have hFint : Integrable F := hf.div_const a
    have hGint : Integrable G := hg.div_const b
    have hHint : Integrable H := hh.div_const c
    have hF1 : ∀ x, F x ≤ 1 :=
      fun x => (div_le_one ha_pos).mpr (le_csSup hfbdd (Set.mem_range_self x))
    have hG1 : ∀ x, G x ≤ 1 :=
      fun x => (div_le_one hb_pos).mpr (le_csSup hgbdd (Set.mem_range_self x))
    have hFmax : sSup (Set.range F) = 1 := csSup_div_self f hfbdd ha_pos
    have hGmax : sSup (Set.range G) = 1 := csSup_div_self g hgbdd hb_pos
    have hFG : ∀ x y, H ((1 - lam) * x + lam * y) ≥ F x ^ (1 - lam) * G y ^ lam := by
      intro x y
      have h1 : F x ^ (1 - lam) = f x ^ (1 - lam) / a ^ (1 - lam) := by
        simp only [hFdef]
        exact Real.div_rpow (hfn x) ha_pos.le (1 - lam)
      have h2 : G y ^ lam = g y ^ lam / b ^ lam := by
        simp only [hGdef]
        exact Real.div_rpow (hgn y) hb_pos.le lam
      have h3 : F x ^ (1 - lam) * G y ^ lam
          = (f x ^ (1 - lam) * g y ^ lam) / (a ^ (1 - lam) * b ^ lam) := by
        rw [h1, h2, div_mul_div_comm]
      rw [h3, hHdef, hcdef]
      exact div_le_div_of_nonneg_right (hfg x y) (le_of_lt (mul_pos (Real.rpow_pos_of_pos ha_pos _)
        (Real.rpow_pos_of_pos hb_pos _)))
    have hnorm := one_dim_normalized F G H lam hl0 hl1 hFnn hGnn hHnn hFint hGint hHint
      hF1 hG1 hFmax hGmax hFG
    have hFa : ∫ x, F x = (∫ x, f x) / a := by rw [hFdef]; exact integral_div a f
    have hGa : ∫ x, G x = (∫ x, g x) / b := by rw [hGdef]; exact integral_div b g
    have hHa : ∫ x, H x = (∫ x, h x) / c := by rw [hHdef]; exact integral_div c h
    rw [hFa, hGa, hHa] at hnorm
    have hfp : 0 ≤ ∫ x, f x := integral_nonneg hfn
    have hgp : 0 ≤ ∫ x, g x := integral_nonneg hgn
    rw [Real.div_rpow hfp ha_pos.le, Real.div_rpow hgp hb_pos.le, hcdef, div_mul_div_comm] at hnorm
    exact (div_le_div_iff_of_pos_right
      (mul_pos (Real.rpow_pos_of_pos ha_pos _) (Real.rpow_pos_of_pos hb_pos _))).mp hnorm

/-- Truncation of an integrable nonnegative function converges in integral. -/
private lemma tendsto_integral_min (f : ℝ → ℝ) (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x) :
    Tendsto (fun n : ℕ => ∫ x, min (f x) (n : ℝ)) atTop (nhds (∫ x, f x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => f x) (fun n => ?_) hf (fun n => ?_) ?_
  · exact (hf.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  · filter_upwards with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn x) (Nat.cast_nonneg n))]
    exact min_le_left _ _
  · filter_upwards with x
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_atTop.2 ⟨⌈f x⌉₊, fun n hn => by exact_mod_cast hn⟩] with n hn
    exact min_eq_left (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))

/-- Prékopa-Leindler in one dimension, general `f, g`, for `0 < lam < 1`. -/
private theorem one_dim_strict (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hfg : ∀ x y, h ((1 - lam) * x + lam * y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x := by
  have hfgN : ∀ (n : ℕ) (x y : ℝ),
      h ((1 - lam) * x + lam * y) ≥ (min (f x) (n:ℝ)) ^ (1 - lam) * (min (g y) (n:ℝ)) ^ lam := by
    intro n x y
    have hfx0 : 0 ≤ min (f x) (n:ℝ) := le_min (hfn x) (Nat.cast_nonneg n)
    have hgy0 : 0 ≤ min (g y) (n:ℝ) := le_min (hgn y) (Nat.cast_nonneg n)
    have h1 : (min (f x) (n:ℝ)) ^ (1 - lam) ≤ f x ^ (1 - lam) :=
      Real.rpow_le_rpow hfx0 (min_le_left _ _) (sub_nonneg.mpr hl1.le)
    have h2 : (min (g y) (n:ℝ)) ^ lam ≤ g y ^ lam :=
      Real.rpow_le_rpow hgy0 (min_le_left _ _) hl0.le
    exact le_trans (mul_le_mul h1 h2 (Real.rpow_nonneg hgy0 lam) (Real.rpow_nonneg (hfn x) (1 - lam)))
      (hfg x y)
  have hbddN : ∀ n : ℕ, BddAbove (Set.range (fun x => min (f x) (n:ℝ))) :=
    fun n => ⟨n, by rintro y ⟨x, rfl⟩; exact min_le_right _ _⟩
  have hbddN' : ∀ n : ℕ, BddAbove (Set.range (fun x => min (g x) (n:ℝ))) :=
    fun n => ⟨n, by rintro y ⟨x, rfl⟩; exact min_le_right _ _⟩
  have hintN : ∀ n : ℕ, Integrable (fun x => min (f x) (n:ℝ)) := by
    intro n
    refine hf.mono' ((hf.aemeasurable.min aemeasurable_const).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfn x) (Nat.cast_nonneg n))]
    exact min_le_left _ _
  have hintN' : ∀ n : ℕ, Integrable (fun x => min (g x) (n:ℝ)) := by
    intro n
    refine hg.mono' ((hg.aemeasurable.min aemeasurable_const).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hgn x) (Nat.cast_nonneg n))]
    exact min_le_left _ _
  have hstep : ∀ n : ℕ,
      (∫ x, min (f x) (n:ℝ)) ^ (1 - lam) * (∫ x, min (g x) (n:ℝ)) ^ lam ≤ ∫ x, h x := by
    intro n
    exact one_dim_bounded _ _ _ lam hl0 hl1
      (fun x => le_min (hfn x) (Nat.cast_nonneg n)) (fun x => le_min (hgn x) (Nat.cast_nonneg n))
      hhn (hintN n) (hintN' n) hh (hbddN n) (hbddN' n) (hfgN n)
  have hlim : Tendsto (fun n : ℕ =>
      (∫ x, min (f x) (n:ℝ)) ^ (1 - lam) * (∫ x, min (g x) (n:ℝ)) ^ lam) atTop
      (nhds ((∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam)) :=
    ((tendsto_integral_min f hf hfn).rpow_const (Or.inr (sub_nonneg.mpr hl1.le))).mul
      ((tendsto_integral_min g hg hgn).rpow_const (Or.inr hl0.le))
  exact le_of_tendsto hlim (Eventually.of_forall hstep)

theorem prekopa_leindler_1d {f g h : ℝ → ℝ}
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g)
    (hh : MeasureTheory.Integrable h)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hfg : ∀ x y, h ((1 - lam) * x + lam * y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x := by
  rcases lt_or_eq_of_le hl0 with hl0' | rfl
  · rcases lt_or_eq_of_le hl1 with hl1' | rfl
    · exact one_dim_strict f g h lam hl0' hl1' hfn hgn hhn hf hg hh hfg
    · -- lam = 1
      have hle : ∀ y, g y ≤ h y := by
        intro y
        have h1 := hfg 0 y
        simp only [sub_self, zero_mul, one_mul, zero_add, Real.rpow_zero, Real.rpow_one,
          one_mul] at h1
        exact h1
      have := integral_mono hg hh hle
      rw [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
      exact this
  · -- lam = 0
    have hle : ∀ x, f x ≤ h x := by
      intro x
      have h1 := hfg x 0
      simp only [sub_zero, one_mul, zero_mul, add_zero, Real.rpow_one, Real.rpow_zero,
        mul_one] at h1
      exact h1
    have := integral_mono hf hh hle
    rw [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact this

end Commons.Analysis.Convex