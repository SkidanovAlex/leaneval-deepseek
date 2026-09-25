import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type
import Submission.Commons.MeasureTheory.Measurable.union_Icc_measurable

open _root_.MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace Commons.Analysis.Maximal

/-! ### Measurability of `hlMax` -/

private lemma hlMax_lt_iff_aux (φ : ℝ → ℝ≥0∞) (x : ℝ) (t : ℝ≥0∞) :
    t < hlMax φ x ↔ ∃ a b : ℝ, a ≤ x ∧ x ≤ b ∧
      t < ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, φ y := by
  rw [hlMax]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := lt_iSup_iff.mp h
    obtain ⟨b, hb⟩ := lt_iSup_iff.mp ha
    obtain ⟨hab, hlt⟩ := lt_iSup_iff.mp hb
    exact ⟨a, b, hab.1, hab.2, hlt⟩
  · rintro ⟨a, b, ha, hb, hlt⟩
    refine lt_iSup_iff.mpr ⟨a, ?_⟩
    refine lt_iSup_iff.mpr ⟨b, ?_⟩
    exact lt_iSup_iff.mpr ⟨⟨ha, hb⟩, hlt⟩

private lemma hlMax_le_of_mem_aux (φ : ℝ → ℝ≥0∞) {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, φ y ≤ hlMax φ x := by
  rw [hlMax]
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ⟨ha, hb⟩ le_rfl))

private def goodIntervals_aux (φ : ℝ → ℝ≥0∞) (t : ℝ≥0∞) : Set (ℝ × ℝ) :=
  {p | t < ENNReal.ofReal (p.2 - p.1)⁻¹ * ∫⁻ y in Set.Icc p.1 p.2, φ y}

private lemma goodIntervals_snd_lt_fst_aux {φ : ℝ → ℝ≥0∞} {t : ℝ≥0∞} {p : ℝ × ℝ}
    (hp : p ∈ goodIntervals_aux φ t) : p.1 < p.2 := by
  rw [goodIntervals_aux, Set.mem_ofPred_eq] at hp
  by_contra h
  push Not at h
  have hinv : (p.2 - p.1)⁻¹ ≤ 0 := inv_nonpos.mpr (sub_nonpos.mpr h)
  have hzero : ENNReal.ofReal (p.2 - p.1)⁻¹ * ∫⁻ y in Set.Icc p.1 p.2, φ y = 0 := by
    rw [ENNReal.ofReal_eq_zero.mpr hinv, zero_mul]
  rw [hzero] at hp
  exact absurd hp not_lt_bot

private lemma levelSet_eq_iUnion_aux (φ : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    {x : ℝ | t < hlMax φ x} = ⋃ p ∈ goodIntervals_aux φ t, Set.Icc p.1 p.2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hlt⟩ := (hlMax_lt_iff_aux φ x t).mp hx
    exact Set.mem_iUnion.mpr ⟨(a, b), Set.mem_iUnion.mpr ⟨hlt, ⟨ha, hb⟩⟩⟩
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hpC, hxp⟩ := Set.mem_iUnion.mp hp
    rw [Set.mem_Icc] at hxp
    exact lt_of_lt_of_le hpC (hlMax_le_of_mem_aux φ hxp.1 hxp.2)

private theorem measurable_hlMax_aux (φ : ℝ → ℝ≥0∞) : Measurable (hlMax φ) := by
  apply measurable_of_Ioi
  intro t
  show MeasurableSet {x : ℝ | t < hlMax φ x}
  rw [levelSet_eq_iUnion_aux]
  exact Commons.MeasureTheory.Measurable.union_Icc_measurable _
    (fun p hp => goodIntervals_snd_lt_fst_aux hp)

/-! ### Subadditivity and boundedness of `hlMax` -/

private lemma hlMax_add_le_aux (u v : ℝ → ℝ≥0∞) (hu : Measurable u) (x : ℝ) :
    hlMax (u + v) x ≤ hlMax u x + hlMax v x := by
  rw [hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  have hsplit : ∫⁻ y in Set.Icc a b, (u + v) y
      = (∫⁻ y in Set.Icc a b, u y) + (∫⁻ y in Set.Icc a b, v y) :=
    lintegral_add_left (μ := volume.restrict (Set.Icc a b)) hu v
  rw [hsplit, mul_add]
  exact add_le_add (hlMax_le_of_mem_aux u hab.1 hab.2) (hlMax_le_of_mem_aux v hab.1 hab.2)

private lemma ofReal_inv_mul_self_le_one (r : ℝ) : ENNReal.ofReal r⁻¹ * ENNReal.ofReal r ≤ 1 := by
  rcases le_total 0 r with h | h
  · rcases eq_or_ne r 0 with hr | hr
    · subst hr; simp
    · rw [← ENNReal.ofReal_mul (inv_nonneg.mpr h), inv_mul_cancel₀ hr]
      simp
  · rw [ENNReal.ofReal_eq_zero.mpr h, mul_zero]
    exact zero_le_one

private lemma hlMax_le_const_aux (f : ℝ → ℝ≥0∞) {C : ℝ≥0∞}
    (hf : ∀ y, f y ≤ C) (x : ℝ) : hlMax f x ≤ C := by
  rw [hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  have h2 : ∫⁻ y in Set.Icc a b, C = C * ENNReal.ofReal (b - a) := by
    rw [setLIntegral_const, Real.volume_Icc]
  have h1 : ∫⁻ y in Set.Icc a b, f y ≤ C * ENNReal.ofReal (b - a) := by
    rw [← h2]; exact lintegral_mono fun y => hf y
  calc ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, f y
      ≤ ENNReal.ofReal (b - a)⁻¹ * (C * ENNReal.ofReal (b - a)) := mul_le_mul_right h1 _
    _ = C * (ENNReal.ofReal (b - a)⁻¹ * ENNReal.ofReal (b - a)) := by ring
    _ ≤ C * 1 := mul_le_mul_right (ofReal_inv_mul_self_le_one (b - a)) C
    _ = C := mul_one C

private theorem hlMax_weak_type_four (f : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    volume {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      ≤ ENNReal.ofReal (4 / lam) * ∫⁻ y, ‖f y‖ₑ := by
  have hsub : ∀ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)}
      ⊆ {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x} := by
    intro n x hx
    have hx' : ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ) := hx
    simp only [hlTruncMax] at hx'
    simp only [hlMax]
    refine lt_of_lt_of_le hx' (iSup_le fun p => ?_)
    exact le_iSup_of_le p.1.1 (le_iSup_of_le p.1.2 (le_iSup_of_le ⟨p.2.1, p.2.2.1⟩ le_rfl))
  have hsup : {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      ⊆ ⋃ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} := by
    intro x hx
    have hx' : ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x := hx
    simp only [hlMax] at hx'
    rcases lt_iSup_iff.mp hx' with ⟨a, ha⟩
    rcases lt_iSup_iff.mp ha with ⟨b, hb⟩
    rcases lt_iSup_iff.mp hb with ⟨hab, hval⟩
    refine Set.mem_iUnion.mpr ⟨Nat.ceil (b - a), ?_⟩
    simp only [hlTruncMax]
    refine lt_of_lt_of_le hval ?_
    exact le_iSup_of_le ⟨(a, b), hab.1, hab.2, Nat.le_ceil (b - a)⟩ le_rfl
  have hmono : Monotone fun n : ℕ =>
      {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} := by
    intro m n hmn x hx
    have hx' : ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (m : ℝ) := hx
    simp only [hlTruncMax] at hx'
    simp only [hlTruncMax]
    refine lt_of_lt_of_le hx' (iSup_le fun p => ?_)
    exact le_iSup_of_le ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.trans (by exact_mod_cast hmn)⟩ le_rfl
  calc volume {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      = volume (⋃ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)}) := by
        rw [Set.Subset.antisymm hsup (Set.iUnion_subset hsub)]
    _ = ⨆ n : ℕ, volume {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} :=
        Monotone.measure_iUnion hmono
    _ ≤ ENNReal.ofReal (4 / lam) * ∫⁻ y, ‖f y‖ₑ :=
        iSup_le fun n : ℕ => volume_levelSet_truncMax_le f hlam

private lemma hlMax_mono {f g : ℝ → ℝ≥0∞} (h : f ≤ g) (x : ℝ) : hlMax f x ≤ hlMax g x := by
  rw [hlMax, hlMax]
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab (mul_le_mul_right (lintegral_mono h) _)))

private lemma enorm_nonneg_eq (f : ℝ → ℝ) (hf : 0 ≤ f) :
    (fun y => ‖f y‖ₑ) = fun y => ENNReal.ofReal (f y) := by
  funext y; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf y)]

private lemma ofReal_lt_ofReal_iff' {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ENNReal.ofReal a < ENNReal.ofReal b ↔ a < b := by
  rcases eq_or_lt_of_le hb with h | h
  · subst h
    simp only [ENNReal.ofReal_zero]
    constructor
    · intro hc; exact absurd hc (not_lt_of_ge bot_le)
    · intro hc; exact absurd hc (not_lt_of_ge ha.le)
  · exact ENNReal.ofReal_lt_ofReal_iff h

private lemma hlMax_ofReal_le_add (φ : ℝ → ℝ) (hφ : Measurable φ) (hφnn : 0 ≤ φ)
    {t : ℝ} (_ht : 0 < t) (x : ℝ) :
    hlMax (fun y => ENNReal.ofReal (φ y)) x ≤
      hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) x + ENNReal.ofReal (t/2) := by
  have hu_nn : 0 ≤ fun y : ℝ => (if t/2 < φ y then φ y else 0 : ℝ) := fun y => by
    by_cases h : t/2 < φ y
    · simp only [h, reduceIte]; exact hφnn y
    · simp only [h, reduceIte]; exact le_rfl
  have hu_meas : Measurable fun y => ENNReal.ofReal (if t/2 < φ y then φ y else 0) :=
    ENNReal.measurable_ofReal.comp
      (Measurable.ite (measurableSet_lt measurable_const hφ) hφ measurable_const)
  have huv : ∀ y, ENNReal.ofReal (φ y) ≤
      ENNReal.ofReal (if t/2 < φ y then φ y else 0)
        + ENNReal.ofReal (if t/2 < φ y then 0 else t/2) := by
    intro y
    by_cases h : t/2 < φ y
    · simp only [h, reduceIte, ENNReal.ofReal_zero, add_zero]; exact le_rfl
    · simp only [h, reduceIte, ENNReal.ofReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (le_of_not_gt h)
  have hbd : ∀ y, ENNReal.ofReal (if t/2 < φ y then 0 else t/2) ≤ ENNReal.ofReal (t/2) := by
    intro y
    by_cases h : t/2 < φ y
    · simp only [h, reduceIte, ENNReal.ofReal_zero]; exact bot_le
    · simp only [h, reduceIte]; exact le_rfl
  calc hlMax (fun y => ENNReal.ofReal (φ y)) x
      ≤ hlMax (fun y => ENNReal.ofReal (if t/2 < φ y then φ y else 0)
              + ENNReal.ofReal (if t/2 < φ y then 0 else t/2)) x := hlMax_mono huv x
    _ ≤ hlMax (fun y => ENNReal.ofReal (if t/2 < φ y then φ y else 0)) x
          + hlMax (fun y => ENNReal.ofReal (if t/2 < φ y then 0 else t/2)) x :=
        hlMax_add_le_aux _ _ hu_meas x
    _ ≤ hlMax (fun y => ENNReal.ofReal (if t/2 < φ y then φ y else 0)) x + ENNReal.ofReal (t/2) :=
        add_le_add_right (hlMax_le_const_aux _ hbd x) _
    _ = hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) x + ENNReal.ofReal (t/2) := by
        rw [← enorm_nonneg_eq (fun y => (if t/2 < φ y then φ y else 0 : ℝ)) hu_nn]

private lemma levelSet_toReal_bound (φ : ℝ → ℝ) (hφ : Measurable φ) (hφnn : 0 ≤ φ)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    volume {a : ℝ | t < ((hlMax (fun y => ENNReal.ofReal (φ y)) a) ⊓ (n : ENNReal)).toReal}
      ≤ ENNReal.ofReal (8 / t) *
        ∫⁻ y in {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}, ENNReal.ofReal (φ y) := by
  have hS : MeasurableSet {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)} :=
    measurableSet_lt measurable_const (ENNReal.measurable_ofReal.comp hφ)
  have h1 : {a : ℝ | t < ((hlMax (fun y => ENNReal.ofReal (φ y)) a) ⊓ (n : ENNReal)).toReal}
      ⊆ {a : ℝ | ENNReal.ofReal t < hlMax (fun y => ENNReal.ofReal (φ y)) a} := by
    intro a ha
    have hfin : (hlMax (fun y => ENNReal.ofReal (φ y)) a ⊓ (n : ENNReal)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right
    have hpos : 0 < (hlMax (fun y => ENNReal.ofReal (φ y)) a ⊓ (n : ENNReal)).toReal :=
      lt_trans ht ha
    have hlt : ENNReal.ofReal t < ENNReal.ofReal ((hlMax (fun y => ENNReal.ofReal (φ y)) a ⊓ (n : ENNReal)).toReal) :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).mpr ha
    rw [ENNReal.ofReal_toReal hfin] at hlt
    exact lt_of_lt_of_le hlt inf_le_left
  have h2 : {a : ℝ | ENNReal.ofReal t < hlMax (fun y => ENNReal.ofReal (φ y)) a} ⊆
      {a : ℝ | ENNReal.ofReal (t/2) < hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) a} := by
    intro a ha
    have hdec := hlMax_ofReal_le_add φ hφ hφnn ht a
    have h2t : ENNReal.ofReal t = ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
    rw [h2t] at ha
    have hlt : ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) <
        hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) a + ENNReal.ofReal (t/2) :=
      lt_of_lt_of_le ha hdec
    exact (ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hlt
  have h3 : volume {a : ℝ | ENNReal.ofReal (t/2) <
        hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) a}
      ≤ ENNReal.ofReal (4 / (t/2)) * ∫⁻ y, ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ :=
    hlMax_weak_type_four _ (by linarith)
  have hu_nn : 0 ≤ fun y : ℝ => (if t/2 < φ y then φ y else 0 : ℝ) := fun y => by
    by_cases h : t/2 < φ y
    · simp only [h, reduceIte]; exact hφnn y
    · simp only [h, reduceIte]; exact le_rfl
  have h4 : ∫⁻ y, ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ
      = ∫⁻ y in {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}, ENNReal.ofReal (φ y) := by
    rw [enorm_nonneg_eq _ hu_nn]
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro y
    by_cases h : t/2 < φ y
    · have hc : ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y) :=
        (ofReal_lt_ofReal_iff' (by linarith) (hφnn y)).mpr h
      simp only [h, reduceIte]
      rw [Set.indicator_of_mem (show y ∈ {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)} from hc)]
    · have hc : ¬ ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y) := by
        intro hcc
        exact absurd ((ofReal_lt_ofReal_iff' (by linarith) (hφnn y)).mp hcc) (not_lt_of_ge (le_of_not_gt h))
      simp only [h, reduceIte, ENNReal.ofReal_zero]
      rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)} from hc)]
  have h4t : ENNReal.ofReal (4 / (t/2)) = ENNReal.ofReal (8 / t) := by
    congr 1
    field_simp
    ring
  calc volume {a : ℝ | t < ((hlMax (fun y => ENNReal.ofReal (φ y)) a) ⊓ (n : ENNReal)).toReal}
      ≤ volume {a : ℝ | ENNReal.ofReal t < hlMax (fun y => ENNReal.ofReal (φ y)) a} :=
        measure_mono h1
    _ ≤ volume {a : ℝ | ENNReal.ofReal (t/2) < hlMax (fun y => ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ) a} :=
        measure_mono h2
    _ ≤ ENNReal.ofReal (4 / (t/2)) * ∫⁻ y, ‖(if t/2 < φ y then φ y else 0 : ℝ)‖ₑ := h3
    _ = ENNReal.ofReal (8 / t) *
        ∫⁻ y in {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}, ENNReal.ofReal (φ y) := by
        rw [h4, h4t]

private lemma ofReal_rpow_mul_ofReal_div {t p : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (8 / t) = ENNReal.ofReal (8 * t ^ (p - 2)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p - 1))]
  congr 1
  have h1 : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h1]
  have h8 : t * (8 / t) = 8 := by field_simp
  rw [mul_assoc, h8, mul_comm]

private lemma inner_rpow_int (c : ℝ) (hc : 0 ≤ c) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (8 / t) *
        (Set.Iio c).indicator (fun _ => (1 : ENNReal)) t
      = ENNReal.ofReal (8 * c ^ (p - 1) / (p - 1)) := by
  have hp1 : 0 < p - 1 := by linarith
  have hpm : -1 < p - 2 := by linarith
  have hA : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (8 / t) *
        (Set.Iio c).indicator (fun _ => (1 : ENNReal)) t)
      = ∫⁻ t in Set.Ioo (0:ℝ) c, ENNReal.ofReal (8 * t ^ (p - 2)) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro t
    by_cases ht : 0 < t
    · by_cases htc : t < c
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht),
            Set.indicator_of_mem (show t ∈ Set.Ioo (0:ℝ) c from ⟨ht, htc⟩),
            Set.indicator_of_mem (show t ∈ Set.Iio c from htc)]
        simp only [mul_one]
        exact ofReal_rpow_mul_ofReal_div ht
      · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0:ℝ) from ht),
            Set.indicator_of_notMem (show t ∉ Set.Ioo (0:ℝ) c from fun h => htc h.2),
            Set.indicator_of_notMem (show t ∉ Set.Iio c from htc)]
        simp
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0:ℝ) from ht),
          Set.indicator_of_notMem (show t ∉ Set.Ioo (0:ℝ) c from fun h => ht h.1)]
  have hInt : IntegrableOn (fun t => 8 * t ^ (p - 2)) (Set.Ioo (0:ℝ) c) volume := by
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, Set.Ioo_self]; exact integrableOn_empty
    · have h := (intervalIntegral.integrableOn_Ioo_rpow_iff hcpos).mpr hpm
      simpa [IntegrableOn] using h.const_mul 8
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0:ℝ) c)] (fun t => 8 * t ^ (p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg ht.1.le _)
  rw [hA]
  have hB : (∫⁻ t in Set.Ioo (0:ℝ) c, ENNReal.ofReal (8 * t ^ (p - 2)))
      = ENNReal.ofReal (8 * c ^ (p - 1) / (p - 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, integral_const_mul,
      ← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl hpm)]
    rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow hp1.ne']
    ring
  exact hB


private lemma final_alg {a p : ℝ} (ha : 0 ≤ a) (hp1 : 0 < p - 1) :
    ENNReal.ofReal a * ENNReal.ofReal (8 * (2*a)^(p-1) / (p-1))
      = ENNReal.ofReal (8 * 2^(p-1) / (p-1)) * ENNReal.ofReal (a ^ p) := by
  rw [← ENNReal.ofReal_mul ha]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * 2^(p-1)/(p-1))]
  congr 1
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]
    rw [Real.zero_rpow (by linarith : p ≠ 0)]
    ring
  · rw [Real.mul_rpow (by norm_num) ha]
    have h2 : a ^ p = a * a ^ (p-1) := by
      have h3 : a ^ (1 + (p-1)) = a ^ (1:ℝ) * a ^ (p-1) := Real.rpow_add h 1 (p-1)
      rw [Real.rpow_one] at h3
      rwa [show 1 + (p-1) = p by ring] at h3
    rw [h2]
    field_simp

private lemma key_double_le {φ : ℝ → ℝ} (hφ : Measurable φ) (hφnn : 0 ≤ φ)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Set.Ioi 0, (ENNReal.ofReal (8 / t) *
        (∫⁻ y, (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) y)) * ENNReal.ofReal (t ^ (p - 1)))
      = ENNReal.ofReal (8 * 2 ^ (p - 1) / (p - 1)) * ∫⁻ y, ENNReal.rpow (ENNReal.ofReal (φ y)) p := by
  have hp1 : 0 < p - 1 := by linarith
  -- step 1: push the t-constants inside the y-integral
  have step1 : (∫⁻ t in Set.Ioi 0, (ENNReal.ofReal (8 / t) *
        (∫⁻ y, (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) y)) * ENNReal.ofReal (t ^ (p - 1)))
      = ∫⁻ t in Set.Ioi 0, ∫⁻ y, ENNReal.ofReal (8/t) *
          (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y) := by
    apply lintegral_congr
    intro t
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  -- measurability for Tonelli
  have hcond : MeasurableSet {q : ℝ × ℝ | ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ q.2)} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2))
      (ENNReal.measurable_ofReal.comp (hφ.comp measurable_snd))
  have hind : Measurable (fun q : ℝ × ℝ =>
      (Set.indicator {y : ℝ | ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ y)} (fun y => ENNReal.ofReal (φ y))) q.2) := by
    have he : (fun q : ℝ × ℝ =>
        (Set.indicator {y : ℝ | ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ y)} (fun y => ENNReal.ofReal (φ y))) q.2)
        = fun q : ℝ × ℝ => if ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ q.2)
            then ENNReal.ofReal (φ q.2) else 0 := by
      funext q; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [he]
    exact Measurable.ite hcond (ENNReal.measurable_ofReal.comp (hφ.comp measurable_snd)) measurable_const
  have hmeas : AEMeasurable (Function.uncurry (fun t y => ENNReal.ofReal (8/t) *
        (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) y)))
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    apply Measurable.aemeasurable
    have h0 : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (8/q.1) *
        (ENNReal.ofReal (q.1^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) q.2)) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_fst)).mul
        ((ENNReal.measurable_ofReal.comp
          ((Real.continuous_rpow_const hp1.le).measurable.comp measurable_fst)).mul hind)
    show Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (8/q.1) *
        (ENNReal.ofReal (q.1^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (q.1/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) q.2))
    exact h0
  -- step 2: Tonelli
  have step2 : (∫⁻ t in Set.Ioi 0, ∫⁻ y, ENNReal.ofReal (8/t) *
          (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y))
      = ∫⁻ y, ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (8/t) *
          (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi 0)) (ν := volume) hmeas
  -- step 3: inner integral for fixed y
  have step3 : ∀ y : ℝ, (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (8/t) *
          (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y))
      = ENNReal.ofReal (8 * 2^(p-1)/(p-1)) * ENNReal.rpow (ENNReal.ofReal (φ y)) p := by
    intro y
    have hG : ∀ t ∈ Set.Ioi (0:ℝ),
        (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
          (fun y => ENNReal.ofReal (φ y))) y
        = (Set.Iio (2 * φ y)).indicator (fun _ => (1 : ENNReal)) t * ENNReal.ofReal (φ y) := by
      intro t ht
      rw [Set.indicator_apply, Set.indicator_apply]
      simp only [Set.mem_ofPred_eq, Set.mem_Iio]
      have heq : (ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)) ↔ t < 2 * φ y := by
        rw [ofReal_lt_ofReal_iff' (by linarith [Set.mem_Ioi.mp ht]) (hφnn y)]
        constructor <;> intro h <;> linarith
      by_cases h : t < 2 * φ y
      · rw [if_pos (heq.mpr h), if_pos h]; ring
      · rw [if_neg (fun hc => h (heq.mp hc)), if_neg h]; ring
    have hG2 : (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (8/t) *
          (ENNReal.ofReal (t^(p-1)) * (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y))
        = ENNReal.ofReal (φ y) * ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t^(p-1)) * ENNReal.ofReal (8/t) *
            (Set.Iio (2*φ y)).indicator (fun _ => (1:ENNReal)) t := by
      rw [← lintegral_const_mul' (ENNReal.ofReal (φ y)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [hG t ht]
      ring
    rw [hG2, inner_rpow_int (2*φ y) (mul_nonneg (by norm_num) (hφnn y)) hp,
        final_alg (hφnn y) hp1, ← ENNReal.ofReal_rpow_of_nonneg (hφnn y) (by linarith : (0:ℝ) ≤ p)]
    rfl
  -- step 4: pull the constant out of the y-integral
  have step4 : (∫⁻ y, ENNReal.ofReal (8 * 2^(p-1)/(p-1)) * ENNReal.rpow (ENNReal.ofReal (φ y)) p)
      = ENNReal.ofReal (8 * 2^(p-1)/(p-1)) * ∫⁻ y, ENNReal.rpow (ENNReal.ofReal (φ y)) p :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [step1, step2, lintegral_congr step3, step4]


private lemma per_n_bound {φ : ℝ → ℝ} (hφ : Measurable φ) (hφnn : 0 ≤ φ)
    {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x ⊓ (n:ENNReal)) p
      ≤ ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1)) *
          ∫⁻ x, ENNReal.rpow (ENNReal.ofReal (φ x)) p := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : (0:ℝ) ≤ p := hp_pos.le
  set g : ℝ → ℝ≥0∞ := fun x => hlMax (fun y => ENNReal.ofReal (φ y)) x with hg
  have hg_meas : Measurable g := by rw [hg]; exact measurable_hlMax_aux _
  set fn : ℝ → ℝ := fun x => (g x ⊓ (n:ENNReal)).toReal with hfn
  have hfn_ne : ∀ x, g x ⊓ (n:ENNReal) ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right
  have hfn_nn : ∀ x, 0 ≤ fn x := fun x => by rw [hfn]; exact ENNReal.toReal_nonneg
  have hfn_meas : Measurable fn := by rw [hfn]; exact (hg_meas.inf measurable_const).ennreal_toReal
  have hofReal : ∀ x, ENNReal.ofReal (fn x) = g x ⊓ (n:ENNReal) := fun x => by
    rw [hfn]; exact ENNReal.ofReal_toReal (hfn_ne x)
  have hcnt : ∫⁻ x, ENNReal.rpow (g x ⊓ (n:ENNReal)) p = ∫⁻ x, ENNReal.ofReal (fn x ^ p) := by
    apply lintegral_congr; intro x
    rw [← hofReal x]
    exact ENNReal.ofReal_rpow_of_nonneg (hfn_nn x) hp0
  rw [hcnt, lintegral_rpow_eq_lintegral_meas_lt_mul volume (Eventually.of_forall hfn_nn)
        hfn_meas.aemeasurable hp_pos]
  have hbound : (∫⁻ t in Set.Ioi 0, volume {a : ℝ | t < fn a} * ENNReal.ofReal (t^(p-1)))
      ≤ ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal (8 / t) *
          (∫⁻ y, (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y)) * ENNReal.ofReal (t ^ (p - 1)) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    have hS : MeasurableSet {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)} :=
      measurableSet_lt measurable_const (ENNReal.measurable_ofReal.comp hφ)
    have h1 : volume {a : ℝ | t < fn a}
        ≤ ENNReal.ofReal (8/t) * ∫⁻ y in {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)},
            ENNReal.ofReal (φ y) := by
      simpa [hfn, hg] using levelSet_toReal_bound φ hφ hφnn ht0 n
    calc volume {a : ℝ | t < fn a} * ENNReal.ofReal (t^(p-1))
        ≤ (ENNReal.ofReal (8/t) * ∫⁻ y in {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)},
            ENNReal.ofReal (φ y)) * ENNReal.ofReal (t^(p-1)) := mul_le_mul_left h1 _
      _ = (ENNReal.ofReal (8 / t) * (∫⁻ y, (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y)) * ENNReal.ofReal (t ^ (p - 1)) := by
          rw [← lintegral_indicator hS]
  calc ENNReal.ofReal p * (∫⁻ t in Set.Ioi 0, volume {a : ℝ | t < fn a} * ENNReal.ofReal (t^(p-1)))
      ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi 0, (ENNReal.ofReal (8 / t) *
          (∫⁻ y, (Set.indicator {y : ℝ | ENNReal.ofReal (t/2) < ENNReal.ofReal (φ y)}
            (fun y => ENNReal.ofReal (φ y))) y)) * ENNReal.ofReal (t ^ (p - 1))) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal p * (ENNReal.ofReal (8 * 2^(p-1)/(p-1)) *
          ∫⁻ y, ENNReal.rpow (ENNReal.ofReal (φ y)) p) := by rw [key_double_le hφ hφnn hp]
    _ = ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1)) *
          ∫⁻ y, ENNReal.rpow (ENNReal.ofReal (φ y)) p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp0]
        congr 1
        ring_nf

private lemma hlMax_rpow_sup_eq {φ : ℝ → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (x : ℝ) :
    (⨆ n : ℕ, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x ⊓ (n:ENNReal)) p)
      = ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x) p := by
  have hsup_a : (⨆ n : ℕ, (hlMax (fun y => ENNReal.ofReal (φ y)) x) ⊓ (n:ENNReal))
      = hlMax (fun y => ENNReal.ofReal (φ y)) x := by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmono_a : Monotone fun n : ℕ => (hlMax (fun y => ENNReal.ofReal (φ y)) x) ⊓ (n:ENNReal) :=
    fun m n h => inf_le_inf_left _ (by exact_mod_cast h)
  have hlim_a : Tendsto (fun n : ℕ => (hlMax (fun y => ENNReal.ofReal (φ y)) x) ⊓ (n:ENNReal))
      atTop (𝓝 (hlMax (fun y => ENNReal.ofReal (φ y)) x)) := by
    have := tendsto_atTop_iSup hmono_a
    rwa [hsup_a] at this
  have hlim_b : Tendsto (fun n : ℕ =>
      ENNReal.rpow ((hlMax (fun y => ENNReal.ofReal (φ y)) x) ⊓ (n:ENNReal)) p)
      atTop (𝓝 (ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x) p)) :=
    ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp hlim_a
  have hmono_b : Monotone fun n : ℕ =>
      ENNReal.rpow ((hlMax (fun y => ENNReal.ofReal (φ y)) x) ⊓ (n:ENNReal)) p :=
    fun m n h => ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast h)) hp0
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono_b) hlim_b

private theorem lintegral_rpow_hlMax_le_real {φ : ℝ → ℝ} (hφ : Measurable φ) (hφnn : 0 ≤ φ)
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x) p
      ≤ ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1)) *
          ∫⁻ x, ENNReal.rpow (ENNReal.ofReal (φ x)) p := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp0 : (0:ℝ) ≤ p := hp_pos.le
  have hg_meas : Measurable (fun x => hlMax (fun y => ENNReal.ofReal (φ y)) x) := measurable_hlMax_aux _
  have hmct : ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x) p
      = ⨆ n : ℕ, ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x ⊓ (n:ENNReal)) p := by
    rw [← lintegral_iSup (f := fun n x => ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x ⊓ (n:ENNReal)) p)
      (fun n => ((ENNReal.continuous_rpow_const (y := p)).measurable).comp (hg_meas.inf measurable_const))
      (fun m n h x => ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast h)) hp0)]
    congr 1
    funext x
    exact (hlMax_rpow_sup_eq hp0 x).symm
  calc ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x) p
      = ⨆ n : ℕ, ∫⁻ x, ENNReal.rpow (hlMax (fun y => ENNReal.ofReal (φ y)) x ⊓ (n:ENNReal)) p := hmct
    _ ≤ ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1)) *
          ∫⁻ x, ENNReal.rpow (ENNReal.ofReal (φ x)) p := iSup_le fun n => per_n_bound hφ hφnn hp n


theorem lintegral_rpow_hlMax_le {ψ : ℝ → ENNReal} (hψ : Measurable ψ) (hψfin : ∀ x, ψ x ≠ ⊤)
    {p : ℝ} (hp : 1 < p) (hH : lintegral volume (fun x => ENNReal.rpow (ψ x) p) < ⊤) :
    lintegral volume (fun x => ENNReal.rpow (Commons.Analysis.Maximal.hlMax ψ x) p)
      ≤ ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1))
        * lintegral volume (fun x => ENNReal.rpow (ψ x) p) := by
  set φ : ℝ → ℝ := fun x => (ψ x).toReal with hφdef
  have hφ : Measurable φ := by rw [hφdef]; exact hψ.ennreal_toReal
  have hφnn : 0 ≤ φ := fun x => by rw [hφdef]; exact ENNReal.toReal_nonneg
  have hψeq : ∀ x, ENNReal.ofReal (φ x) = ψ x := by
    intro x; rw [hφdef]; exact ENNReal.ofReal_toReal (hψfin x)
  simpa only [hψeq] using lintegral_rpow_hlMax_le_real hφ hφnn hp


end Commons.Analysis.Maximal