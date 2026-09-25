import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_weak_type
import Submission.Commons.MeasureTheory.Measurable.union_Icc_measurable
import Submission.Commons.Analysis.Maximal.hlMax_eq_iSup_rat
import Submission.Commons.Analysis.Maximal.lintegral_rpow_hlMax_le

namespace Commons.Analysis.Maximal

open _root_.MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-! ### Level-set description of `hlMax` -/

lemma hlMax_lt_iff (φ : ℝ → ℝ≥0∞) (x : ℝ) (t : ℝ≥0∞) :
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

lemma hlMax_le_of_mem (φ : ℝ → ℝ≥0∞) {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, φ y ≤ hlMax φ x := by
  rw [hlMax]
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ⟨ha, hb⟩ le_rfl))

/-- The set of intervals whose average of `φ` exceeds `t`. -/
def goodIntervals (φ : ℝ → ℝ≥0∞) (t : ℝ≥0∞) : Set (ℝ × ℝ) :=
  {p | t < ENNReal.ofReal (p.2 - p.1)⁻¹ * ∫⁻ y in Set.Icc p.1 p.2, φ y}

lemma goodIntervals_snd_lt_fst {φ : ℝ → ℝ≥0∞} {t : ℝ≥0∞} {p : ℝ × ℝ}
    (hp : p ∈ goodIntervals φ t) : p.1 < p.2 := by
  rw [goodIntervals, Set.mem_ofPred_eq] at hp
  by_contra h
  push Not at h
  have hinv : (p.2 - p.1)⁻¹ ≤ 0 := inv_nonpos.mpr (sub_nonpos.mpr h)
  have hzero : ENNReal.ofReal (p.2 - p.1)⁻¹ * ∫⁻ y in Set.Icc p.1 p.2, φ y = 0 := by
    rw [ENNReal.ofReal_eq_zero.mpr hinv, zero_mul]
  rw [hzero] at hp
  exact absurd hp not_lt_bot

lemma levelSet_eq_iUnion (φ : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    {x : ℝ | t < hlMax φ x} = ⋃ p ∈ goodIntervals φ t, Set.Icc p.1 p.2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hlt⟩ := (hlMax_lt_iff φ x t).mp hx
    exact Set.mem_iUnion.mpr ⟨(a, b), Set.mem_iUnion.mpr ⟨hlt, ⟨ha, hb⟩⟩⟩
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hpC, hxp⟩ := Set.mem_iUnion.mp hp
    rw [Set.mem_Icc] at hxp
    exact lt_of_lt_of_le hpC (hlMax_le_of_mem φ hxp.1 hxp.2)

/-- **Measurability of the Hardy--Littlewood maximal function** of an arbitrary (not
necessarily measurable) function. -/
theorem measurable_hlMax (φ : ℝ → ℝ≥0∞) : Measurable (hlMax φ) := by
  apply measurable_of_Ioi
  intro t
  show MeasurableSet {x : ℝ | t < hlMax φ x}
  rw [levelSet_eq_iUnion]
  exact _root_.Commons.MeasureTheory.Measurable.union_Icc_measurable _
    (fun p hp => goodIntervals_snd_lt_fst hp)

/-! ### A measurable minorant of `φ` capturing all its interval averages -/

/-- For a rational interval `J`, a measurable minorant of `φ` with the same integral over `J`. -/
noncomputable def innerMinorant (φ : ℝ → ℝ≥0∞) (p : ℚ × ℚ) : ℝ → ℝ≥0∞ :=
  Classical.choose
    (exists_measurable_le_lintegral_eq (volume.restrict (Set.Icc (p.1 : ℝ) (p.2 : ℝ))) φ)

lemma innerMinorant_spec (φ : ℝ → ℝ≥0∞) (p : ℚ × ℚ) :
    Measurable (innerMinorant φ p) ∧ innerMinorant φ p ≤ φ ∧
      ∫⁻ x, φ x ∂(volume.restrict (Set.Icc (p.1 : ℝ) (p.2 : ℝ)))
        = ∫⁻ x, innerMinorant φ p x ∂(volume.restrict (Set.Icc (p.1 : ℝ) (p.2 : ℝ))) :=
  Classical.choose_spec (exists_measurable_le_lintegral_eq _ φ)

lemma measurable_innerMinorant (φ : ℝ → ℝ≥0∞) (p : ℚ × ℚ) : Measurable (innerMinorant φ p) :=
  (innerMinorant_spec φ p).1

lemma innerMinorant_le (φ : ℝ → ℝ≥0∞) (p : ℚ × ℚ) : innerMinorant φ p ≤ φ :=
  (innerMinorant_spec φ p).2.1

lemma lintegral_innerMinorant_eq (φ : ℝ → ℝ≥0∞) (q r : ℚ) :
    ∫⁻ x in Set.Icc (q : ℝ) (r : ℝ), φ x
      = ∫⁻ x in Set.Icc (q : ℝ) (r : ℝ), innerMinorant φ (q, r) x :=
  (innerMinorant_spec φ (q, r)).2.2

/-- The pointwise supremum of the `innerMinorant`s over all rational intervals: a measurable
minorant of `φ` whose interval averages dominate those of `φ`. -/
noncomputable def innerHull (φ : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun x => ⨆ (p : ℚ × ℚ), innerMinorant φ p x

lemma measurable_innerHull (φ : ℝ → ℝ≥0∞) : Measurable (innerHull φ) :=
  Measurable.iSup (fun p => measurable_innerMinorant φ p)

lemma innerHull_le (φ : ℝ → ℝ≥0∞) : innerHull φ ≤ φ :=
  fun x => iSup_le fun p => innerMinorant_le φ p x

/-- Each rational-interval minorant is dominated by the hull. -/
lemma innerMinorant_le_innerHull (φ : ℝ → ℝ≥0∞) (p : ℚ × ℚ) :
    innerMinorant φ p ≤ innerHull φ :=
  fun x => le_iSup (fun p : ℚ × ℚ => innerMinorant φ p x) p

lemma hlMax_le_hlMax_innerHull (φ : ℝ → ℝ≥0∞) (x : ℝ) :
    hlMax φ x ≤ hlMax (innerHull φ) x := by
  rw [hlMax_eq_iSup_rat φ x]
  refine iSup_le fun q => iSup_le fun r => iSup_le fun hqr => ?_
  have hJ : ∫⁻ y in Set.Icc (q : ℝ) (r : ℝ), φ y
      ≤ ∫⁻ y in Set.Icc (q : ℝ) (r : ℝ), innerHull φ y := by
    rw [lintegral_innerMinorant_eq φ q r]
    exact lintegral_mono fun y => innerMinorant_le_innerHull φ (q, r) y
  exact le_trans (mul_le_mul_right hJ _) (hlMax_le_of_mem (innerHull φ) hqr.1 hqr.2)


open scoped Classical in
/-- **Strong `(p,p)` type (`p > 1`) of the (centred) Hardy--Littlewood maximal function on
`ℝ`**: `∫ (M f)^p ≤ C^p ∫ |f|^p`, where `M f x = sup { (b-a)⁻¹ ∫_a^b |f| : a ≤ x ≤ b }`. -/
theorem real_maximal_strong_type (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
      ∫⁻ x, (⨆ (a : ℝ) (b : ℝ) (_ : a ≤ x ∧ x ≤ b),
          ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ‖f y‖ₑ) ^ p
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := by linarith
  set K : ℝ := 8 * p * 2 ^ (p - 1) / (p - 1) with hK
  have hKpos : 0 < K := by
    rw [hK]
    positivity
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hKpos _, fun f => ?_⟩
  set φ : ℝ → ℝ≥0∞ := fun y => ‖f y‖ₑ with hφ
  have hφfin : ∀ x, φ x ≠ ⊤ := by
    intro x
    change ‖f x‖ₑ ≠ ⊤
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_ne_top
  set ψ : ℝ → ℝ≥0∞ := innerHull φ with hψ
  have hψmeas : Measurable ψ := measurable_innerHull φ
  have hψle : ψ ≤ φ := innerHull_le φ
  have hψfin : ∀ x, ψ x ≠ ⊤ := fun x => ne_top_of_le_ne_top (hφfin x) (hψle x)
  have hL : (∫⁻ x, (⨆ (a : ℝ) (b : ℝ) (_ : a ≤ x ∧ x ≤ b),
        ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ‖f y‖ₑ) ^ p)
      = ∫⁻ x, (hlMax φ x) ^ p := rfl
  have hCp : (K ^ (1 / p)) ^ p = K := by
    rw [← Real.rpow_mul hKpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  rw [hL]
  by_cases htop : ∫⁻ x, (φ x) ^ p = ⊤
  · rw [htop, hCp]
    exact le_top.trans (le_of_eq
      (ENNReal.mul_top (ENNReal.ofReal_pos.mpr hKpos).ne').symm)
  · have hH : ∫⁻ x, (ψ x) ^ p < ⊤ :=
      lt_of_le_of_lt (lintegral_mono fun x => ENNReal.rpow_le_rpow (hψle x) hp0.le)
        (lt_top_iff_ne_top.mpr htop)
    have h1 : ∫⁻ x, (hlMax φ x) ^ p ≤ ∫⁻ x, (hlMax ψ x) ^ p :=
      lintegral_mono fun x => ENNReal.rpow_le_rpow (hlMax_le_hlMax_innerHull φ x) hp0.le
    have h2 := lintegral_rpow_hlMax_le hψmeas hψfin hp hH
    have h3 : ∫⁻ x, (ψ x) ^ p ≤ ∫⁻ x, (φ x) ^ p :=
      lintegral_mono fun x => ENNReal.rpow_le_rpow (hψle x) hp0.le
    calc ∫⁻ x, (hlMax φ x) ^ p
        ≤ ∫⁻ x, (hlMax ψ x) ^ p := h1
      _ ≤ ENNReal.ofReal K * ∫⁻ x, (ψ x) ^ p := h2
      _ ≤ ENNReal.ofReal K * ∫⁻ x, (φ x) ^ p := mul_le_mul_right h3 _
      _ = ENNReal.ofReal ((K ^ (1 / p)) ^ p) * ∫⁻ x, (φ x) ^ p := by rw [hCp]

end Commons.Analysis.Maximal

