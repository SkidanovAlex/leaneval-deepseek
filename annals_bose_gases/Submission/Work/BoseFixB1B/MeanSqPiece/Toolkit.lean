import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ENNReal Real

namespace Work.BoseFixB1B.MeanSqPiece
namespace CruxMean

/-- The 1D window `[-ℓ/2, ℓ/2] ∩ [s t - s/2, s t + s/2]`. -/
def I1 (s ℓ t : ℝ) : Set ℝ :=
  Set.Icc (-(ℓ / 2)) (ℓ / 2) ∩ Set.Icc (s * t - s / 2) (s * t + s / 2)

/-- The length of the 1D window. -/
noncomputable def L1 (s ℓ t : ℝ) : ℝ := (volume (I1 s ℓ t)).toReal

/-- The `n`-fold product of windows, as a subset of the coordinate space `Fin n → ℝ`. -/
def Bx {n : ℕ} (s ℓ : ℝ) (u : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => I1 s ℓ (u i))

/-- The `n`-fold product of `[-ℓ/2,ℓ/2]`, as a subset of the coordinate space `Fin n → ℝ`. -/
def Cx (n : ℕ) (ℓ : ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (-(ℓ / 2)) (ℓ / 2))

/-- The 1D crux estimate, packaged as a `Prop` so that it can be passed as a hypothesis
(and proved later as `Work.BoseFixB1B.MeanSqPiece.CruxMean.oneD`). -/
abbrev OneDLemma : Prop :=
  ∀ {s ℓ : ℝ}, 0 < s → s ≤ ℓ → ∀ F : ℝ → ENNReal,
    AEMeasurable F (volume : Measure ℝ) →
    ∫⁻ t : ℝ, (ENNReal.ofReal (1 / L1 s ℓ t) * ∫⁻ y in I1 s ℓ t, F y) ^ 2
      ≤ ENNReal.ofReal (9 / s) * ∫⁻ y in Set.Icc (-(ℓ / 2)) (ℓ / 2), F y ^ 2

@[simp] lemma mem_I1 {s ℓ t y : ℝ} :
    y ∈ I1 s ℓ t ↔ y ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2) ∧ y ∈ Set.Icc (s * t - s / 2) (s * t + s / 2) :=
  Iff.rfl

@[simp] lemma mem_Bx {n : ℕ} {s ℓ : ℝ} {u x : Fin n → ℝ} :
    x ∈ Bx s ℓ u ↔ ∀ i, x i ∈ I1 s ℓ (u i) := by
  rw [Bx, Set.mem_pi]
  simp

@[simp] lemma mem_Cx {n : ℕ} {ℓ : ℝ} {x : Fin n → ℝ} :
    x ∈ Cx n ℓ ↔ ∀ i, x i ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2) := by
  rw [Cx, Set.mem_pi]
  simp

lemma measurableSet_I1 (s ℓ t : ℝ) : MeasurableSet (I1 s ℓ t) :=
  measurableSet_Icc.inter measurableSet_Icc

lemma I1_subset (s ℓ t : ℝ) : I1 s ℓ t ⊆ Set.Icc (-(ℓ / 2)) (ℓ / 2) := Set.inter_subset_left

lemma L1_nonneg (s ℓ t : ℝ) : 0 ≤ L1 s ℓ t := ENNReal.toReal_nonneg

lemma measurableSet_Bx {n : ℕ} (s ℓ : ℝ) (u : Fin n → ℝ) : MeasurableSet (Bx s ℓ u) := by
  rw [Bx]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_I1 s ℓ (u i))

lemma measurableSet_Cx (n : ℕ) (ℓ : ℝ) : MeasurableSet (Cx n ℓ) := by
  rw [Cx]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)

end CruxMean
end Work.BoseFixB1B.MeanSqPiece

namespace Work.BoseFixB1B.MeanSqPiece
namespace CruxMean

lemma I1_eq_Icc (s ℓ t : ℝ) :
    I1 s ℓ t = Set.Icc (max (-(ℓ / 2)) (s * t - s / 2)) (min (ℓ / 2) (s * t + s / 2)) := by
  rw [I1, Set.Icc_inter_Icc]

lemma L1_eq (s ℓ t : ℝ) :
    L1 s ℓ t = max (min (ℓ / 2) (s * t + s / 2) - max (-(ℓ / 2)) (s * t - s / 2)) 0 := by
  rw [L1, I1_eq_Icc, Real.volume_Icc]
  by_cases h : 0 ≤ min (ℓ / 2) (s * t + s / 2) - max (-(ℓ / 2)) (s * t - s / 2)
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · push_neg at h
    rw [ENNReal.ofReal_eq_zero.mpr h.le, ENNReal.toReal_zero, max_eq_right h.le]

end CruxMean
end Work.BoseFixB1B.MeanSqPiece

namespace Work.BoseFixB1B.MeanSqPiece.CruxMean

variable {α : Type*} [MeasurableSpace α]

/-! ## Squared Cauchy–Schwarz for lintegrals -/

/-- **Cauchy–Schwarz** (`p = q = 2` Hölder, squared) for `ℝ≥0∞`-valued lintegrals. -/
lemma sq_lintegral_mul_le (μ : Measure α) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num,
    ENNReal.rpow_inv_natCast_pow (show (2 : ℕ) ≠ 0 by norm_num),
    ENNReal.rpow_inv_natCast_pow (show (2 : ℕ) ≠ 0 by norm_num)]
  simp

/-- Cauchy–Schwarz for set lintegrals. -/
lemma sq_setLIntegral_mul_le {J : Set ℝ} {f g : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    (∫⁻ y in J, f y * g y) ^ 2 ≤ (∫⁻ y in J, f y ^ 2) * (∫⁻ y in J, g y ^ 2) :=
  sq_lintegral_mul_le (volume.restrict J)
    (hf.mono_measure Measure.restrict_le_self) (hg.mono_measure Measure.restrict_le_self)

/-! ## The geometry of the 1D window -/

/-- In the left regime the window's right end lies inside `[-ℓ/2, ℓ/2]`. -/
lemma left_upper {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : s * t - s / 2 ≤ -(ℓ / 2)) :
    s * t + s / 2 ≤ ℓ / 2 := by
  by_contra hc
  rw [not_le] at hc
  linarith

/-- In the right regime the window's left end lies inside `[-ℓ/2, ℓ/2]`. -/
lemma right_lower {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : ℓ / 2 ≤ s * t + s / 2) :
    -(ℓ / 2) ≤ s * t - s / 2 := by
  by_contra hc
  rw [not_le] at hc
  linarith

/-- Left regime: the window is `[-ℓ/2, s t + s/2]`. -/
lemma I1_eq_left {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : s * t - s / 2 ≤ -(ℓ / 2)) :
    I1 s ℓ t = Set.Icc (-(ℓ / 2)) (s * t + s / 2) := by
  rw [I1_eq_Icc, max_eq_left h, min_eq_right (left_upper hsl h)]

/-- Left regime: the length is `s t + s/2 + ℓ/2` (clamped at `0`). -/
lemma L1_eq_left {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : s * t - s / 2 ≤ -(ℓ / 2)) :
    L1 s ℓ t = max (s * t + s / 2 + ℓ / 2) 0 := by
  rw [L1_eq, max_eq_left h, min_eq_right (left_upper hsl h)]
  congr 1
  ring

/-- Right regime: the window is `[s t - s/2, ℓ/2]`. -/
lemma I1_eq_right {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : ℓ / 2 ≤ s * t + s / 2) :
    I1 s ℓ t = Set.Icc (s * t - s / 2) (ℓ / 2) := by
  rw [I1_eq_Icc, min_eq_left h, max_eq_right (right_lower hsl h)]

/-- Right regime: the length is `ℓ/2 - s t + s/2` (clamped at `0`). -/
lemma L1_eq_right {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : ℓ / 2 ≤ s * t + s / 2) :
    L1 s ℓ t = max (ℓ / 2 - s * t + s / 2) 0 := by
  rw [L1_eq, min_eq_left h, max_eq_right (right_lower hsl h)]
  congr 1
  ring

/-- Middle regime: the window sits inside the box. -/
lemma I1_eq_mid {s ℓ t : ℝ} (h1 : -(ℓ / 2) < s * t - s / 2)
    (h2 : s * t + s / 2 < ℓ / 2) :
    I1 s ℓ t = Set.Icc (s * t - s / 2) (s * t + s / 2) := by
  rw [I1_eq_Icc, max_eq_right h1.le, min_eq_right h2.le]

/-- Middle regime: the length is `s`. -/
lemma L1_eq_mid {s ℓ t : ℝ} (hs : 0 < s) (h1 : -(ℓ / 2) < s * t - s / 2)
    (h2 : s * t + s / 2 < ℓ / 2) :
    L1 s ℓ t = s := by
  rw [L1_eq, max_eq_right h1.le, min_eq_right h2.le]
  have h : s * t + s / 2 - (s * t - s / 2) = s := by ring
  rw [h, max_eq_left hs.le]

/-- The window is contained in `[-ℓ/2,ℓ/2]`. -/
lemma mem_I1_bounds {s ℓ t y : ℝ} (hy : y ∈ I1 s ℓ t) :
    -(ℓ / 2) ≤ y ∧ y ≤ ℓ / 2 := hy.1

/-- Membership in the window, in the form used for the counting. -/
lemma mem_I1_iff' {s ℓ t y : ℝ} :
    y ∈ I1 s ℓ t ↔ -(ℓ / 2) ≤ y ∧ y ≤ ℓ / 2 ∧ s * t - s / 2 ≤ y ∧ y ≤ s * t + s / 2 := by
  rw [mem_I1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- The `t`-set on which a fixed `y` lies in the window has measure at most `1`. -/
lemma measure_tube_le_one {s ℓ : ℝ} (hs : 0 < s) (y : ℝ) :
    volume {t : ℝ | y ∈ I1 s ℓ t} ≤ 1 := by
  have hsub : {t : ℝ | y ∈ I1 s ℓ t} ⊆ Set.Icc ((y - s / 2) / s) ((y + s / 2) / s) := by
    intro t ht
    have ht' : y ∈ I1 s ℓ t := ht
    rw [mem_I1_iff'] at ht'
    have h1 : t ≤ (y + s / 2) / s := by
      rw [le_div_iff₀ hs]
      linarith [ht'.2.2.2]
    have h2 : (y - s / 2) / s ≤ t := by
      rw [div_le_iff₀ hs]
      linarith [ht'.2.2.1]
    exact ⟨h2, h1⟩
  calc volume {t : ℝ | y ∈ I1 s ℓ t} ≤ volume (Set.Icc ((y - s / 2) / s) ((y + s / 2) / s)) :=
        measure_mono hsub
    _ = ENNReal.ofReal ((y + s / 2) / s - (y - s / 2) / s) := Real.volume_Icc
    _ = 1 := by
        rw [show (y + s / 2) / s - (y - s / 2) / s = 1 by field_simp; ring]
        simp

/-! ## The weighted `L¹`-norms over the window -/

/-- Translation of an interval set-lintegral. -/
lemma setLIntegral_Icc_comp_add (a b c : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y in Set.Icc a b, f (y + c) = ∫⁻ u in Set.Icc (a + c) (b + c), f u := by
  have h1 : ∫⁻ y in Set.Icc a b, f (y + c)
      = ∫⁻ y : ℝ, (Set.Icc a b).indicator (fun y => f (y + c)) y :=
    (lintegral_indicator measurableSet_Icc _).symm
  have h2 : ∫⁻ y : ℝ, (Set.Icc a b).indicator (fun y => f (y + c)) y
      = ∫⁻ y : ℝ, (Set.Icc (a + c) (b + c)).indicator f y := by
    rw [← MeasureTheory.lintegral_add_right_eq_self
      (fun y : ℝ => (Set.Icc a b).indicator (fun y => f (y + c)) y) (-c)]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_Icc]
    by_cases h : a ≤ y + -c ∧ y + -c ≤ b
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
      congr 1
      ring
    · rw [if_neg h, if_neg (fun hh => h ⟨by linarith [hh.1], by linarith [hh.2]⟩)]
  rw [h1, h2, lintegral_indicator measurableSet_Icc]

/-- `∫⁻_{u ∈ (0,L]} (√u)⁻¹ du = 2√L` for `L ≥ 0`. -/
lemma lintegral_inv_sqrt_Ioc {L : ℝ} (hL : 0 ≤ L) :
    ∫⁻ u in Set.Ioc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹
      = 2 * ENNReal.ofReal (Real.sqrt L) := by
  rcases eq_or_lt_of_le hL with h | h
  · subst h
    rw [Set.Ioc_self, setLIntegral_empty, Real.sqrt_zero, ENNReal.ofReal_zero, mul_zero]
  · have hint : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) (Set.Ioc (0 : ℝ) L) volume :=
      (by
        rw [← Set.uIoc_of_le h.le]
        exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).def')
    have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
        (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact Real.rpow_nonneg hu.1.le _
    have hcongr : (fun u : ℝ => (ENNReal.ofReal (Real.sqrt u))⁻¹)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) L)]
          (fun u : ℝ => ENNReal.ofReal (u ^ (-(1 / 2) : ℝ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.rpow_neg hu.1.le, ← Real.sqrt_eq_rpow,
        ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hu.1)]
    rw [lintegral_congr_ae hcongr,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := volume.restrict (Set.Ioc (0 : ℝ) L)) hint h0]
    congr 1
    rw [← intervalIntegral.integral_of_le h.le,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2))),
      show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero,
      Real.sqrt_eq_rpow]
    have hrpow : L ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * L ^ ((1 : ℝ) / 2) := by
      rw [div_eq_mul_inv, show (((1 : ℝ) / 2))⁻¹ = 2 by norm_num, mul_comm]
    rw [hrpow, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- `∫⁻_{u ∈ [0,L]} (√u)⁻¹ du = 2√(L ∨ 0)`. -/
lemma lintegral_inv_sqrt_Icc {L : ℝ} :
    ∫⁻ u in Set.Icc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹
      = 2 * ENNReal.ofReal (Real.sqrt (max L 0)) := by
  by_cases hL0 : L ≤ 0
  · have hnull : Set.Icc (0 : ℝ) L =ᵐ[volume] (∅ : Set ℝ) := by
      rw [ae_eq_empty, Real.volume_Icc, ENNReal.ofReal_eq_zero]
      linarith
    rw [setLIntegral_congr hnull, setLIntegral_empty, max_eq_right hL0, Real.sqrt_zero,
      ENNReal.ofReal_zero, mul_zero]
  · have hL0' : 0 < L := not_le.mp hL0
    have hsub : Set.Icc (0 : ℝ) L ⊆ Set.Ioc (0 : ℝ) L ∪ {0} := by
      intro u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨h, hu.2⟩
    have h1 : ∫⁻ u : ℝ, (Set.Icc (0 : ℝ) L).indicator
          (fun u => (ENNReal.ofReal (Real.sqrt u))⁻¹) u
        ≤ ∫⁻ u : ℝ, ((Set.Ioc (0 : ℝ) L).indicator
            (fun u => (ENNReal.ofReal (Real.sqrt u))⁻¹) u
          + ({0} : Set ℝ).indicator (fun _ => (⊤ : ℝ≥0∞)) u) := by
      refine lintegral_mono fun u => ?_
      by_cases hu : u ∈ Set.Icc (0 : ℝ) L
      · rcases hsub hu with h | h
        · have hne : u ≠ 0 := ne_of_gt h.1
          simp [Set.indicator_of_mem hu, Set.indicator_of_mem h, hne]
        · subst h
          simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hle2 : ∫⁻ u in Set.Icc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹
        ≤ ∫⁻ u in Set.Ioc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹ := by
      rw [← lintegral_indicator measurableSet_Icc]
      refine h1.trans (le_of_eq ?_)
      rw [lintegral_add_right _ (Measurable.indicator measurable_const
          (measurableSet_singleton 0)), lintegral_indicator measurableSet_Ioc,
        lintegral_indicator (measurableSet_singleton 0), setLIntegral_const,
        measure_singleton (0 : ℝ), mul_zero, add_zero]
    have heq : ∫⁻ u in Set.Icc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹
        = ∫⁻ u in Set.Ioc (0 : ℝ) L, (ENNReal.ofReal (Real.sqrt u))⁻¹ :=
      le_antisymm hle2 (lintegral_mono_set (fun u hu => ⟨hu.1.le, hu.2⟩))
    rw [heq, lintegral_inv_sqrt_Ioc hL0'.le, max_eq_left hL0'.le]

/-- **The left-regime weight integral**: `∫_{I(t)} (y+ℓ/2)^{-1/2} = 2√(L(t))`. -/
lemma weight_left {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : s * t - s / 2 ≤ -(ℓ / 2)) :
    ∫⁻ y in I1 s ℓ t, (ENNReal.ofReal (Real.sqrt (y + ℓ / 2)))⁻¹
      = 2 * ENNReal.ofReal (Real.sqrt (L1 s ℓ t)) := by
  rw [I1_eq_left hsl h, L1_eq_left hsl h,
    setLIntegral_Icc_comp_add (-(ℓ / 2)) (s * t + s / 2) (ℓ / 2)
      (fun u => (ENNReal.ofReal (Real.sqrt u))⁻¹),
    show -(ℓ / 2) + ℓ / 2 = (0 : ℝ) by ring, lintegral_inv_sqrt_Icc]

/-- Reflection of an interval set-lintegral. -/
lemma setLIntegral_Icc_comp_neg (a b : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in Set.Icc a b, g (-y) = ∫⁻ v in Set.Icc (-b) (-a), g v := by
  have h1 : ∫⁻ y in Set.Icc a b, g (-y)
      = ∫⁻ y : ℝ, (Set.Icc a b).indicator (fun y => g (-y)) y :=
    (lintegral_indicator measurableSet_Icc _).symm
  have h2 : ∫⁻ y : ℝ, (Set.Icc a b).indicator (fun y => g (-y)) y
      = ∫⁻ y : ℝ, (Set.Icc (-b) (-a)).indicator g y := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      measurableEmbedding_neg (fun y : ℝ => (Set.Icc a b).indicator (fun y => g (-y)) y)]
    refine lintegral_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_Icc]
    by_cases h : a ≤ -y ∧ -y ≤ b
    · rw [if_pos h, if_pos ⟨by linarith [h.2], by linarith [h.1]⟩]
      simp
    · rw [if_neg h, if_neg (fun hh => h ⟨by linarith [hh.2], by linarith [hh.1]⟩)]
  rw [h1, h2, lintegral_indicator measurableSet_Icc]

/-- Reflection + shift of an interval set-lintegral. -/
lemma setLIntegral_Icc_comp_sub (a b c : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in Set.Icc a b, g (c - y) = ∫⁻ u in Set.Icc (c - b) (c - a), g u := by
  have h1 : ∫⁻ y in Set.Icc a b, g (c - y)
      = ∫⁻ y in Set.Icc a b, (fun z => g (-z)) (y + (-c)) := by
    refine lintegral_congr fun y => ?_
    exact congrArg g (by ring)
  rw [h1, setLIntegral_Icc_comp_add a b (-c) (fun z => g (-z)),
    show a + -c = -(c - a) by ring, show b + -c = -(c - b) by ring,
    setLIntegral_Icc_comp_neg (-(c - a)) (-(c - b)) g,
    show -(-(c - b)) = c - b by ring, show -(-(c - a)) = c - a by ring]

/-- **The right-regime weight integral**: `∫_{I(t)} (ℓ/2-y)^{-1/2} = 2√(L(t))`. -/
lemma weight_right {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : ℓ / 2 ≤ s * t + s / 2) :
    ∫⁻ y in I1 s ℓ t, (ENNReal.ofReal (Real.sqrt (ℓ / 2 - y)))⁻¹
      = 2 * ENNReal.ofReal (Real.sqrt (L1 s ℓ t)) := by
  rw [I1_eq_right hsl h, L1_eq_right hsl h,
    setLIntegral_Icc_comp_sub (s * t - s / 2) (ℓ / 2) (ℓ / 2)
      (fun u => (ENNReal.ofReal (Real.sqrt u))⁻¹),
    show ℓ / 2 - (s * t - s / 2) = ℓ / 2 - s * t + s / 2 by ring,
    show ℓ / 2 - ℓ / 2 = (0 : ℝ) by ring, lintegral_inv_sqrt_Icc]

/-! ## The counting computations (the removal of the logarithm) -/

/-- The `L¹`-norm of the weight over the window, in the form used by the counting. -/
lemma weight_left_Icc {s ℓ y : ℝ} (hsl : s ≤ ℓ) (h : s * y - s / 2 ≤ -(ℓ / 2)) :
    ∫⁻ u in I1 s ℓ y, (ENNReal.ofReal (Real.sqrt (u + ℓ / 2)))⁻¹ = 2 * ENNReal.ofReal (Real.sqrt (L1 s ℓ y)) :=
  weight_left hsl h

/-- **Left-regime counting.**  For `y` in the box, the total weight of the windows `I(t)` that
contain `y` and stick out to the left, measured with `(y + ℓ/2)^{-1/2}`, is at most `4/s`.

This is the sharp (log-free) step: the window length `L(t) = s t + s/2 + ℓ/2` is used as the
integration variable, and the antiderivative `-4/s·L^{-1/2}` of `2 L^{-3/2}` is evaluated at the
two ends. -/
lemma counting_left {s ℓ : ℝ} (hs : 0 < s) (hsl : s ≤ ℓ) {y : ℝ}
    (hy : y ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2)) :
    (ENNReal.ofReal (Real.sqrt (y + ℓ / 2))) *
        (∫⁻ t in Set.Icc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
          ENNReal.ofReal (2 * (L1 s ℓ t) ^ (-(3 / 2) : ℝ)))
      ≤ ENNReal.ofReal (4 / s) := by
  have hy0 : 0 ≤ y + ℓ / 2 := by linarith [hy.1]
  rcases eq_or_lt_of_le hy0 with hty | hty
  · rw [← hty, Real.sqrt_zero, ENNReal.ofReal_zero, zero_mul]
    exact zero_le
  · by_cases ht0 : ((y - s / 2) / s) ≤ ((s - ℓ) / (2 * s))
    swap
    · rw [Set.Icc_eq_empty_of_lt (not_le.mp ht0), setLIntegral_empty, mul_zero]
      exact zero_le
    rw [setLIntegral_congr (Ioc_ae_eq_Icc (a := (y - s / 2) / s)
      (b := (s - ℓ) / (2 * s))).symm]
    have hlow : ∀ t ∈ Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
        y + ℓ / 2 ≤ s * t + s / 2 + ℓ / 2 := by
      intro t ht
      have ht1 : (y - s / 2) / s ≤ t := ht.1.le
      rw [div_le_iff₀ hs] at ht1
      linarith
    have hL : ∀ t ∈ Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
        L1 s ℓ t = s * t + s / 2 + ℓ / 2 := by
      intro t ht
      have ht2 : t ≤ (s - ℓ) / (2 * s) := ht.2
      have ht2' : s * t ≤ (s - ℓ) / 2 := by
        rw [show (s - ℓ) / (2 * s) = ((s - ℓ) / 2) / s by ring, le_div_iff₀ hs] at ht2
        linarith
      exact (L1_eq_left hsl (by linarith)).trans (max_eq_left (by linarith [hlow t ht]))
    have hcongr : ∫⁻ t in Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
          ENNReal.ofReal (2 * (L1 s ℓ t) ^ (-(3 / 2) : ℝ))
        = ∫⁻ t in Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
          ENNReal.ofReal (2 * (s * t + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ)) := by
      rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s))
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hL t ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    rw [hcongr]
    have hcont : ContinuousOn (fun t : ℝ => 2 * (s * t + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ))
        (Set.Icc ((y - s / 2) / s) ((s - ℓ) / (2 * s))) := by
      refine continuousOn_of_forall_continuousAt fun t ht => ?_
      rw [Set.mem_Icc] at ht
      have h1 : y + ℓ / 2 ≤ s * t + s / 2 + ℓ / 2 := by
        have ht1 : (y - s / 2) / s ≤ t := ht.1
        rw [div_le_iff₀ hs] at ht1
        linarith
      have hpos : 0 < s * t + s / 2 + ℓ / 2 := by linarith
      have hbase : ContinuousAt (fun t : ℝ => s * t + s / 2 + ℓ / 2) t := by fun_prop
      exact continuousAt_const.mul (hbase.rpow_const (Or.inl hpos.ne'))
    have hint : IntegrableOn (fun t : ℝ => 2 * (s * t + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ))
        (Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s))) volume :=
      (ContinuousOn.integrableOn_compact isCompact_Icc hcont).mono_set Set.Ioc_subset_Icc_self
    have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)))]
        (fun t : ℝ => 2 * (s * t + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [hlow t ht]) _)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)))) hint h0]
    have h1e : s * ((y - s / 2) / s) + (s / 2 + ℓ / 2) = y + ℓ / 2 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hs.ne']
      ring
    have h2e : s * ((s - ℓ) / (2 * s)) + (s / 2 + ℓ / 2) = s := by
      rw [← mul_div_assoc, mul_comm s (s - ℓ), mul_div_mul_right _ _ hs.ne']
      ring
    have hkey : ∫ t in Set.Ioc ((y - s / 2) / s) ((s - ℓ) / (2 * s)),
          2 * (s * t + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ)
        = 4 / s * ((y + ℓ / 2) ^ (-(1 / 2) : ℝ) - s ^ (-(1 / 2) : ℝ)) := by
      rw [← intervalIntegral.integral_of_le ht0]
      have hfun : (fun x : ℝ => 2 * (s * x + s / 2 + ℓ / 2) ^ (-(3 / 2) : ℝ))
          = fun x : ℝ => (fun u : ℝ => 2 * u ^ (-(3 / 2) : ℝ))
              (s * x + (s / 2 + ℓ / 2)) := by
        funext x
        rw [show s * x + s / 2 + ℓ / 2 = s * x + (s / 2 + ℓ / 2) by ring]
      rw [hfun]
      have h0mem : (0 : ℝ) ∉ Set.uIcc (y + ℓ / 2) s := by
        rw [Set.mem_uIcc]
        rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith [hty, hs]
      have hrpow : ∫ u in (y + ℓ / 2)..s, u ^ (-(3 / 2) : ℝ)
          = (s ^ (-(1 / 2) : ℝ) - (y + ℓ / 2) ^ (-(1 / 2) : ℝ)) / (-(1 / 2)) := by
        rw [integral_rpow (Or.inr ⟨by norm_num, h0mem⟩)]
        norm_num
      rw [intervalIntegral.integral_comp_mul_add (fun u : ℝ => 2 * u ^ (-(3 / 2) : ℝ))
          hs.ne' (s / 2 + ℓ / 2), h1e, h2e,
        smul_eq_mul, intervalIntegral.integral_const_mul, hrpow]
      ring
    rw [hkey]
    by_cases hnn : 0 ≤ 4 / s * ((y + ℓ / 2) ^ (-(1 / 2) : ℝ) - s ^ (-(1 / 2) : ℝ))
    · rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (y + ℓ / 2))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Real.sqrt (y + ℓ / 2) * (y + ℓ / 2) ^ (-(1 / 2) : ℝ) = 1 := by
        rw [Real.rpow_neg hty.le, Real.sqrt_eq_rpow,
          mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hty _))]
      have h2 : Real.sqrt (y + ℓ / 2) * s ^ (-(1 / 2) : ℝ) = Real.sqrt ((y + ℓ / 2) / s) := by
        have hs' : s ^ (-(1 / 2) : ℝ) = (Real.sqrt s)⁻¹ := by
          rw [Real.rpow_neg hs.le, Real.sqrt_eq_rpow]
        rw [hs', inv_eq_one_div, mul_one_div]
        exact (Real.sqrt_div hty.le s).symm
      calc Real.sqrt (y + ℓ / 2) * (4 / s * ((y + ℓ / 2) ^ (-(1 / 2) : ℝ) - s ^ (-(1 / 2) : ℝ)))
          = 4 / s * (Real.sqrt (y + ℓ / 2) * (y + ℓ / 2) ^ (-(1 / 2) : ℝ))
            - 4 / s * (Real.sqrt (y + ℓ / 2) * s ^ (-(1 / 2) : ℝ)) := by ring
        _ = 4 / s * 1 - 4 / s * Real.sqrt ((y + ℓ / 2) / s) := by rw [h1, h2]
        _ = 4 / s * (1 - Real.sqrt ((y + ℓ / 2) / s)) := by ring
        _ ≤ 4 / s := by
            have h4 : 0 ≤ Real.sqrt ((y + ℓ / 2) / s) := Real.sqrt_nonneg _
            have h5 : (0 : ℝ) < 4 / s := by positivity
            nlinarith
    · rw [not_le] at hnn
      have hz : ENNReal.ofReal (4 / s * ((y + ℓ / 2) ^ (-(1 / 2) : ℝ) - s ^ (-(1 / 2) : ℝ)))
          = 0 := ENNReal.ofReal_eq_zero.mpr hnn.le
      rw [hz, mul_zero]
      exact zero_le

/-! ## The weighted Cauchy–Schwarz and the left-regime bound -/

/-- The left-regime weight `y ↦ (y + ℓ/2)^{1/2}`, as an `ℝ≥0∞`-valued function. -/
def wgtL (ℓ : ℝ) : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (y + ℓ / 2))

/-- The square root of the left-regime weight, `y ↦ (y + ℓ/2)^{1/4}`. -/
def wgtL' (ℓ : ℝ) : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (Real.sqrt (y + ℓ / 2)))

lemma wgtL'_sq (ℓ y : ℝ) : wgtL' ℓ y ^ 2 = wgtL ℓ y := by
  rw [wgtL, wgtL', ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma wgtL'_inv_sq (ℓ y : ℝ) : ((wgtL' ℓ y)⁻¹) ^ 2 = (wgtL ℓ y)⁻¹ := by
  rw [← ENNReal.inv_pow, wgtL'_sq]

lemma measurable_wgtL' (ℓ : ℝ) : Measurable (wgtL' ℓ) := by
  show Measurable fun y : ℝ => ENNReal.ofReal (Real.sqrt (Real.sqrt (y + ℓ / 2)))
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp
      (Real.continuous_sqrt.measurable.comp (measurable_id.add_const _)))

/-- On a window inside the box the product `w' · (w')⁻¹` is `1` a.e. -/
lemma wgtL'_mul_inv_ae {ℓ : ℝ} {J : Set ℝ} (hJ : MeasurableSet J)
    (hsub : J ⊆ Set.Ici (-(ℓ / 2))) :
    (fun y : ℝ => wgtL' ℓ y * (wgtL' ℓ y)⁻¹) =ᵐ[volume.restrict J] (fun _ => 1) := by
  filter_upwards [ae_restrict_mem hJ,
    ae_restrict_of_ae (show ∀ᵐ y ∂(volume : Measure ℝ), y ≠ -(ℓ / 2) from by
      rw [MeasureTheory.ae_iff]
      simpa using measure_singleton (-(ℓ / 2)))] with y hy hne
  have hpos : 0 < y + ℓ / 2 := by
    have h1 : -(ℓ / 2) ≤ y := hsub hy
    rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · exact absurd h.symm hne
  have hspos : 0 < Real.sqrt (Real.sqrt (y + ℓ / 2)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hpos)
  simp only [wgtL']
  rw [← ENNReal.ofReal_inv_of_pos hspos, ← ENNReal.ofReal_mul hspos.le,
    mul_inv_cancel₀ hspos.ne', ENNReal.ofReal_one]
/-- The ENNReal arithmetic of the weight: `(1/L)²·(2√L) = 2 L^{-3/2}`. -/
lemma ofReal_inv_sq_mul_sqrt {L : ℝ} (hL : 0 ≤ L) :
    (ENNReal.ofReal (1 / L)) ^ 2 * (2 * ENNReal.ofReal (Real.sqrt L))
      = ENNReal.ofReal (2 * L ^ (-(3 / 2) : ℝ)) := by
  rcases eq_or_lt_of_le hL with h | h
  · subst h
    rw [div_zero, Real.sqrt_zero, Real.zero_rpow (by norm_num : (-(3 / 2) : ℝ) ≠ 0)]
    simp
  · have hL2 : (1 / L) ^ 2 = L ^ (-2 : ℝ) := by
      rw [div_pow, one_pow, one_div, Real.rpow_neg h.le, Real.rpow_two]
    have hsq : Real.sqrt L = L ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow L
    have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [show (ENNReal.ofReal (1 / L)) ^ 2 = ENNReal.ofReal ((1 / L) ^ 2) from by
        rw [ENNReal.ofReal_pow (by positivity)],
      hL2, hsq, htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h.le _)]
    congr 1
    rw [← mul_assoc, mul_comm (L ^ (-2 : ℝ)) 2, mul_assoc,
      ← Real.rpow_add h (-2) (1 / 2), show (-2 : ℝ) + 1 / 2 = -(3 / 2) by norm_num]

/-- The pointwise Cauchy–Schwarz bound of the left regime. -/
lemma cs_left {s ℓ t : ℝ} (hsl : s ≤ ℓ) (h : s * t - s / 2 ≤ -(ℓ / 2))
    {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    (ENNReal.ofReal (1 / L1 s ℓ t) * ∫⁻ y in I1 s ℓ t, F y) ^ 2
      ≤ ENNReal.ofReal (2 * (L1 s ℓ t) ^ (-(3 / 2) : ℝ))
          * (∫⁻ y in I1 s ℓ t, F y ^ 2 * wgtL ℓ y) := by
  have hJ : MeasurableSet (I1 s ℓ t) := measurableSet_I1 s ℓ t
  have hsub : I1 s ℓ t ⊆ Set.Ici (-(ℓ / 2)) := fun y hy => (mem_I1_iff'.mp hy).1
  have hwm : Measurable (wgtL' ℓ) := measurable_wgtL' ℓ
  have h1 : AEMeasurable (fun y => F y * wgtL' ℓ y) volume := hF.mul hwm.aemeasurable
  have h2 : AEMeasurable (fun y => (wgtL' ℓ y)⁻¹) volume := hwm.inv.aemeasurable
  have hCS := sq_setLIntegral_mul_le (J := I1 s ℓ t) h1 h2
  have hae : (fun y : ℝ => F y) =ᵐ[volume.restrict (I1 s ℓ t)]
      (fun y => (F y * wgtL' ℓ y) * (wgtL' ℓ y)⁻¹) := by
    filter_upwards [wgtL'_mul_inv_ae hJ hsub] with y hy
    rw [mul_assoc, hy, mul_one]
  have hsq : (∫⁻ y in I1 s ℓ t, (fun y => F y * wgtL' ℓ y) y * (fun y => (wgtL' ℓ y)⁻¹) y) ^ 2
      = (∫⁻ y in I1 s ℓ t, F y) ^ 2 := by
    congr 1
    exact (lintegral_congr_ae hae).symm
  have hf2 : ∫⁻ y in I1 s ℓ t, ((fun y => F y * wgtL' ℓ y) y) ^ 2
      = ∫⁻ y in I1 s ℓ t, F y ^ 2 * wgtL ℓ y := by
    refine lintegral_congr fun y => ?_
    rw [mul_pow, wgtL'_sq]
  have hg2 : ∫⁻ y in I1 s ℓ t, ((fun y => (wgtL' ℓ y)⁻¹) y) ^ 2
      = ∫⁻ y in I1 s ℓ t, (wgtL ℓ y)⁻¹ := by
    refine lintegral_congr fun y => wgtL'_inv_sq ℓ y
  rw [hsq, hf2, hg2] at hCS
  have hwit := weight_left hsl h
  simp only [wgtL] at hCS
  rw [hwit] at hCS
  calc (ENNReal.ofReal (1 / L1 s ℓ t) * ∫⁻ y in I1 s ℓ t, F y) ^ 2
      = (ENNReal.ofReal (1 / L1 s ℓ t)) ^ 2 * (∫⁻ y in I1 s ℓ t, F y) ^ 2 := by ring
    _ ≤ (ENNReal.ofReal (1 / L1 s ℓ t)) ^ 2
          * ((∫⁻ y in I1 s ℓ t, F y ^ 2 * wgtL ℓ y)
              * (2 * ENNReal.ofReal (Real.sqrt (L1 s ℓ t)))) :=
        mul_le_mul_of_nonneg_left hCS (zero_le)
    _ = ((ENNReal.ofReal (1 / L1 s ℓ t)) ^ 2 * (2 * ENNReal.ofReal (Real.sqrt (L1 s ℓ t))))
          * (∫⁻ y in I1 s ℓ t, F y ^ 2 * wgtL ℓ y) := by ring
    _ = ENNReal.ofReal (2 * (L1 s ℓ t) ^ (-(3 / 2) : ℝ))
          * (∫⁻ y in I1 s ℓ t, F y ^ 2 * wgtL ℓ y) := by
        rw [ofReal_inv_sq_mul_sqrt (L1_nonneg s ℓ t)]

end Work.BoseFixB1B.MeanSqPiece.CruxMean
