import Mathlib
import Submission.Commons.Probability.Levy.essen_level_set_bound
import Submission.Commons.Probability.Levy.levy_interval_L1
import Submission.Commons.Probability.Levy.concentration_sq_bound
import Submission.Commons.Probability.Levy.levelB_vol_le
import Submission.Commons.Probability.Levy.levelB_measurable
import Submission.Commons.Probability.Levy.levelB_nonneg

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace Commons.Probability.Levy

/-! # `product_integral_core_r1`

Proof route (Esseen-level-set method, `r = 1`):

1. `levelSet_E_le`: per-index level-set bound on the window `E = {|t| ≤ 1}`,
   derived from `essen_level_set_bound` (window `E` sits inside `{|t| ≤ 1/ρ}` since `ρ ≤ 1`).
2. `M-section` Fubini decomposition: the integral of the product of the moduli of the
   characteristic functions over `E` equals the integral (over the cube of levels) of the
   measure of the section of a product set `G`.
3. τ-layer-cake: the section measure is at most the minimum of the per-index level bounds;
   using the layer cake formula the integral is bounded by `∫₀^∞ ∏ (1 - w_i τ²/C²)₊ dτ`,
   which is `≤ ∫₀^∞ exp(-τ² Σ w_i / C²) dτ = C√π / (2√(Σ w_i))` (Gaussian half-line integral).
-/

/-! ## Part I : elementary facts -/

/-- inline concentration supremum (same as in the target statement) -/
def coreQ (μ : Measure ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}

/-- concentration gap -/
def coreq (μ : Measure ℝ) (ρ : ℝ) : ℝ := 1 - (coreQ μ ρ).toReal

/-- spread weight -/
def corew (μ : Measure ℝ) (ρ : ℝ) : ℝ := coreq μ ρ * ρ ^ 2

/-- the window `{|t| ≤ 1}` -/
def coreE : Set ℝ := {t : ℝ | |t| ≤ 1}

lemma coreE_eq : coreE = Set.Icc (-1) 1 := by
  ext t
  constructor
  · intro ht; change |t| ≤ 1 at ht; exact abs_le.mp ht
  · intro ht; change -1 ≤ t ∧ t ≤ 1 at ht; exact abs_le.mpr ht

lemma coreE_volume : (volume coreE).toReal = 2 := by
  rw [coreE_eq]
  norm_num [Real.volume_Icc]

lemma coreq_toReal_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) : 0 ≤ coreq μ ρ := by
  unfold coreq coreQ
  exact sub_nonneg.mpr (ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [sSup_le_iff]
    rintro a ⟨l, rfl⟩
    exact le_trans (measure_mono (Set.subset_univ _)) (by simp)))

/-- per-index level-set volume bound on the unit window (from `essen_level_set_bound`) -/
lemma levelSet_E_le (C₀ : ℝ)
    (hEss : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ →
      (0 < 1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}).toReal) →
      ∀ (η : ℝ), 0 ≤ η →
        (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η ≤ ‖charFun μ t‖}).toReal ≤
          C₀ * Real.sqrt (η / (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}).toReal)) / ρ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < coreq μ ρ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (volume {t : ℝ | t ∈ coreE ∧ s ≤ ‖charFun μ t‖}).toReal ≤
        C₀ * Real.sqrt (1 - s) / Real.sqrt (corew μ ρ) := by
  intro s hs0 hs1
  have hη : 0 ≤ 1 - s := by linarith
  have hQpos : 0 < 1 - (coreQ μ ρ).toReal := by simpa [coreq] using hq
  have hq0 : 0 ≤ coreq μ ρ := coreq_toReal_nonneg μ ρ
  have hsqrt_w : Real.sqrt (corew μ ρ) = Real.sqrt (coreq μ ρ) * ρ := by
    unfold corew
    rw [Real.sqrt_mul hq0]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_pos hρ0]
  have hsqd : Real.sqrt ((1 - s) / (1 - (coreQ μ ρ).toReal)) =
      Real.sqrt (1 - s) / Real.sqrt (1 - (coreQ μ ρ).toReal) := by
    rw [Real.sqrt_div hη]
  have hb := hEss μ ρ hρ0 (by simpa [coreq, coreQ] using hq) (1 - s) hη
  have hset : {t : ℝ | t ∈ coreE ∧ s ≤ ‖charFun μ t‖} ⊆
      {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖} := by
    intro t ht
    change t ∈ coreE ∧ s ≤ ‖charFun μ t‖ at ht
    change |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖
    constructor
    · have htE : |t| ≤ 1 := by simpa [coreE] using ht.1
      rw [one_div]
      exact le_trans htE ((one_le_inv₀ hρ0).mpr hρ1)
    · linarith [ht.2]
  have hfin : volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖} ≠ ∞ := by
    have hbd : {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖} ⊆ Set.Icc (-(1 / ρ) - 1) ((1 / ρ) + 1) := by
      intro t ht
      change |t| ≤ 1 / ρ ∧ _ ≤ ‖charFun μ t‖ at ht
      have habs := abs_le.mp ht.1
      change t ∈ Set.Icc (-(1 / ρ) - 1) (1 / ρ + 1)
      rw [Set.mem_Icc]
      constructor <;> nlinarith
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hbd) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hb' : (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖}).toReal ≤
      C₀ * Real.sqrt (1 - s) / Real.sqrt (corew μ ρ) := by
    calc
      (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - (1 - s) ≤ ‖charFun μ t‖}).toReal
          ≤ C₀ * Real.sqrt ((1 - s) / (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}).toReal)) / ρ := hb
      _ = C₀ * Real.sqrt ((1 - s) / (1 - (coreQ μ ρ).toReal)) / ρ := by rfl
      _ = C₀ * (Real.sqrt (1 - s) / Real.sqrt (1 - (coreQ μ ρ).toReal)) / ρ := by rw [hsqd]
      _ = C₀ * Real.sqrt (1 - s) / (Real.sqrt (coreq μ ρ) * ρ) := by
          unfold coreq
          field_simp [hρ0.ne']
      _ = C₀ * Real.sqrt (1 - s) / Real.sqrt (corew μ ρ) := by
          rw [hsqrt_w]
  exact le_trans (measureReal_mono hset hfin) hb'

/-! ## Part II : the level functions and their per-coordinate measure -/

/-- `charFun` norm is a [0,1] valued measurable function -/
lemma measurable_abs_charFun (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (fun t : ℝ => ‖charFun μ t‖) := by
  exact (MeasureTheory.measurable_charFun (μ := μ)).norm

lemma charFun_norm_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ ‖charFun μ t‖ := norm_nonneg _

lemma charFun_norm_le_one' (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : ‖charFun μ t‖ ≤ 1 :=
  MeasureTheory.norm_charFun_le_one (μ := μ) (t := t)

/-- cube space -/
abbrev CubeSpace (m : ℕ) := Fin m → ℝ

/-- volume on the cube space is the product of volume -/
lemma volume_pi_eq (m : ℕ) : (volume : Measure (CubeSpace m)) = Measure.pi (fun _ : Fin m => volume) := by
  rw [MeasureTheory.volume_pi]

/-- measure of a box in cube space -/
lemma pi_box (m : ℕ) (s : Fin m → Set ℝ) :
    (volume : Measure (CubeSpace m)) (Set.univ.pi s) = ∏ i, volume (s i) := by
  rw [volume_pi_eq]
  exact Measure.pi_pi (fun _ : Fin m => (volume : Measure ℝ)) s

lemma mem_univ_pi_iff {m : ℕ} {s : Fin m → Set ℝ} {x : CubeSpace m} :
    x ∈ Set.univ.pi s ↔ ∀ i, x i ∈ s i := Set.mem_univ_pi

/-- box is measurable if coordinate sets are -/
lemma measurable_box {m : ℕ} (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.univ.pi s) := by
  classical
  rw [Set.pi_def]
  simpa [Finset.mem_univ] using
    (Finset.measurableSet_biInter Finset.univ (fun i _ => (hs i).preimage (measurable_pi_apply i)))

/-- box measure inside the unit cube = product of per-coordinate measures -/
lemma pi_box_cube {m : ℕ} (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hsub : ∀ i, s i ⊆ Set.Icc (0 : ℝ) 1) :
    ((volume : Measure (CubeSpace m)).restrict (Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1)))
        (Set.univ.pi s) = ∏ i, volume (s i) := by
  rw [Measure.restrict_apply (measurable_box s hs)]
  have hEq : Set.univ.pi s ∩ Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1) = Set.univ.pi s := by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx
      constructor
      · exact hx
      · rw [mem_univ_pi_iff]
        intro i
        exact hsub i (mem_univ_pi_iff.mp hx i)
  rw [hEq]
  exact pi_box m s

lemma prod_real_exp_fin (m : ℕ) (x : Fin m → ℝ) :
    (∏ i, Real.exp (x i)) = Real.exp (∑ i, x i) := by
  induction' m with m ih
  · simp
  · rw [Fin.prod_univ_succ, ih, Fin.sum_univ_succ, Real.exp_add]

lemma toReal_prod_fin (m : ℕ) (a : Fin m → ℝ≥0∞) :
    (∏ i, a i).toReal = ∏ i, (a i).toReal := by
  simpa using (ENNReal.toReal_prod Finset.univ a)

/-- product of sub-level measures (inside the unit interval) bounded by the Gaussian factor -/
lemma cube_box_real_bound {m : ℕ} (B : Fin m → ℝ → ℝ) (w : Fin m → ℝ) (C : ℝ)
    (τ : ℝ)
    (hBmeas : ∀ i, Measurable (B i))
    (hlevel : ∀ i, (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
        Real.exp (-(w i) * τ ^ 2 / C ^ 2)) :
    (((volume : Measure (CubeSpace m)).restrict
        (Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1))).real
          (Set.univ.pi (fun i => {s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1))) ≤
      Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2) := by
  have hsub : ∀ i, ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro i x hx
    exact hx.2
  have hmeas : ∀ i, MeasurableSet ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1) := by
    intro i
    exact (measurableSet_le measurable_const (hBmeas i)).inter measurableSet_Icc
  have hbox := pi_box_cube (m := m) (fun i => {s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1) hmeas hsub
  calc
    (((volume : Measure (CubeSpace m)).restrict
        (Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1))).real
          (Set.univ.pi (fun i => {s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)))
        = (∏ i, volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal := by
            rw [Measure.real_def]
            rw [hbox]
    _ = ∏ i, (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal := by
            rw [toReal_prod_fin]
    _ ≤ ∏ i, Real.exp (-(w i) * τ ^ 2 / C ^ 2) := by
            exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hlevel i)
    _ = Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2) := by
            have hE : (∏ i, Real.exp (-(w i) * τ ^ 2 / C ^ 2)) = Real.exp (∑ i, (-(w i) * τ ^ 2 / C ^ 2)) :=
              prod_real_exp_fin m (fun i => -(w i) * τ ^ 2 / C ^ 2)
            rw [hE]
            congr 1
            have hEx : (∑ i, (-(w i) * τ ^ 2 / C ^ 2)) = (-(∑ i, w i)) * τ ^ 2 / C ^ 2 := by
              calc
                (∑ i, -(w i) * τ ^ 2 / C ^ 2) = (∑ i, -(w i * τ ^ 2) / C ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
                _ = (∑ i, -(w i * τ ^ 2)) / C ^ 2 := by
                  rw [Finset.sum_div]
                _ = -(∑ i, w i * τ ^ 2) / C ^ 2 := by
                  rw [Finset.sum_neg_distrib]
                _ = -((∑ i, w i) * τ ^ 2) / C ^ 2 := by
                  congr 1
                  rw [← Finset.sum_mul]
                _ = (-(∑ i, w i)) * τ ^ 2 / C ^ 2 := by ring
            exact hEx

/-! ## Part III : section measure and Fubini -/

/-- measure on the t-line restricted to the window -/
def coreEM : Measure ℝ := volume.restrict coreE

lemma coreEM_finite : IsFiniteMeasure coreEM := by
  unfold coreEM
  exact ⟨by
    rw [Measure.restrict_apply_univ]
    rw [coreE_eq]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩

/-- the t-section product set -/
def coreGSet {m : ℕ} (φ : Fin m → ℝ → ℝ) : Set (CubeSpace m × ℝ) :=
  {z | z.2 ∈ coreE ∧ ∀ i : Fin m, 0 < z.1 i ∧ z.1 i ≤ φ i z.2}

lemma measurable_coreGSet {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i)) :
    MeasurableSet (coreGSet φ) := by
  unfold coreGSet coreE
  have h1 : MeasurableSet {z : CubeSpace m × ℝ | |z.2| ≤ 1} :=
    (measurable_snd.norm) measurableSet_Iic
  have h2 (i : Fin m) : MeasurableSet {z : CubeSpace m × ℝ | 0 < z.1 i ∧ z.1 i ≤ φ i z.2} := by
    have hz1 : Measurable (fun z : CubeSpace m × ℝ => z.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hphi : Measurable (fun z : CubeSpace m × ℝ => φ i z.2) := (hφmeas i).comp measurable_snd
    exact (measurableSet_lt measurable_const hz1).inter (measurableSet_le hz1 hphi)
  have hAll : MeasurableSet (⋂ i : Fin m, {z : CubeSpace m × ℝ | 0 < z.1 i ∧ z.1 i ≤ φ i z.2}) :=
    MeasurableSet.iInter (fun i => h2 i)
  have hEq : {z : CubeSpace m × ℝ | z.2 ∈ {t : ℝ | |t| ≤ 1} ∧
      ∀ i : Fin m, 0 < z.1 i ∧ z.1 i ≤ φ i z.2} =
      {z : CubeSpace m × ℝ | |z.2| ≤ 1} ∩
        (⋂ i : Fin m, {z : CubeSpace m × ℝ | 0 < z.1 i ∧ z.1 i ≤ φ i z.2}) := by
    ext z
    constructor <;> intro hz <;> simpa [Set.mem_iInter] using hz
  rw [hEq]
  exact h1.inter hAll

/-- ENNReal-valued section measure -/
noncomputable def coreMsect {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) : ℝ≥0∞ :=
  coreEM {t : ℝ | (s, t) ∈ coreGSet φ}

/-- real-valued section measure -/
noncomputable def coreMreal {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) : ℝ :=
  coreEM.real {t : ℝ | (s, t) ∈ coreGSet φ}

lemma coreMsect_lt_top {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) : coreMsect φ s < ⊤ := by
  unfold coreMsect
  exact lt_of_le_of_lt (measure_mono (by
    intro t ht
    change (s, t) ∈ coreGSet φ at ht
    exact ht.1)) (by
      have hE : coreE ⊆ Set.univ := Set.subset_univ coreE
      exact lt_of_le_of_lt (measure_mono hE) (by
        unfold coreEM
        rw [Measure.restrict_apply_univ]
        rw [coreE_eq]
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top))

lemma coreMsect_eq_ofReal {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) :
    coreMsect φ s = ENNReal.ofReal (coreMreal φ s) := by
  unfold coreMsect coreMreal
  rw [Measure.real_def]
  exact (ENNReal.ofReal_toReal (ne_of_lt (coreMsect_lt_top φ s))).symm

/-- real section measure is measurable -/
lemma measurable_coreMreal {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i)) :
    Measurable (coreMreal φ) := by
  unfold coreMreal
  letI : IsFiniteMeasure coreEM := coreEM_finite
  have hSec := measurable_measure_prodMk_left_finite
    (α := CubeSpace m) (β := ℝ) (ν := coreEM) (s := coreGSet φ) (measurable_coreGSet φ hφmeas)
  have hSec' : Measurable (fun s : CubeSpace m => (coreEM (Prod.mk s ⁻¹' coreGSet φ)).toReal) :=
    hSec.ennreal_toReal
  have hSet (s : CubeSpace m) : {t : ℝ | (s, t) ∈ coreGSet φ} = (Prod.mk s ⁻¹' coreGSet φ) := by
    ext t; rfl
  have hconvert : (fun s : CubeSpace m => coreEM.real {t : ℝ | (s, t) ∈ coreGSet φ}) =
      (fun s : CubeSpace m => (coreEM (Prod.mk s ⁻¹' coreGSet φ)).toReal) := by
    funext s
    rw [Measure.real_def]
    rw [hSet s]
  rwa [hconvert]

/-- volume of a box at fixed t -/
lemma box_vol_at_t {m : ℕ} (φ : Fin m → ℝ → ℝ) (t : ℝ) :
    (volume : Measure (CubeSpace m)) {s : CubeSpace m | ∀ i, 0 < s i ∧ s i ≤ φ i t} =
      ∏ i, volume (Set.Ioc (0 : ℝ) (φ i t)) := by
  have hEq : {s : CubeSpace m | ∀ i, 0 < s i ∧ s i ≤ φ i t} =
      Set.univ.pi (fun i => Set.Ioc (0 : ℝ) (φ i t)) := by
    ext s
    constructor
    · intro hs
      rw [mem_univ_pi_iff]
      intro i
      exact hs i
    · intro hs
      intro i
      exact (mem_univ_pi_iff.mp hs i)
  rw [hEq]
  exact pi_box m (fun i => Set.Ioc (0 : ℝ) (φ i t))

/-- volume of Ioc 0 a -/
lemma volume_Ioc_ofReal {a : ℝ} (ha : 0 ≤ a) : volume (Set.Ioc (0 : ℝ) a) = ENNReal.ofReal a := by
  rw [Real.volume_Ioc]
  congr 1
  ring

/-! ## Part IV : Fubini decomposition over the section set -/

/-- indicator of the section set -/
noncomputable def coreFsec {m : ℕ} (φ : Fin m → ℝ → ℝ) : CubeSpace m × ℝ → ℝ≥0∞ :=
  (coreGSet φ).indicator (fun _ : CubeSpace m × ℝ => (1 : ℝ≥0∞))

lemma measurable_coreFsec {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i)) :
    Measurable (coreFsec φ) := by
  unfold coreFsec
  exact Measurable.indicator (by fun_prop : Measurable (fun _ : CubeSpace m × ℝ => (1 : ℝ≥0∞)))
    (measurable_coreGSet φ hφmeas)

lemma coreE_measurable : MeasurableSet coreE := by
  unfold coreE
  exact continuous_abs.measurable measurableSet_Iic

lemma mem_coreGSet_E {m : ℕ} (φ : Fin m → ℝ → ℝ) {s : CubeSpace m} {t : ℝ}
    (h : (s, t) ∈ coreGSet φ) : t ∈ coreE := by
  change (s, t) ∈ coreGSet φ at h
  exact h.1

lemma coreMsect_eq_volume {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) :
    coreMsect φ s = (volume : Measure ℝ) {t : ℝ | (s, t) ∈ coreGSet φ} := by
  unfold coreMsect coreEM
  exact Measure.restrict_eq_self (volume : Measure ℝ) (by
    intro t ht
    exact mem_coreGSet_E φ ht)

lemma inner_sect_s {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i)) (s : CubeSpace m) :
    (∫⁻ t, coreFsec φ (s, t) ∂volume) = coreMsect φ s := by
  calc
    (∫⁻ t, coreFsec φ (s, t) ∂volume)
        = (∫⁻ t, ({t : ℝ | (s, t) ∈ coreGSet φ}).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) t ∂volume) := by
            apply lintegral_congr
            intro t
            unfold coreFsec
            rfl
    _ = (volume : Measure ℝ) {t : ℝ | (s, t) ∈ coreGSet φ} := by
            have hsec : MeasurableSet {t : ℝ | (s, t) ∈ coreGSet φ} :=
              (measurable_coreGSet φ hφmeas).preimage (by fun_prop : Measurable (fun t : ℝ => (s, t)))
            rw [MeasureTheory.lintegral_indicator hsec (fun _ : ℝ => (1 : ℝ≥0∞))]
            simp
    _ = coreMsect φ s := (coreMsect_eq_volume φ s).symm


/-- inner integral over the cube at fixed t -/
lemma inner_sect_t {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i))
    (hφ01 : ∀ i t, 0 ≤ φ i t) (t : ℝ) :
    (∫⁻ s : CubeSpace m, coreFsec φ (s, t) ∂volume) =
      coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t)) t := by
  calc
    (∫⁻ s : CubeSpace m, coreFsec φ (s, t) ∂volume)
        = (∫⁻ s : CubeSpace m, ({s' : CubeSpace m | (s', t) ∈ coreGSet φ}).indicator
            (fun _ : CubeSpace m => (1 : ℝ≥0∞)) s ∂volume) := by
            apply lintegral_congr
            intro s
            by_cases hs : (s, t) ∈ coreGSet φ <;> simp [coreFsec, hs]
    _ = (volume : Measure (CubeSpace m)) {s : CubeSpace m | (s, t) ∈ coreGSet φ} := by
            have hsec : MeasurableSet {s : CubeSpace m | (s, t) ∈ coreGSet φ} :=
              (measurable_coreGSet φ hφmeas).preimage (by fun_prop : Measurable (fun s : CubeSpace m => (s, t)))
            rw [MeasureTheory.lintegral_indicator hsec (fun _ : CubeSpace m => (1 : ℝ≥0∞))]
            simp
    _ = coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t)) t := by
            by_cases ht : t ∈ coreE
            · have hEqSet : {s : CubeSpace m | (s, t) ∈ coreGSet φ} =
                {s : CubeSpace m | ∀ i, 0 < s i ∧ s i ≤ φ i t} := by
                ext s
                constructor
                · intro hs
                  intro i
                  exact hs.2 i
                · intro hs
                  change (s, t) ∈ coreGSet φ
                  change t ∈ coreE ∧ ∀ i : Fin m, 0 < s i ∧ s i ≤ φ i t
                  exact ⟨ht, hs⟩
              rw [hEqSet]
              rw [box_vol_at_t φ t]
              have hbox : (∏ i, volume (Set.Ioc (0 : ℝ) (φ i t))) =
                  (∏ i, ENNReal.ofReal (φ i t)) := by
                apply Finset.prod_congr rfl
                intro i hi
                exact volume_Ioc_ofReal (hφ01 i t)
              rw [hbox]
              simp [ht]
            · have hEqSet : {s : CubeSpace m | (s, t) ∈ coreGSet φ} = ∅ := by
                ext s
                constructor
                · intro hs
                  have ht' : t ∈ coreE := hs.1
                  exact False.elim (ht ht')
                · intro hmem
                  exact False.elim (by simpa using hmem)
              rw [hEqSet]
              simp [ht]

/-- Fubini identity: product measure of the section set in both orders -/
lemma fubini_sect (m : ℕ) (φ : Fin m → ℝ → ℝ) (hφmeas : ∀ i, Measurable (φ i))
    (hφ01 : ∀ i t, 0 ≤ φ i t) :
    (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume) =
      ∫⁻ s : CubeSpace m, coreMsect φ s ∂volume := by
  let f : CubeSpace m × ℝ → ℝ≥0∞ := coreFsec φ
  have hf : Measurable f := measurable_coreFsec φ hφmeas
  calc
    (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume)
        = (∫⁻ z : CubeSpace m × ℝ, f z ∂((volume : Measure (CubeSpace m)).prod volume)) := by
            rw [lintegral_prod_symm' (μ := (volume : Measure (CubeSpace m))) (ν := volume) f hf]
            apply lintegral_congr
            intro t
            exact (inner_sect_t φ hφmeas hφ01 t).symm
    _ = ∫⁻ s : CubeSpace m, coreMsect φ s ∂volume := by
            rw [lintegral_prod (μ := (volume : Measure (CubeSpace m))) (ν := volume) f hf.aemeasurable]
            apply lintegral_congr
            intro s
            exact inner_sect_s φ hφmeas s

/-! ## Part V : main bound -/

/-! ## Part V : Fubini details -/

/-! ## Part VI : τ-layer-cake bound -/

/-- unit cube in the cube space -/
def coreCube (m : ℕ) : Set (CubeSpace m) := Set.univ.pi (fun _ : Fin m => Set.Icc (0 : ℝ) 1)

lemma mem_coreCube_iff {m : ℕ} (s : CubeSpace m) : s ∈ coreCube m ↔ ∀ i, s i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [coreCube]
  exact Set.mem_univ_pi

/-- `μ.real s ≤ a` with `μ s` finite and `a ≥ 0` implies `μ s ≤ ofReal a` -/
lemma measureReal_le_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {a : ℝ}
    (hfin : μ s ≠ ∞) (ha : 0 ≤ a) (h : μ.real s ≤ a) : μ s ≤ ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_toReal hfin]
  exact (ENNReal.ofReal_le_ofReal_iff ha).2 (by simpa [Measure.real_def] using h)

/-- coreMreal is nonnegative -/
lemma coreMreal_nonneg {m : ℕ} (φ : Fin m → ℝ → ℝ) (s : CubeSpace m) : 0 ≤ coreMreal φ s := by
  unfold coreMreal
  exact ENNReal.toReal_nonneg

/-- section measure vanishes unless the level vector lies in the cube -/
lemma coreMreal_eq_zero_of_not_mem_cube {m : ℕ} (φ : Fin m → ℝ → ℝ)
    (hφ01 : ∀ i t, φ i t ∈ Set.Icc (0 : ℝ) 1) {s : CubeSpace m}
    (hs : s ∉ coreCube m) : coreMreal φ s = 0 := by
  have hsome : ∃ j, ¬ s j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [mem_coreCube_iff] at hs
    exact not_forall.mp hs
  rcases hsome with ⟨j, hnj⟩
  have hGempty : {t : ℝ | (s, t) ∈ coreGSet φ} = ∅ := by
    ext t
    constructor
    · intro htmem
      change (s, t) ∈ coreGSet φ at htmem
      have hscond : 0 < s j ∧ s j ≤ φ j t := htmem.2 j
      have hφle : φ j t ≤ 1 := (Set.mem_Icc.mp (hφ01 j t)).2
      have hnj' : ¬ (s j ∈ Set.Icc (0 : ℝ) 1) := hnj
      rw [Set.mem_Icc] at hnj'
      push_neg at hnj'
      by_cases hs0 : 0 ≤ s j
      · have hbig : 1 < s j := hnj' hs0
        linarith [hscond.2, hφle]
      · linarith [hscond.1, hs0]
    · intro hmem
      simpa using hmem
  unfold coreMreal
  rw [hGempty]
  simp

/-- level set {τ ≤ Mreal} (τ > 0) lies inside the cube -/
lemma pos_le_Mreal_mem_cube {m : ℕ} (φ : Fin m → ℝ → ℝ)
    (hφ01 : ∀ i t, φ i t ∈ Set.Icc (0 : ℝ) 1) {s : CubeSpace m} {τ : ℝ}
    (hτ : 0 < τ) (hM : τ ≤ coreMreal φ s) : s ∈ coreCube m := by
  by_contra hnot
  have hM0 : coreMreal φ s = 0 := coreMreal_eq_zero_of_not_mem_cube φ hφ01 hnot
  linarith

/-- box around τ of the per-coordinate level sets -/
def tauBox {m : ℕ} (B : Fin m → ℝ → ℝ) (τ : ℝ) : Set (CubeSpace m) :=
  Set.univ.pi (fun i => ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1))

lemma mem_tauBox_iff {m : ℕ} (B : Fin m → ℝ → ℝ) (τ : ℝ) (s : CubeSpace m) :
    s ∈ tauBox B τ ↔ ∀ i, τ ≤ B i (s i) ∧ s i ∈ Set.Icc (0 : ℝ) 1 := by
  simp [tauBox]

lemma tauBox_sub_cube {m : ℕ} (B : Fin m → ℝ → ℝ) (τ : ℝ) : tauBox B τ ⊆ coreCube m := by
  intro s hs
  rw [mem_coreCube_iff]
  intro i
  exact ((mem_tauBox_iff B τ s).mp hs i).2

/-- volume of the τ-box (real) is bounded by the Gaussian factor -/
lemma box_volume_real_bound {m : ℕ} (B : Fin m → ℝ → ℝ) (w : Fin m → ℝ) (C : ℝ)
    (τ : ℝ)
    (hBmeas : ∀ i, Measurable (B i))
    (hlevel : ∀ i, (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
        Real.exp (-(w i) * τ ^ 2 / C ^ 2)) :
    (volume : Measure (CubeSpace m)).real (tauBox B τ) ≤
      Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2) := by
  have hres : ((volume : Measure (CubeSpace m)).restrict (coreCube m)) (tauBox B τ) =
      (volume : Measure (CubeSpace m)) (tauBox B τ) :=
    Measure.restrict_eq_self (volume : Measure (CubeSpace m)) (tauBox_sub_cube B τ)
  have hvol_eq : (volume : Measure (CubeSpace m)).real (tauBox B τ) =
      ((volume : Measure (CubeSpace m)).restrict (coreCube m)).real (tauBox B τ) := by
    unfold Measure.real
    rw [hres]
  rw [hvol_eq]
  change ((volume : Measure (CubeSpace m)).restrict (coreCube m)).real
      (Set.univ.pi (fun i => ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1))) ≤
      Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)
  exact cube_box_real_bound (m := m) (B := B) (w := w) (C := C) τ hBmeas hlevel

/-- volume of the level set {τ ≤ Mreal} is bounded by the per-coordinate Gaussian factor -/
lemma tau_level_volume_le {m : ℕ} (φ : Fin m → ℝ → ℝ) (B : Fin m → ℝ → ℝ) (w : Fin m → ℝ)
    (C : ℝ) (hCpos : 0 < C)
    (hφmeas : ∀ i, Measurable (φ i))
    (hφ01 : ∀ i t, φ i t ∈ Set.Icc (0 : ℝ) 1)
    (hBmeas : ∀ i, Measurable (B i))
    (hMB : ∀ (s : CubeSpace m) (j : Fin m), coreMreal φ s ≤ B j (s j))
    (hBvol : ∀ i τ, 0 ≤ τ → (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
        Real.exp (-(w i) * τ ^ 2 / C ^ 2))
    (τ : ℝ) (hτ : 0 < τ) :
    (volume : Measure (CubeSpace m)) {s : CubeSpace m | τ ≤ coreMreal φ s} ≤
      ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)) := by
  let box : Set (CubeSpace m) := tauBox B τ
  have hsub : {s : CubeSpace m | τ ≤ coreMreal φ s} ⊆ box := by
    intro s hs
    rw [mem_tauBox_iff]
    intro j
    constructor
    · exact le_trans hs (hMB s j)
    · exact (mem_coreCube_iff s).mp (pos_le_Mreal_mem_cube φ hφ01 (s := s) (τ := τ) hτ hs) j
  have hsubCube : {s : CubeSpace m | τ ≤ coreMreal φ s} ⊆ coreCube m := by
    intro s hs
    exact pos_le_Mreal_mem_cube φ hφ01 (s := s) (τ := τ) hτ hs
  have hmeasL : MeasurableSet {s : CubeSpace m | τ ≤ coreMreal φ s} :=
    measurableSet_le measurable_const (measurable_coreMreal φ hφmeas)
  have hbox : ((volume : Measure (CubeSpace m)).restrict (coreCube m)) box ≤
      ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)) := by
    have hfin : ((volume : Measure (CubeSpace m)).restrict (coreCube m)) box ≠ ∞ := by
      have hcube_lt : ((volume : Measure (CubeSpace m)).restrict (coreCube m)) (coreCube m) < ∞ := by
        rw [Measure.restrict_apply (by unfold coreCube; exact measurable_box _ (fun _ : Fin m => measurableSet_Icc))]
        rw [inter_self]
        unfold coreCube
        rw [pi_box]
        simp
      exact ne_of_lt (lt_of_le_of_lt
        (measure_mono (μ := ((volume : Measure (CubeSpace m)).restrict (coreCube m))) (tauBox_sub_cube B τ)) hcube_lt)
    have hbox_real : ((volume : Measure (CubeSpace m)).restrict (coreCube m)).real box ≤
        Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2) := by
      have hvol_eq : ((volume : Measure (CubeSpace m)).restrict (coreCube m)).real box =
          (volume : Measure (CubeSpace m)).real box := by
        unfold Measure.real
        rw [Measure.restrict_eq_self (volume : Measure (CubeSpace m)) (tauBox_sub_cube B τ)]
      rw [hvol_eq]
      change (volume : Measure (CubeSpace m)).real (tauBox B τ) ≤
          Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)
      have hBvol' : ∀ i, (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
          Real.exp (-(w i) * τ ^ 2 / C ^ 2) := fun i => hBvol i τ (le_of_lt hτ)
      exact box_volume_real_bound (m := m) (B := B) (w := w) (C := C) τ hBmeas hBvol'
    exact measureReal_le_ofReal hfin (by positivity) hbox_real
  calc
    (volume : Measure (CubeSpace m)) {s : CubeSpace m | τ ≤ coreMreal φ s}
        = ((volume : Measure (CubeSpace m)).restrict (coreCube m)) {s : CubeSpace m | τ ≤ coreMreal φ s} := by
            rw [Measure.restrict_apply hmeasL]
            rw [show {s : CubeSpace m | τ ≤ coreMreal φ s} ∩ coreCube m = {s : CubeSpace m | τ ≤ coreMreal φ s} by
              exact inter_eq_left.mpr hsubCube]
    _ ≤ ((volume : Measure (CubeSpace m)).restrict (coreCube m)) box := by
            exact measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)) := hbox

/-! ## Part VII : Gaussian half-line integral and the abstract τ-bound -/

/-- integrability of the Gaussian tail factor on the half-line -/
lemma integrable_half_exp {D C : ℝ} (hD : 0 < D) (hC : 0 < C) :
    Integrable (fun τ : ℝ => Real.exp (-(D * τ ^ 2 / C ^ 2)))
      (volume.restrict (Set.Ioi 0)) := by
  -- exponent: exp (-D τ² / C²) = exp (-(D/C²) τ²): use integrable_exp_neg_mul_sq (D/C²)
  have hb : 0 < D / C ^ 2 := div_pos hD (pow_pos hC 2)
  have hmain : Integrable (fun τ : ℝ => Real.exp (-(D / C ^ 2) * τ ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  -- equal integrands
  have hfun : (fun τ : ℝ => Real.exp (-(D * τ ^ 2 / C ^ 2))) =
      (fun τ : ℝ => Real.exp (-(D / C ^ 2) * τ ^ 2)) := by
    funext τ
    congr 1
    field_simp [pow_ne_zero 2 hC.ne']
  rw [hfun]
  exact hmain.restrict

/-- value of the half-line Gaussian integral -/
lemma gaussian_half_value {D C : ℝ} (hD : 0 < D) (hC : 0 < C) :
    (∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(D * τ ^ 2 / C ^ 2))) =
      C * Real.sqrt Real.pi / (2 * Real.sqrt D) := by
  have hb : 0 < D / C ^ 2 := div_pos hD (pow_pos hC 2)
  have hrew : (fun τ : ℝ => Real.exp (-(D * τ ^ 2 / C ^ 2))) =
      (fun τ : ℝ => Real.exp (-(D / C ^ 2) * τ ^ 2)) := by
    funext τ
    congr 1
    field_simp [pow_ne_zero 2 hC.ne']
  calc
    (∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(D * τ ^ 2 / C ^ 2)))
        = ∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(D / C ^ 2) * τ ^ 2) := by
            rw [hrew]
    _ = Real.sqrt (Real.pi / (D / C ^ 2)) / 2 := integral_gaussian_Ioi (D / C ^ 2)
    _ = C * Real.sqrt Real.pi / (2 * Real.sqrt D) := by
            have hfrac : Real.pi / (D / C ^ 2) = Real.pi * C ^ 2 / D := by
              field_simp [hD.ne', pow_ne_zero 2 hC.ne']
            rw [hfrac]
            have hsq : Real.sqrt (Real.pi * C ^ 2 / D) = C * Real.sqrt Real.pi / Real.sqrt D := by
              have hnum0 : 0 ≤ Real.pi * C ^ 2 := by positivity
              rw [Real.sqrt_div hnum0 D]
              congr 1
              rw [Real.sqrt_mul (by positivity : 0 ≤ Real.pi)]
              rw [Real.sqrt_sq_eq_abs]
              rw [abs_of_pos hC]
              ring
            rw [hsq]
            ring

/-- `∫⁻ (τ in Ioi 0) ofReal(exp(-Dτ²/C²))` equals ofReal of the Gaussian value -/
lemma lintegral_half_exp {D C : ℝ} (hD : 0 < D) (hC : 0 < C) :
    (∫⁻ τ in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(D * τ ^ 2 / C ^ 2)))) =
      ENNReal.ofReal (C * Real.sqrt Real.pi / (2 * Real.sqrt D)) := by
  -- convert to real integral
  have hlin : ENNReal.ofReal (∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(D * τ ^ 2 / C ^ 2))) =
      ∫⁻ τ in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(D * τ ^ 2 / C ^ 2))) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrable_half_exp hD hC) (Filter.Eventually.of_forall (fun τ => (Real.exp_pos _).le))]
  calc
    (∫⁻ τ in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(D * τ ^ 2 / C ^ 2))))
        = ENNReal.ofReal (∫ τ in Set.Ioi (0 : ℝ), Real.exp (-(D * τ ^ 2 / C ^ 2))) := hlin.symm
    _ = ENNReal.ofReal (C * Real.sqrt Real.pi / (2 * Real.sqrt D)) := by
            rw [gaussian_half_value hD hC]

/-- main abstract τ-bound for the section lintegral -/
lemma core_sect_tau_bound {m : ℕ} (φ : Fin m → ℝ → ℝ) (B : Fin m → ℝ → ℝ) (w : Fin m → ℝ)
    (C : ℝ) (hCpos : 0 < C)
    (hφmeas : ∀ i, Measurable (φ i))
    (hφ01 : ∀ i t, φ i t ∈ Set.Icc (0 : ℝ) 1)
    (hBmeas : ∀ i, Measurable (B i))
    (hMB : ∀ (s : CubeSpace m) (j : Fin m), coreMreal φ s ≤ B j (s j))
    (hBvol : ∀ i τ, 0 ≤ τ → (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
        Real.exp (-(w i) * τ ^ 2 / C ^ 2))
    (hw0 : ∀ i, 0 ≤ w i) (hDpos : 0 < ∑ i, w i) :
    (∫⁻ s : CubeSpace m, coreMsect φ s ∂volume) ≤
      ENNReal.ofReal (C * Real.sqrt Real.pi / (2 * Real.sqrt (∑ i, w i))) := by
  have hMmeas : Measurable (coreMreal φ) := measurable_coreMreal φ hφmeas
  have hMnn : 0 ≤ᵐ[volume] (fun s : CubeSpace m => coreMreal φ s) :=
    Filter.Eventually.of_forall (fun s => coreMreal_nonneg φ s)
  have hMsect_eq : (∫⁻ s : CubeSpace m, coreMsect φ s ∂volume) =
      (∫⁻ s : CubeSpace m, ENNReal.ofReal (coreMreal φ s) ∂volume) := by
    apply lintegral_congr
    intro s
    exact coreMsect_eq_ofReal φ s
  have hcake := MeasureTheory.lintegral_eq_lintegral_meas_le (μ := (volume : Measure (CubeSpace m)))
    hMnn hMmeas.aemeasurable
  have hle_point (τ : ℝ) (hτ : 0 < τ) :
      ((volume : Measure (CubeSpace m)) {s : CubeSpace m | τ ≤ coreMreal φ s}) ≤
        ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2)) :=
    tau_level_volume_le φ B w C hCpos hφmeas hφ01 hBmeas hMB hBvol τ hτ
  have hmono_tau :
      (∫⁻ τ in Set.Ioi (0 : ℝ),
          ((volume : Measure (CubeSpace m)) {s : CubeSpace m | τ ≤ coreMreal φ s})) ≤
      (∫⁻ τ in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2))) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff']
    · apply Filter.Eventually.of_forall
      intro τ hτ
      exact hle_point τ hτ
    · exact measurableSet_Ioi
  calc
    (∫⁻ s : CubeSpace m, coreMsect φ s ∂volume)
        = (∫⁻ s : CubeSpace m, ENNReal.ofReal (coreMreal φ s) ∂volume) := hMsect_eq
    _ = (∫⁻ τ in Set.Ioi (0 : ℝ),
        ((volume : Measure (CubeSpace m)) {s : CubeSpace m | τ ≤ coreMreal φ s})) := hcake
    _ ≤ (∫⁻ τ in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2))) := hmono_tau
    _ = ENNReal.ofReal (C * Real.sqrt Real.pi / (2 * Real.sqrt (∑ i, w i))) := by
            have hrew3 : (fun τ : ℝ => ENNReal.ofReal
                (Real.exp (-(∑ i, w i) * τ ^ 2 / C ^ 2))) =
                (fun τ : ℝ => ENNReal.ofReal
                (Real.exp (-((∑ i, w i) * τ ^ 2 / C ^ 2)))) := by
              funext τ
              congr 1
              congr 1
              ring
            rw [hrew3]
            exact lintegral_half_exp hDpos hCpos

/-! ## Part VIII : concrete instantiation and main lemma -/

/-- product of `ofReal` over `Fin m` -/
lemma ofReal_prod_fin (m : ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i, ENNReal.ofReal (a i)) = ENNReal.ofReal (∏ i, a i) := by
  induction' m with m ih
  · simp
  · rw [Fin.prod_univ_succ, ih (fun i => a i.succ) (fun i => ha i.succ)]
    rw [← ENNReal.ofReal_mul (ha 0)]
    congr 1
    exact (Fin.prod_univ_succ (n := m) (f := a)).symm

/-- the window measure is finite -/
lemma coreEM_lt_top : coreEM Set.univ < ∞ := by
  exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by
    unfold coreEM
    rw [Measure.restrict_apply_univ]
    rw [coreE_eq]
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top)

/-- window mass of any set is at most 2 -/
lemma coreEM_mass_le_two (A : Set ℝ) : coreEM.real A ≤ 2 := by
  have hmono := measureReal_mono (μ := coreEM) (s₁ := A) (s₂ := Set.univ) (Set.subset_univ A)
    (ne_of_lt coreEM_lt_top)
  have hto : (coreEM Set.univ).toReal = 2 := by
    unfold coreEM
    rw [Measure.restrict_apply_univ]
    rw [coreE_eq]
    norm_num [Real.volume_Icc]
  have hle : coreEM.real A ≤ (coreEM Set.univ).toReal := hmono
  simpa [hto] using hle

/-- window level-mass for a charFun equals the plain volume level-set bound (alive case). -/
lemma window_level_charFun_volume {μ : Measure ℝ} [IsFiniteMeasure μ] (s : ℝ) :
    coreEM.real {t : ℝ | t ∈ coreE ∧ s ≤ ‖charFun μ t‖} =
      (volume {t : ℝ | t ∈ coreE ∧ s ≤ ‖charFun μ t‖}).toReal := by
  unfold coreEM
  rw [Measure.real_def]
  congr 1
  rw [Measure.restrict_apply (by
    exact coreE_measurable.inter (measurableSet_le measurable_const (measurable_abs_charFun (μ := μ))))]
  congr 1
  ext t
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, h.1⟩

/-- `Icc (-1) 1` and `Ioc (-1) 1` are a.e. equal for volume -/
lemma Icc_Ioc_ae_eq : (Set.Icc (-1 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Set.Ioc (-1 : ℝ) 1) := by
  rw [Filter.eventuallyEq_set]
  rw [MeasureTheory.ae_iff]
  have hsub : {x | ¬ (x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Ioc (-1 : ℝ) 1)} ⊆ ({-1} : Set ℝ) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hx
    constructor
    · intro hcc
      exact ⟨lt_of_le_of_ne (Set.mem_Icc.mp hcc).1 (Ne.symm hne), (Set.mem_Icc.mp hcc).2⟩
    · intro hoc
      exact ⟨le_of_lt (Set.mem_Ioc.mp hoc).1, (Set.mem_Ioc.mp hoc).2⟩
  have hvol : volume ({-1} : Set ℝ) = 0 := by simp
  exact measure_mono_null hsub hvol

/-- interval integral over `[-1,1]` of a continuous nonnegative function equals the toReal of
the window-lintegral of `ofReal` -/
lemma interval_integral_eq_coreE_lintegral {g : ℝ → ℝ} (hgcont : Continuous g) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in (-(1 : ℝ))..(1 : ℝ), g t) =
      (∫⁻ t, (coreE.indicator (fun t : ℝ => ENNReal.ofReal (g t))) t ∂volume).toReal := by
  have hset : coreE = Set.Icc (-1 : ℝ) 1 := coreE_eq
  have hinteq : (∫ t in (-(1 : ℝ))..(1 : ℝ), g t) = ∫ t, ((Set.Icc (-1 : ℝ) 1 : Set ℝ).indicator g) t ∂volume := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc (-1:ℝ) 1))]
    have hfuneq : (fun t : ℝ => (Set.Ioc (-1 : ℝ) 1).indicator g t) =ᵐ[volume]
        (fun t : ℝ => (Set.Icc (-1 : ℝ) 1).indicator g t) := by
      rw [Filter.EventuallyEq]
      rw [MeasureTheory.ae_iff]
      have hsub : {t | (Set.Ioc (-1 : ℝ) 1).indicator g t ≠ (Set.Icc (-1 : ℝ) 1).indicator g t} ⊆ ({-1} : Set ℝ) := by
        intro t ht
        rw [Set.mem_singleton_iff]
        by_contra hne
        apply ht
        by_cases h : t ∈ Set.Icc (-1 : ℝ) 1
        · have : t ∈ Set.Ioc (-1 : ℝ) 1 := ⟨lt_of_le_of_ne (Set.mem_Icc.mp h).1 (Ne.symm hne), (Set.mem_Icc.mp h).2⟩
          simp [h, this]
        · have : t ∉ Set.Ioc (-1 : ℝ) 1 := by
            intro hi
            apply h
            exact ⟨le_of_lt (Set.mem_Ioc.mp hi).1, (Set.mem_Ioc.mp hi).2⟩
          simp [h, this]
      have hvol : volume ({-1} : Set ℝ) = 0 := by simp
      exact measure_mono_null hsub hvol
    rw [integral_congr_ae hfuneq]
  rw [hinteq]
  have h0 : 0 ≤ᵐ[volume] (fun t : ℝ => (Set.Icc (-1 : ℝ) 1).indicator g t) := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1 <;> simp [ht, hg0]
  have hmea : AEStronglyMeasurable (fun t : ℝ => (Set.Icc (-1 : ℝ) 1).indicator g t) volume :=
    (hgcont.measurable.indicator measurableSet_Icc).aestronglyMeasurable
  have hreal := MeasureTheory.integral_eq_lintegral_of_nonneg_ae h0 hmea
  rw [hreal]
  apply congrArg ENNReal.toReal
  apply lintegral_congr
  intro t
  rw [hset]
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1 <;> simp [ht]

lemma product_integral_core_r1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
        (ρ : Fin m → ℝ), (∀ i : Fin m, 0 < ρ i) → (∀ i : Fin m, ρ i ≤ 1) →
        (0 < ∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
            * (ρ i) ^ 2) →
        (∫ t in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤
          C / Real.sqrt (∑ i : Fin m,
            (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal)
              * (ρ i) ^ 2) := by
  classical
  rcases essen_level_set_bound with ⟨C₀, hC₀pos, hEssen⟩
  refine ⟨C₀ * Real.sqrt Real.pi / 2, by positivity, ?_⟩
  intro m μ hprobinst ρ hρ0 hρ1 hD
  letI : ∀ i : Fin m, MeasureTheory.IsProbabilityMeasure (μ i) := hprobinst
  haveI : ∀ i : Fin m, IsFiniteMeasure (μ i) := fun i => by infer_instance
  let φ : Fin m → ℝ → ℝ := fun i t => ‖charFun (μ i) t‖
  let w : Fin m → ℝ := fun i => corew (μ i) (ρ i)
  let B : Fin m → ℝ → ℝ := fun i => (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then
      (if 0 < w i then C₀ * Real.sqrt (1 - s) / Real.sqrt (w i) else 2) else 0)
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    unfold w
    unfold corew
    exact mul_nonneg (coreq_toReal_nonneg (μ i) (ρ i)) (sq_nonneg (ρ i))
  have hD0 : 0 < ∑ i, w i := by
    simpa [w, corew, coreq, coreQ] using hD
  have hφmeas : ∀ i, Measurable (φ i) := by
    intro i
    exact measurable_abs_charFun (μ := μ i)
  have hφ01 : ∀ i t, φ i t ∈ Set.Icc (0 : ℝ) 1 := by
    intro i t
    constructor
    · unfold φ
      exact norm_nonneg _
    · unfold φ
      exact charFun_norm_le_one' (μ i) t
  have hBmeas : ∀ i, Measurable (B i) := by
    intro i
    exact levelB_measurable C₀ (w i)
  have hB0 : ∀ i s, 0 ≤ B i s := by
    intro i s
    exact levelB_nonneg C₀ (w i) (le_of_lt hC₀pos) s
  have hBvol : ∀ i τ, 0 ≤ τ → (volume ({s : ℝ | τ ≤ B i s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
      Real.exp (-(w i) * τ ^ 2 / C₀ ^ 2) := by
    intro i τ hτ
    have h := levelB_vol_le (w := w i) (C := C₀) hC₀pos hτ
    have hEx : Real.exp (-(w i * τ ^ 2 / C₀ ^ 2)) = Real.exp (-(w i) * τ ^ 2 / C₀ ^ 2) := by
      congr 1
      ring
    rw [← hEx]
    simpa [B] using h
  have hMB : ∀ (s : CubeSpace m) (j : Fin m), coreMreal φ s ≤ B j (s j) := by
    intro s j
    by_cases hsI : s j ∈ Set.Icc (0 : ℝ) 1
    · -- section ⊆ window-level set of coordinate j
      have hsecsub : {t : ℝ | (s, t) ∈ coreGSet φ} ⊆ {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} := by
        intro t ht
        change (s, t) ∈ coreGSet φ at ht
        change t ∈ coreE ∧ s j ≤ φ j t
        exact ⟨ht.1, ht.2 j |>.2⟩
      have hfin2 : coreEM {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} ≠ ∞ := by
        exact ne_of_lt (lt_of_le_of_lt (measure_mono (by intro t ht; simp)) coreEM_lt_top)
      have hmono : coreMreal φ s ≤ coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} := by
        unfold coreMreal
        exact measureReal_mono hsecsub hfin2
      by_cases hwj : 0 < w j
      · -- alive
        have hval : (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w j then
            C₀ * Real.sqrt (1 - s) / Real.sqrt (w j) else 2) else 0) (s j)
            = C₀ * Real.sqrt (1 - (s j)) / Real.sqrt (w j) := by
          simp [hsI, hwj]
        have hs0 : 0 ≤ s j := (Set.mem_Icc.mp hsI).1
        have hs1 : s j ≤ 1 := (Set.mem_Icc.mp hsI).2
        have hρ2pos : 0 < (ρ j) ^ 2 := sq_pos_of_pos (hρ0 j)
        have hwj' : 0 < coreq (μ j) (ρ j) * (ρ j) ^ 2 := by simpa [w, corew] using hwj
        have hwjcore : 0 < coreq (μ j) (ρ j) := by
          by_contra hnot
          have hqnn : 0 ≤ coreq (μ j) (ρ j) := coreq_toReal_nonneg (μ j) (ρ j)
          have hqz : coreq (μ j) (ρ j) = 0 := le_antisymm (le_of_not_gt hnot) hqnn
          have hwz : coreq (μ j) (ρ j) * (ρ j) ^ 2 = 0 := by rw [hqz]; simp
          linarith
        have hlev := levelSet_E_le C₀ hEssen (μ j) (ρ j) (hρ0 j) (hρ1 j) hwjcore (s j) hs0 hs1
        -- window level-mass = volume level-bound
        have hwin : coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} ≤
            C₀ * Real.sqrt (1 - s j) / Real.sqrt (w j) := by
          calc
            coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ ‖charFun (μ j) t‖}
                = (volume {t : ℝ | t ∈ coreE ∧ s j ≤ ‖charFun (μ j) t‖}).toReal := by
                    rw [window_level_charFun_volume (μ := μ j) (s := s j)]
            _ ≤ C₀ * Real.sqrt (1 - s j) / Real.sqrt (w j) := by
                    simpa [w, corew, coreq, coreQ] using hlev
        calc
          coreMreal φ s ≤ coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} := hmono
          _ ≤ C₀ * Real.sqrt (1 - s j) / Real.sqrt (w j) := by
              simpa [φ] using hwin
          _ = B j (s j) := by
              unfold B
              exact hval.symm
      · -- dead: bound by 2
        have hwin : coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} ≤ 2 := by
          exact coreEM_mass_le_two _
        have hval : (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w j then
            C₀ * Real.sqrt (1 - s) / Real.sqrt (w j) else 2) else 0) (s j) = 2 := by
          simp [hsI, hwj]
        calc
          coreMreal φ s ≤ coreEM.real {t : ℝ | t ∈ coreE ∧ s j ≤ φ j t} := hmono
          _ ≤ 2 := hwin
          _ = B j (s j) := by unfold B; exact hval.symm
    · -- s j outside the unit interval: section measure is zero
      have hsnotcube : s ∉ coreCube m := by
        rw [mem_coreCube_iff]
        intro h
        exact hsI (h j)
      have hM0 : coreMreal φ s = 0 := coreMreal_eq_zero_of_not_mem_cube φ hφ01 hsnotcube
      have hBnn : 0 ≤ B j (s j) := hB0 j (s j)
      linarith
  have hBd : (∫⁻ s : CubeSpace m, coreMsect φ s ∂volume) ≤
      ENNReal.ofReal (C₀ * Real.sqrt Real.pi / (2 * Real.sqrt (∑ i, w i))) := by
    exact core_sect_tau_bound φ B w C₀ hC₀pos hφmeas hφ01 hBmeas hMB hBvol hw0 hD0
  -- the lintegral over E of the product
  have hlin : (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume) =
      ∫⁻ s : CubeSpace m, coreMsect φ s ∂volume := by
    exact fubini_sect m φ hφmeas (fun i t => (hφ01 i t).1)
  have hmain_lin : (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume) ≤
      ENNReal.ofReal (C₀ * Real.sqrt Real.pi / (2 * Real.sqrt (∑ i, w i))) := by
    rw [hlin]
    exact hBd
  -- connect the real interval integral
  let g : ℝ → ℝ := fun t => ∏ i, φ i t
  have hgcont : Continuous g := by
    unfold g φ
    classical
    have hprod := continuous_finset_prod (s := Finset.univ) (f := fun i : Fin m => fun t : ℝ => ‖charFun (μ i) t‖)
      (by intro i hi; fun_prop)
    simpa using hprod
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    unfold g
    exact Finset.prod_nonneg (fun i hi => norm_nonneg _)
  have hconv := interval_integral_eq_coreE_lintegral hgcont hg0
  -- replace ∏ ofReal(φ) with ofReal ∏ φ in the lintegral integrand
  have hfun_eq : (fun t : ℝ => coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t)) t) =
      (fun t : ℝ => coreE.indicator (fun t : ℝ => ENNReal.ofReal (∏ i, φ i t)) t) := by
    funext t
    by_cases ht : t ∈ coreE
    · simp [ht, ofReal_prod_fin m (fun i => φ i t) (fun i => (hφ01 i t).1)]
    · simp [ht]
  have hconv' : (∫ t in (-(1 : ℝ))..(1 : ℝ), g t) =
      (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume).toReal := by
    calc
      (∫ t in (-(1 : ℝ))..(1 : ℝ), g t)
          = (∫⁻ t, (coreE.indicator (fun t : ℝ => ENNReal.ofReal (g t))) t ∂volume).toReal := hconv
      _ = (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume).toReal := by
          congr 1
          rw [hfun_eq]
  have hmain_lin' : (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume) ≤
      ENNReal.ofReal ((C₀ * Real.sqrt Real.pi / 2) / Real.sqrt (∑ i, w i)) := by
    have hval : ENNReal.ofReal (C₀ * Real.sqrt Real.pi / (2 * Real.sqrt (∑ i, w i))) =
        ENNReal.ofReal ((C₀ * Real.sqrt Real.pi / 2) / Real.sqrt (∑ i, w i)) := by
      congr 1
      field_simp [show (Real.sqrt (∑ i, w i)) ≠ 0 by exact ne_of_gt (Real.sqrt_pos.mpr hD0)]
    simpa [hval] using hmain_lin
  have htoReal : (∫ t in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤
      (C₀ * Real.sqrt Real.pi / 2) / Real.sqrt (∑ i, w i) := by
    calc
      (∫ t in (-(1 : ℝ))..(1 : ℝ), ∏ i : Fin m, ‖charFun (μ i) t‖)
          = (∫ t in (-(1 : ℝ))..(1 : ℝ), g t) := by rfl
      _ = (∫⁻ t, (coreE.indicator (fun t : ℝ => ∏ i, ENNReal.ofReal (φ i t))) t ∂volume).toReal := hconv'
      _ ≤ ((ENNReal.ofReal ((C₀ * Real.sqrt Real.pi / 2) / Real.sqrt (∑ i, w i))).toReal) := by
          exact (ENNReal.toReal_le_toReal
            (ne_of_lt (lt_of_le_of_lt hmain_lin' ENNReal.ofReal_lt_top))
            (by simp)).2 hmain_lin'
      _ = (C₀ * Real.sqrt Real.pi / 2) / Real.sqrt (∑ i, w i) := by
          rw [ENNReal.toReal_ofReal]
          positivity
  -- rewrite the sum to the statement's sum
  have hsum_eq : (∑ i : Fin m, w i) = ∑ i : Fin m,
      (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold w corew coreq coreQ
    rfl
  simpa [hsum_eq] using htoReal

end Commons.Probability.Levy
