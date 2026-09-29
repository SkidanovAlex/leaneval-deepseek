import Mathlib
import Submission.Commons.Probability.RandomMatrix.spectral_norm_bounded_entries

/-!
# Concentration of measure for the box discrepancy on `[0,1)^n`

This module proves the measure-concentration estimate underlying the Erdős--Turán approach
to the "fine holonomy bound" of Calegari--Dimitrov--Tang, without going through the
Erdős--Turán trigonometric inequality: a direct grid (cell-decomposition) argument followed by
Hoeffding's inequality for the empirical counts of the grid cells.

Main results (for the uniform probability measure `nu` on `[0,1)` and its `n`-fold product
`muP n` on `Fin n → ℝ`):

* `disc t` is the **box discrepancy** of the point configuration `t`, the supremum over
  half-open subintervals `[a,b) ⊆ [0,1]` of `|(b-a) - #{i : t i ∈ [a,b)}/n|`;
* `disc_le_one : disc t ≤ 1`;
* `exists_grid_dev_of_disc_le` — the grid approximation: if `4 < m·ε` then a configuration with
  `disc t ≥ ε` has some grid interval `[k/m, l/m)` (`k,l ≤ m`) whose deviation is `≥ ε/2`;
* `measure_dev_le` — the Hoeffding bound for the deviation of a single grid interval;
* `disc_concentration` — **concentration of measure**:
  `(muP n).real {t | ε ≤ disc t} ≤ min 1 (100·ε⁻²·exp(-n·ε²/8))`, a bound with the (optimal)
  exponent `ε²` in place of the classical Erdős--Turán-derived `ε⁴`.

REMARK on the definition of the discrepancy.  `disc` is the supremum over *half-open* intervals
`[a,b)` with `0 ≤ a ≤ b ≤ 1` (the convention that makes the grid argument work), whereas the paper
uses closed intervals `I ⊂ [0,1)`.  The two suprema coincide: given a closed interval `I`, any
slightly enlarged half-open interval `[a-η, b+η)` contains all points of `I` and has measure
`μ(I) + 2η`, so the half-open supremum is at least `|#{t i ∈ I}/n - μ(I)| - 2η` for every `η > 0`;
letting `η → 0` gives the inequality in the direction used here (the converse is immediate since a
half-open interval is contained in the corresponding closed one up to boundary points).  Hence
`disc_concentration` applies to the paper's discrepancy function as well.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Submission.CDT.Discrepancy

/-! ## 1. The uniform probability measure on `[0,1)` and its product -/

/-- Lebesgue measure restricted to `[0,1)`. -/
noncomputable def nu : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ico 0 1)

lemma nu_univ : nu Set.univ = 1 := by
  simp only [nu, Measure.restrict_apply_univ, Real.volume_Ico, sub_zero]
  norm_num

instance instNu : IsProbabilityMeasure nu := ⟨nu_univ⟩

lemma nu_Ico {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1) :
    nu (Set.Ico a b) = ENNReal.ofReal (b - a) := by
  simp only [nu]
  rw [Measure.restrict_apply measurableSet_Ico]
  have h : Set.Ico a b ∩ Set.Ico 0 1 = Set.Ico a b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ico]
    exact ⟨fun h => h.1, fun h => ⟨h, ⟨le_trans h0 h.1, lt_of_lt_of_le h.2 h1⟩⟩⟩
  rw [h, Real.volume_Ico]

lemma nu_real_Ico {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    nu.real (Set.Ico a b) = b - a := by
  rw [measureReal_def, nu_Ico h0 h1, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma nu_real_le_one (s : Set ℝ) : nu.real s ≤ 1 := by
  have := measureReal_mono (μ := nu) (Set.subset_univ s)
  rwa [probReal_univ] at this

lemma nu_real_nonneg (s : Set ℝ) : 0 ≤ nu.real s := ENNReal.toReal_nonneg

/-- The `n`-fold product of `nu`; the uniform probability measure on `[0,1)^n`. -/
noncomputable def muP (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => nu)

instance instMuP (n : ℕ) : IsProbabilityMeasure (muP n) := by
  unfold muP; infer_instance

/-! ## 2. The box discrepancy -/

/-- The number of points `t i` lying in the half-open interval `[a,b)`. -/
noncomputable def cnt {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => t i ∈ Set.Ico a b)).card

lemma cnt_le {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) : cnt t a b ≤ n := by
  simp only [cnt]
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i : Fin n => t i ∈ Set.Ico a b)

lemma cnt_coe_nonneg {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) : (0:ℝ) ≤ (cnt t a b : ℝ) := by
  positivity

lemma cnt_coe_le {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) (hn : 0 < n) :
    (cnt t a b : ℝ) / n ≤ 1 := by
  have h : (cnt t a b : ℝ) ≤ (n:ℝ) := by exact_mod_cast cnt_le t a b
  rw [div_le_one (by exact_mod_cast hn)]
  exact h

/-- The box discrepancy of the point configuration `t`: the supremum over half-open
subintervals `[a,b)` of `[0,1]` of the deviation of the empirical count from the length. -/
noncomputable def disc {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => |(p.2 - p.1) - (cnt t p.1 p.2 : ℝ)/(n:ℝ)|) ''
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1})

lemma disc_bddAbove {n : ℕ} (t : Fin n → ℝ) :
    BddAbove ((fun p : ℝ × ℝ => |(p.2 - p.1) - (cnt t p.1 p.2 : ℝ)/(n:ℝ)|) ''
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}) := by
  refine ⟨2, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨h0, h12, h21⟩ := hp
  have h1 : (0:ℝ) ≤ p.2 - p.1 := by linarith
  have h2 : p.2 - p.1 ≤ 1 := by linarith
  have h3 : (cnt t p.1 p.2 : ℝ) / (n:ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact cnt_coe_le t p.1 p.2 hn
  have h4 : (0:ℝ) ≤ (cnt t p.1 p.2 : ℝ) / (n:ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

lemma disc_nonempty {n : ℕ} (t : Fin n → ℝ) :
    ((fun p : ℝ × ℝ => |(p.2 - p.1) - (cnt t p.1 p.2 : ℝ)/(n:ℝ)|) ''
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}).Nonempty :=
  ⟨_, (0,0), ⟨le_refl 0, le_refl 0, by norm_num⟩, rfl⟩

lemma disc_le_one {n : ℕ} (t : Fin n → ℝ) : disc t ≤ 1 := by
  refine csSup_le (disc_nonempty t) ?_
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨h0, h12, h21⟩ := hp
  have h1 : (0:ℝ) ≤ p.2 - p.1 := by linarith
  have h2 : p.2 - p.1 ≤ 1 := by linarith
  have h3 : (cnt t p.1 p.2 : ℝ) / (n:ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact cnt_coe_le t p.1 p.2 hn
  have h4 : (0:ℝ) ≤ (cnt t p.1 p.2 : ℝ) / (n:ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- The grid deviation at the pair `(k,l)`: the deviation of the empirical count on
the half-open interval `[k/m, l/m)` from the measure of that interval. -/
noncomputable def dev {n : ℕ} (t : Fin n → ℝ) (m : ℕ) (k l : ℕ) : ℝ :=
  (cnt t ((k:ℝ)/m) ((l:ℝ)/m) : ℝ)/(n:ℝ) - nu.real (Set.Ico ((k:ℝ)/m) ((l:ℝ)/m))

lemma div_lt_of_lt_floor {x : ℝ} {m : ℕ} (hm : (0:ℝ) < m) {l : ℕ} (h : x * m < (l:ℝ) + 1) :
    x - 1/m < (l:ℝ)/m := by
  rw [lt_div_iff₀ hm]
  have : (x - 1/(m:ℝ)) * m = x * m - 1 := by field_simp
  rw [this]; linarith

lemma lt_div_of_lt_ceil {x : ℝ} {m : ℕ} (hm : (0:ℝ) < m) {k : ℕ} (h : (k:ℝ) < x * m + 1) :
    (k:ℝ)/m < x + 1/m := by
  rw [div_lt_iff₀ hm]
  have : (x + 1/(m:ℝ)) * m = x * m + 1 := by field_simp
  rw [this]; exact h

lemma div_m_cast_le {m : ℕ} (hm : (0:ℝ) < m) {a b : ℕ} (h : a ≤ b) :
    (a:ℝ)/m ≤ (b:ℝ)/m :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hm)

lemma div_m_cast_le_one {m : ℕ} (hm : (0:ℝ) < m) {a : ℕ} (h : a ≤ m) : (a:ℝ)/m ≤ 1 := by
  rw [div_le_one hm]
  exact_mod_cast h

lemma dev_eq {n m k l : ℕ} (t : Fin n → ℝ) (h : k ≤ l) (hm : (0:ℝ) < m) (hl : l ≤ m) :
    dev t m k l = (cnt t ((k:ℝ)/m) ((l:ℝ)/m) : ℝ)/(n:ℝ) - ((l:ℝ)/m - (k:ℝ)/m) := by
  rw [dev, nu_real_Ico (by positivity) (div_m_cast_le hm h) (div_m_cast_le_one hm hl)]

/-! ## 3. The tail bound for a single grid interval -/

open Commons.Probability.RandomMatrix

lemma integral_indicator_Ico_eval {n : ℕ} (i : Fin n) (a b : ℝ) :
    ∫ t : Fin n → ℝ, (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) ∂(muP n)
      = nu.real (Set.Ico a b) := by
  rw [show (muP n) = Measure.pi (fun _ : Fin n => nu) from rfl]
  rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => nu) (i := i)
    (f := (Set.Ico a b).indicator (1 : ℝ → ℝ))
    (measurable_const.indicator measurableSet_Ico).aestronglyMeasurable,
    integral_indicator_one measurableSet_Ico]

lemma indicator_Ico_apply {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) = if t i ∈ Set.Ico a b then 1 else 0 :=
  Set.indicator_apply _ _ _

lemma sum_indicator_eval {n : ℕ} (t : Fin n → ℝ) (a b : ℝ) :
    (∑ i : Fin n, (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i)) = (cnt t a b : ℝ) := by
  simp only [indicator_Ico_apply, cnt]
  rw [Finset.sum_boole]

lemma integral_indicator_Ico_sub {n : ℕ} (i : Fin n) (a b : ℝ) :
    ∫ t : Fin n → ℝ, ((Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) - nu.real (Set.Ico a b))
      ∂(muP n) = 0 := by
  have hmeas : AEStronglyMeasurable (fun t : Fin n → ℝ =>
      (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i)) (muP n) :=
    ((measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply i)).aestronglyMeasurable
  rw [integral_sub (Integrable.of_bound hmeas 1 (by
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_le]
      rw [indicator_Ico_apply]
      split <;> norm_num)) (integrable_const _)]
  rw [integral_indicator_Ico_eval i a b, integral_const]
  simp [probReal_univ]

lemma abs_indicator_Ico_sub_le_one {n : ℕ} (t : Fin n → ℝ) (i : Fin n) (a b : ℝ) :
    |(Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) - nu.real (Set.Ico a b)| ≤ 1 := by
  rw [abs_le]
  have hJ0 : 0 ≤ nu.real (Set.Ico a b) := nu_real_nonneg _
  have hJ1 : nu.real (Set.Ico a b) ≤ 1 := nu_real_le_one _
  have h : (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) = 0 ∨
      (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) = 1 := by
    rw [indicator_Ico_apply]
    split
    · right; rfl
    · left; rfl
  rcases h with h | h <;> rw [h] <;> constructor <;> linarith

lemma sum_X_eq {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℝ) (a b : ℝ) :
    (∑ i : Fin n, ((Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) - nu.real (Set.Ico a b)))
      = (n:ℝ) * ((cnt t a b : ℝ)/(n:ℝ) - nu.real (Set.Ico a b)) := by
  rw [Finset.sum_sub_distrib]
  simp only [sum_indicator_eval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have : (n:ℝ) ≠ 0 := by positivity
  field_simp

lemma measure_dev_le {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (k l : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (muP n).real {t : Fin n → ℝ | δ ≤ |dev t m k l|} ≤ 2 * Real.exp (-(n:ℝ) * δ^2 / 2) := by
  classical
  set a : ℝ := (k:ℝ)/m with ha
  set b : ℝ := (l:ℝ)/m with hb
  have hdev : ∀ t : Fin n → ℝ, dev t m k l = (cnt t a b : ℝ)/(n:ℝ) - nu.real (Set.Ico a b) := by
    intro t; rw [dev, ha, hb]
  set X : Fin n → (Fin n → ℝ) → ℝ :=
    fun i t => (Set.Ico a b).indicator (1 : ℝ → ℝ) (t i) - nu.real (Set.Ico a b) with hX
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    exact ((measurable_const.indicator measurableSet_Ico).comp (measurable_pi_apply i)).sub_const _
  have hindep : iIndepFun X (muP n) := by
    have h0 : iIndepFun (fun i (t : Fin n → ℝ) => X i t) (Measure.pi (fun _ : Fin n => nu)) :=
      iIndepFun_pi (μ := fun _ : Fin n => nu) (X := fun _ (x : ℝ) =>
        (Set.Ico a b).indicator (1 : ℝ → ℝ) x - nu.real (Set.Ico a b))
        (fun _ => ((measurable_const.indicator measurableSet_Ico).sub_const _).aemeasurable)
    rw [show (muP n) = Measure.pi (fun _ : Fin n => nu) from rfl]
    exact h0
  have hsub : ∀ i, HasSubgaussianMGF (X i) (Kp 1) (muP n) := by
    intro i
    refine entry_subG (muP n) (X i) (hXmeas i) 1 (by norm_num) ?_ ?_
    · intro t
      rw [hX]
      exact abs_indicator_Ico_sub_le_one t i a b
    · rw [hX]
      exact integral_indicator_Ico_sub i a b
  have htail := abs_sum_tail (muP n) X hindep (fun _ => Kp 1) hsub (ε := (n:ℝ) * δ) (by positivity)
  have hsumc : (((∑ _i : Fin n, Kp 1 : ℝ≥0)) : ℝ) = (n:ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
      Kp_coe 1 (by norm_num)]
    simp
  rw [hsumc] at htail
  have hXsum : ∀ t : Fin n → ℝ, (∑ i, X i t)
      = (n:ℝ) * ((cnt t a b : ℝ)/(n:ℝ) - nu.real (Set.Ico a b)) := by
    intro t
    rw [hX]
    exact sum_X_eq hn t a b
  have hset : {t : Fin n → ℝ | δ ≤ |dev t m k l|}
      = {t : Fin n → ℝ | (n:ℝ) * δ ≤ |∑ i, X i t|} := by
    ext t
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hdev t, hXsum t, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
    constructor <;> intro hh
    · exact mul_le_mul_of_nonneg_left hh (by positivity)
    · exact le_of_mul_le_mul_left hh (by positivity)
  rw [← hset] at htail
  have harg : -((n:ℝ) * δ)^2 / (2 * (n:ℝ)) = -(n:ℝ) * δ^2 / 2 := by
    field_simp
  rw [harg] at htail
  exact htail

/-! ## 4. The discrepancy bound -/

lemma measureReal_biUnion_finset_le {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (s : Finset ι) (A : ι → Set Ω) :
    μ.real (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.real (A i) := by
  have h1 : μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) := measure_biUnion_finset_le s A
  have hfin : ∀ i ∈ s, μ (A i) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  have htop : (∑ i ∈ s, μ (A i)) ≠ ⊤ := by
    rw [← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun i hi => lt_top_iff_ne_top.mpr (hfin i hi)
  have h2 : (∑ i ∈ s, μ (A i)).toReal = ∑ i ∈ s, μ.real (A i) := by
    rw [ENNReal.toReal_sum hfin]; rfl
  calc μ.real (⋃ i ∈ s, A i) = (μ (⋃ i ∈ s, A i)).toReal := rfl
    _ ≤ (∑ i ∈ s, μ (A i)).toReal := ENNReal.toReal_mono htop h1
    _ = ∑ i ∈ s, μ.real (A i) := h2

/-- **The grid approximation.**  If `4 < m ε` then every configuration whose box discrepancy is
at least `ε` has some grid interval `[k/m, l/m)` (`k,l ≤ m`) whose deviation is at least `ε/2`. -/
lemma exists_grid_dev_of_disc_le {n m : ℕ} {ε : ℝ} (hε : 0 < ε) (hm : 4 < (m:ℝ) * ε)
    (t : Fin n → ℝ) (ht : ε ≤ disc t) :
    ∃ k l : ℕ, k ≤ m ∧ l ≤ m ∧ ε/2 < |dev t m k l| := by
  have hmpos : (0:ℝ) < m := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2m : 2/(m:ℝ) < ε/2 := by
    rw [div_lt_div_iff₀ hmpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hlt : ε/2 + 2/(m:ℝ) < disc t := by linarith
  obtain ⟨y, hymem, hy⟩ := (lt_csSup_iff (disc_bddAbove t) (disc_nonempty t)).mp hlt
  obtain ⟨p, hp, rfl⟩ := hymem
  simp only at hy
  obtain ⟨hp0, hp12, hp21⟩ := hp
  have hp1 : p.1 ≤ 1 := le_trans hp12 hp21
  have hp1m : (0:ℝ) ≤ p.1 * m := mul_nonneg hp0 (le_of_lt hmpos)
  have hp2m : (0:ℝ) ≤ p.2 * m := mul_nonneg (le_trans hp0 hp12) (le_of_lt hmpos)
  have hp1mm : p.1 * m ≤ (m:ℝ) := mul_le_of_le_one_left (le_of_lt hmpos) hp1
  have hp2mm : p.2 * m ≤ (m:ℝ) := mul_le_of_le_one_left (le_of_lt hmpos) hp21
  set kp : ℕ := ⌊p.1 * (m:ℝ)⌋₊ with hkp
  set lp : ℕ := ⌈p.2 * (m:ℝ)⌉₊ with hlp
  set km : ℕ := ⌈p.1 * (m:ℝ)⌉₊ with hkm
  set lm : ℕ := ⌊p.2 * (m:ℝ)⌋₊ with hlm
  have hkp_le : (kp:ℝ) ≤ p.1 * m := Nat.floor_le hp1m
  have hlp_ge : p.2 * m ≤ (lp:ℝ) := Nat.le_ceil _
  have hkm_ge : p.1 * m ≤ (km:ℝ) := Nat.le_ceil _
  have hlm_le : (lm:ℝ) ≤ p.2 * m := Nat.floor_le hp2m
  have hkm_lt : (km:ℝ) < p.1 * m + 1 := Nat.ceil_lt_add_one hp1m
  have hlm_gt : p.2 * m < (lm:ℝ) + 1 := Nat.lt_floor_add_one _
  have hkp_gt : p.1 * m < (kp:ℝ) + 1 := Nat.lt_floor_add_one _
  have hlp_lt : (lp:ℝ) < p.2 * m + 1 := Nat.ceil_lt_add_one hp2m
  have hkp_m : kp ≤ m := Nat.floor_le_of_le hp1mm
  have hlp_m : lp ≤ m := Nat.ceil_le.mpr hp2mm
  have hkm_m : km ≤ m := Nat.ceil_le.mpr hp1mm
  have hlm_m : lm ≤ m := Nat.floor_le_of_le hp2mm
  have hp12m : p.1 * m ≤ p.2 * m := mul_le_mul_of_nonneg_right hp12 (le_of_lt hmpos)
  have hkp_lp : kp ≤ lp := by
    have h : (kp:ℝ) ≤ (lp:ℝ) := by linarith
    exact_mod_cast h
  by_cases hsign : (0:ℝ) ≤ (p.2 - p.1) - (cnt t p.1 p.2 : ℝ)/(n:ℝ)
  · -- the interval `[p.1,p.2)` has too few points: use the inner grid interval
    have hL : ε/2 + 2/(m:ℝ) < (p.2 - p.1) - (cnt t p.1 p.2 : ℝ)/(n:ℝ) := by
      rw [abs_of_nonneg hsign] at hy; exact hy
    have hm2 : 2 ≤ (p.2 - p.1) * m := by
      have hd : (0:ℝ) ≤ (cnt t p.1 p.2 : ℝ)/(n:ℝ) := by positivity
      have h : 2/(m:ℝ) < p.2 - p.1 := by linarith
      rw [div_lt_iff₀ hmpos] at h
      linarith
    have hkl : km ≤ lm := by
      have h : (km:ℝ) ≤ (lm:ℝ) := by nlinarith
      exact_mod_cast h
    have hcnt_in : cnt t ((km:ℝ)/m) ((lm:ℝ)/m) ≤ cnt t p.1 p.2 := by
      simp only [cnt]
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨le_trans (by rw [le_div_iff₀ hmpos]; linarith) hi.1,
        lt_of_lt_of_le hi.2 (by rw [div_le_iff₀ hmpos]; linarith)⟩
    have hnu_in : (p.2 - p.1) - 2/m ≤ nu.real (Set.Ico ((km:ℝ)/m) ((lm:ℝ)/m)) := by
      rw [nu_real_Ico (by positivity) (div_m_cast_le hmpos hkl) (div_m_cast_le_one hmpos hlm_m)]
      have h1 : (km:ℝ)/m < p.1 + 1/(m:ℝ) := lt_div_of_lt_ceil hmpos hkm_lt
      have h2 : (lm:ℝ)/m > p.2 - 1/(m:ℝ) := div_lt_of_lt_floor hmpos hlm_gt
      field_simp at h1 h2 ⊢
      linarith
    refine ⟨km, lm, hkm_m, hlm_m, ?_⟩
    rw [dev, lt_abs]
    right
    have h1 : (cnt t ((km:ℝ)/m) ((lm:ℝ)/m) : ℝ)/(n:ℝ) ≤ (cnt t p.1 p.2 : ℝ)/(n:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcnt_in) (by positivity)
    linarith
  · -- the interval `[p.1,p.2)` has too many points: use the outer grid interval
    have hL : ε/2 + 2/(m:ℝ) < (cnt t p.1 p.2 : ℝ)/(n:ℝ) - (p.2 - p.1) := by
      rw [abs_of_neg (not_le.mp hsign)] at hy
      linarith
    have hentry : ∀ i : Fin n, t i ∈ Set.Ico p.1 p.2 →
        t i ∈ Set.Ico ((kp:ℝ)/m) ((lp:ℝ)/m) := by
      intro i hi
      exact ⟨le_trans (by rw [div_le_iff₀ hmpos]; linarith [hkp_le]) hi.1,
        lt_of_lt_of_le hi.2 (by rw [le_div_iff₀ hmpos]; linarith [Nat.le_ceil (p.2 * (m:ℝ))])⟩
    have hcnt_out : cnt t p.1 p.2 ≤ cnt t ((kp:ℝ)/m) ((lp:ℝ)/m) := by
      simp only [cnt]
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hentry i hi
    have hnu_out : nu.real (Set.Ico ((kp:ℝ)/m) ((lp:ℝ)/m)) ≤ (p.2 - p.1) + 2/m := by
      rw [nu_real_Ico (by positivity) (div_m_cast_le hmpos hkp_lp) (div_m_cast_le_one hmpos hlp_m)]
      have h1 : (lp:ℝ)/m < p.2 + 1/(m:ℝ) := lt_div_of_lt_ceil hmpos hlp_lt
      have h2 : (kp:ℝ)/m > p.1 - 1/(m:ℝ) := div_lt_of_lt_floor hmpos hkp_gt
      field_simp at h1 h2 ⊢
      linarith
    refine ⟨kp, lp, hkp_m, hlp_m, ?_⟩
    rw [dev, lt_abs]
    left
    have h1 : (cnt t p.1 p.2 : ℝ)/(n:ℝ) ≤ (cnt t ((kp:ℝ)/m) ((lp:ℝ)/m) : ℝ)/(n:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcnt_out) (by positivity)
    linarith

/-! ## 5. Concentration of measure for the box discrepancy -/

theorem disc_concentration {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    (muP n).real {t : Fin n → ℝ | ε ≤ disc t}
      ≤ min 1 (100 * (ε⁻¹)^2 * Real.exp (-(n:ℝ) * ε^2 / 8)) := by
  rcases lt_or_ge (1:ℝ) ε with h1 | h1
  · have hempty : {t : Fin n → ℝ | ε ≤ disc t} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt (disc_le_one t) h1
    rw [hempty, measureReal_empty]
    exact le_min zero_le_one (by positivity)
  · set m : ℕ := ⌊4/ε⌋₊ + 1 with hm
    have hmε : 4 < (m:ℝ) * ε := by
      have h := Nat.lt_floor_add_one (4/ε)
      rw [div_lt_iff₀ hε] at h
      simpa [hm] using h
    have hmpos : (0:ℝ) < m := by
      by_contra h
      rw [not_lt] at h
      nlinarith
    have hmle : (m:ℝ) ≤ 4/ε + 1 := by
      have h := Nat.floor_le (show (0:ℝ) ≤ 4/ε from by positivity)
      simp only [hm]
      push_cast
      linarith
    have hm1 : (m:ℝ) + 1 ≤ 6 * ε⁻¹ := by
      have h2 : (2:ℝ) ≤ 2 * ε⁻¹ := by
        rw [le_mul_inv_iff₀ hε]; linarith
      have h3 : (m:ℝ) ≤ 4 * ε⁻¹ + 1 := by
        have := hmle
        rw [div_eq_mul_inv] at this
        linarith
      linarith
    -- the union of the exceptional events over the grid
    have hsub : {t : Fin n → ℝ | ε ≤ disc t} ⊆
        ⋃ p ∈ (Finset.univ : Finset (Fin (m+1) × Fin (m+1))),
          {t : Fin n → ℝ | ε/2 < |dev t m (p.1 : ℕ) (p.2 : ℕ)|} := by
      intro t ht
      obtain ⟨k, l, hk, hl, hdev⟩ := exists_grid_dev_of_disc_le hε hmε t ht
      exact Set.mem_iUnion.mpr ⟨(⟨k, Nat.lt_succ_of_le hk⟩, ⟨l, Nat.lt_succ_of_le hl⟩),
        Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hdev⟩⟩
    have hbound : (muP n).real {t : Fin n → ℝ | ε ≤ disc t}
        ≤ ((m+1)*(m+1) : ℕ) * (2 * Real.exp (-(n:ℝ) * (ε/2)^2 / 2)) := by
      have hstep : (muP n).real {t : Fin n → ℝ | ε ≤ disc t}
          ≤ ∑ p ∈ (Finset.univ : Finset (Fin (m+1) × Fin (m+1))),
              (2 * Real.exp (-(n:ℝ) * (ε/2)^2 / 2)) := by
        refine (measureReal_mono hsub (measure_ne_top _ _)).trans
          ((measureReal_biUnion_finset_le _ _ _).trans ?_)
        apply Finset.sum_le_sum
        intro p hp
        exact (measureReal_mono (Set.ofPred_subset_ofPred.mpr (fun t ht => le_of_lt ht))
          (measure_ne_top _ _)).trans (measure_dev_le hn (p.1 : ℕ) (p.2 : ℕ) (by positivity))
      refine hstep.trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hmain : (muP n).real {t : Fin n → ℝ | ε ≤ disc t}
        ≤ 100 * (ε⁻¹)^2 * Real.exp (-(n:ℝ) * ε^2 / 8) := by
      refine hbound.trans ?_
      have hexp : Real.exp (-(n:ℝ) * (ε/2)^2 / 2) = Real.exp (-(n:ℝ) * ε^2 / 8) := by
        congr 1; ring
      rw [hexp]
      have hcast : ((m+1)*(m+1) : ℕ) = (m+1) * (m+1) := rfl
      have hx : (0:ℝ) ≤ ((m+1 : ℕ) : ℝ) := by positivity
      have h5 : ((m+1 : ℕ) : ℝ) ≤ 6 * ε⁻¹ := by
        push_cast; exact hm1
      have hgap : 2 * (((m+1 : ℕ) : ℝ))^2 ≤ 100 * (ε⁻¹)^2 := by
        have he : (0:ℝ) < ε⁻¹ := inv_pos.mpr hε
        nlinarith [h5, hx, he]
      have hexpnn : (0:ℝ) ≤ Real.exp (-(n:ℝ) * ε^2 / 8) := Real.exp_nonneg _
      push_cast at hgap
      rw [hcast]
      push_cast
      nlinarith [hgap, hexpnn]
    refine le_min ?_ hmain
    have : (muP n).real {t : Fin n → ℝ | ε ≤ disc t} ≤ (muP n).real Set.univ :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    rwa [probReal_univ] at this

end Submission.CDT.Discrepancy
