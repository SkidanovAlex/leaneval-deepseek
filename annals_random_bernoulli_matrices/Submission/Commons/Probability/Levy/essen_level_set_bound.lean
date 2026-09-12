import Mathlib
import Submission.Commons.Probability.Levy.levy_interval_L1
import Submission.Commons.Probability.Levy.concentration_sq_bound
import Submission.Commons.Probability.Levy.levy_interval_mass_bound
import Submission.Commons.Measure.Resonance.arc_measure
import Submission.Commons.Measure.Markov.measureReal_markov

/-! # Esseen level-set bound

We prove the single-variable "essential level set" estimate used in the Esséen-type proof
of the Lévy--Kolmogorov--Rogozin inequality: for a probability measure `μ` on `ℝ`, `ρ > 0`
and the Lévy concentration `Q(ρ) = sup_l μ (Icc (l−ρ) (l+ρ))`, if `1 − Q(ρ) > 0`, then the
Lebesgue measure of the set of `t ∈ [−1/ρ, 1/ρ]` where `|charFun μ t| ≥ 1 − η` is at most
`C · √(η / (1 − Q(ρ))) / ρ` for a universal constant `C`.

## Proof outline

*Trigonometry (arc measure).*  For `0 ≤ α`, `|y| ≥ ρ`, the measure of
`{t : |t| ≤ 1/ρ ∧ 1 − cos (t·y) ≤ α}` is `O(√α/ρ)`: the set is contained in the union of the
arcs `|t·y − 2πk| ≤ 2√α` (`k : ℤ`), at most `O(|y|/ρ)` of which meet the dual window, each of
length `4√α/|y|`.  (Published separately as `Commons.Measure.Resonance.arc_measure`.)

*Symmetrization.*  Let `X, X′ ~ μ` be independent and put `Y := X − X′` (law `ν`).  Then
`g(t) := E cos (t·Y) = |charFun μ t|²`, hence the level set `|charFun μ t| ≥ 1 − η` is
contained in `{t : 1 − g(t) ≤ 2η}`.  The concentration function of `ν` is bounded by that of
`μ` (every window mass of `ν` is an average of window masses of `μ`), so with
`p := ν {|y| > ρ}` we have `p ≥ 1 − Q_μ(ρ) > 0`.

*Markov + Fubini.*  For `t` in the level set, `E_ν[1 − cos (tY)] ≤ 2η`, so restricting to the
far set `F := {|y| > ρ}` gives `∫_F (1 − cos (t·y)) dν ≤ 2η`.  Markov's inequality (applied to
the restricted measure) shows that at least half of the `F`-mass satisfies
`1 − cos (t·y) ≤ 2·(2η/p)`.  Integrating over `t` in the level set and swapping the order of
integration, every `y ∈ F` contributes at most the arc measure bound `O(√(4η/p)/ρ)`, giving
`vol{level set} = O(√(η/p)/ρ) = O(√(η/(1−Q_μ(ρ)))/ρ)`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace Commons.Probability.Levy

/-! ## Part II: the difference measure and its characteristic function -/

/-- the law of the difference of two independent samples. -/
noncomputable def diffLaw (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)

/-- norm of the characteristic function of the difference equals the square of the norm. -/
lemma norm_charFun_diff (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖charFun (diffLaw μ) t‖ = ‖charFun μ t‖ ^ 2 := by
  simpa [diffLaw] using norm_charFun_difference μ t

/-- `(charFun (diffLaw μ) t) = ‖charFun μ t‖²` as a real complex number. -/
lemma charFun_diff_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (diffLaw μ) t = (‖charFun μ t‖ ^ 2 : ℝ) := by
  have h := charFun_difference μ t
  change charFun ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2)) t = (‖charFun μ t‖ ^ 2 : ℝ)
  rw [h]
  have hmul : charFun μ t * starRingEnd ℂ (charFun μ t) = (‖charFun μ t‖ ^ 2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact hmul

/-- `Re (charFun (diffLaw μ) t) = ‖charFun μ t‖²`. -/
lemma re_charFun_diff (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun (diffLaw μ) t).re = ‖charFun μ t‖ ^ 2 := by
  rw [charFun_diff_eq]
  exact Complex.ofReal_re (‖charFun μ t‖ ^ 2)

/-- `E_ν[cos (tY)] = ‖charFun μ t‖²`. -/
lemma integral_cos_diff (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) = ‖charFun μ t‖ ^ 2 := by
  haveI : IsProbabilityMeasure (diffLaw μ) := by
    rw [diffLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have h1 : (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) = (charFun (diffLaw μ) t).re := by
    have h := integral_cos_eq_re_char (μ := diffLaw μ) (t := t) (a := 0)
    simpa using h
  rw [h1]
  exact re_charFun_diff μ t


/-! ## Part III: concentration function of the difference is dominated -/

/-- Lévy concentration of a measure on `ℝ` at half-width `ρ` (sup over window centres). -/
noncomputable def levyQ (μ : Measure ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}

/-- A window mass of the difference law is at most the supremum window mass of `μ`. -/
lemma diffLaw_window_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ l : ℝ) :
    diffLaw μ (Set.Icc (l - ρ) (l + ρ)) ≤ levyQ μ ρ := by
  let w : Set ℝ := Set.Icc (l - ρ) (l + ρ)
  have hw : MeasurableSet w := measurableSet_Icc
  have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := by fun_prop
  have hsec : ∀ x : ℝ, μ {y : ℝ | x - y ∈ w} ≤ levyQ μ ρ := by
    intro x
    have hset : {y : ℝ | x - y ∈ w} = Set.Icc ((x - l) - ρ) ((x - l) + ρ) := by
      ext y
      change x - y ∈ Set.Icc (l - ρ) (l + ρ) ↔ y ∈ Set.Icc ((x - l) - ρ) ((x - l) + ρ)
      rw [Set.mem_Icc, Set.mem_Icc]
      constructor <;> intro hy <;> constructor <;> nlinarith
    rw [hset]
    unfold levyQ
    exact le_sSup ⟨x - l, rfl⟩
  calc
    diffLaw μ w = (μ.prod μ) ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' w) := by
      unfold diffLaw
      rw [Measure.map_apply hsub hw]
    _ ≤ levyQ μ ρ := by
      have hs : MeasurableSet ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' w) := hsub hw
      have hinner : ∀ x : ℝ, μ (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' w)) =
          μ {y : ℝ | x - y ∈ w} := by
        intro x
        congr 2
      calc
        (μ.prod μ) ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' w)
            = ∫⁻ x : ℝ, μ (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' w)) ∂μ := by
              exact Measure.prod_apply hs
        _ = ∫⁻ x : ℝ, μ {y : ℝ | x - y ∈ w} ∂μ := by
              exact lintegral_congr (fun x => hinner x)
        _ ≤ ∫⁻ x : ℝ, levyQ μ ρ ∂μ := lintegral_mono (fun x => hsec x)
        _ = levyQ μ ρ * μ Set.univ := lintegral_const _
        _ = levyQ μ ρ := by
              simpa [MeasureTheory.IsProbabilityMeasure.measure_univ]

/-- Concentration of the difference law is at most concentration of `μ`. -/
lemma levyQ_diff_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) :
    levyQ (diffLaw μ) ρ ≤ levyQ μ ρ := by
  unfold levyQ
  rw [sSup_le_iff]
  rintro a ⟨l, rfl⟩
  exact diffLaw_window_le μ ρ l

/-- For probability measures, the concentration is at most one. -/
lemma levyQ_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) : levyQ μ ρ ≤ 1 := by
  unfold levyQ
  rw [sSup_le_iff]
  rintro a ⟨l, rfl⟩
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp)

/-- `levyQ` has finite `toReal`. -/
lemma levyQ_ne_top (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) : levyQ μ ρ ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (levyQ_le_one μ ρ) (by simp))


/-! ## Part IV: containment of the level set and mass of the far set -/

/-- `diffLaw` of a probability measure is a probability measure. -/
lemma isProbabilityMeasure_diffLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diffLaw μ) := by
  rw [diffLaw]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The `μ`-level set is contained in the squared level set of the difference law. -/
lemma levelSet_subset_sq (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ η : ℝ) :
    {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η ≤ ‖charFun μ t‖}
      ⊆ {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖} := by
  intro t ht
  rcases ht with ⟨htw, hη⟩
  constructor
  · exact htw
  · have hnorm : ‖charFun (diffLaw μ) t‖ = ‖charFun μ t‖ ^ 2 := norm_charFun_diff μ t
    rw [hnorm]
    by_cases hη1 : 1 ≤ η
    · have hsq0 : 0 ≤ ‖charFun μ t‖ ^ 2 := sq_nonneg ‖charFun μ t‖
      exact le_trans (by nlinarith) hsq0
    · have hsq : (1 - η) ^ 2 ≤ ‖charFun μ t‖ ^ 2 := by
        have hle : |1 - η| ≤ ‖charFun μ t‖ := by
          rw [abs_of_nonneg (by linarith : 0 ≤ 1 - η)]
          exact hη
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg (charFun μ t))] using hle)
      have hsq' : 1 - 2 * η ≤ (1 - η) ^ 2 := by nlinarith [sq_nonneg η]
      exact le_trans hsq' hsq

/-- The set `{y | |y| > ρ}` (the "far set"). -/
def farSet (ρ : ℝ) : Set ℝ := {y : ℝ | ρ < |y|}

/-- The far set is the complement of the closed `ρ`-ball. -/
lemma farSet_compl (ρ : ℝ) : (farSet ρ)ᶜ = {y : ℝ | |y| ≤ ρ} := by
  ext y
  simp [farSet]

/-- Mass of the far set under the difference law is at least `1 − Q_μ(ρ)`. -/
lemma far_mass_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ) :
    1 - (levyQ μ ρ).toReal ≤ (diffLaw μ).real (farSet ρ) := by
  haveI : IsProbabilityMeasure (diffLaw μ) := isProbabilityMeasure_diffLaw μ
  have hball : {y : ℝ | |y| ≤ ρ} = Set.Icc (-ρ) ρ := by
    ext y
    constructor
    · intro h
      change |y| ≤ ρ at h
      exact abs_le.mp h
    · intro h
      change -ρ ≤ y ∧ y ≤ ρ at h
      exact abs_le.mpr h
  have hIcc : (diffLaw μ).real (Set.Icc (-ρ) ρ) = (diffLaw μ).real {y : ℝ | |y| ≤ ρ} := by
    rw [hball]
  have hcomp : (diffLaw μ).real (farSet ρ) = 1 - (diffLaw μ).real {y : ℝ | |y| ≤ ρ} := by
    have hc : {y : ℝ | |y| ≤ ρ} = (farSet ρ)ᶜ := by
      rw [farSet_compl ρ]
    have hm : MeasurableSet {y : ℝ | |y| ≤ ρ} := by
      rw [hball]
      exact measurableSet_Icc
    calc
      (diffLaw μ).real (farSet ρ) = (diffLaw μ).real ((farSet ρ)ᶜᶜ) := by simp
      _ = 1 - (diffLaw μ).real ((farSet ρ)ᶜ) := probReal_compl_eq_one_sub (by
          -- MeasurableSet (farSet ρ)ᶜ : need measurable: farSet complement = ball measurable
          rw [farSet_compl ρ]
          exact hm)
      _ = 1 - (diffLaw μ).real {y : ℝ | |y| ≤ ρ} := by rw [farSet_compl ρ]
  have hle : (diffLaw μ).real (Set.Icc (-ρ) ρ) ≤ (levyQ μ ρ).toReal := by
    have h : diffLaw μ (Set.Icc (-ρ) ρ) ≤ levyQ μ ρ := by
      simpa using diffLaw_window_le μ ρ 0
    have htopν : diffLaw μ (Set.Icc (-ρ) ρ) ≠ ⊤ := measure_ne_top (diffLaw μ) _
    have htopQ : levyQ μ ρ ≠ ⊤ := levyQ_ne_top μ ρ
    exact (ENNReal.toReal_le_toReal htopν htopQ).mpr h
  calc
    1 - (levyQ μ ρ).toReal ≤ 1 - (diffLaw μ).real (Set.Icc (-ρ) ρ) := by linarith
    _ = 1 - (diffLaw μ).real {y : ℝ | |y| ≤ ρ} := by rw [hIcc]
    _ = (diffLaw μ).real (farSet ρ) := hcomp.symm



/-! ## Part V: energy bound and Markov estimate on the far set -/

/-- For `t` on the squared level set `{1 − 2η ≤ ‖charFun ν t‖}`, the "energy"
`E_ν[1 − cos(tY)]` is at most `2η`. -/
lemma energy_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (t η : ℝ) (hη : 0 ≤ η)
    (ht : 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖) :
    (∫ y : ℝ, 1 - Real.cos (t * y) ∂diffLaw μ) ≤ 2 * η := by
  haveI : IsProbabilityMeasure (diffLaw μ) := isProbabilityMeasure_diffLaw μ
  have hc1 : Integrable (fun y : ℝ => (1 : ℝ)) (diffLaw μ) := by
    exact integrable_const (1 : ℝ)
  have hcosfun : Integrable (fun y : ℝ => Real.cos (t * y)) (diffLaw μ) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    apply ae_of_all
    intro y
    exact Real.abs_cos_le_one (t * y)
  have hint : (∫ y : ℝ, 1 - Real.cos (t * y) ∂diffLaw μ)
      = 1 - (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) := by
    calc
      (∫ y : ℝ, 1 - Real.cos (t * y) ∂diffLaw μ)
          = (∫ y : ℝ, (1 : ℝ) - Real.cos (t * y) ∂diffLaw μ) := by rfl
      _ = (∫ y : ℝ, (1 : ℝ) ∂diffLaw μ) - (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) :=
            integral_sub hc1 hcosfun
      _ = 1 - (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) := by
            rw [integral_const (1 : ℝ)]
            simp [MeasureTheory.IsProbabilityMeasure.measure_univ]
  rw [hint]
  have hcos : (∫ y : ℝ, Real.cos (t * y) ∂diffLaw μ) = ‖charFun (diffLaw μ) t‖ := by
    have hc := integral_cos_diff μ t
    rw [← norm_charFun_diff μ t] at hc
    exact hc
  rw [hcos]
  linarith

/-- The far set `{|y| > ρ}` is measurable. -/
lemma farSet_measurable (ρ : ℝ) : MeasurableSet (farSet ρ) := by
  have hpre : farSet ρ = (fun y : ℝ => |y|) ⁻¹' Set.Ioi ρ := rfl
  rw [hpre]
  exact measurableSet_Ioi.preimage continuous_abs.measurable

/-! ## Part VI: measurability and elementary trig bounds -/

/-- `1 − cos x` is nonnegative. -/
lemma one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  have hcos : Real.cos x ≤ 1 := (abs_le.mp (Real.abs_cos_le_one x)).2
  linarith

/-- `|1 − cos x| ≤ 2`. -/
lemma abs_one_sub_cos_le_two (x : ℝ) : |1 - Real.cos x| ≤ 2 := by
  have hc := Real.abs_cos_le_one x
  have h1 : 1 - Real.cos x ≤ 2 := by linarith [(abs_le.mp hc).1]
  have h2 : -(2) ≤ 1 - Real.cos x := by linarith [(abs_le.mp hc).2]
  exact abs_le.mpr ⟨h2, h1⟩

/-- The far-resonance sublevel set `{y | 1 − cos (t·y) ≤ a}` is measurable. -/
lemma cos_sublevel_measurable (t a : ℝ) :
    MeasurableSet {y : ℝ | 1 - Real.cos (t * y) ≤ a} := by
  have hcont : Continuous (fun y : ℝ => 1 - Real.cos (t * y)) := by fun_prop
  have hset : {y : ℝ | 1 - Real.cos (t * y) ≤ a} =
      (fun y : ℝ => 1 - Real.cos (t * y)) ⁻¹' Set.Iic a := by
    ext y
    rfl
  rw [hset]
  exact (measurableSet_Iic : MeasurableSet (Set.Iic a)).preimage hcont.measurable

/-- The squared level set `{t | |t| ≤ 1/ρ ∧ 1 − 2η ≤ ‖charFun (diffLaw μ) t‖}` is measurable. -/
lemma sqLevelSet_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ η : ℝ) :
    MeasurableSet {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖} := by
  haveI : IsProbabilityMeasure (diffLaw μ) := isProbabilityMeasure_diffLaw μ
  have hcont2 : Continuous (fun t : ℝ => ‖charFun (diffLaw μ) t‖) := by fun_prop
  have hset : {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖} =
      ((fun t : ℝ => |t|) ⁻¹' Set.Iic (1 / ρ)) ∩
      ((fun t : ℝ => ‖charFun (diffLaw μ) t‖) ⁻¹' Set.Ici (1 - 2 * η)) := by
    ext t
    rfl
  rw [hset]
  exact (measurableSet_Iic.preimage continuous_abs.measurable).inter
    (measurableSet_Ici.preimage hcont2.measurable)

/-- Intersection of the far set with a sublevel set is measurable. -/
lemma farSet_inter_cos_sublevel_measurable (ρ t a : ℝ) :
    MeasurableSet (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) :=
  (farSet_measurable ρ).inter (cos_sublevel_measurable t a)

/-- The window `{|t| ≤ 1/ρ}` has finite Lebesgue measure. -/
lemma window_volume_finite (ρ : ℝ) : volume {t : ℝ | |t| ≤ 1 / ρ} ≠ ∞ := by
  have hset : {t : ℝ | |t| ≤ 1 / ρ} ⊆ Set.Icc (-(1 / ρ) - 1) ((1 / ρ) + 1) := by
    intro t ht
    change |t| ≤ 1 / ρ at ht
    rw [Set.mem_Icc]
    have habs := abs_le.mp ht
    constructor <;> nlinarith
  have hfin : volume (Set.Icc (-(1 / ρ) - 1) ((1 / ρ) + 1)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top.ne
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hset) (lt_top_iff_ne_top.mpr hfin))

/-- The window `{|t| ≤ 1/ρ}` is measurable. -/
lemma window_measurable (ρ : ℝ) : MeasurableSet {t : ℝ | |t| ≤ 1 / ρ} := by
  have hset : {t : ℝ | |t| ≤ 1 / ρ} = (fun t : ℝ => |t|) ⁻¹' Set.Iic (1 / ρ) := by
    ext t
    rfl
  rw [hset]
  exact (measurableSet_Iic : MeasurableSet (Set.Iic (1 / ρ))).preimage continuous_abs.measurable

/-! ## Part VII: Markov concentration on the far set -/

/-- On the squared level set, at least half of the far-set mass satisfies the energy
sublevel bound `1 − cos(t·y) ≤ 4η/p` (where `p` is the far-set mass): this is Markov's
inequality applied to the energy restricted to the far set. -/
lemma far_resonant_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ η t : ℝ)
    (hη : 0 < η) (hp : 0 < (diffLaw μ).real (farSet ρ))
    (ht : 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖) :
    (diffLaw μ).real (farSet ρ) / 2 ≤
      (diffLaw μ).real (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤
        4 * η / (diffLaw μ).real (farSet ρ)}) := by
  haveI : IsProbabilityMeasure (diffLaw μ) := isProbabilityMeasure_diffLaw μ
  let p : ℝ := (diffLaw μ).real (farSet ρ)
  let a : ℝ := 4 * η / p
  have hp0 : 0 < p := by simpa [p] using hp
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by positivity) hp0
  have ha0 : 0 ≤ a := le_of_lt ha
  have hη0 : 0 ≤ η := le_of_lt hη
  let f : ℝ → ℝ := (farSet ρ).indicator (fun y : ℝ => 1 - Real.cos (t * y))
  have hfval (y : ℝ) (hy : y ∈ farSet ρ) : f y = 1 - Real.cos (t * y) := by
    simp [f, hy]
  have hfval0 (y : ℝ) (hy : y ∉ farSet ρ) : f y = 0 := by
    simp [f, hy]
  have hf_nonneg : ∀ᵐ y ∂(diffLaw μ), 0 ≤ f y := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ farSet ρ
    · rw [hfval y hy]
      exact one_sub_cos_nonneg (t * y)
    · rw [hfval0 y hy]
  have hf_meas : Measurable f := by
    exact (by fun_prop : Measurable (fun y : ℝ => 1 - Real.cos (t * y))).indicator (farSet_measurable ρ)
  have hf_int : Integrable f (diffLaw μ) := by
    refine Integrable.of_bound (f := f) (μ := diffLaw μ) ?_ (2 : ℝ) ?_
    · exact hf_meas.aestronglyMeasurable
    · apply ae_of_all
      intro y
      by_cases hy : y ∈ farSet ρ
      · rw [hfval y hy]
        exact abs_one_sub_cos_le_two (t * y)
      · rw [hfval0 y hy]
        simp
  have hg_meas : Measurable (fun y : ℝ => 1 - Real.cos (t * y)) := by fun_prop
  have hg_int : Integrable (fun y : ℝ => 1 - Real.cos (t * y)) (diffLaw μ) := by
    refine Integrable.of_bound (f := fun y : ℝ => 1 - Real.cos (t * y)) (μ := diffLaw μ)
      ?_ (2 : ℝ) ?_
    · exact hg_meas.aestronglyMeasurable
    · apply ae_of_all
      intro y
      exact abs_one_sub_cos_le_two (t * y)
  have hE : (∫ y : ℝ, 1 - Real.cos (t * y) ∂diffLaw μ) ≤ 2 * η := energy_le μ t η hη0 ht
  have hf_le : (∫ y : ℝ, f y ∂diffLaw μ) ≤
      (∫ y : ℝ, 1 - Real.cos (t * y) ∂diffLaw μ) := by
    refine integral_mono hf_int hg_int ?_
    intro y
    by_cases hy : y ∈ farSet ρ
    · rw [hfval y hy]
    · rw [hfval0 y hy]
      exact one_sub_cos_nonneg (t * y)
  have hEf : (∫ y : ℝ, f y ∂diffLaw μ) ≤ 2 * η := le_trans hf_le hE
  have hmarkov := Commons.Measure.Markov.measureReal_markov (μ := diffLaw μ) (f := f) hf_nonneg hf_int a ha
  have hmarkov' : a * (diffLaw μ).real {x : ℝ | a ≤ f x} ≤ 2 * η := le_trans hmarkov hEf
  have hbadset : {x : ℝ | a ≤ f x} = farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)} := by
    ext y
    change a ≤ f y ↔ y ∈ farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}
    by_cases hy : y ∈ farSet ρ
    · rw [hfval y hy]
      simp [hy]
    · rw [hfval0 y hy]
      have ha_not : ¬ a ≤ 0 := by nlinarith
      simp [hy, ha_not]
  have hM : a * (diffLaw μ).real (farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}) ≤ 2 * η := by
    rwa [← hbadset]
  have hm_le : (diffLaw μ).real (farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}) ≤ 2 * η / a := by
    have hm : (diffLaw μ).real (farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}) * a ≤ 2 * η := by
      simpa [mul_comm] using hM
    exact (le_div_iff₀ ha).mpr hm
  have hdiv : (diffLaw μ).real (farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}) ≤ p / 2 := by
    calc
      (diffLaw μ).real (farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)}) ≤ 2 * η / a := hm_le
      _ = p / 2 := by
        dsimp [a]
        field_simp [hp0.ne', (ne_of_gt hη)]
        ring
  let bad : Set ℝ := farSet ρ ∩ {y : ℝ | a < 1 - Real.cos (t * y)}
  let good : Set ℝ := farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}
  have hbad_meas : MeasurableSet bad := by
    have hcont : Continuous (fun y : ℝ => 1 - Real.cos (t * y)) := by fun_prop
    have hset : bad = farSet ρ ∩ (fun y : ℝ => 1 - Real.cos (t * y)) ⁻¹' Set.Ioi a := by
      ext y
      rfl
    rw [hset]
    exact (farSet_measurable ρ).inter (measurableSet_Ioi.preimage hcont.measurable)
  have hbad_sub : bad ⊆ farSet ρ ∩ {y : ℝ | a ≤ 1 - Real.cos (t * y)} := by
    intro y hy
    change y ∈ farSet ρ ∧ a < 1 - Real.cos (t * y) at hy
    change y ∈ farSet ρ ∧ a ≤ 1 - Real.cos (t * y)
    exact ⟨hy.1, le_of_lt hy.2⟩
  have hbad_le : (diffLaw μ).real bad ≤ p / 2 := by
    exact le_trans (measureReal_mono hbad_sub) hdiv
  have hgood_sdiff : good = farSet ρ \ bad := by
    ext y
    simp [good, bad]
  have hsplit : (diffLaw μ).real (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) =
      p - (diffLaw μ).real bad := by
    dsimp [good] at hgood_sdiff
    rw [hgood_sdiff]
    have hsub2 : bad ⊆ farSet ρ := by
      intro y hy
      change y ∈ farSet ρ ∧ a < 1 - Real.cos (t * y) at hy
      exact hy.1
    simpa [p] using measureReal_sdiff (s₁ := farSet ρ) (s₂ := bad) hsub2 hbad_meas
  have hgoal : p / 2 ≤ (diffLaw μ).real (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) := by
    rw [hsplit]
    have hle' : (diffLaw μ).real bad ≤ p / 2 := hbad_le
    have hnonneg : 0 ≤ (diffLaw μ).real bad := by positivity
    nlinarith
  simpa [p, a] using hgoal



/-! ## Part VIII: the level-set measure bound via Fubini -/

/-- Core level-set bound for the *difference* law: on the squared level set
`{t | |t| ≤ 1/ρ ∧ 1 − 2η ≤ ‖charFun (diffLaw μ) t‖}`, the volume is bounded by
`4·C₀·√(η/(1 − Q_μ(ρ)))/ρ`, whenever the per-point arc estimate holds with constant `C₀`
and the concentration gap `1 − Q_μ(ρ)` is positive. -/
lemma level_bound_diffLaw (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (harc : ∀ (ρ y α : ℝ), 0 < ρ → ρ ≤ |y| → 0 ≤ α →
      (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ α}).toReal ≤ C₀ * Real.sqrt α / ρ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hδ : 0 < 1 - (levyQ μ ρ).toReal) :
    volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖} ≤
      (4 * C₀) * Real.sqrt (η / (1 - (levyQ μ ρ).toReal)) / ρ := by
  let S : Set ℝ := {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖}
  let p : ℝ := (diffLaw μ).real (farSet ρ)
  let δ : ℝ := 1 - (levyQ μ ρ).toReal
  let a : ℝ := 4 * η / p
  let J : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ∈ farSet ρ ∧ 1 - Real.cos (z.1 * z.2) ≤ a}
  haveI : IsProbabilityMeasure (diffLaw μ) := isProbabilityMeasure_diffLaw μ
  have hSmeas : MeasurableSet S := by simpa [S] using sqLevelSet_measurable μ ρ η
  have hδ0 : 0 < δ := by simpa [δ] using hδ
  have hδp : δ ≤ p := by simpa [δ, p] using far_mass_ge μ ρ
  have hp : 0 < p := lt_of_lt_of_le hδ0 hδp
  have hp0' : p ≠ 0 := ne_of_gt hp
  have hη0 : 0 ≤ η := le_of_lt hη
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by positivity) hp
  have ha0 : 0 ≤ a := le_of_lt ha
  have hSwin : S ⊆ {t : ℝ | |t| ≤ 1 / ρ} := by
    intro t ht
    change |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖ at ht
    exact ht.1
  have hSfin : volume S ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hSwin) (lt_top_iff_ne_top.mpr (window_volume_finite ρ)))
  have hJmeas : MeasurableSet J := by
    have h1 : MeasurableSet {z : ℝ × ℝ | z.2 ∈ farSet ρ} :=
      (farSet_measurable ρ).preimage measurable_snd
    have hcont : Continuous (fun z : ℝ × ℝ => 1 - Real.cos (z.1 * z.2)) := by fun_prop
    have h2 : MeasurableSet {z : ℝ × ℝ | 1 - Real.cos (z.1 * z.2) ≤ a} := by
      have hset : {z : ℝ × ℝ | 1 - Real.cos (z.1 * z.2) ≤ a} =
          (fun z : ℝ × ℝ => 1 - Real.cos (z.1 * z.2)) ⁻¹' Set.Iic a := by
        ext z
        rfl
      rw [hset]
      exact (measurableSet_Iic : MeasurableSet (Set.Iic a)).preimage hcont.measurable
    have hJeq : J = ({z : ℝ × ℝ | z.2 ∈ farSet ρ} ∩ {z : ℝ × ℝ | 1 - Real.cos (z.1 * z.2) ≤ a}) := by
      ext z
      rfl
    rw [hJeq]
    exact h1.inter h2
  have hfiber_t (t : ℝ) : Prod.mk t ⁻¹' J =
      farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a} := by
    ext y
    rfl
  have hfiber_y (y : ℝ) : (fun x : ℝ => (x, y)) ⁻¹' J =
      {t : ℝ | y ∈ farSet ρ ∧ 1 - Real.cos (t * y) ≤ a} := by
    ext t
    rfl
  -- per-point lower bound (Markov): for t on the level set
  have hper_t (t : ℝ) (htS : t ∈ S) :
      ENNReal.ofReal (p / 2) ≤ (diffLaw μ) (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) := by
    have htcond : 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖ := by
      change |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖ at htS
      exact htS.2
    have hfr := far_resonant_lower μ ρ η t hη hp htcond
    have hfr' : p / 2 ≤ (diffLaw μ).real (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) := by
      simpa [p, a] using hfr
    have hfin : (diffLaw μ) (farSet ρ ∩ {y : ℝ | 1 - Real.cos (t * y) ≤ a}) ≠ ∞ :=
      measure_ne_top (diffLaw μ) _
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mpr hfr'
  have hae_lower : ∀ᵐ t ∂(volume.restrict S),
      ENNReal.ofReal (p / 2) ≤ (diffLaw μ) (Prod.mk t ⁻¹' J) := by
    rw [ae_restrict_iff' hSmeas]
    apply ae_of_all
    intro t htS
    rw [hfiber_t t]
    exact hper_t t htS
  -- per-point upper bound (arc measure): for y in the far set
  have hper_y (y : ℝ) (hy : y ∈ farSet ρ) :
      (volume.restrict S) ((fun x : ℝ => (x, y)) ⁻¹' J) ≤
        ENNReal.ofReal (C₀ * Real.sqrt a / ρ) := by
    have hyfar : ρ < |y| := by simpa [farSet] using hy
    have hto : (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a}).toReal ≤
        C₀ * Real.sqrt a / ρ := by
      exact harc ρ y a hρ (le_of_lt hyfar) ha0
    have harc0 : 0 ≤ C₀ * Real.sqrt a / ρ := by positivity
    have hxfin : volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a} ≠ ∞ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.mpr (window_volume_finite ρ)))
      intro t ht
      change |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a at ht
      exact ht.1
    have harcEN : volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a} ≤
        ENNReal.ofReal (C₀ * Real.sqrt a / ρ) := by
      exact (ENNReal.toReal_le_toReal hxfin ENNReal.ofReal_lt_top.ne).1
        (by simpa [ENNReal.toReal_ofReal harc0] using hto)
    have hsub : ((fun x : ℝ => (x, y)) ⁻¹' J) ∩ S ⊆
        {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a} := by
      intro t ht
      rcases ht with ⟨htJmem, htS⟩
      have htJ : (t, y) ∈ J := by simpa using htJmem
      have htS' : |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖ := by
        change |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖ at htS
        exact htS
      exact ⟨htS'.1, by simpa using htJ.2⟩
    calc
      (volume.restrict S) ((fun x : ℝ => (x, y)) ⁻¹' J)
          = volume (((fun x : ℝ => (x, y)) ⁻¹' J) ∩ S) := by
              exact Measure.restrict_apply (hJmeas.preimage (by fun_prop : Measurable (fun x : ℝ => (x, y))))
      _ ≤ volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ a} := measure_mono hsub
      _ ≤ ENNReal.ofReal (C₀ * Real.sqrt a / ρ) := harcEN
  -- upper estimate, integrating over y (Fubini / Tonelli)
  have hUpper : ((volume.restrict S).prod (diffLaw μ)) J ≤
      ENNReal.ofReal (C₀ * Real.sqrt a / ρ) * (diffLaw μ) (farSet ρ) := by
    have hpoint (y : ℝ) : (volume.restrict S) ((fun x : ℝ => (x, y)) ⁻¹' J) ≤
        (farSet ρ).indicator (fun _ : ℝ => ENNReal.ofReal (C₀ * Real.sqrt a / ρ)) y := by
      by_cases hy : y ∈ farSet ρ
      · simp [hy, hper_y y hy]
      · have hfiber_empty : (fun x : ℝ => (x, y)) ⁻¹' J = ∅ := by
          ext t
          simp [J, hy]
        rw [hfiber_empty]
        simp [hy]
    calc
      ((volume.restrict S).prod (diffLaw μ)) J
          = ∫⁻ y : ℝ, (volume.restrict S) ((fun x : ℝ => (x, y)) ⁻¹' J) ∂(diffLaw μ) := by
              exact Measure.prod_apply_symm hJmeas
      _ ≤ ∫⁻ y : ℝ, (farSet ρ).indicator (fun _ : ℝ => ENNReal.ofReal (C₀ * Real.sqrt a / ρ)) y ∂(diffLaw μ) := by
              exact lintegral_mono hpoint
      _ = ENNReal.ofReal (C₀ * Real.sqrt a / ρ) * (diffLaw μ) (farSet ρ) := by
              rw [MeasureTheory.lintegral_indicator (farSet_measurable ρ)]
              simp [MeasureTheory.lintegral_const]
  -- lower estimate, integrating over t
  have hLower : ENNReal.ofReal (p / 2) * volume S ≤
      ((volume.restrict S).prod (diffLaw μ)) J := by
    have hL : ((volume.restrict S).prod (diffLaw μ)) J =
        ∫⁻ t : ℝ, (diffLaw μ) (Prod.mk t ⁻¹' J) ∂(volume.restrict S) := by
      exact Measure.prod_apply hJmeas
    calc
      ENNReal.ofReal (p / 2) * volume S
          = ENNReal.ofReal (p / 2) * (volume.restrict S) Set.univ := by
              rw [Measure.restrict_apply_univ]
      _ = ∫⁻ t : ℝ, ENNReal.ofReal (p / 2) ∂(volume.restrict S) := by
              rw [MeasureTheory.lintegral_const]
      _ ≤ ∫⁻ t : ℝ, (diffLaw μ) (Prod.mk t ⁻¹' J) ∂(volume.restrict S) := lintegral_mono_ae hae_lower
      _ = ((volume.restrict S).prod (diffLaw μ)) J := hL.symm
  -- combine (all extended reals) and extract reals
  have hChain : ENNReal.ofReal (p / 2) * volume S ≤
      ENNReal.ofReal (C₀ * Real.sqrt a / ρ) * (diffLaw μ) (farSet ρ) := le_trans hLower hUpper
  have harc0 : 0 ≤ C₀ * Real.sqrt a / ρ := by positivity
  have htop1 : ENNReal.ofReal (p / 2) * volume S ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
  have htop2 : ENNReal.ofReal (C₀ * Real.sqrt a / ρ) * (diffLaw μ) (farSet ρ) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (diffLaw μ) (farSet ρ))
  have hto : (ENNReal.ofReal (p / 2) * volume S).toReal ≤
      (ENNReal.ofReal (C₀ * Real.sqrt a / ρ) * (diffLaw μ) (farSet ρ)).toReal :=
    (ENNReal.toReal_le_toReal htop1 htop2).2 hChain
  have hChainReal : (p / 2) * (volume S).toReal ≤ (C₀ * Real.sqrt a / ρ) * p := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ p / 2)] at hto
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal harc0] at hto
    simpa [p, measureReal_def] using hto
  -- algebra: from (p/2)·x ≤ arc·p with p > 0
  have hstep1 : (volume S).toReal ≤ 2 * (C₀ * Real.sqrt a / ρ) := by
    have hle2 : (volume S).toReal ≤ (C₀ * Real.sqrt a / ρ) * p / (p / 2) := by
      exact (le_div_iff₀ (by positivity : 0 < p / 2)).mpr
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hChainReal)
    have hcalc : (C₀ * Real.sqrt a / ρ) * p / (p / 2) = 2 * (C₀ * Real.sqrt a / ρ) := by
      field_simp [hp0']
    exact hle2.trans_eq hcalc
  -- √a = 2√(η/p)
  have hsqrt_a : Real.sqrt a = 2 * Real.sqrt (η / p) := by
    dsimp [a]
    calc
      Real.sqrt (4 * η / p) = Real.sqrt (4 * (η / p)) := by ring_nf
      _ = Real.sqrt 4 * Real.sqrt (η / p) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (η / p)]
      _ = 2 * Real.sqrt (η / p) := by norm_num
  have hsple : Real.sqrt (η / p) ≤ Real.sqrt (η / δ) := by
    have hdivle : η / p ≤ η / δ := by
      rw [div_le_div_iff₀ hp (by simpa [δ] using hδ0)]
      nlinarith
    exact Real.sqrt_le_sqrt hdivle
  have hvol : (volume S).toReal ≤ (4 * C₀) * Real.sqrt (η / δ) / ρ := by
    calc
      (volume S).toReal ≤ 2 * (C₀ * Real.sqrt a / ρ) := hstep1
      _ = (4 * C₀) * Real.sqrt (η / p) / ρ := by
            rw [hsqrt_a]
            field_simp
            ring
      _ ≤ (4 * C₀) * Real.sqrt (η / δ) / ρ := by
            have hC₀4 : 0 ≤ 4 * C₀ := by nlinarith
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsple hC₀4) (le_of_lt hρ)
  simpa [S, δ, measureReal_def] using hvol

/-! ## Part IX: the single-variable Esséen level-set bound -/

/-- Any subwindow of the dual window has finite Lebesgue measure. -/
lemma window_inter_volume_finite (ρ : ℝ) (P : ℝ → Prop) :
    volume {t : ℝ | |t| ≤ 1 / ρ ∧ P t} ≠ ∞ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.mpr (window_volume_finite ρ)))
  intro t ht
  change |t| ≤ 1 / ρ ∧ P t at ht
  exact ht.1

/-- Level-set bound for `μ` itself, `η > 0`: the volume of
`{t | |t| ≤ 1/ρ ∧ 1 − η ≤ ‖charFun μ t‖}` is at most `4·C₀·√(η/(1 − Q_μ(ρ)))/ρ`. -/
lemma level_bound_mu (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (harc : ∀ (ρ y α : ℝ), 0 < ρ → ρ ≤ |y| → 0 ≤ α →
      (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ α}).toReal ≤ C₀ * Real.sqrt α / ρ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η)
    (hδ : 0 < 1 - (levyQ μ ρ).toReal) :
    volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η ≤ ‖charFun μ t‖} ≤
      (4 * C₀) * Real.sqrt (η / (1 - (levyQ μ ρ).toReal)) / ρ := by
  have hbd := level_bound_diffLaw C₀ hC₀ harc μ ρ η hρ hη hδ
  have hsub := levelSet_subset_sq μ ρ η
  have hfin : volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖} ≠ ∞ := by
    exact window_inter_volume_finite ρ (fun t => 1 - 2 * η ≤ ‖charFun (diffLaw μ) t‖)
  exact le_trans (measureReal_mono hsub hfin) hbd

/-- **Esséen level-set bound** (Tikhomirov 2020, estimate (essen)): for a probability measure
`μ` on `ℝ` and `ρ > 0`, if `1 − Q_μ(ρ) > 0` where `Q_μ(ρ)` is the supremum of the mass of
closed windows of half-width `ρ`, then for every `η ≥ 0` the Lebesgue measure of
`{t : |t| ≤ 1/ρ ∧ 1 − η ≤ |charFun μ t|}` is at most `C·√(η/(1 − Q_μ(ρ)))/ρ`. -/
lemma essen_level_set_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (ρ : ℝ), 0 < ρ →
        (0 < 1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}).toReal) →
        ∀ (η : ℝ), 0 ≤ η →
          (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η ≤ ‖charFun μ t‖}).toReal ≤
            C * Real.sqrt (η / (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - ρ) (l + ρ))}).toReal)) / ρ := by
  rcases Commons.Measure.Resonance.arc_measure with ⟨Carc, hCarc_pos, harc⟩
  have hCarc0 : 0 ≤ Carc := le_of_lt hCarc_pos
  refine ⟨4 * Carc, by positivity, ?_⟩
  intro μ _hμ ρ hρ hδ η hη0
  have hδL : 0 < 1 - (levyQ μ ρ).toReal := by
    simpa [levyQ] using hδ
  by_cases hηpos : 0 < η
  · -- case η > 0
    have hbd := level_bound_mu Carc hCarc0 harc μ ρ η hρ hηpos hδL
    simpa [levyQ, measureReal_def] using hbd
  · -- case η = 0
    have hηeq : η = 0 := le_antisymm (le_of_not_gt hηpos) hη0
    let L0 : Set ℝ := {t : ℝ | |t| ≤ 1 / ρ ∧ 1 ≤ ‖charFun μ t‖}
    have hL0 : (volume L0).toReal = 0 := by
      apply le_antisymm
      · refine le_of_forall_pos_le_add (fun ε hε => ?_)
        let η' : ℝ := (ε * ρ / (8 * Carc)) ^ 2 * (1 - (levyQ μ ρ).toReal)
        have hη'pos : 0 < η' := by
          dsimp [η']
          positivity
        have hη'0 : 0 ≤ η' := le_of_lt hη'pos
        have hbd' := level_bound_mu Carc hCarc0 harc μ ρ η' hρ hη'pos hδL
        have hsub0 : L0 ⊆ {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η' ≤ ‖charFun μ t‖} := by
          intro t ht
          change |t| ≤ 1 / ρ ∧ 1 ≤ ‖charFun μ t‖ at ht
          change |t| ≤ 1 / ρ ∧ 1 - η' ≤ ‖charFun μ t‖
          exact ⟨ht.1, by linarith⟩
        have hfin' : volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η' ≤ ‖charFun μ t‖} ≠ ∞ := by
          exact window_inter_volume_finite ρ (fun t => 1 - η' ≤ ‖charFun μ t‖)
        have hmono' : (volume L0).toReal ≤
            volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η' ≤ ‖charFun μ t‖} := by
          simpa [measureReal_def] using measureReal_mono hsub0 hfin'
        have hδnz : (1 - (levyQ μ ρ).toReal) ≠ 0 := ne_of_gt hδL
        have hsqrt : Real.sqrt (η' / (1 - (levyQ μ ρ).toReal)) = ε * ρ / (8 * Carc) := by
          dsimp [η']
          calc
            Real.sqrt (((ε * ρ / (8 * Carc)) ^ 2 * (1 - (levyQ μ ρ).toReal)) /
                (1 - (levyQ μ ρ).toReal))
                = Real.sqrt ((ε * ρ / (8 * Carc)) ^ 2) := by
                    congr 1
                    field_simp [hδnz]
            _ = ε * ρ / (8 * Carc) := by
                    rw [Real.sqrt_sq_eq_abs]
                    rw [abs_of_pos]
                    positivity
        calc
          (volume L0).toReal
              ≤ volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - η' ≤ ‖charFun μ t‖} := hmono'
          _ ≤ (4 * Carc) * Real.sqrt (η' / (1 - (levyQ μ ρ).toReal)) / ρ := hbd'
          _ ≤ 0 + ε := by
                rw [hsqrt]
                have hCp : Carc ≠ 0 := ne_of_gt hCarc_pos
                have hρp : ρ ≠ 0 := ne_of_gt hρ
                field_simp [hCp, hρp]
                nlinarith
      · exact ENNReal.toReal_nonneg
    rw [hηeq]
    -- LHS set: {t | |t| ≤ 1/ρ ∧ 1 - 0 ≤ ‖charFun μ t‖} = L0
    have hset : {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - 0 ≤ ‖charFun μ t‖} = L0 := by
      ext t
      simp [L0]
    rw [hset, hL0]
    simp

end Commons.Probability.Levy
