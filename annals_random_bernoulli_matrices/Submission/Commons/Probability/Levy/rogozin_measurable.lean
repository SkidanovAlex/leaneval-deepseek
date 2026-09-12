import Mathlib
import Submission.Commons.Probability.Levy.rogozin_variable_radii

/-!
# Variable-radius Lévy–Kolmogorov–Rogozin inequality (measurable version)

`Commons.Probability.Levy.rogozin_measurable`: Tikhomirov 2020, Lemma l:lkr (Rogozin 1961;
Kesten 1969).  For mutually independent measurable real random variables on a probability
space and radii `r > 0`, `ρ i ∈ (0, r]` with
`D := Σ_i (1 − cf(ξ i, ρ i))·(ρ i)² > 0`, where
`cf(ξ, t) := sSup {a : ℝ≥0∞ | ∃ l, a = P{|ξ − l| ≤ t}}`,
we have `cf(Σξ i, r) ≤ C·r/√D` for a universal constant `C > 0`.

The development below defines `concentrationFunction` (definitionally equal to the inline
`sSup` expressions of the statement) and proves its elementary calculus: interval masses are
below the sup, monotonicity in the radius, the bound by 1 on probability spaces, invariance
under translations, sign change and scaling, values for constants, and the measurability
facts for the preimage sets.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Commons.Probability.Levy

noncomputable section

namespace RogozinMeasurable



/-- Lévy concentration function (closed intervals), inline-sup form. -/
def CF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |ξ x - l| ≤ t}}

-- every interval mass below the sup
lemma le_CF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ) (t l : ℝ) :
    P {x : Ω | |ξ x - l| ≤ t} ≤ CF P ξ t := by
  unfold CF
  exact le_sSup ⟨l, rfl⟩

-- CF is monotone in t
lemma CF_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ)
    {t1 t2 : ℝ} (h : t1 ≤ t2) : CF P ξ t1 ≤ CF P ξ t2 := by
  unfold CF
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  have hsub : {x | |ξ x - l| ≤ t1} ⊆ {x | |ξ x - l| ≤ t2} := by
    intro x hx
    exact le_trans hx h
  exact le_trans (measure_mono hsub) (le_CF P ξ t2 l)

-- CF bounded by 1 for probability measure
lemma CF_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (t : ℝ) : CF P ξ t ≤ 1 := by
  unfold CF
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp)

-- shift invariance: cf(ξ + c, t) = cf(ξ, t)
lemma CF_add_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → ℝ) (t c : ℝ) : CF P (fun x => ξ x + c) t = CF P ξ t := by
  unfold CF
  apply le_antisymm
  · rw [sSup_le_iff]
    rintro b ⟨l, rfl⟩
    have hrewrite : {x : Ω | |ξ x + c - l| ≤ t} = {x : Ω | |ξ x - (l - c)| ≤ t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have hnum : |ξ x + c - l| = |ξ x - (l - c)| := by
        congr 1
        ring
      rw [hnum]
    rw [hrewrite]
    exact le_sSup ⟨l - c, rfl⟩
  · rw [sSup_le_iff]
    rintro b ⟨l, rfl⟩
    have hrewrite : {x : Ω | |ξ x - l| ≤ t} = {x : Ω | |ξ x + c - (l + c)| ≤ t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have hnum : |ξ x - l| = |ξ x + c - (l + c)| := by
        congr 1
        ring
      rw [hnum]
    rw [hrewrite]
    exact le_sSup ⟨l + c, rfl⟩

-- CF of a constant: 1 for t >= 0
lemma CF_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) : CF P (fun _ : Ω => c) t = 1 := by
  unfold CF
  apply le_antisymm
  · refine sSup_le ?_
    rintro b ⟨l, rfl⟩
    exact le_trans (measure_mono (Set.subset_univ _)) (by simp)
  · have hset : {x : Ω | |c - c| ≤ t} = Set.univ := by
      ext x
      simp [ht]
    have hmem : (1 : ℝ≥0∞) ∈ {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |c - l| ≤ t}} := by
      refine ⟨c, ?_⟩
      rw [hset]
      simp
    exact le_sSup hmem

/-- The interval `{y : ℝ | |y - l| ≤ t}` is measurable (it is a closed interval). -/
lemma measurableSet_abs_le (l t : ℝ) : MeasurableSet {y : ℝ | |y - l| ≤ t} := by
  have hset : {y : ℝ | |y - l| ≤ t} = Set.Icc (l - t) (l + t) := by
    ext y
    change |y - l| ≤ t ↔ y ∈ Set.Icc (l - t) (l + t)
    rw [Set.mem_Icc, abs_le]
    constructor
    · intro h
      constructor <;> nlinarith
    · intro h
      constructor <;> nlinarith
  rw [hset]
  exact measurableSet_Icc

/-- Preimage of a closed interval under a measurable function is measurable. -/
lemma measurableSet_abs_le_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (l t : ℝ) :
    MeasurableSet {x : Ω | |ξ x - l| ≤ t} := by
  have hset : {x : Ω | |ξ x - l| ≤ t} = ξ ⁻¹' {y : ℝ | |y - l| ≤ t} := by
    ext x
    simp
  rw [hset]
  exact hξ (measurableSet_abs_le l t)



/-- `|-z - l| = |z - (-l)|`. -/
lemma abs_neg_sub_eq (z l : ℝ) : |-z - l| = |z - (-l)| := by
  rw [show -z - l = -(z + l) by ring, abs_neg, show z + l = z - (-l) by ring]

/-- `|z - l| = |-z - (-l)|`. -/
lemma abs_sub_neg_sub_eq (z l : ℝ) : |z - l| = |-z - (-l)| := by
  rw [abs_sub_comm]
  congr 1
  ring

-- negation invariance: cf(-ξ, t) = cf(ξ, t)
lemma CF_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ) (t : ℝ) :
    CF P (fun x => -ξ x) t = CF P ξ t := by
  unfold CF
  apply le_antisymm
  · rw [sSup_le_iff]
    rintro b ⟨l, rfl⟩
    have hrewrite : {x : Ω | |-ξ x - l| ≤ t} = {x : Ω | |ξ x - (-l)| ≤ t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have hnum : |-ξ x - l| = |ξ x - (-l)| := abs_neg_sub_eq (ξ x) l
      rw [hnum]
    rw [hrewrite]
    exact le_sSup ⟨-l, rfl⟩
  · rw [sSup_le_iff]
    rintro b ⟨l, rfl⟩
    have hrewrite : {x : Ω | |ξ x - l| ≤ t} = {x : Ω | |-ξ x - (-l)| ≤ t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have hnum : |ξ x - l| = |-ξ x - (-l)| := abs_sub_neg_sub_eq (ξ x) l
      rw [hnum]
    rw [hrewrite]
    exact le_sSup ⟨-l, rfl⟩


/-- For 0 < a, |a·b − l| ≤ a·t iff |b − l/a| ≤ t. -/
lemma abs_mul_sub_le_iff_div {a b l t : ℝ} (ha : 0 < a) :
    |a * b - l| ≤ a * t ↔ |b - l / a| ≤ t := by
  have hmul : |a * b - l| = a * |b - l / a| := by
    rw [show a * b - l = a * (b - l / a) by
          rw [mul_sub]
          congr 1
          rw [mul_div_cancel₀]
          exact ha.ne']
    rw [abs_mul, abs_of_pos ha]
  rw [hmul]
  exact mul_le_mul_iff_of_pos_left ha

/-- Scaling invariance: cf(a·ξ, a·t) = cf(ξ, t) for a > 0. -/
lemma CF_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → ℝ) {a t : ℝ} (ha : 0 < a) :
    CF P (fun ω => a * ξ ω) (a * t) = CF P ξ t := by
  classical
  unfold CF
  apply le_antisymm
  · rw [sSup_le_iff]
    intro b hb
    rcases hb with ⟨l, rfl⟩
    have hset : {x : Ω | |a * ξ x - l| ≤ a * t} = {x : Ω | |ξ x - l / a| ≤ t} := by
      ext x
      exact abs_mul_sub_le_iff_div (a := a) (b := ξ x) (l := l) (t := t) ha
    rw [hset]
    exact le_sSup ⟨l / a, rfl⟩
  · rw [sSup_le_iff]
    intro b hb
    rcases hb with ⟨l, rfl⟩
    have hset : {x : Ω | |ξ x - l| ≤ t} = {x : Ω | |a * ξ x - a * l| ≤ a * t} := by
      ext x
      change |ξ x - l| ≤ t ↔ |a * ξ x - a * l| ≤ a * t
      rw [abs_mul_sub_le_iff_div (a := a) (b := ξ x) (l := a * l) (t := t) ha]
      rw [show (a * l) / a = l by field_simp [ha.ne']]
    rw [hset]
    exact le_sSup ⟨a * l, rfl⟩

/-- toReal of CF is nonneg. -/
lemma CF_toReal_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : Ω → ℝ) (t : ℝ) : 0 ≤ (CF P ξ t).toReal := by
  exact ENNReal.toReal_nonneg

/-- For a probability measure, CF ≤ 1 and CF ≠ ⊤. -/
lemma CF_ne_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (t : ℝ) : CF P ξ t ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (CF_le_one P ξ t) (by simp))

/-- toReal of CF ≤ 1 for a probability measure. -/
lemma CF_toReal_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → ℝ) (t : ℝ) : (CF P ξ t).toReal ≤ 1 := by
  have h := CF_le_one P ξ t
  -- ENNReal.toReal_le_toReal
  have htop : CF P ξ t ≠ ⊤ := CF_ne_top P ξ t
  have h1top : (1 : ℝ≥0∞) ≠ ⊤ := by simp
  have h' := (ENNReal.toReal_le_toReal htop h1top).mpr h
  simpa using h' 

/-- `1 - (CF ...).toReal ≥ 0`. -/
lemma one_sub_CF_toReal_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Ω → ℝ) (t : ℝ) : 0 ≤ 1 - (CF P ξ t).toReal := by
  exact sub_nonneg.mpr (CF_toReal_le_one P ξ t)


/-- Concentration function of a probability measure on the line: sup over closed intervals
of half-width `t` of the mass.  -/
def Q (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - t) (l + t))}

/-- `P {x | |ξ x - l| ≤ t} = (P.map ξ) (Icc (l-t) (l+t))` for measurable `ξ`. -/
lemma map_apply_Icc_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (l t : ℝ) :
    P {x : Ω | |ξ x - l| ≤ t} = (P.map ξ) (Set.Icc (l - t) (l + t)) := by
  have hset : {x : Ω | |ξ x - l| ≤ t} = ξ ⁻¹' {y : ℝ | |y - l| ≤ t} := by
    ext x
    simp
  rw [hset]
  have hicc : {y : ℝ | |y - l| ≤ t} = Set.Icc (l - t) (l + t) := by
    ext y
    change |y - l| ≤ t ↔ y ∈ Set.Icc (l - t) (l + t)
    rw [Set.mem_Icc, abs_le]
    constructor
    · intro h; constructor <;> nlinarith
    · intro h; constructor <;> nlinarith
  rw [hicc]
  exact (Measure.map_apply hξ (measurableSet_Icc : MeasurableSet (Set.Icc (l - t) (l + t)))).symm

/-- The Ω-level concentration function of a measurable variable equals the concentration
function of its pushforward law. -/
lemma CF_eq_Q_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (t : ℝ) :
    CF P ξ t = Q (P.map ξ) t := by
  unfold CF Q
  apply le_antisymm
  · rw [sSup_le_iff]
    rintro a ha
    rcases ha with ⟨l, rfl⟩
    have hmem : P {x : Ω | |ξ x - l| ≤ t} ∈
        {a : ℝ≥0∞ | ∃ l' : ℝ, a = (P.map ξ) (Set.Icc (l' - t) (l' + t))} := by
      refine ⟨l, ?_⟩
      exact map_apply_Icc_abs P hξ l t
    exact le_sSup hmem
  · rw [sSup_le_iff]
    rintro a ha
    rcases ha with ⟨l, rfl⟩
    have hmem : (P.map ξ) (Set.Icc (l - t) (l + t)) ∈
        {a : ℝ≥0∞ | ∃ l' : ℝ, a = P {x : Ω | |ξ x - l'| ≤ t}} := by
      refine ⟨l, ?_⟩
      exact (map_apply_Icc_abs P hξ l t).symm
    exact le_sSup hmem

/-- `Q` is monotone in the radius. -/
lemma Q_mono (μ : Measure ℝ) {t1 t2 : ℝ} (h : t1 ≤ t2) : Q μ t1 ≤ Q μ t2 := by
  unfold Q
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  have hsub : Set.Icc (l - t1) (l + t1) ⊆ Set.Icc (l - t2) (l + t2) := by
    intro y hy
    rw [Set.mem_Icc] at hy
    rw [Set.mem_Icc]
    constructor <;> linarith
  refine le_trans (measure_mono hsub) ?_
  exact le_sSup ⟨l, rfl⟩

/-- `Q` is bounded by 1 on probability measures. -/
lemma Q_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : Q μ t ≤ 1 := by
  unfold Q
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp)

lemma sum_charFun_eq_prod {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Fin m → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P) :
    charFun (P.map (fun ω => ∑ i : Fin m, ξ i ω)) =
      fun t : ℝ => ∏ i : Fin m, charFun (P.map (ξ i)) t := by
  funext t
  have hprod := ProbabilityTheory.iIndepFun.charFun_map_fun_sum_eq_prod (E := ℝ)
    (fun i => (hξ i).aemeasurable) hind
  -- hprod : charFun (P.map (fun ω => ∑ i, ξ i ω)) = ∏ i, charFun (P.map (ξ i))
  simpa using congrFun hprod t

/-- norm of product of complex numbers = product of norms. -/
lemma norm_prod_charFun_le {m : ℕ} {μ : Fin m → Measure ℝ} (t : ℝ) :
    ‖∏ i, charFun (μ i) t‖ = ∏ i, ‖charFun (μ i) t‖ := by
  rw [Complex.norm_prod]




/-- Sum of measurable functions is measurable. -/
lemma measurable_finset_sum {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] [Fintype ι]
    {f : ι → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => ∑ i : ι, f i x) := by
  classical
  have hind : ∀ s : Finset ι, Measurable (fun x => ∑ i ∈ s, f i x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a t hat ht
      have hsplit : (fun x : Ω => ∑ i ∈ insert a t, f i x) =
          fun x : Ω => f a x + ∑ i ∈ t, f i x := by
        funext x
        exact Finset.sum_insert hat
      rw [hsplit]
      exact (hf a).add ht
  simpa using hind Finset.univ


end RogozinMeasurable

end

theorem rogozin_measurable :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (ξ : Fin m → Ω → ℝ),
        ProbabilityTheory.iIndepFun ξ P → (∀ i : Fin m, Measurable (ξ i)) →
        ∀ (r : ℝ), 0 < r → ∀ (ρ : Fin m → ℝ),
        (∀ i : Fin m, 0 < ρ i) → (∀ i : Fin m, ρ i ≤ r) →
        (0 < ∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |ξ i x - l| ≤ ρ i}}).toReal) * (ρ i) ^ 2) →
        sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |(∑ i : Fin m, ξ i x) - l| ≤ r}} ≤
          ENNReal.ofReal (C * r / Real.sqrt (∑ i : Fin m,
            (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |ξ i x - l| ≤ ρ i}}).toReal) * (ρ i) ^ 2)) := by
  rcases rogozin_variable_radii with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro m Ω _ms P _prob ξ hξ_indep hξ_meas r hr ρ hρpos hρle hD
  classical
  let μ : Fin m → Measure ℝ := fun i => Measure.map (ξ i) P
  let ν : Measure ℝ := Measure.map (fun ω : Ω => ∑ i : Fin m, ξ i ω) P
  have hξsum_meas : Measurable (fun ω : Ω => ∑ i : Fin m, ξ i ω) := RogozinMeasurable.measurable_finset_sum hξ_meas
  haveI : ∀ i : Fin m, MeasureTheory.IsProbabilityMeasure (μ i) := by
    intro i
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map (hξ_meas i).aemeasurable
  haveI : MeasureTheory.IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hξsum_meas.aemeasurable
  have hLHS_eq :
      (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |(∑ i : Fin m, ξ i x) - l| ≤ r}}) =
        sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = ν (Set.Icc (l - r) (l + r))} := by
    have hCF := RogozinMeasurable.CF_eq_Q_map P hξsum_meas r
    simpa [RogozinMeasurable.CF, RogozinMeasurable.Q, ν] using hCF
  have hsup_i : ∀ i : Fin m,
      (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |ξ i x - l| ≤ ρ i}}) =
        sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - ρ i) (l + ρ i))} := by
    intro i
    simpa [RogozinMeasurable.CF, RogozinMeasurable.Q, μ] using RogozinMeasurable.CF_eq_Q_map P (hξ_meas i) (ρ i)
  have hDsum :
      (∑ i : Fin m, (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x : Ω | |ξ i x - l| ≤ ρ i}}).toReal) * (ρ i) ^ 2) =
        (∑ i : Fin m, (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsup_i]
  have hDμ : 0 < ∑ i : Fin m,
      (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2 := by
    rw [← hDsum]
    exact hD
  have hchar : ∀ t : ℝ, ‖charFun ν t‖ ≤ ∏ i : Fin m, ‖charFun (μ i) t‖ := by
    intro t
    have hE : charFun ν t = ∏ i : Fin m, charFun (μ i) t := by
      dsimp [ν, μ]
      simpa using congrFun (RogozinMeasurable.sum_charFun_eq_prod P ξ hξ_meas hξ_indep) t
    rw [hE]
    exact le_of_eq (RogozinMeasurable.norm_prod_charFun_le t)
  rw [hLHS_eq, hDsum]
  exact hmain m μ ν r hr ρ hρpos hρle hchar hDμ

end Commons.Probability.Levy