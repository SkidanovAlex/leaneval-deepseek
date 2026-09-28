import Mathlib
import Submission.Work.HP.MMDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace Work.HP

/-! ## The fibre radius

For `s = ‖c‖` and `rv = ‖v‖ ≥ 0`, the largest possible `‖a‖` with `a` in the fibre over `v`
(where `v ⊥ c`) of the cone--band region `{t : ‖t‖ ≤ 1 ∧ |⟪c,t⟫| ≤ ‖t‖}`. -/

/-- The radius of the one-dimensional fibre. -/
def fiberA (s rv : ℝ) : ℝ :=
  if 1 < s ^ 2 then min (Real.sqrt (1 - rv ^ 2)) (rv / Real.sqrt (s ^ 2 - 1))
  else Real.sqrt (1 - rv ^ 2)

lemma fiberA_nonneg (s rv : ℝ) (hrv : 0 ≤ rv) : 0 ≤ fiberA s rv := by
  unfold fiberA
  split_ifs with h
  · exact le_min (Real.sqrt_nonneg _) (div_nonneg hrv (Real.sqrt_nonneg _))
  · exact Real.sqrt_nonneg _

lemma fiberA_eq_zero_of_one_le {s rv : ℝ} (h : 1 ≤ rv) : fiberA s rv = 0 := by
  unfold fiberA
  split_ifs with h2
  · rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [h])]
    exact min_eq_left (div_nonneg (by positivity) (Real.sqrt_nonneg _))
  · exact Real.sqrt_eq_zero_of_nonpos (by nlinarith [h])

lemma fiberA_le_sqrt (s rv : ℝ) : fiberA s rv ≤ Real.sqrt (1 - rv ^ 2) := by
  unfold fiberA
  split_ifs with h
  · exact min_le_left _ _
  · exact le_rfl

lemma fiberA_le_one (s rv : ℝ) : fiberA s rv ≤ 1 :=
  (fiberA_le_sqrt s rv).trans (Real.sqrt_le_one.mpr (by linarith [sq_nonneg rv]))

lemma measurable_fiberA (s : ℝ) : Measurable (fun rv : ℝ => fiberA s rv) := by
  unfold fiberA
  split_ifs with h
  · measurability
  · measurability

/-! ## The volume of a ball in a one-dimensional space -/

lemma one_dim_ball_vol {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]
    (h1 : Module.finrank ℝ K = 1) {A : ℝ} (hA : 0 ≤ A) :
    volume {a : K | ‖a‖ ≤ A} = ENNReal.ofReal (2 * A) := by
  haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (by rw [h1]; norm_num)
  have hcl : {a : K | ‖a‖ ≤ A} = Metric.closedBall (0 : K) A := by
    ext a; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hcl, InnerProductSpace.volume_closedBall, h1, pow_one]
  have hG : (√Real.pi ^ 1 / Real.Gamma (↑(1 : ℕ) / 2 + 1)) = (2 : ℝ) := by
    have hG' : Real.Gamma (↑(1 : ℕ) / 2 + 1) = √Real.pi / 2 := by
      have h2 : Real.Gamma ((1 : ℝ) / 2 + 1) = √Real.pi / 2 := by
        rw [show ((1 : ℝ) / 2 + 1) = 1 / 2 + 1 from by norm_num,
          Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
        ring
      simpa using h2
    rw [hG', pow_one]
    have hpi : √Real.pi ≠ 0 := by positivity
    field_simp
  rw [hG, ← ENNReal.ofReal_mul hA]
  ring_nf

/-! ## Geometry of the orthogonal decomposition along `c` -/

section geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The inner product of `c` with a vector of `(ℝc)ᗮ` vanishes. -/
lemma inner_orthogonal_right (c : E) (v : ↥(Submodule.span ℝ {c})ᗮ) :
    inner ℝ c (v : E) = 0 := by
  have h := (Submodule.mem_orthogonal' (Submodule.span ℝ {c}) (v : E)).mp v.2 c
    (Submodule.mem_span_singleton_self c)
  rwa [real_inner_comm] at h

/-- A vector of `(ℝc)ᗮ` is orthogonal to every vector of `ℝc`. -/
lemma inner_orthogonal_left (c : E) (a : ↥(Submodule.span ℝ {c}))
    (v : ↥(Submodule.span ℝ {c})ᗮ) : inner ℝ (a : E) (v : E) = 0 := by
  have h := (Submodule.mem_orthogonal' (Submodule.span ℝ {c}) (v : E)).mp v.2 (a : E) a.2
  rwa [real_inner_comm] at h

/-- For `a ∈ ℝc`, `|⟪c,a⟫| = ‖c‖‖a‖`. -/
lemma abs_inner_span (c : E) (a : ↥(Submodule.span ℝ {c})) :
    |inner ℝ c (a : E)| = ‖c‖ * ‖a‖ := by
  obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp a.2
  have ha : (a : E) = mu • c := hmu.symm
  have hnorm : ‖a‖ = |mu| * ‖c‖ := by
    change ‖(a : E)‖ = |mu| * ‖c‖
    rw [ha, norm_smul, Real.norm_eq_abs]
  have hinner : inner ℝ c (a : E) = mu * ‖c‖ ^ 2 := by
    rw [ha, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hinner, hnorm, abs_mul, abs_of_nonneg (sq_nonneg (‖c‖))]
  ring

/-- The fibre of the cone--band region over `v`, as two quadratic inequalities. -/
lemma fiber_set_eq (c : E) (v : ↥(Submodule.span ℝ {c})ᗮ) :
    {a : ↥(Submodule.span ℝ {c}) |
        ((a : E) + (v : E)) ∈ {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}}
      = {a : ↥(Submodule.span ℝ {c}) |
          ‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2} := by
  ext a
  simp only [Set.mem_ofPred_eq]
  set t : E := (a : E) + (v : E) with ht
  have hinner_av : inner ℝ (a : E) (v : E) = 0 := inner_orthogonal_left c a v
  have hnormsq : ‖t‖ ^ 2 = ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a : E) (v : E) hinner_av
    rw [ht, pow_two, pow_two, pow_two]
    exact h
  have hcv : inner ℝ c (v : E) = 0 := inner_orthogonal_right c v
  have hct : inner ℝ c t = inner ℝ c (a : E) := by
    rw [ht, inner_add_right, hcv, add_zero]
  have htabs : |inner ℝ c t| = ‖c‖ * ‖a‖ := by rw [hct, abs_inner_span]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← hnormsq]
      simpa [pow_two] using mul_self_le_mul_self (norm_nonneg t) h1
    · rw [htabs] at h2
      have h3 : (‖c‖ * ‖a‖) ^ 2 ≤ ‖t‖ ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2
      rw [mul_pow, hnormsq] at h3
      exact h3
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h3 : ‖t‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by rw [hnormsq]; simpa using h1
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg (norm_nonneg t), abs_one] at h4
    · rw [htabs]
      have h3 : (‖c‖ * ‖a‖) ^ 2 ≤ ‖t‖ ^ 2 := by rw [mul_pow, hnormsq]; exact h2
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
        abs_of_nonneg (norm_nonneg t)] at h4

/-- The measure of the fibre over `v`. -/
lemma fiber_measure (c : E) (hc : c ≠ 0) (v : ↥(Submodule.span ℝ {c})ᗮ) :
    volume {a : ↥(Submodule.span ℝ {c}) |
        ‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2}
      = ENNReal.ofReal (2 * fiberA ‖c‖ ‖v‖) := by
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ {c}) = 1 := by
    simpa using finrank_span_singleton (K := ℝ) (V := E) hc
  have hzero : volume ({0} : Set ↥(Submodule.span ℝ {c})) = 0 := by
    have hb := one_dim_ball_vol (K := ↥(Submodule.span ℝ {c})) h1 (A := (0 : ℝ)) le_rfl
    have hset : ({0} : Set ↥(Submodule.span ℝ {c}))
        = {a : ↥(Submodule.span ℝ {c}) | ‖a‖ ≤ (0 : ℝ)} := by
      ext a; simp [norm_le_zero_iff]
    rw [← hset] at hb
    simpa using hb
  have hsub0 : ∀ (hv : 1 ≤ ‖v‖), {a : ↥(Submodule.span ℝ {c}) |
        ‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2} ⊆ {0} := by
    intro hv a ⟨h1', _⟩
    have h3 : ‖a‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg a, h1', hv]
    have h2 : ‖a‖ = 0 := by nlinarith [norm_nonneg a, h3]
    simpa using h2
  rcases lt_or_ge (1 : ℝ) (‖c‖ ^ 2) with hgt | hle
  · rcases lt_or_ge (‖v‖) 1 with hlt | hge
    · have hpos : 0 < ‖c‖ ^ 2 - 1 := by linarith
      have hrv0 : 0 ≤ ‖v‖ := norm_nonneg v
      have hP : 0 ≤ Real.sqrt (1 - ‖v‖ ^ 2) := Real.sqrt_nonneg _
      have hQ : 0 ≤ ‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1) :=
        div_nonneg hrv0 (Real.sqrt_nonneg _)
      have hsq : ‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1)
          = Real.sqrt (‖v‖ ^ 2 / (‖c‖ ^ 2 - 1)) := by
        rw [Real.sqrt_div (sq_nonneg ‖v‖), Real.sqrt_sq hrv0]
      have hkey : ∀ a : ↥(Submodule.span ℝ {c}),
          (‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2) ↔
            ‖a‖ ≤ min (Real.sqrt (1 - ‖v‖ ^ 2)) (‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1)) := by
        intro a
        have hx : 0 ≤ ‖a‖ := norm_nonneg a
        have h1n : (0 : ℝ) ≤ 1 - ‖v‖ ^ 2 := by nlinarith
        constructor
        · rintro ⟨h1', h2'⟩
          have e1 : ‖a‖ ≤ Real.sqrt (1 - ‖v‖ ^ 2) := by
            rw [Real.le_sqrt hx h1n]; linarith
          have e2 : ‖a‖ ≤ ‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1) := by
            rw [hsq, Real.le_sqrt hx (by positivity), le_div_iff₀ hpos]
            nlinarith
          exact le_min e1 e2
        · intro h
          have e1 : ‖a‖ ≤ Real.sqrt (1 - ‖v‖ ^ 2) := le_trans h (min_le_left _ _)
          have e2 : ‖a‖ ≤ ‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1) := le_trans h (min_le_right _ _)
          refine ⟨?_, ?_⟩
          · rw [Real.le_sqrt hx h1n] at e1; linarith
          · rw [hsq, Real.le_sqrt hx (by positivity), le_div_iff₀ hpos] at e2
            nlinarith
      have hset : {a : ↥(Submodule.span ℝ {c}) |
            ‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2}
          = {a : ↥(Submodule.span ℝ {c}) |
            ‖a‖ ≤ min (Real.sqrt (1 - ‖v‖ ^ 2)) (‖v‖ / Real.sqrt (‖c‖ ^ 2 - 1))} := by
        ext a; exact hkey a
      rw [hset, fiberA, ite_eq_left hgt]
      exact one_dim_ball_vol h1 (le_min hP hQ)
    · rw [fiberA_eq_zero_of_one_le hge, mul_zero, ENNReal.ofReal_zero]
      exact le_antisymm (by
        calc volume _ ≤ volume ({0} : Set ↥(Submodule.span ℝ {c})) := measure_mono (hsub0 hge)
          _ = 0 := hzero) bot_le
  · have hz : fiberA ‖c‖ ‖v‖ = Real.sqrt (1 - ‖v‖ ^ 2) := by
      rw [fiberA, ite_eq_right (not_lt.mpr hle)]
    rw [hz]
    by_cases hr : ‖v‖ < 1
    · have h1n : (0 : ℝ) ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
      have hset : {a : ↥(Submodule.span ℝ {c}) |
            ‖a‖ ^ 2 + ‖v‖ ^ 2 ≤ 1 ∧ ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖v‖ ^ 2}
          = {a : ↥(Submodule.span ℝ {c}) | ‖a‖ ≤ Real.sqrt (1 - ‖v‖ ^ 2)} := by
        ext a
        simp only [Set.mem_ofPred_eq]
        have hx : 0 ≤ ‖a‖ := norm_nonneg a
        constructor
        · rintro ⟨h1', _⟩
          rw [Real.le_sqrt hx h1n]; linarith
        · intro h
          have h2 := h
          rw [Real.le_sqrt hx h1n] at h2
          refine ⟨by linarith, ?_⟩
          have h3 : ‖c‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 := by nlinarith [hle, sq_nonneg ‖a‖]
          linarith [sq_nonneg ‖v‖]
      rw [hset]
      exact one_dim_ball_vol h1 (Real.sqrt_nonneg _)
    · have hge : 1 ≤ ‖v‖ := le_of_not_gt hr
      rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith), mul_zero, ENNReal.ofReal_zero]
      exact le_antisymm (by
        calc volume _ ≤ volume ({0} : Set ↥(Submodule.span ℝ {c})) := measure_mono (hsub0 hge)
          _ = 0 := hzero) bot_le

/-- The volume of the cone--band region as an integral over the orthogonal complement of `c`. -/
theorem bandRegion_measure_eq (c : E) (hc : c ≠ 0) :
    volume {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}
      = ∫⁻ v : ↥(Submodule.span ℝ {c})ᗮ, ENNReal.ofReal (2 * fiberA ‖c‖ ‖v‖) := by
  set S : Set E := {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖} with hS
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {t : E | ‖t‖ ≤ 1} := isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {t : E | |inner ℝ c t| ≤ ‖t‖} :=
      isClosed_le (continuous_const.inner continuous_id).abs continuous_norm
    have := h1.inter h2
    simpa [hS, Set.ofPred_and] using this
  have hSmeas : MeasurableSet S := hSclosed.measurableSet
  have hmp : MeasurePreserving
      (⇑((Submodule.span ℝ {c}).measurableEquivProd (0 : E)))
      (volume : Measure E)
      (volume : Measure (↥(Submodule.span ℝ {c}) × ↥(Submodule.span ℝ {c})ᗮ)) := by
    have h1 := Submodule.measurePreserving_measurableEquivProd (Submodule.span ℝ {c}) (0 : E)
    rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h1
  set g : ↥(Submodule.span ℝ {c}) × ↥(Submodule.span ℝ {c})ᗮ → ENNReal :=
    (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm ⁻¹' S).indicator 1 with hg
  have hgmeas : Measurable g := by
    rw [hg]
    exact measurable_const.indicator (hSmeas.preimage
      (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm.measurable))
  have hgt : ∀ t : E, g ((Submodule.span ℝ {c}).measurableEquivProd (0 : E) t)
      = S.indicator (1 : E → ENNReal) t := by
    intro t
    have hft : (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)) t)
        ∈ (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm ⁻¹' S) ↔ t ∈ S := by
      simp
    rw [hg]
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem (hft.mpr ht), Set.indicator_of_mem (show t ∈ S from ht)]
      rfl
    · rw [Set.indicator_of_notMem (fun h => ht (hft.mp h)),
        Set.indicator_of_notMem (show t ∉ S from ht)]
  have step1 : volume S
      = ∫⁻ p : ↥(Submodule.span ℝ {c}) × ↥(Submodule.span ℝ {c})ᗮ, g p ∂volume := by
    rw [← hmp.lintegral_comp hgmeas]
    rw [show (∫⁻ t : E, g ((Submodule.span ℝ {c}).measurableEquivProd (0 : E) t) ∂volume)
        = ∫⁻ t : E, S.indicator (1 : E → ENNReal) t ∂volume from lintegral_congr hgt]
    exact (lintegral_indicator_one hSmeas).symm
  have step2 : ∫⁻ p : ↥(Submodule.span ℝ {c}) × ↥(Submodule.span ℝ {c})ᗮ, g p ∂volume
      = ∫⁻ v : ↥(Submodule.span ℝ {c})ᗮ, ∫⁻ a : ↥(Submodule.span ℝ {c}), g (a, v) ∂volume
          ∂volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.lintegral_prod_symm g hgmeas.aemeasurable
  rw [step1, step2]
  refine lintegral_congr (fun v => ?_)
  have hsymm : ∀ a : ↥(Submodule.span ℝ {c}),
      ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) = (a : E) + (v : E) := by
    intro a
    rw [Submodule.measurableEquivProd_symm_apply]
    simp [vadd_eq_add]
  have hT : {a : ↥(Submodule.span ℝ {c}) |
        ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S}
      = {a : ↥(Submodule.span ℝ {c}) |
        ((a : E) + (v : E)) ∈ {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}} := by
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [hsymm a]
  have hTmeas : MeasurableSet {a : ↥(Submodule.span ℝ {c}) |
      ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S} :=
    hSmeas.preimage ((((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm.measurable).comp
      (measurable_prodMk_right (y := v)))
  have hinner : ∫⁻ a : ↥(Submodule.span ℝ {c}), g (a, v) ∂volume
      = volume {a : ↥(Submodule.span ℝ {c}) |
        ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S} := by
    rw [hg]
    rw [show (fun a : ↥(Submodule.span ℝ {c}) =>
          ((((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm ⁻¹' S).indicator
            (1 : ↥(Submodule.span ℝ {c}) × ↥(Submodule.span ℝ {c})ᗮ → ENNReal)) (a, v))
        = ({a : ↥(Submodule.span ℝ {c}) |
            ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S}).indicator
            (1 : ↥(Submodule.span ℝ {c}) → ENNReal) from by
      funext a
      by_cases h : ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S
      · rw [Set.indicator_of_mem (show (a, v) ∈
            (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm ⁻¹' S) from h),
          Set.indicator_of_mem (show a ∈ {a : ↥(Submodule.span ℝ {c}) |
            ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S} from h)]
        rfl
      · rw [Set.indicator_of_notMem (show (a, v) ∉
            (((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm ⁻¹' S) from h),
          Set.indicator_of_notMem (show a ∉ {a : ↥(Submodule.span ℝ {c}) |
            ((Submodule.span ℝ {c}).measurableEquivProd (0 : E)).symm (a, v) ∈ S} from h)]]
    rw [lintegral_indicator_one hTmeas]
  rw [hinner, hT, fiber_set_eq c v, fiber_measure c hc v]


/-! ## Volumes and moments of balls in a finite-dimensional real inner product space

These identify the canonical (orthonormal-basis normalised) `volume` with the constants
`ballVol k` of the workspace. -/

section balls
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma finrank_pos_of_one_le (hd : 1 ≤ Module.finrank ℝ F) : 0 < Module.finrank ℝ F :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one hd

lemma ballVol_nonneg (k : ℕ) : 0 ≤ ballVol k := ENNReal.toReal_nonneg

/-- The unit-ball constant is the classical Gamma formula. -/
lemma ballVol_eq_gamma (k : ℕ) (hk : 1 ≤ k) :
    ballVol k = Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
  have hne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  unfold ballVol
  rw [EuclideanSpace.volume_closedBall (Fin k) 0 1]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal
    (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (le_of_lt (Real.Gamma_pos_of_pos (by
        have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        linarith))))]

lemma ballVol_pos (k : ℕ) (hk : 1 ≤ k) : 0 < ballVol k := by
  rw [ballVol_eq_gamma k hk]
  exact div_pos (pow_pos (Real.sqrt_pos_of_pos Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by
      have h : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith))

/-- The volume of the unit ball in `F` is `ballVol (finrank ℝ F)`. -/
lemma volume_unitBall (hd : 1 ≤ Module.finrank ℝ F) :
    volume (Metric.ball (0 : F) 1) = ENNReal.ofReal (ballVol (Module.finrank ℝ F)) := by
  haveI : Nontrivial F := Module.nontrivial_of_finrank_pos (finrank_pos_of_one_le hd)
  rw [InnerProductSpace.volume_ball]
  rw [ballVol_eq_gamma _ hd]
  simp

/-- The volume of a ball of radius `r` in `F`. -/
lemma volume_closedBall_eq (hd : 1 ≤ Module.finrank ℝ F) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : F) r)
      = ENNReal.ofReal (ballVol (Module.finrank ℝ F) * r ^ (Module.finrank ℝ F)) := by
  rw [Measure.addHaar_closedBall volume 0 hr, volume_unitBall hd]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr _), mul_comm]

/-- The first moment of the Euclidean unit ball: `∫ ‖v‖ = d/(d+1) · ballVol d`. -/
lemma integral_norm_closedBall (hd : 1 ≤ Module.finrank ℝ F) :
    ∫ v in Metric.closedBall (0 : F) 1, ‖v‖ ∂volume
      = (Module.finrank ℝ F : ℝ) / ((Module.finrank ℝ F : ℝ) + 1) * ballVol (Module.finrank ℝ F) := by
  classical
  haveI : Nontrivial F := Module.nontrivial_of_finrank_pos (finrank_pos_of_one_le hd)
  have hV : volume.real (Metric.ball (0 : F) 1) = ballVol (Module.finrank ℝ F) := by
    rw [Measure.real, volume_unitBall hd, ENNReal.toReal_ofReal (ballVol_nonneg _)]
  have hd0 : Module.finrank ℝ F - 1 + 1 = Module.finrank ℝ F := Nat.sub_add_cancel hd
  have hfun : ∀ v : F, (Metric.closedBall (0 : F) 1).indicator (fun v => ‖v‖) v
      = (fun y : ℝ => if y ≤ 1 then y else 0) ‖v‖ := by
    intro v
    have h' : ‖v‖ ≤ 1 ↔ v ∈ Metric.closedBall (0 : F) 1 := by
      simp [Metric.mem_closedBall, dist_eq_norm]
    by_cases h : v ∈ Metric.closedBall (0 : F) 1
    · rw [Set.indicator_of_mem h]
      exact (if_pos (h'.mpr h)).symm
    · rw [Set.indicator_of_notMem h]
      exact (if_neg (fun hh => h (h'.mp hh))).symm
  have hcongr : ∀ y : ℝ,
      (Set.Ioi (0 : ℝ)).indicator
          (fun y => y ^ (Module.finrank ℝ F - 1) * (if y ≤ 1 then y else 0)) y
        = (Set.Ioc (0 : ℝ) 1).indicator (fun y => y ^ Module.finrank ℝ F) y := by
    intro y
    by_cases h0 : (0 : ℝ) < y
    · by_cases h1 : y ≤ 1
      · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from h0),
          Set.indicator_of_mem (show y ∈ Set.Ioc (0 : ℝ) 1 from ⟨h0, h1⟩),
          if_pos h1, ← pow_succ, hd0]
      · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from h0),
          Set.indicator_of_notMem (show y ∉ Set.Ioc (0 : ℝ) 1 from fun h => h1 h.2),
          if_neg h1, mul_zero]
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi (0 : ℝ) from h0),
        Set.indicator_of_notMem (show y ∉ Set.Ioc (0 : ℝ) 1 from fun h => h0 h.1)]
  have hIoc : ∫ y in Set.Ioc (0 : ℝ) 1, y ^ Module.finrank ℝ F ∂volume
      = 1 / ((Module.finrank ℝ F : ℝ) + 1) := by
    rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [integral_pow]
    simp [zero_pow (by omega : Module.finrank ℝ F + 1 ≠ 0)]
  have hint : ∫ y in Set.Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ F - 1) * (if y ≤ 1 then y else 0) ∂volume
      = 1 / ((Module.finrank ℝ F : ℝ) + 1) := by
    rw [← hIoc, ← MeasureTheory.integral_indicator (μ := volume) (f := fun y : ℝ =>
      y ^ (Module.finrank ℝ F - 1) * (if y ≤ 1 then y else 0)) measurableSet_Ioi,
      ← MeasureTheory.integral_indicator (μ := volume) (f := fun y : ℝ =>
        y ^ Module.finrank ℝ F) measurableSet_Ioc]
    exact integral_congr_ae (Filter.Eventually.of_forall hcongr)
  rw [← MeasureTheory.integral_indicator (μ := volume) (f := fun v : F => ‖v‖)
    measurableSet_closedBall]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := volume) (F := ℝ)
    (f := fun y : ℝ => if y ≤ 1 then y else 0)]
  rw [hV]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [hint]
  ring

end balls


/-! ## Generic integrability helper -/

lemma integrable_of_bounded_support {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {f : F → ℝ} (hf : Measurable f) (hsupp : Function.support f ⊆ Metric.closedBall (0 : F) 1)
    {K : ℝ} (hbd : ∀ v, ‖f v‖ ≤ K) : Integrable f volume := by
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
  exact Measure.integrableOn_of_bounded (MeasureTheory.measure_closedBall_lt_top).ne
    hf.aestronglyMeasurable (Filter.Eventually.of_forall hbd)

/-- The real-valued form of the volume identity. -/
theorem bandRegion_real_eq (c : E) (hc : c ≠ 0) :
    (volume {t : E | ‖t‖ ≤ 1 ∧ |inner ℝ c t| ≤ ‖t‖}).toReal
      = ∫ v : ↥(Submodule.span ℝ {c})ᗮ, 2 * fiberA ‖c‖ ‖v‖ ∂volume := by
  have h := bandRegion_measure_eq c hc
  have hfA : Measurable (fun v : ↥(Submodule.span ℝ {c})ᗮ => 2 * fiberA ‖c‖ ‖v‖) :=
    measurable_const.mul ((measurable_fiberA ‖c‖).comp continuous_norm.measurable)
  have hsupp : Function.support (fun v : ↥(Submodule.span ℝ {c})ᗮ => 2 * fiberA ‖c‖ ‖v‖)
      ⊆ Metric.closedBall (0 : ↥(Submodule.span ℝ {c})ᗮ) 1 := by
    intro v hv
    simp only [Function.mem_support, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    exact hv (by simpa using fiberA_eq_zero_of_one_le (s := ‖c‖) (rv := ‖v‖) hlt.le)
  have hbd : ∀ v : ↥(Submodule.span ℝ {c})ᗮ, ‖2 * fiberA ‖c‖ ‖v‖‖ ≤ 2 := by
    intro v
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) (fiberA_nonneg ‖c‖ ‖v‖ (norm_nonneg v)))]
    linarith [fiberA_le_one ‖c‖ ‖v‖]
  have hint : Integrable (fun v : ↥(Submodule.span ℝ {c})ᗮ => 2 * fiberA ‖c‖ ‖v‖) volume :=
    integrable_of_bounded_support hfA hsupp hbd
  have hnn : 0 ≤ᵐ[volume] (fun v : ↥(Submodule.span ℝ {c})ᗮ => 2 * fiberA ‖c‖ ‖v‖) :=
    Filter.Eventually.of_forall (fun v =>
      mul_nonneg (by norm_num) (fiberA_nonneg ‖c‖ ‖v‖ (norm_nonneg v)))
  rw [h]
  rw [← ENNReal.toReal_ofReal (integral_nonneg (f := fun v : ↥(Submodule.span ℝ {c})ᗮ =>
    2 * fiberA ‖c‖ ‖v‖) (fun v =>
    mul_nonneg (by norm_num) (fiberA_nonneg ‖c‖ ‖v‖ (norm_nonneg v))))]
  congr 1
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm

/-! ## Elementary real inequalities -/

lemma one_sub_sqrt_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - Real.sqrt (1 - x) ≤ x := by
  have h1 : (0 : ℝ) ≤ 1 - x := by linarith
  have h2 : 1 - x ≤ Real.sqrt (1 - x) := by
    rw [Real.le_sqrt h1 h1]; nlinarith
  linarith

lemma one_sub_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    1 - r ^ n ≤ n * (1 - r) := by
  have := one_add_mul_sub_le_pow (a := r) (by linarith : (-1 : ℝ) ≤ r) n
  linarith

lemma inv_sqrt_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 / Real.sqrt (1 - x) - 1 ≤ x := by
  have h1x : 0 < 1 - x := by linarith
  have hsqrt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr h1x
  have h1 : (1 : ℝ) ≤ (1 + x) * Real.sqrt (1 - x) := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 + x),
      ← Real.sqrt_mul (sq_nonneg (1 + x)) (1 - x)]
    rw [Real.le_sqrt (by norm_num) (by nlinarith)]
    nlinarith [sq_nonneg x]
  have h2 : 1 / Real.sqrt (1 - x) ≤ 1 + x := by
    rw [div_le_iff₀ hsqrt]; linarith
  linarith

lemma inv_sqrt_one_sub_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 4) :
    1 / Real.sqrt (1 - x) ≤ 2 := by
  have h1x : 0 < 1 - x := by linarith
  have hsqrt : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr h1x
  have h2 : (1 : ℝ) / 2 ≤ Real.sqrt (1 - x) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ hsqrt]; linarith

/-! ## The abstract volume asymptotic -/


end geometry

end Work.HP

/-
# Guidance for `Work.HP.bandVol_asymp` (the abstract volume asymptotic)

The infrastructure in this file is sorry-free and imports `Submission.Work.HP.MMDefs`
(which provides `ballVol` and `deltaV`).

Setting: `E` finite-dimensional real inner product space with `d := finrank ℝ E ≥ 2`,
`0 ≠ c : E`, `s := ‖c‖`.  The region is `R c := {t : E | ‖t‖ ≤ 1 ∧ |⟪c,t⟫| ≤ ‖t‖}`.
Goal: `∃ C > 0, ∀ c ≠ 0, |(volume (R c)).toReal - M| ≤ C * M * min 1 (1/‖c‖²)`
with `M := 2 * ((d:ℝ)-1)/(d:ℝ) * ballVol (d-1) / s`.

Available here (all proved):
* `bandRegion_real_eq c hc : (volume (R c)).toReal = ∫ v : ↥(span ℝ {c})ᗮ, 2 * fiberA ‖c‖ ‖v‖`.
* `fiberA`: for `1 < s²` it is `min (√(1-rv²)) (rv/√(s²-1))` (and `√(1-rv²)` otherwise);
  `fiberA_nonneg`, `fiberA_le_sqrt`, `fiberA_le_one`, `fiberA_eq_zero_of_one_le`, `measurable_fiberA`.
* `volume_closedBall_eq (hd) (r) (hr) : volume (closedBall 0 r) = ofReal (ballVol (finrank ℝ F) * r ^ finrank)`.
* `integral_norm_closedBall (hd) : ∫ v in closedBall 0 1, ‖v‖ = d/(d+1) * ballVol d`
  (so on `W := ↥(span ℝ {c})ᗮ`, whose `finrank` is `d-1`, the value is `J := ((d:ℝ)-1)/(d:ℝ) * ballVol (d-1)`).
* `integrable_of_bounded_support` to get `Integrable` of the bounded, ball-supported integrands.
* Real inequalities `one_sub_sqrt_le`, `one_sub_pow_le`, `inv_sqrt_one_sub_sub_le`, `inv_sqrt_one_sub_le_two`.

Suggested route.  Let `W := ↥(span ℝ {c})ᗮ` (so `finrank ℝ W = d - 1`), `J := ∫_{closedBall 0 1} ‖v‖`.
* Case `s² ≤ 2`: `fiberA ≤ 1` and `fiberA = 0` off the closed unit ball, so
  `I ≤ 2 * ballVol (d-1)`, and `min 1 (1/s²) ≥ 1/2`; `C = 2d+8` works.
* Case `2 < s²`: with `b(v) := ‖v‖/√(s²-1)`, `ind` the indicator of the unit ball of `W`
  and `shell := {r < ‖v‖ ∧ ‖v‖ ≤ 1}`, `r := √(1-1/s²)`:
  - `2*fiberA s ‖v‖ ≤ 2*b(v)*ind(v)`, hence `I ≤ 2J/√(s²-1)`; note `2J/√(s²-1) - M`
    `= M*(1/√(1-1/s²) - 1) ≤ M/s²` by `inv_sqrt_one_sub_sub_le`;
  - `2*fiberA s ‖v‖ ≥ 2*b(v)*ind(v) - 2*b(v)*shell(v)`, and
    `∫ 2*b*shell ≤ (2/√(s²-1)) * vol(shell)` with
    `vol(shell) = ballVol (d-1) * (1 - r^(d-1)) ≤ ballVol (d-1) * (d-1)/s²`
    (use `volume_closedBall_eq` and `one_sub_pow_le`, `one_sub_sqrt_le`);
    combined with `√(s²-1) ≥ s/2` this gives `M - I ≤ M * 2d/s²`.
  Hence `|I - M| ≤ M*(2d+1)/s²`, and `min 1 (1/s²) = 1/s²` in this case.
-/
