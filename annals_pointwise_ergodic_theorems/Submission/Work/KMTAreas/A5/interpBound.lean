/-
# Interpolation of the two endpoint estimates of §5 (Krause--Mirek--Tao, Annals 195 (2022))

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), §5 combines the two endpoint estimates of the minor-arc parts of
the bilinear averages -- an `l^{p0} (x) l^{q0} -> l^1` estimate (`anf`, Hölder plus the
Ionescu--Wainger `l^{V1}` bound) and an `l^{p1} (x) l^{q1} -> l^{r1/(r1-1)}` estimate (`improv`)
-- into the `l^p (x) l^q -> l^r` estimate at the reciprocally interpolated exponents

`1/p = (1-theta)/p0 + theta/p1`, `1/q = (1-theta)/q0 + theta/q1`, `1/r = 1 - theta/r1`.

The interpolation is Stein's trilinear interpolation, applied to the pairing
`Lambda u v w = ∫ x, T u v x * w x ∂count` (the `l^1` endpoint of the output pairs with `l^∞`, the
`r1/(r1-1)` endpoint with `l^{r1}`; the third exponent `1/r` of the output corresponds to the
pairing exponent `r' = r/(r-1)`, i.e. `1/r' = theta/r1`, which is exactly `1/r = 1 - theta/r1`).

The three ingredients are
* `Work.KMTAreas.A5.interpExpansion` (in `interpDefs`), the level-set expansion of `T` on the
  analytic families of two simple functions, which uses only the linearity of `T` on *bounded*
  functions;
* `Work.KMTAreas.A5.interpEndpointTop` and `...interpEndpointR1` (in `interpDefs`), the two
  endpoint estimates for the pairing, both from Hölder's inequality and the two hypotheses;
* `interpDecomp` below, the level-set decomposition of the pairing (the `hLambda` input of the
  three-lines argument), and its consequence (boundedness on the strip).

The final step is duality for the `L^r` seminorm
(`Work.Analysis.Interpolation.eLpNorm_le_of_forall_simpleFunc_integral_le`), after the a priori
finiteness of `||T f g||_r`, which follows from the two endpoint estimates by the log-convexity of
the `L^p` seminorm (`Interp.eLpNorm_interp`).
-/
import Mathlib
import Submission.Work.KMTAreas.A5.stein_trilinear_top
import Submission.Work.KMTAreas.A5.interpDefs

namespace Work.KMTAreas.A5

open MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The analytic family of a simple function, in the abbreviated form used in the proofs below. -/
abbrev interpAFam (f : SimpleFunc ℤ ℂ) (t₀ t₁ z : ℂ) : ℤ → ℂ :=
  Work.Analysis.Interpolation.analyticFamily (f : ℤ → ℂ) t₀ t₁ z

/-- The `z`-dependent coefficient `phasePow c (expFamily t₀ t₁ z)` of the level-set expansion. -/
abbrev interpPH (t₀ t₁ z : ℂ) (c : ℂ) : ℂ :=
  Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z)

/-- The indicator of a level set of a simple function. -/
abbrev interpIND (f : SimpleFunc ℤ ℂ) (c : ℂ) : ℤ → ℂ :=
  Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))

/-- The level-set expansion of the analytic family, in the abbreviated notation. -/
lemma interpAFam_eq_sum (f : SimpleFunc ℤ ℂ) (t₀ t₁ z : ℂ) :
    interpAFam f t₀ t₁ z = ∑ c ∈ f.range, interpPH t₀ t₁ z c • interpIND f c :=
  Work.Analysis.Interpolation.analyticFamily_eq_sum f t₀ t₁ z

/-- The coefficient of the level set `{0}` vanishes. -/
lemma interpPH_zero (t₀ t₁ z : ℂ) : interpPH t₀ t₁ z 0 = 0 :=
  Work.Analysis.Interpolation.phasePow_zero_left _

/-- The `L^r` seminorm of the indicator of a level set. -/
lemma eLpNorm_interpIND (f : SimpleFunc ℤ ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (interpIND f c) (ENNReal.ofReal r) Measure.count
      = (Measure.count (f ⁻¹' {c})) ^ (1 / r) :=
  Work.Analysis.Interpolation.eLpNorm_indicator_one
    (measurableSet_preimage (SimpleFunc.measurable f) (measurableSet_singleton c)) hr

/-- **The level-set decomposition of the pairing `Lambda u v w = ∫ T u v · w`.**  Given the
expansion of `T` on the two analytic families (hypothesis `hexp`, supplied by
`Work.KMTAreas.A5.interpExpansion`), the pairing of `T` applied to the three analytic families
expands as the finite triple sum over the level sets of the three simple functions, with the
`z`-dependent entire coefficients `phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)
* phasePow e (expFamily v₀ v₁ z)` in front of the `z`-independent "matrix coefficients"
`∫ T 1_{f⁻¹{c}} 1_{g⁻¹{d}} · 1_{h⁻¹{e}}`.

The hypotheses `hf`, `hg` (finiteness of the nonzero level sets of `f`, `g`) and the `l^1` endpoint
estimate `h₀` are exactly what is needed for the integrability of the summands: the nonzero level
sets of `f` and `g` have finite measure, so the corresponding level-set indicators lie in
`l^{p0}`, `l^{q0}`, whence `T 1_{f⁻¹{c}} 1_{g⁻¹{d}} ∈ l^1` by `h₀`; the remaining factor is an
`l^∞` function.  The terms in which one of the level values vanishes are identically zero. -/
theorem interpDecomp (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    {p₀ q₀ : ℝ} (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) {M₀ : ℝ≥0}
    (h₀ : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
          * eLpNorm v (ENNReal.ofReal q₀) Measure.count)
    (f g h : SimpleFunc ℤ ℂ)
    (hf : ∀ c ∈ f.range, c ≠ 0 → Measure.count (f ⁻¹' {c}) < ⊤)
    (hg : ∀ c ∈ g.range, c ≠ 0 → Measure.count (g ⁻¹' {c}) < ⊤)
    (hh : ∀ c ∈ h.range, c ≠ 0 → Measure.count (h ⁻¹' {c}) < ⊤)
    (t₀ t₁ u₀ u₁ v₀ v₁ z : ℂ)
    (hexp : T (Work.Analysis.Interpolation.analyticFamily (f : ℤ → ℂ) t₀ t₁ z)
        (Work.Analysis.Interpolation.analyticFamily (g : ℤ → ℂ) u₀ u₁ z)
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily u₀ u₁ z))
            • T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))) :
    trilinearT T (interpAFam f t₀ t₁ z) (interpAFam g u₀ u₁ z) (interpAFam h v₀ v₁ z)
      = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (interpPH t₀ t₁ z c * interpPH u₀ u₁ z d * interpPH v₀ v₁ z e)
          * trilinearT T (interpIND f c) (interpIND g d) (interpIND h e) := by
  classical
  have hterm : ∀ a b c : ℤ → ℂ, trilinearT T a b c = ∫ x, T a b x * c x ∂Measure.count :=
    fun a b c => trilinearT_of_aemeasurable (T := T) (measurable_of_countable c).aemeasurable
  have hpoint : ∀ y : ℤ, T (interpAFam f t₀ t₁ z) (interpAFam g u₀ u₁ z) y
        * (interpAFam h v₀ v₁ z) y
      = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (interpPH t₀ t₁ z c * interpPH u₀ u₁ z d * interpPH v₀ v₁ z e)
            * ((T (interpIND f c) (interpIND g d)) y * (interpIND h e) y) := by
    intro y
    rw [hexp, interpAFam_eq_sum (f := h)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [mul_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    conv_lhs => rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    ring
  have hint : ∀ e ∈ h.range, ∀ d ∈ g.range, ∀ c ∈ f.range,
      Integrable (fun y : ℤ => (interpPH t₀ t₁ z c * interpPH u₀ u₁ z d * interpPH v₀ v₁ z e)
        * ((T (interpIND f c) (interpIND g d)) y * (interpIND h e) y)) Measure.count := by
    intro e he d hd c hc
    by_cases hc0 : c = 0
    · subst hc0
      have hz : (fun y : ℤ => (interpPH t₀ t₁ z 0 * interpPH u₀ u₁ z d * interpPH v₀ v₁ z e)
          * ((T (interpIND f 0) (interpIND g d)) y * (interpIND h e) y)) = 0 := by
        funext y
        simp [interpPH_zero]
      rw [hz]
      exact integrable_zero ℤ ℂ Measure.count
    by_cases hd0 : d = 0
    · subst hd0
      have hz : (fun y : ℤ => (interpPH t₀ t₁ z c * interpPH u₀ u₁ z 0 * interpPH v₀ v₁ z e)
          * ((T (interpIND f c) (interpIND g 0)) y * (interpIND h e) y)) = 0 := by
        funext y
        simp [interpPH_zero]
      rw [hz]
      exact integrable_zero ℤ ℂ Measure.count
    by_cases he0 : e = 0
    · subst he0
      have hz : (fun y : ℤ => (interpPH t₀ t₁ z c * interpPH u₀ u₁ z d * interpPH v₀ v₁ z 0)
          * ((T (interpIND f c) (interpIND g d)) y * (interpIND h 0) y)) = 0 := by
        funext y
        simp [interpPH_zero]
      rw [hz]
      exact integrable_zero ℤ ℂ Measure.count
    have hIndF : eLpNorm (interpIND f c) (ENNReal.ofReal p₀) Measure.count < ⊤ := by
      rw [eLpNorm_interpIND f c hp₀]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt (hf c hc hc0))
    have hIndG : eLpNorm (interpIND g d) (ENNReal.ofReal q₀) Measure.count < ⊤ := by
      rw [eLpNorm_interpIND g d hq₀]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt (hg d hd hd0))
    have hX : MemLp (T (interpIND f c) (interpIND g d)) 1 Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt (h₀ _ _)
          (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hIndF) hIndG))
    have hI : MemLp (interpIND h e) ⊤ Measure.count := by
      refine memLp_top_of_bound (measurable_of_countable _).aestronglyMeasurable 1 ?_
      filter_upwards with y
      rw [interpIND]
      rw [Set.indicator_apply]
      split_ifs <;> simp
    exact (hX.integrable_mul hI).const_mul _
  simp only [hterm]
  rw [show (∫ x, T (interpAFam f t₀ t₁ z) (interpAFam g u₀ u₁ z) x
        * (interpAFam h v₀ v₁ z) x ∂Measure.count)
      = ∫ x, (∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (interpPH t₀ t₁ z c * interpPH u₀ u₁ z d * interpPH v₀ v₁ z e)
            * ((T (interpIND f c) (interpIND g d)) x * (interpIND h e) x)) ∂Measure.count from
    integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum _ (fun e he => integrable_finsetSum _
    (fun d hd => integrable_finsetSum _ (fun c hc => hint e he d hd c hc)))]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [integral_finsetSum _ (fun d hd => integrable_finsetSum _ (fun c hc => hint e he d hd c hc))]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [integral_finsetSum _ (fun c hc => hint e he d hd c hc)]
  exact Finset.sum_congr rfl fun c hc => integral_const_mul _ _

theorem interpBound (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ u' → Work.KMTAreas.A5.BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ v → Work.KMTAreas.A5.BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    {p₀ p₁ q₀ q₁ r₁ p q r θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hr₁ : 1 < r₁) (hp : 0 < p) (hq : 0 < q) (hr : 1 < r) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    (hrθ : 1 / r = 1 - θ / r₁)
    {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
          * eLpNorm v (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ u v : ℤ → ℂ, eLpNorm (T u v) (ENNReal.ofReal (r₁ / (r₁ - 1))) Measure.count
      ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
          * eLpNorm v (ENNReal.ofReal q₁) Measure.count) :
    ∀ f g : SimpleFunc ℤ ℂ,
      (∀ c ∈ f.range, c ≠ 0 → Measure.count (f ⁻¹' {c}) < ⊤) →
      (∀ c ∈ g.range, c ≠ 0 → Measure.count (g ⁻¹' {c}) < ⊤) →
      eLpNorm (T (f : ℤ → ℂ) (g : ℤ → ℂ)) (ENNReal.ofReal r) Measure.count
        ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
          * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count
          * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal q) Measure.count := by
  intro f g hf hg
  -- finiteness of the level sets and of the endpoint norms
  have hf' : ∀ c : ℂ, c ≠ 0 → Measure.count (f ⁻¹' {c}) < ⊤ :=
    Work.Analysis.Interpolation.simpleFunc_fiber_lt_top_of_range f hf
  have hg' : ∀ c : ℂ, c ≠ 0 → Measure.count (g ⁻¹' {c}) < ⊤ :=
    Work.Analysis.Interpolation.simpleFunc_fiber_lt_top_of_range g hg
  have hmemf : ∀ {s : ℝ}, 0 < s → MemLp (f : ℤ → ℂ) (ENNReal.ofReal s) Measure.count :=
    fun {s} _ => SimpleFunc.memLp_of_finite_measure_preimage _ hf'
  have hmemg : ∀ {s : ℝ}, 0 < s → MemLp (g : ℤ → ℂ) (ENNReal.ofReal s) Measure.count :=
    fun {s} _ => SimpleFunc.memLp_of_finite_measure_preimage _ hg'
  have hA : eLpNorm (T (f : ℤ → ℂ) (g : ℤ → ℂ)) (ENNReal.ofReal 1) Measure.count < ⊤ := by
    rw [ENNReal.ofReal_one]
    exact lt_of_le_of_lt (h₀ _ _) (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (hmemf hp₀).eLpNorm_lt_top)
      (hmemg hq₀).eLpNorm_lt_top)
  have hB : eLpNorm (T (f : ℤ → ℂ) (g : ℤ → ℂ))
      (ENNReal.ofReal (r₁ / (r₁ - 1))) Measure.count < ⊤ :=
    lt_of_le_of_lt (h₁ _ _) (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (hmemf hp₁).eLpNorm_lt_top)
      (hmemg hq₁).eLpNorm_lt_top)
  -- the exponent relation in the conjugate form used by the log-convexity of the `L^p` seminorm
  have hrel : 1 / r = (1 - θ) / 1 + θ / (r₁ / (r₁ - 1)) := by
    have h2 : θ / (r₁ / (r₁ - 1)) = θ - θ / r₁ := by field_simp
    rw [h2, div_one]
    linarith [hrθ]
  have hfin : eLpNorm (T (f : ℤ → ℂ) (g : ℤ → ℂ)) (ENNReal.ofReal r) Measure.count < ⊤ :=
    (Interp.eLpNorm_interp (μ := Measure.count) (f := T (f : ℤ → ℂ) (g : ℤ → ℂ))
      (p₀ := 1) (p₁ := r₁ / (r₁ - 1)) (p := r)
      one_pos (by positivity) (by linarith : (0 : ℝ) < r) hθ₀ hθ₁ hrel
      (measurable_of_countable _).aemeasurable).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) (ne_of_lt hA))
        (ENNReal.rpow_lt_top_of_nonneg hθ₀.le (ne_of_lt hB)))
  -- duality for the `L^r` seminorm
  refine Work.Analysis.Interpolation.eLpNorm_le_of_forall_simpleFunc_integral_le
    (ν := Measure.count) (q := r) (h := T (f : ℤ → ℂ) (g : ℤ → ℂ))
    (C := (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
      * eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count
      * eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal q) Measure.count) hr ?_ hfin ?_
  · exact (measurable_of_countable _).aemeasurable
  · intro H hHfin
    have hHlevel : ∀ e ∈ H.range, e ≠ 0 → Measure.count (H ⁻¹' {e}) < ⊤ :=
      fun e he he0 => SimpleFunc.measure_preimage_lt_top_of_memLp
        (ENNReal.ofReal_ne_zero_iff.mpr (div_pos (lt_trans zero_lt_one hr) (by linarith)))
        ENNReal.ofReal_ne_top H (MeasureTheory.memLp_iff.mpr hHfin) e he0
    -- the level-set decomposition of the pairing, the `hLambda` input of the three-lines argument
    have hΛ : ∀ z : ℂ, trilinearT T (interpAFam f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
        (interpAFam g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
        (interpAFam H (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z)
      = ∑ e ∈ H.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (interpPH ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z c
            * interpPH ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z d
            * interpPH (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z e)
          * trilinearT T (interpIND f c) (interpIND g d) (interpIND H e) :=
      fun z => interpDecomp T hp₀ hq₀ h₀ f g H (fun c _ hc => hf' c hc) (fun c _ hc => hg' c hc)
        hHlevel ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ)
        ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) (0 : ℂ) (((r / (r - 1)) / r₁ : ℝ) : ℂ) z
        (interpExpansion T hlin₁ hlin₂ f g ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ)
          ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
    -- Stein's trilinear interpolation at the interpolated exponents
    have hstein := stein_trilinear_top (Λ := fun u v w => trilinearT T u v w) f g H
      hp₀ hp₁ hq₀ hq₁ (by linarith : (0 : ℝ) < r₁) hp hq hr hθ₀ hθ₁ hpθ hqθ hrθ
      (interpEndpointTop T h₀) (interpEndpointR1 T hr₁ h₁) hΛ
      (Work.Analysis.Interpolation.bddAbove_trilinear_family (fun u v w => trilinearT T u v w)
        f g H (p / p₀) (p / p₁) (q / q₀) (q / q₁) 0 ((r / (r - 1)) / r₁) hΛ)
    rw [trilinearT_of_aemeasurable (T := T) (SimpleFunc.aemeasurable H)] at hstein
    simpa only [mul_assoc] using hstein

end

end Work.KMTAreas.A5
