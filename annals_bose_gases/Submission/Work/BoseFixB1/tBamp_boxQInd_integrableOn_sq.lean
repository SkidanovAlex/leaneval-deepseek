import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.measurable_tBamp_boxQInd_pair
import Submission.Work.SlotWord.abs_boxQInd_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.tBamp_boxQInd_integrableOn_sq`

The squared modulus of the windowed amplitude of FS's box mean-free projection
`Q_{B,i} = boxQInd volA A i` of a **continuous** state is `IntegrableOn` the ambient box
`abox n a`, for an arbitrary measurable box `A ⊆ acube a` (with arbitrary normalisation
`volA : ℝ`) and an arbitrary continuous compactly supported window `χ`.

## The argument

* `Ψ` is continuous, the box `abox n a` is compact (`a > 0`), so `Ψ` has a sup bound `B` there;
* the box `A` sits in `acube a`, hence has finite volume, and `Work.SlotWord.abs_boxQInd_le_of_bound`
  bounds the projection on the box by `M := B + |volA|⁻¹·(B·|A|)`;
* **the decisive point** is that `boxQInd` is supported in `{y | y i ∈ A}`: inside
  `tBamp χ p (boxQInd …) i x = ∫ z, χ z e^{−i⟪p,z⟫} (boxQInd … (x_{i←z}))` the indicator is
  evaluated at the *updated* coordinate `z`.  Hence the amplitude integrand is bounded by
  `|χ z| · M` for **every** `z` (`z ∈ A`: the updated configuration `x_{i←z}` is again in
  `abox n a`; `z ∉ A`: the projection vanishes identically), with no support hypothesis on `χ`;
* so `‖tBamp …‖ ≤ M·∫|χ|` uniformly on the box, the amplitude is measurable, and `abox n a`
  has finite measure, so `MeasureTheory.IntegrableOn.of_bound` closes.
-/

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The box projection vanishes when the slot coordinate is outside the box -/

/-- Both terms of FS's `Q_{B,i} = 1_{B,i}·Φ − P_{B,i}Φ` carry the indicator of the box in the
slot-`i` coordinate, so the projection vanishes whenever that coordinate lies outside `B`. -/
private lemma boxQInd_eq_zero_of_notMem {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) {x : Submission.BoseGases.X N}
    (hx : x i ∉ A) :
    Work.UBBInputs8.boxQInd volA A i Φ x = 0 := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  rw [Set.indicator_of_notMem hx]
  ring

/-! ## 2. The pointwise bound on the windowed amplitude -/

/-- **The windowed amplitude of the box projection is bounded by the window mass times the
box-projection bound.**  If `χ` is continuous with compact support, `Φ` is bounded by `B` on
`abox N a`, and the box `A ⊆ acube a` has finite volume, then for `x ∈ abox N a`

`‖tBamp χ p (Q_{A,i}Φ) i x‖ ≤ M · ∫|χ|`,  `M = B + |volA|⁻¹·(B·|A|)`.

No support hypothesis on `χ` is used: the state `Q_{A,i}Φ` already vanishes off the set where
the slot-`i` coordinate lies in `A`, and for `z ∈ A ⊆ acube a` the updated configuration
`x_{i←z}` stays inside `abox N a`. -/
private theorem norm_tBamp_boxQInd_le {N : ℕ} {a volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAa : A ⊆ Submission.BoseGases.acube a)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχcs : HasCompactSupport χ)
    {Φ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hΦb : ∀ y ∈ Submission.BoseGases.abox N a, |Φ y| ≤ B) (i : Fin N)
    (p : EuclideanSpace ℝ (Fin 3)) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N a) :
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
      ≤ (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)) *
          ∫ z, |χ z| := by
  have hM0 : 0 ≤ B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A) :=
    add_nonneg hB (mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
      (mul_nonneg hB measureReal_nonneg))
  -- the projection is bounded on the box
  have hQb : ∀ y ∈ Submission.BoseGases.abox N a,
      |Work.UBBInputs8.boxQInd volA A i Φ y|
        ≤ B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A) :=
    fun y hy => Work.SlotWord.abs_boxQInd_le_of_bound a hAa hB hfin
      (fun y' hy' => hΦb y' ((Submission.BoseGases.mem_abox_iff N a y').mpr hy'))
      i y ((Submission.BoseGases.mem_abox_iff N a y).mp hy)
  -- integrability of the dominating integrand
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχcs
  have hint : Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        |χ z| * (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A))) :=
    (hχint.abs).mul_const _
  have hexp : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    rw [Complex.norm_exp]
    simp
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) : ℂ)‖
        ≤ |χ z| * (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)) := by
    intro z
    have hnorm1 : ‖(χ z : ℂ)‖ = |χ z| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hnorm2 : ‖(Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) : ℂ)‖
        = |Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [norm_mul, hexp z, mul_one, hnorm1, hnorm2]
    by_cases hz : z ∈ A
    · -- the updated configuration is again in the box
      have hmem : Function.update x i z ∈ Submission.BoseGases.abox N a := by
        rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hAa hz
        · rw [if_neg hj]; exact hx j
      exact mul_le_mul_of_nonneg_left (hQb _ hmem) (abs_nonneg _)
    · -- off the box the projection vanishes identically
      have hzero : Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) = 0 :=
        boxQInd_eq_zero_of_notMem i Φ (by rw [Function.update_self i z x]; exact hz)
      rw [hzero, abs_zero, mul_zero]
      exact mul_nonneg (abs_nonneg _) hM0
  calc ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Φ) i x‖
      = ‖∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) : ℂ)‖ := by
        simp only [Work.SmallBoxTBWord.tBamp]
    _ ≤ ∫ z, ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, |χ z| *
          (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)) *
          ∫ z, |χ z| := by
        rw [integral_mul_const]; ring

/-! ## 3. Measurability of the amplitude -/

/-- The amplitude `x ↦ tBamp χ p Ψ i x` is measurable for a measurable window `χ` and a
measurable state `Ψ`: the integrand `(x,z) ↦ χ z · e^{−i⟪p,z⟫} · Ψ (x_{i←z})` is jointly
measurable, so the parametric Bochner integral is strongly measurable
(`StronglyMeasurable.integral_prod_right'`). -/
private theorem measurable_tBamp_aux {N : ℕ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : Measurable χ) (p : EuclideanSpace ℝ (Fin 3)) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Measurable Ψ) (i : Fin N) :
    Measurable (fun x : Submission.BoseGases.X N => Work.SmallBoxTBWord.tBamp χ p Ψ i x) := by
  have hprod : Continuous (fun q : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
      (p, q.2)) := continuous_const.prodMk continuous_snd
  have hinner_c : Continuous (fun q : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
      (inner ℝ p q.2 : ℂ)) := Complex.continuous_ofReal.comp (continuous_inner.comp hprod)
  have hexp_meas : Measurable (fun q : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner_c).neg)).measurable
  have hJ : Measurable (fun q : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        (Ψ (Function.update q.1 i q.2) : ℂ)) := by
    refine Measurable.mul (Measurable.mul ?_ hexp_meas) ?_
    · exact Complex.continuous_ofReal.measurable.comp (hχ.comp measurable_snd)
    · exact Complex.continuous_ofReal.measurable.comp (hΨ.comp measurable_update')
  have hSM := hJ.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
  simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable

/-! ## 4. The square of a bounded measurable function on the finite box -/

/-- A measurable real function with a uniform sup bound on `abox n a` has integrable square
over the finite-measure box `abox n a`. -/
private theorem integrableOn_sq_of_bound {n : ℕ} {a : ℝ} (ha : 0 < a)
    {g : Submission.BoseGases.X n → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox n a, |g x| ≤ C) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => g x ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := by
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n a ha.le)
    (hg.pow_const 2).aestronglyMeasurable (max C 0 ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n a)]
    with x hx
  have h1 : |g x| ≤ max C 0 := le_trans (hC x hx) (le_max_left _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-! ## 5. The target -/

theorem tBamp_boxQInd_integrableOn_sq {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ)
    (i : Fin n) (q : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      (Submission.BoseGases.abox n a) MeasureTheory.volume := by
  classical
  -- a sup bound for `Ψ` over the compact box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n ha).exists_bound_of_continuousOn
    hΨ.continuousOn
  let B : ℝ := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hΨb : ∀ y ∈ Submission.BoseGases.abox n a, |Ψ y| ≤ B := by
    intro y hy
    have h1 : ‖Ψ y‖ ≤ C := hC y hy
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  -- the box `Ac ⊆ acube a` has finite volume
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) Ac < ⊤ :=
    lt_of_le_of_lt (measure_mono hAcsub) (Submission.BoseGases.acube_compact ha).measure_lt_top
  -- the uniform bound on the amplitude
  have hbound : ∀ x ∈ Submission.BoseGases.abox n a,
      |‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖|
        ≤ (B + |volA|⁻¹ * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real Ac)) *
            ∫ z : EuclideanSpace ℝ (Fin 3), |χ z| := by
    intro x hx
    rw [abs_of_nonneg (norm_nonneg _)]
    exact norm_tBamp_boxQInd_le (A := Ac) (Φ := Ψ) hAcsub hfin hχc hχs hB0 hΨb i q hx
  -- measurability of the amplitude
  have hQm : Measurable (fun x : Submission.BoseGases.X n =>
      Work.UBBInputs8.boxQInd volA Ac i Ψ x) :=
    Work.SlotWord.measurable_boxQInd volA Ac hAcm i hΨ.measurable
  have hmeas : Measurable (fun x : Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖) :=
    (measurable_tBamp_aux hχc.measurable q hQm i).norm
  exact integrableOn_sq_of_bound ha hmeas hbound

end

end Work.BoseFixB1
