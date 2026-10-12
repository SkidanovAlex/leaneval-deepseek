import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Split

/-! Route: Tonelli on the nonnegative integrand, `Submission.BoseGases.integral_pair_scale`
(`∫ x, chiScale ℓ x * chiScale ℓ (x - y) = ℓ^3 * convScale ℓ y`, in `Submission.KernelIds`), the
pointwise cancellation `|wScaled ℓ h y| * convScale ℓ y = |h y| * 1_{convScale ℓ y ≠ 0}` (division
convention `h/0 = 0`, `convScale_nonneg`) and `convScale ℓ y ≠ 0 → ‖y‖ < ℓ` give
`∫∫ ‖χ(x)W₁(y)χ(x-y)‖ = ℓ^3 ∫_y |h y| 1_{convScale ℓ y ≠ 0} dy ≤ ℓ^3 ∫_{ball 0 ℓ} |h|`, finite by
`LocallyIntegrable` + `LocallyIntegrable.integrableOn_isCompact`.  The statement is the
`integrable_chi_wScaled_chi` of `SmallBoxPairDecomp` with its `Integrable h`/support/dilute-regime
hypotheses replaced by mere local integrability.

## What is actually formalised here

The above route is followed, in the *fibre* form of Tonelli (`integrable_prod_iff'`, integrating
the *first* variable first) rather than in the raw `∫⁻` form: for fixed `y` the `x`-fibre

  `x ↦ ‖χ_ℓ(x)·W₁(y)·χ_ℓ(x−y)‖`

is (a constant times) a compactly supported continuous function, hence integrable, and its integral
is computed exactly by `integral_pair_scale` together with the pointwise cancellation
`abs_wScaled_mul_convScale`:

  `∫ x, ‖χ_ℓ(x)·W₁(y)·χ_ℓ(x−y)‖ = ℓ^3 · (if (χ⋆χ)_ℓ(y) = 0 then 0 else |h y|)`.

Since `(χ⋆χ)_ℓ(y) ≠ 0` forces `‖y‖ ≤ ℓ` (`convScale_support_norm_le`, from the support of
`χ ⋆ χ` inside `ball 0 1`, i.e. `Submission.BoseGases.chi_eq_zero_of_norm_gt`), the outer function
is dominated by `ℓ³·|h|·1_{closedBall 0 ℓ}`, which is integrable by `LocallyIntegrable` alone
(`LocallyIntegrable.integrableOn_isCompact` on the compact ball, then `Integrable.indicator`).
No support, boundedness or integrability assumption on `h` beyond local integrability is used,
and in particular no `L¹`-bound on `W₁ = wScaled ℓ h` itself is needed — the numerator/denominator
cancellation is exact.

The two component lemmas were also delegated in parallel to
`Submission/Work/BoseFixB3/Split/convScale_norm_le.lean` and
`Submission/Work/BoseFixB3/Split/integral_norm_chi_wScaled_chi.lean`; the private copies below make
this module self-contained. -/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

/-! ## 1. The support of `χ ⋆ χ` -/

/-- `χ ⋆ χ` vanishes outside the closed unit ball: the two factors can only be nonzero when
`‖u‖ ≤ 1/2` and `‖x − u‖ ≤ 1/2`, forcing `‖x‖ ≤ 1`. -/
private lemma conv3chi_eq_zero_of_one_lt_norm (x : EuclideanSpace ℝ (Fin 3)) (hx : 1 < ‖x‖) :
    Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x = 0 := by
  show (∫ u : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.chi u * Submission.BoseGases.chi (x - u)) = 0
  have hzero : ∀ u : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chi u * Submission.BoseGases.chi (x - u) = 0 := by
    intro u
    by_cases hu : Submission.BoseGases.chi u = 0
    · rw [hu, zero_mul]
    · have hu' : ‖u‖ ≤ 1 / 2 :=
        le_of_not_gt (fun hgt => hu (Submission.BoseGases.chi_eq_zero_of_norm_gt u hgt))
      by_cases hxu : Submission.BoseGases.chi (x - u) = 0
      · rw [hxu, mul_zero]
      · have hxu' : ‖x - u‖ ≤ 1 / 2 :=
          le_of_not_gt (fun hgt => hxu (Submission.BoseGases.chi_eq_zero_of_norm_gt (x - u) hgt))
        have hxle : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := by
          have h := norm_add_le (x - u) u
          rwa [sub_add_cancel] at h
        linarith
  rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chi u * Submission.BoseGases.chi (x - u)) = fun _ => (0 : ℝ) from
    funext hzero]
  simp

/-- The support bound for the scaled convolution: `(χ⋆χ)_ℓ(y) ≠ 0` forces `‖y‖ ≤ ℓ`. -/
private lemma convScale_support_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : Submission.BoseGases.convScale ℓ y ≠ 0) : ‖y‖ ≤ ℓ := by
  have h1 : ‖(ℓ⁻¹) • y‖ ≤ 1 := by
    by_contra h
    rw [not_le] at h
    exact hy (conv3chi_eq_zero_of_one_lt_norm ((ℓ⁻¹) • y) h)
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hℓ))] at h1
  calc ‖y‖ = ℓ * ((ℓ⁻¹) * ‖y‖) := by field_simp
    _ ≤ ℓ * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hℓ)
    _ = ℓ := by ring

/-! ## 2. The exact numerator/denominator cancellation -/

/-- The defining cancellation of the renormalised kernel, in absolute values: because
`W₁ = h/(χ⋆χ)_ℓ` with Lean's total division (`h/0 = 0`) and `(χ⋆χ)_ℓ ≥ 0`,

  `|W₁(y)|·(χ⋆χ)_ℓ(y) = if (χ⋆χ)_ℓ(y) = 0 then 0 else |h y|`. -/
private lemma abs_wScaled_mul_convScale {ℓ : ℝ} (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wScaled ℓ h y| * Submission.BoseGases.convScale ℓ y
      = if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y| := by
  by_cases hc : Submission.BoseGases.convScale ℓ y = 0
  · simp [Submission.BoseGases.wScaled, hc]
  · have hpos : 0 < Submission.BoseGases.convScale ℓ y :=
      lt_of_le_of_ne (Submission.BoseGases.convScale_nonneg ℓ y) (Ne.symm hc)
    rw [if_neg hc, Submission.BoseGases.wScaled, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hc]

/-! ## 3. The exact `x`-fibre integral -/

/-- The `x`-fibre integral of the absolute value of the pair kernel: pulling out the constant
`W₁(y)`, computing `∫ x, χ_ℓ(x)χ_ℓ(x−y) = ℓ³(χ⋆χ)_ℓ(y)` (`integral_pair_scale`) and cancelling
against the denominator gives `ℓ³·|h y|` on the support of `(χ⋆χ)_ℓ` and `0` outside it. -/
private lemma integral_norm_chi_wScaled_chi {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : EuclideanSpace ℝ (Fin 3) → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.wScaled ℓ h y * Submission.BoseGases.chiScale ℓ (x - y)‖)
      = ℓ ^ 3 * (if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y|) := by
  have h1 : (fun x : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.wScaled ℓ h y * Submission.BoseGases.chiScale ℓ (x - y)‖)
      = fun x : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.wScaled ℓ h y| *
          (Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ (x - y)) := by
    funext x
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x),
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ (x - y))]
    ring
  rw [h1, integral_const_mul, Submission.BoseGases.integral_pair_scale hℓ y,
    show |Submission.BoseGases.wScaled ℓ h y| * (ℓ ^ 3 * Submission.BoseGases.convScale ℓ y)
        = ℓ ^ 3 * (|Submission.BoseGases.wScaled ℓ h y| * Submission.BoseGases.convScale ℓ y)
      by ring,
    abs_wScaled_mul_convScale h y]

/-! ## 4. Integrability of the `x`-fibres -/

/-- For fixed `y` the `x`-fibre `χ_ℓ(x)·W₁(y)·χ_ℓ(x−y)` is integrable: it is a constant times a
product of two bounded continuous compactly supported factors. -/
private lemma integrable_fibre_chi_wScaled_chi {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : EuclideanSpace ℝ (Fin 3) → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiScale ℓ x *
      Submission.BoseGases.wScaled ℓ h y * Submission.BoseGases.chiScale ℓ (x - y))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hχ : Integrable (Submission.BoseGases.chiScale ℓ)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (Submission.BoseGases.chiScale_continuous ℓ).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiScale_hasCompactSupport (ℓ := ℓ) (ne_of_gt hℓ))
  have hSnn : 0 ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by positivity
  have hχle : ∀ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiScale ℓ x ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro x
    rw [← abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)]
    exact Submission.BoseGases.abs_chiScale_le ℓ x
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ x *
        Submission.BoseGases.wScaled ℓ h y * Submission.BoseGases.chiScale ℓ (x - y)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).mul continuous_const).mul
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_id.sub continuous_const))
  have hc : (0 : ℝ) ≤
      |Submission.BoseGases.wScaled ℓ h y| * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
    mul_nonneg (abs_nonneg _) hSnn
  refine Integrable.mono (hχ.const_mul (|Submission.BoseGases.wScaled ℓ h y| *
      (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹)) hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hLHS : ‖Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.wScaled ℓ h y *
        Submission.BoseGases.chiScale ℓ (x - y)‖ =
      Submission.BoseGases.chiScale ℓ x * |Submission.BoseGases.wScaled ℓ h y| *
        Submission.BoseGases.chiScale ℓ (x - y) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x),
      abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ (x - y))]
  have hRHS : ‖(|Submission.BoseGases.wScaled ℓ h y| *
        (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) *
        Submission.BoseGases.chiScale ℓ x‖ =
      |Submission.BoseGases.wScaled ℓ h y| * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
        Submission.BoseGases.chiScale ℓ x := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc (Submission.BoseGases.chiScale_nonneg ℓ x))]
  rw [hLHS, hRHS]
  calc Submission.BoseGases.chiScale ℓ x * |Submission.BoseGases.wScaled ℓ h y| *
        Submission.BoseGases.chiScale ℓ (x - y)
      ≤ Submission.BoseGases.chiScale ℓ x * |Submission.BoseGases.wScaled ℓ h y| *
          (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
        mul_le_mul_of_nonneg_left (hχle (x - y))
          (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x) (abs_nonneg _))
    _ = |Submission.BoseGases.wScaled ℓ h y| * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
          Submission.BoseGases.chiScale ℓ x := by ring

/-! ## 5. The theorem -/

theorem integrable_chi_wScaled_chi_local {ℓ : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hli : MeasureTheory.LocallyIntegrable h) :
    MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ h q.2
          * Submission.BoseGases.chiScale ℓ (q.1 - q.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hhae : AEMeasurable h := hli.aestronglyMeasurable.aemeasurable
  have haesm : AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ h q.2
          * Submission.BoseGases.chiScale ℓ (q.1 - q.2)) (volume.prod volume) := by
    have hW : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wScaled ℓ h q.2) (volume.prod volume) :=
      (hhae.comp_snd).div (((Submission.BoseGases.convScale_continuous ℓ).measurable.comp
        measurable_snd).aemeasurable)
    have h1 : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ h q.2)
        (volume.prod volume) :=
      (((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp
        measurable_fst).aemeasurable).mul hW
    have h2 : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ (q.1 - q.2)) (volume.prod volume) :=
      (((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp
        (measurable_fst.sub measurable_snd)).aemeasurable)
    exact (h1.mul h2).aestronglyMeasurable
  refine (MeasureTheory.integrable_prod_iff' haesm).mpr ⟨?_, ?_⟩
  · filter_upwards with y
    exact integrable_fibre_chi_wScaled_chi hℓ h y
  · have heq : (fun y : EuclideanSpace ℝ (Fin 3) => ∫ x : EuclideanSpace ℝ (Fin 3),
        ‖(fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ q.1 * Submission.BoseGases.wScaled ℓ h q.2
            * Submission.BoseGases.chiScale ℓ (q.1 - q.2)) (x, y)‖)
        = fun y : EuclideanSpace ℝ (Fin 3) =>
            ℓ ^ 3 * (if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y|) := by
      funext y
      exact integral_norm_chi_wScaled_chi hℓ h y
    rw [heq]
    have hk : IntegrableOn h (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ) volume :=
      hli.integrableOn_isCompact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ)
    have hkabs : IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) => ℓ ^ 3 * |h y|)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ) volume := by
      show Integrable (fun y : EuclideanSpace ℝ (Fin 3) => ℓ ^ 3 * |h y|)
        (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ))
      exact (show Integrable h
        (volume.restrict (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ)) from
          hk).abs.const_mul (ℓ ^ 3)
    have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ).indicator
          (fun y => ℓ ^ 3 * |h y|) y) volume :=
      hkabs.integrable_indicator measurableSet_closedBall
    refine Integrable.mono hdom ?_ ?_
    · have hset : MeasurableSet
          {y : EuclideanSpace ℝ (Fin 3) | Submission.BoseGases.convScale ℓ y = 0} :=
        (Submission.BoseGases.convScale_continuous ℓ).measurable (measurableSet_singleton 0)
      have hif : (fun y : EuclideanSpace ℝ (Fin 3) =>
            (if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y|))
          = {y : EuclideanSpace ℝ (Fin 3) | Submission.BoseGases.convScale ℓ y = 0}ᶜ.indicator
              (fun y => |h y|) := by
        funext y
        by_cases hc : Submission.BoseGases.convScale ℓ y = 0
        · rw [if_pos hc, Set.indicator_of_notMem (by simpa using hc)]
        · rw [if_neg hc, Set.indicator_of_mem (by simpa using hc)]
      have hif_ae : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
          (if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y|)) volume := by
        rw [hif]
        exact hhae.abs.indicator hset.compl
      exact hif_ae.aestronglyMeasurable.const_mul (ℓ ^ 3)
    · filter_upwards with y
      have hifnn : 0 ≤ (if Submission.BoseGases.convScale ℓ y = 0 then 0 else |h y|) := by
        split
        · norm_num
        · exact abs_nonneg _
      have hgnn : 0 ≤ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ).indicator
          (fun y => ℓ ^ 3 * |h y|) y :=
        Set.indicator_nonneg (fun _ _ => mul_nonneg (pow_nonneg (le_of_lt hℓ) 3) (abs_nonneg _)) y
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hℓ) 3) hifnn), abs_of_nonneg hgnn]
      by_cases hc : Submission.BoseGases.convScale ℓ y = 0
      · rw [if_pos hc, mul_zero]
        exact hgnn
      · rw [if_neg hc]
        have hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ := by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
          exact convScale_support_norm_le hℓ hc
        rw [Set.indicator_of_mem hy]

end

end Work.BoseFixB3.Split
