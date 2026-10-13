import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Every angular slot of `u` is dominated by `AngRHS`

`AngRHS k γ u g` (see `remov/slice_ang_reduce.lean`) is the sum of the five weighted norms

* `∫ g^{(k)}² sin(2θ)^{2k-γ}`,   (the source term)
* `∑_{j=3}^{k+1} ∫ u^{(j)}² sin(2θ)^{2j-4-γ}`,
* `∫ u''² sin(2θ)^{-η}`,
* `∫ u'²`,   `∫ u²`.

The present file proves that for `1 ≤ γ ≤ 5/4` and `k ≥ 2` **every** slot
`∫ u^{(j)}² sin(2θ)^{2k-γ}` with `j ≤ k+1` (and the corresponding integrability)
is bounded by `AngRHS k γ u g`.  The only mathematical input is that the weight
`sin(2θ)^{2k-γ}` is dominated by the matching weight of the corresponding summand:

* `j = 0, 1`: `sin(2θ)^{2k-γ} ≤ 1`;
* `j = 2`:     `sin(2θ)^{2k-γ} ≤ sin(2θ)^{-η}`  (`-η ≤ 2k - γ`);
* `j ≥ 3`:     `sin(2θ)^{2k-γ} ≤ sin(2θ)^{2j-4-γ}`  (`j ≤ k+2`),

each applied after multiplication by the nonnegative factor `u^{(j)}²`.

The reduction is packaged in `angSlot_weight_mono`, which turns the monotonicity of
the weight (on `(0,π/2)`, where `0 < sin(2θ) ≤ 1`, plus the trivial endpoint case
`sin(2θ) = 0`) into simultaneous integrability and integral comparison.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## Elementary facts about `Iθ`, and the `rpow`/`iteratedDeriv` bridges

The statement uses `Real.rpow` explicitly, so the comparison lemmas are restated with
`Real.rpow` on the left-hand side (the corresponding Mathlib lemmas are stated with the
`x ^ y` notation, which `rw` does not match against `Real.rpow`). -/

lemma angSlot_Iθ_measurable : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

lemma angSlot_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma angSlot_rpow_zero (x : ℝ) : Real.rpow x (0 : ℝ) = 1 := Real.rpow_zero x

lemma angSlot_zero_rpow {y : ℝ} (hy : y ≠ 0) : Real.rpow (0 : ℝ) y = 0 := Real.zero_rpow hy

lemma angSlot_iteratedDeriv_two (u : ℝ → ℝ) : iteratedDeriv 2 u = deriv (deriv u) := by
  rw [iteratedDeriv_succ', iteratedDeriv_one]

lemma angSlot_itd0_mul_rpow_zero (u : ℝ → ℝ) :
    (fun θ : ℝ => (iteratedDeriv 0 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (0 : ℝ))
      = fun θ : ℝ => (u θ) ^ 2 := by
  funext θ
  simp only [iteratedDeriv_zero, angSlot_rpow_zero, mul_one]

lemma angSlot_itd1_mul_rpow_zero (u : ℝ → ℝ) :
    (fun θ : ℝ => (iteratedDeriv 1 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (0 : ℝ))
      = fun θ : ℝ => (deriv u θ) ^ 2 := by
  funext θ
  simp only [iteratedDeriv_one, angSlot_rpow_zero, mul_one]

lemma angSlot_itd2_mul_rpow (u : ℝ → ℝ) (q : ℝ) :
    (fun θ : ℝ => (iteratedDeriv 2 u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q)
      = fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
  funext θ
  simp only [angSlot_iteratedDeriv_two]

/-! ## Measurability of the iterated derivatives on `Iθ` -/

/-- `iteratedDeriv j u` is almost everywhere strongly measurable for the restriction of the
Lebesgue measure to `Iθ`, as soon as `u ∈ C^{k+2}` on the *open* interval and `j ≤ k+2`:
on the open interval the function is continuous (`ContDiffOn.continuousOn_iteratedDerivWithin`
combined with `iteratedDerivWithin = iteratedDeriv` there), and the two endpoints of `Iθ`
form a null set. -/
theorem angSlot_measurable_iteratedDeriv {k j : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2))) (hj : j ≤ k + 2) :
    AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo.uniqueDiffOn
  have hle : (j : WithTop ℕ∞) ≤ (k + 2 : WithTop ℕ∞) := by
    exact_mod_cast (show j ≤ k + 2 by omega)
  have hc : ContinuousOn (iteratedDerivWithin j u (Set.Ioo 0 (Real.pi / 2)))
      (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn_iteratedDerivWithin hle hs
  have hc' : ContinuousOn (fun θ => iteratedDeriv j u θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hc.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)
  have h1 : AEStronglyMeasurable (fun θ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hc'.aestronglyMeasurable measurableSet_Ioo
  have hae : (Work.Spaces.Iθ : Set ℝ) =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rwa [Measure.restrict_congr_set hae]

/-! ## The weight comparison: a larger `rpow` exponent gives a smaller weight -/

/-- **The slot comparison.**  For `0 < Q` and `q ≤ Q`, the `Q`-weighted slot of
`iteratedDeriv j u` is integrable as soon as the `q`-weighted one is, and its integral is at
most the `q`-weighted integral.

On `(0,π/2)` the weight comparison is monotonicity of `x ↦ x^r` on `0 < x ≤ 1`; at the
endpoints `sin(2θ) = 0` the left-hand side vanishes because `Q ≠ 0`, while the right-hand
side is nonnegative. -/
theorem angSlot_weight_mono {Q q : ℝ} (hQ : 0 < Q) (hq : q ≤ Q) (j : ℕ) {u : ℝ → ℝ}
    (hA : AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ))
    (hIntBig : IntegrableOn
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q)
        Work.Spaces.Iθ) :
    IntegrableOn
        (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
          Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
        ≤ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) q) := by
  have hrpow : Continuous (fun x : ℝ => x ^ Q) :=
    continuous_iff_continuousAt.mpr (fun x => Real.continuousAt_rpow_const x Q (Or.inr hQ.le))
  have hsin2 : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcontQ : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) Q) := hrpow.comp hsin2
  have hsmQ : AEStronglyMeasurable
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (hA.pow 2).mul hcontQ.measurable.aestronglyMeasurable
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q
        ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
    filter_upwards [MeasureTheory.ae_restrict_mem angSlot_Iθ_measurable] with θ hθ
    rcases eq_or_lt_of_le (angSlot_sin_two_nonneg hθ) with h0 | hpos
    · rw [← h0, angSlot_zero_rpow (ne_of_gt hQ), mul_zero]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg le_rfl q)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) hq) (sq_nonneg _)
  have hnorm : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      ‖(iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q‖
        ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) q := by
    filter_upwards [hae, MeasureTheory.ae_restrict_mem angSlot_Iθ_measurable] with θ hle hθ
    have hnn : 0 ≤ (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) Q)
    rw [Real.norm_of_nonneg hnn]
    exact hle
  have hIntQ : IntegrableOn
      (fun θ : ℝ => (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) Q)
        Work.Spaces.Iθ := hIntBig.mono' hsmQ hnorm
  exact ⟨hIntQ, integral_mono_ae hIntQ hIntBig hae⟩

/-! ## `AngRHS` unfolded -/

lemma angSlot_AngRHS_unfold (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) :
    AngRHS k γ u g
      = (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := rfl

/-! ## The target -/

theorem angSlot_le_AngRHS (k : ℕ) (hk : 2 ≤ k) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      ∀ j : ℕ, j ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  intro γ u g _hγ1 hγ2 hu _hcont hInt_gk hInt_high hInt_2 hInt_1 hInt_0 j hj
  have hQpos : 0 < 2 * (k : ℝ) - γ := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => iteratedDeriv j u θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    angSlot_measurable_iteratedDeriv hu (by omega)
  -- nonnegativity of the four remaining components of `AngRHS`
  have hnn1 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))
  have hnn2 : 0 ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j _ => setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _)))
  have hnn3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))
  have hnn4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ _ => sq_nonneg _)
  have hnn5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    setIntegral_nonneg angSlot_Iθ_measurable (fun θ _ => sq_nonneg _)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj3
  · -- `j = 0`: the slot is dominated by `∫ u²`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 0 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (0 : ℝ)) Work.Spaces.Iθ := by
      simpa only [iteratedDeriv_zero, angSlot_rpow_zero, mul_one] using hInt_0
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith : (0 : ℝ) ≤ 2 * (k : ℝ) - γ) 0 hmeas hbig
    rw [angSlot_itd0_mul_rpow_zero u] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn3, hnn4]
  · -- `j = 1`: the slot is dominated by `∫ u'²`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 1 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (0 : ℝ)) Work.Spaces.Iθ := by
      simpa only [iteratedDeriv_one, angSlot_rpow_zero, mul_one] using hInt_1
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith : (0 : ℝ) ≤ 2 * (k : ℝ) - γ) 1 hmeas hbig
    rw [angSlot_itd1_mul_rpow_zero u] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn3, hnn5]
  · -- `j = 2`: the slot is dominated by `∫ u''² sin(2θ)^{-η}`
    have hbig : IntegrableOn (fun θ : ℝ => (iteratedDeriv 2 u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
      simpa only [angSlot_iteratedDeriv_two] using hInt_2
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos
      (by linarith [hQpos, Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 2 * (k : ℝ) - γ)
      2 hmeas hbig
    rw [angSlot_itd2_mul_rpow u (-(Work.Spaces.eta))] at hle
    refine ⟨hInt, le_trans hle ?_⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn2, hnn4, hnn5]
  · -- `3 ≤ j`: the slot is one summand of the `j`-sum of `AngRHS`
    have hjmem : j ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hj3, hj⟩
    have hq : 2 * (j : ℝ) - 4 - γ ≤ 2 * (k : ℝ) - γ := by
      have hjle : (j : ℝ) ≤ (k : ℝ) + 2 := by
        exact_mod_cast (show j ≤ k + 2 by omega)
      linarith
    obtain ⟨hInt, hle⟩ := angSlot_weight_mono hQpos hq j hmeas (hInt_high j hjmem)
    have hsum : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
        ≤ ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      Finset.single_le_sum
        (s := Finset.Icc 3 (k + 1))
        (f := fun i => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv i u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (i : ℝ) - 4 - γ))
        (fun i _ => setIntegral_nonneg angSlot_Iθ_measurable (fun θ hθ =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (angSlot_sin_two_nonneg hθ) _))) hjmem
    refine ⟨hInt, le_trans hle (le_trans hsum ?_)⟩
    rw [angSlot_AngRHS_unfold]
    linarith [hnn1, hnn3, hnn4, hnn5]

end Work.FTS.EllipticEst.remov
