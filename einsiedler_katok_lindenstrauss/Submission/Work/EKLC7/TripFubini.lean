import Mathlib
import Submission.Work.EKLC7.CoordTripDefs
import Submission.Work.EKLC7.TripAux.integral_prod_prod

/-!
# `TripFubini`: Fubini for the triple product of three pushforward measures

Proves `Work.EKLC7.TripFubini`: for continuous maps `e₁ e₂ e₃ : ℝ → SL₃(ℝ)`, a continuous `ψ`
with `ψ x = e₁ x.1 * e₂ x.2.1 * e₃ x.2.2`, and measures `μᵢ = (αᵢ).map eᵢ` (`αᵢ` finite on
compacts), the iterated integral of `f (x * y * z)` against `μ₁, μ₂, μ₃` equals the integral of `f`
against the pushforward of `μ₁ ⊗ (μ₂ ⊗ μ₃)` along the product map.

The `μᵢ` are only locally finite, so Mathlib's Fubini theorem does not apply directly to the
`SL₃`-side integrand `(x, y, z) ↦ f (x * y * z)`: that function is *not* compactly supported.  The
proof instead changes variables along the three `eᵢ` (`MeasureTheory.integral_map`, whose only
measurability inputs are compositions of `f` with continuous maps), producing the iterated integral
over `ℝ³`; there the integrand `x ↦ f (ψ x)` *is* compactly supported thanks to the lexicographic
escape condition `hlex`, so Fubini applies.

Steps:

* `hasCompactSupport_comp_of_lex` — the escape condition confines the support of `x ↦ f (ψ x)` to a
  compact box;
* `tripFubini_alpha` — the three changes of variables `μᵢ → αᵢ`;
* `tripFubini_lhs`, `tripFubini_rhs` — the two sides, both reduced to `∫ x, f (ψ x) ∂(α₁⊗α₂⊗α₃)`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

open Work.EKLContract

namespace Work.EKLC7

/-! ## Compact support of `f ∘ ψ` -/

/-- Compact support of `f ∘ ψ` from the lexicographic escape condition. -/
theorem hasCompactSupport_comp_of_lex {ψ : ℝ × ℝ × ℝ → SL3}
    (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x, (∀ a b : Fin 3, |toMat (ψ x) a b| ≤ M) →
      |x.1| ≤ M' ∧ |x.2.1| ≤ M' ∧ |x.2.2| ≤ M')
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    HasCompactSupport (fun x : ℝ × ℝ × ℝ => f (ψ x)) := by
  have hφc : Continuous (fun g : SL3 => ∑ p : Fin 3 × Fin 3, |toMat g p.1 p.2|) := by
    refine continuous_finsetSum _ (fun p _ => ?_)
    exact (continuous_toMat_entry p.1 p.2).abs
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn f.hasCompactSupport hφc.continuousOn
  obtain ⟨M', hM'⟩ := hlex (max M 0)
  have hsub : Function.support (fun x : ℝ × ℝ × ℝ => f (ψ x)) ⊆
      Set.Icc (-(max M' 0)) (max M' 0) ×ˢ (Set.Icc (-(max M' 0)) (max M' 0) ×ˢ
        Set.Icc (-(max M' 0)) (max M' 0)) := by
    intro x hx
    have hxt : ψ x ∈ tsupport f := subset_tsupport _ hx
    have hentry : ∀ a b : Fin 3, |toMat (ψ x) a b| ≤ max M 0 := by
      intro a b
      have h1 : |toMat (ψ x) a b| ≤ ∑ p : Fin 3 × Fin 3, |toMat (ψ x) p.1 p.2| :=
        Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |toMat (ψ x) p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (a, b))
      have h3 : (0:ℝ) ≤ ∑ p : Fin 3 × Fin 3, |toMat (ψ x) p.1 p.2| :=
        Finset.sum_nonneg (fun p _ => abs_nonneg _)
      have h4 : ‖(∑ p : Fin 3 × Fin 3, |toMat (ψ x) p.1 p.2| : ℝ)‖ ≤ M := hM (ψ x) hxt
      rw [Real.norm_eq_abs, abs_of_nonneg h3] at h4
      exact le_trans h1 (le_trans h4 (le_max_left M 0))
    obtain ⟨e1, e2, e3⟩ := hM' x hentry
    have hb1 : |x.1| ≤ max M' 0 := le_trans e1 (le_max_left M' 0)
    have hb2 : |x.2.1| ≤ max M' 0 := le_trans e2 (le_max_left M' 0)
    have hb3 : |x.2.2| ≤ max M' 0 := le_trans e3 (le_max_left M' 0)
    refine ⟨?_, ?_, ?_⟩ <;> rw [Set.mem_Icc] <;> exact abs_le.mp ‹_›
  rw [hasCompactSupport_def]
  exact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
    isClosed_closure (closure_minimal hsub (isCompact_Icc.prod (isCompact_Icc.prod
      isCompact_Icc)).isClosed)

/-- The iterated integral over `SL₃` rewritten as an iterated integral over `ℝ`. -/
theorem tripFubini_alpha {e₁ e₂ e₃ : ℝ → SL3} (hc₁ : Continuous e₁) (hc₂ : Continuous e₂)
    (hc₃ : Continuous e₃) {α₁ α₂ α₃ : Measure ℝ} [SFinite α₂] [SFinite α₃]
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    ∫ x, ∫ y, ∫ z, f (x * y * z) ∂(α₃.map e₃) ∂(α₂.map e₂) ∂(α₁.map e₁)
      = ∫ x₁, ∫ x₂, ∫ x₃, f (e₁ x₁ * e₂ x₂ * e₃ x₃) ∂α₃ ∂α₂ ∂α₁ := by
  have h1 : ∀ x y : SL3, (∫ z, f (x * y * z) ∂(α₃.map e₃))
      = ∫ t, f (x * y * e₃ t) ∂α₃ := by
    intro x y
    exact MeasureTheory.integral_map (hc₃.measurable.aemeasurable)
      ((f.continuous.comp (by fun_prop : Continuous fun z : SL3 => x * y * z)).aestronglyMeasurable)
  have h2 : ∀ x : SL3, (∫ y, ∫ t, f (x * y * e₃ t) ∂α₃ ∂(α₂.map e₂))
      = ∫ s, ∫ t, f (x * e₂ s * e₃ t) ∂α₃ ∂α₂ := by
    intro x
    refine MeasureTheory.integral_map (hc₂.measurable.aemeasurable) ?_
    exact (StronglyMeasurable.integral_prod_right' (ν := α₃)
      (f := fun w : SL3 × ℝ => f (x * w.1 * e₃ w.2))
      ((f.continuous.comp (by fun_prop : Continuous fun z : SL3 × ℝ => x * z.1 * e₃ z.2))).stronglyMeasurable).aestronglyMeasurable
  have h3 : (∫ x, ∫ s, ∫ t, f (x * e₂ s * e₃ t) ∂α₃ ∂α₂ ∂(α₁.map e₁))
      = ∫ x₁, ∫ s, ∫ t, f (e₁ x₁ * e₂ s * e₃ t) ∂α₃ ∂α₂ ∂α₁ := by
    refine MeasureTheory.integral_map (hc₁.measurable.aemeasurable) ?_
    have hG : StronglyMeasurable (fun w : SL3 × ℝ => ∫ t, f (w.1 * e₂ w.2 * e₃ t) ∂α₃) :=
      StronglyMeasurable.integral_prod_right' (ν := α₃)
        (f := fun z : (SL3 × ℝ) × ℝ => f (z.1.1 * e₂ z.1.2 * e₃ z.2))
        ((f.continuous.comp (by fun_prop :
          Continuous fun z : (SL3 × ℝ) × ℝ => z.1.1 * e₂ z.1.2 * e₃ z.2))).stronglyMeasurable
    exact (StronglyMeasurable.integral_prod_right' (ν := α₂) hG).aestronglyMeasurable
  calc ∫ x, ∫ y, ∫ z, f (x * y * z) ∂(α₃.map e₃) ∂(α₂.map e₂) ∂(α₁.map e₁)
      = ∫ x, ∫ y, ∫ t, f (x * y * e₃ t) ∂α₃ ∂(α₂.map e₂) ∂(α₁.map e₁) := by simp only [h1]
    _ = ∫ x, ∫ s, ∫ t, f (x * e₂ s * e₃ t) ∂α₃ ∂α₂ ∂(α₁.map e₁) := by simp only [h2]
    _ = ∫ x₁, ∫ s, ∫ t, f (e₁ x₁ * e₂ s * e₃ t) ∂α₃ ∂α₂ ∂α₁ := h3


/-! ## The two sides of the identity, both reduced to `∫ x, f (ψ x)` over `ℝ³` -/

/-- The left-hand side of `TripFubini`, rewritten as the integral over `ℝ³` of `f ∘ ψ`. -/
theorem tripFubini_lhs {e₁ e₂ e₃ : ℝ → SL3} (hc₁ : Continuous e₁) (hc₂ : Continuous e₂)
    (hc₃ : Continuous e₃) {ψ : ℝ × ℝ × ℝ → SL3} (hψ : Continuous ψ)
    (hψeq : ∀ p, e₁ p.1 * e₂ p.2.1 * e₃ p.2.2 = ψ p)
    (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x, (∀ a b : Fin 3, |toMat (ψ x) a b| ≤ M) →
      |x.1| ≤ M' ∧ |x.2.1| ≤ M' ∧ |x.2.2| ≤ M')
    {α₁ α₂ α₃ : Measure ℝ} [IsFiniteMeasureOnCompacts α₁] [IsFiniteMeasureOnCompacts α₂]
    [IsFiniteMeasureOnCompacts α₃] (f : CompactlySupportedContinuousMap SL3 ℝ) :
    ∫ x, ∫ y, ∫ z, f (x * y * z) ∂(α₃.map e₃) ∂(α₂.map e₂) ∂(α₁.map e₁)
      = ∫ p, f (ψ p) ∂(α₁.prod (α₂.prod α₃)) := by
  rw [tripFubini_alpha hc₁ hc₂ hc₃ (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) f]
  rw [Work.EKLC7.TripAux.integral_prod_prod (fun p : ℝ × ℝ × ℝ => f (ψ p))
      ((f.continuous.comp hψ).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_of_lex hlex f))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p₁ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun p₂ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun p₃ => ?_)
  exact congrArg f (hψeq (p₁, p₂, p₃))

/-- The right-hand side of `TripFubini`, rewritten as the integral over `ℝ³` of `f ∘ ψ`. -/
theorem tripFubini_rhs {e₁ e₂ e₃ : ℝ → SL3} (hc₁ : Continuous e₁) (hc₂ : Continuous e₂)
    (hc₃ : Continuous e₃) {ψ : ℝ × ℝ × ℝ → SL3}
    (hψeq : ∀ p, e₁ p.1 * e₂ p.2.1 * e₃ p.2.2 = ψ p)
    {α₁ α₂ α₃ : Measure ℝ} [SFinite α₁] [SFinite α₂] [SFinite α₃]
    (f : CompactlySupportedContinuousMap SL3 ℝ) :
    ∫ g, f g ∂(((α₁.map e₁).prod ((α₂.map e₂).prod (α₃.map e₃))).map
        (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2))
      = ∫ p, f (ψ p) ∂(α₁.prod (α₂.prod α₃)) := by
  let Φ : ℝ × ℝ × ℝ → SL3 × SL3 × SL3 := fun p => (e₁ p.1, (e₂ p.2.1, e₃ p.2.2))
  have hΦc : Continuous Φ := by
    show Continuous fun p : ℝ × ℝ × ℝ => (e₁ p.1, (e₂ p.2.1, e₃ p.2.2))
    fun_prop
  have hΦ : (α₁.map e₁).prod ((α₂.map e₂).prod (α₃.map e₃))
      = (α₁.prod (α₂.prod α₃)).map Φ := by
    have h2 : (α₂.map e₂).prod (α₃.map e₃) = (α₂.prod α₃).map (Prod.map e₂ e₃) :=
      Measure.map_prod_map α₂ α₃ hc₂.measurable hc₃.measurable
    have h1 : (α₁.map e₁).prod ((α₂.prod α₃).map (Prod.map e₂ e₃))
        = (α₁.prod (α₂.prod α₃)).map (Prod.map e₁ (Prod.map e₂ e₃)) :=
      Measure.map_prod_map α₁ (α₂.prod α₃) hc₁.measurable
        (hc₂.measurable.prodMap hc₃.measurable)
    rw [h2, h1]
    refine Measure.map_congr (Filter.Eventually.of_forall fun p => ?_)
    rfl
  calc ∫ g, f g ∂(((α₁.map e₁).prod ((α₂.map e₂).prod (α₃.map e₃))).map
        (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2))
      = ∫ u, f (u.1 * u.2.1 * u.2.2)
          ∂((α₁.map e₁).prod ((α₂.map e₂).prod (α₃.map e₃))) :=
        MeasureTheory.integral_map continuous_mult3.measurable.aemeasurable
          f.continuous.aestronglyMeasurable
    _ = ∫ u, f (u.1 * u.2.1 * u.2.2) ∂((α₁.prod (α₂.prod α₃)).map Φ) := by rw [hΦ]
    _ = ∫ p, f ((Φ p).1 * (Φ p).2.1 * (Φ p).2.2) ∂(α₁.prod (α₂.prod α₃)) :=
        MeasureTheory.integral_map hΦc.measurable.aemeasurable
          ((f.continuous.comp continuous_mult3).aestronglyMeasurable)
    _ = ∫ p, f (ψ p) ∂(α₁.prod (α₂.prod α₃)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        exact congrArg f (hψeq p)

/-! ## The main theorem -/

theorem TripFubini {e₁ e₂ e₃ : ℝ → Work.EKLContract.SL3} (hc₁ : Continuous e₁) (hc₂ : Continuous e₂) (hc₃ : Continuous e₃) {ψ : ℝ × ℝ × ℝ → Work.EKLContract.SL3} (hψ : Continuous ψ) (hψeq : ∀ x, e₁ x.1 * e₂ x.2.1 * e₃ x.2.2 = ψ x) (hlex : ∀ M : ℝ, ∃ M' : ℝ, ∀ x, (∀ a b : Fin 3, |Work.EKLContract.toMat (ψ x) a b| ≤ M) → |x.1| ≤ M' ∧ |x.2.1| ≤ M' ∧ |x.2.2| ≤ M') {α₁ α₂ α₃ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasureOnCompacts α₁] [MeasureTheory.IsFiniteMeasureOnCompacts α₂] [MeasureTheory.IsFiniteMeasureOnCompacts α₃] {μ₁ μ₂ μ₃ : MeasureTheory.Measure Work.EKLContract.SL3} [MeasureTheory.IsFiniteMeasureOnCompacts μ₁] [MeasureTheory.IsFiniteMeasureOnCompacts μ₂] [MeasureTheory.IsFiniteMeasureOnCompacts μ₃] (h₁ : μ₁ = α₁.map e₁) (h₂ : μ₂ = α₂.map e₂) (h₃ : μ₃ = α₃.map e₃) (f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) : ∫ x, ∫ y, ∫ z, f (x * y * z) ∂μ₃ ∂μ₂ ∂μ₁ = ∫ g, f g ∂((μ₁.prod (μ₂.prod μ₃)).map (fun u : Work.EKLContract.SL3 × Work.EKLContract.SL3 × Work.EKLContract.SL3 => u.1 * u.2.1 * u.2.2)) := by
  rw [h₁, h₂, h₃]
  rw [tripFubini_lhs hc₁ hc₂ hc₃ hψ hψeq hlex f]
  exact (tripFubini_rhs hc₁ hc₂ hc₃ hψeq f).symm

end Work.EKLC7
