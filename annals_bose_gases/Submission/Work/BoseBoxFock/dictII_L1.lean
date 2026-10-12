import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockII_dict
import Submission.Work.BoseBoxFock.dictIIAux.aeConvClamp
import Submission.Work.BoseBoxFock.dictIIAux.integrableOn_kBound_slots
import Submission.Work.BoseBoxFock.dictIIAux.kBoundIntegral
import Submission.Work.BoseBoxFock.dictIIAux.symmMeasRep
import Submission.Work.BoseBoxFock.dictIIAux.tendstoRhsClamp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dictII_L1` — the block-`II` dictionary for `L¹` pair kernels

`Work.BoseBoxFock.blockII_dict` proves the per-pair identity

    ½ℓ⁻³(re rowShape21 + re rowShape23) = ∫_{abox}(PᵢPⱼΨ)(QⱼQᵢΨ)k(xᵢ,xⱼ)

for a pair kernel `k` that is **measurable and bounded**.  The hypotheses that actually occur in
the `Q₂`-row instantiation are only `AEStronglyMeasurable` + `Integrable` (the honest weights are
only `L¹`), and this module removes the boundedness:

    `Work.BoseBoxFock.dictII_L1` : the same identity for `k` with
    `AEStronglyMeasurable (uncurry k) volume` and `Integrable (uncurry k) volume`.

## Route (see `dictIIDefs` for the vocabulary)

* `rowShape21_re_gen` / `rowShape23_re_gen` — the two row shapes at a **general** kernel reduce to
  the explicit triple integrals `JL21` / `JL23` of `qmqKR` (`hkm`-free copies of
  `bII_rowShape21_re` / `bII_rowShape23_re`, whose proofs never used the measurability);
* `symmMeasRep` — an a.e.-equal symmetric **measurable** representative `f` of `k`, so that the
  clamped kernels `clampK N f` are measurable, bounded and symmetric, and `blockII_dict` applies;
* `clampK N f → f` pointwise with `|clampK N f| ≤ |f|`;
* `kBoundIntegral` — the pointwise dominator `kBound ℓ f` of `qmqKR ℓ (clampK N f)` is integrable
  with `∫ kBound ≤ 4∫|f|`;
* three nested dominated-convergence theorems give `JL21 (clampK N f) → JL21 k` and
  `JL23 (clampK N f) → JL23 k`; `tendstoRhsClamp` gives the same for the first-quantised right-hand
  side;
* conclusion by `½ℓ⁻³ℓ⁻³(JL21(kₙ) + JL23(kₙ)) = LHS(kₙ) = RHS(kₙ)` (`blockII_dict`) and passage to
  the limit.

Everything in this file is `sorry`-free.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## 1. The two explicit triple integrals of the block-`II` row shapes -/

/-- **The block-`II.1` row shape at a general kernel**: `hkm`-free copy of `bII_rowShape21_re`. -/
theorem rowShape21_re_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ}
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (qmqKernel ℓ k) p).re
      = ((ℓ ^ 3)⁻¹ : ℝ) * JL21 ℓ Ψ k p := by
  have hΘs := bII_boxRestrictC_support hℓ Ψ
  have h21 := (rowShape_pinCond_gen hℓ (c := c) (Θ := boxRestrictC ℓ Ψ)
      (K := qmqKernel ℓ k) (p := p) hp hΘs).1
  have hpt : ∀ (x : Xn n) (y u : E3),
      star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k u y
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)
      = ((boxRestrictR ℓ Ψ x * qmqKR ℓ k u y
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u) : ℝ) : ℂ) := by
    intro x y u
    have h1 : star (boxRestrictC ℓ Ψ x) = ((boxRestrictR ℓ Ψ x : ℝ) : ℂ) := by
      rw [← ofReal_boxRestrictR]
      exact Complex.conj_ofReal _
    rw [qmqKernel_eq_ofReal, h1, ← ofReal_boxRestrictR]
    rw [show Work.BoseBoxFock.qmqKernelR ℓ k u y = qmqKR ℓ k u y from rfl]
    push_cast
    ring
  have hI : (∫ x : Xn n, ∫ y : E3, ∫ u : E3, star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k u y
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (((∫ x : Xn n, ∫ y : E3, ∫ u : E3, boxRestrictR ℓ Ψ x * qmqKR ℓ k u y
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) : ℝ) : ℂ) := by
    simp only [hpt]
    exact bII_integral_ofReal_iter
  have hcc : c * c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h1 : c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
      have h2 := hc
      rw [hr] at h2
      exact h2
    rw [eq_inv_of_mul_eq_one_left h1, ← Complex.ofReal_inv]
  rw [h21, hI, hcc, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [boxRestrict_triple_reduce hℓ (q := fun _ y u => qmqKR ℓ k u y) hp]
  rfl

/-- **The block-`II.2` row shape at a general kernel**: `hkm`-free copy of `bII_rowShape23_re`. -/
theorem rowShape23_re_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {k : E3 → E3 → ℝ}
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k) p).re
      = ((ℓ ^ 3)⁻¹ : ℝ) * JL23 ℓ Ψ k p := by
  have hΘs := bII_boxRestrictC_support hℓ Ψ
  have h23 := (rowShape_pinCond_gen hℓ (c := c) (Θ := boxRestrictC ℓ Ψ)
      (K := qmqKernel ℓ k) (p := p) hp hΘs).2
  have hpt : ∀ (x : Xn n) (y u : E3),
      star (boxRestrictC ℓ Ψ x) * qmqKernel ℓ k (x p.1) (x p.2)
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)
      = ((boxRestrictR ℓ Ψ x * qmqKR ℓ k (x p.1) (x p.2)
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u) : ℝ) : ℂ) := by
    intro x y u
    have h1 : star (boxRestrictC ℓ Ψ x) = ((boxRestrictR ℓ Ψ x : ℝ) : ℂ) := by
      rw [← ofReal_boxRestrictR]
      exact Complex.conj_ofReal _
    rw [qmqKernel_eq_ofReal, h1, ← ofReal_boxRestrictR]
    rw [show Work.BoseBoxFock.qmqKernelR ℓ k (x p.1) (x p.2) = qmqKR ℓ k (x p.1) (x p.2) from rfl]
    push_cast
    ring
  have hI : (∫ x : Xn n, ∫ y : E3, ∫ u : E3, star (boxRestrictC ℓ Ψ x)
        * qmqKernel ℓ k (x p.1) (x p.2)
        * boxRestrictC ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u))
      = (((∫ x : Xn n, ∫ y : E3, ∫ u : E3, boxRestrictR ℓ Ψ x * qmqKR ℓ k (x p.1) (x p.2)
          * boxRestrictR ℓ Ψ (Function.update (Function.update x p.1 y) p.2 u)) : ℝ) : ℂ) := by
    simp only [hpt]
    exact bII_integral_ofReal_iter
  have hcc : c * c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h1 : c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
      have h2 := hc
      rw [hr] at h2
      exact h2
    rw [eq_inv_of_mul_eq_one_left h1, ← Complex.ofReal_inv]
  have hcc' : (starRingEnd ℂ) c * (starRingEnd ℂ) c = (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) := by
    simpa only [hr] using hcc
  rw [h23, hI, hcc', ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [boxRestrict_triple_reduce hℓ (q := fun x _ _ => qmqKR ℓ k (x p.1) (x p.2)) hp]
  rfl

/-! ## 2. Finite-measure and integrability preliminaries -/

theorem isFiniteMeasure_cubeμ (ℓ : ℝ) (hℓ : 0 < ℓ) : IsFiniteMeasure (cubeμ ℓ) :=
  ⟨by rw [show cubeμ ℓ = (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) from rfl,
      Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ)]
      exact ENNReal.ofReal_lt_top⟩

theorem isFiniteMeasure_acubePair (ℓ : ℝ) (hℓ : 0 < ℓ) : IsFiniteMeasure (acubePair ℓ) := by
  haveI := isFiniteMeasure_cubeμ ℓ hℓ
  refine ⟨?_⟩
  rw [show (Set.univ : Set (E3 × E3)) = Set.univ ×ˢ Set.univ from by ext p; simp, acubePair,
    Measure.prod_prod, Measure.restrict_apply_univ,
    Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Integrability on the full product space restricts to the cube pair. -/
theorem integrable_acubePair_of_integrable {ℓ : ℝ} {b : E3 → E3 → ℝ}
    (hb : Integrable (Function.uncurry b) (volume : Measure (E3 × E3))) :
    Integrable (Function.uncurry b) (acubePair ℓ) := by
  have h := hb.integrableOn (s := Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)
  rw [acubePair, Measure.prod_restrict]
  exact h

/-- A continuous state is bounded on the compact centred box. -/
theorem exists_abox_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := Ψ) hΨc.continuousOn
  exact ⟨max C₀ 0, le_max_right _ _, fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)⟩

/-- The clamped kernel is integrable on the cube pair (bounded on a finite measure space). -/
theorem integrable_clampK_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {b : E3 → E3 → ℝ}
    (hbm : Measurable (Function.uncurry b)) :
    Integrable (Function.uncurry (clampK N b)) (acubePair ℓ) := by
  haveI := isFiniteMeasure_acubePair ℓ hℓ
  refine Integrable.of_bound (clampK_measurable N hbm).aestronglyMeasurable (N : ℝ) ?_
  filter_upwards with q
  simpa [Function.uncurry] using clampK_abs_le_n N b q.1 q.2

/-- The double box average of the clamped kernel is bounded by that of the kernel. -/
theorem double_integral_clampK_le {ℓ : ℝ} (hℓ : 0 < ℓ) {b : E3 → E3 → ℝ}
    (hbm : Measurable (Function.uncurry b))
    (hbi : Integrable (Function.uncurry b) (acubePair ℓ)) (N : ℕ) :
    (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |clampK N b w' y'|)
      ≤ ∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'| := by
  haveI := isFiniteMeasure_cubeμ ℓ hℓ
  haveI := isFiniteMeasure_acubePair ℓ hℓ
  have h1 : Integrable (fun q : E3 × E3 => |b q.1 q.2|) (acubePair ℓ) := by
    simpa [Function.uncurry, Real.norm_eq_abs] using hbi.abs
  have h2 : Integrable (fun q : E3 × E3 => |clampK N b q.1 q.2|) (acubePair ℓ) := by
    simpa [Function.uncurry, Real.norm_eq_abs] using (integrable_clampK_pair hℓ N hbm).abs
  rw [← MeasureTheory.integral_prod (μ := cubeμ ℓ) (ν := cubeμ ℓ)
        (f := fun q : E3 × E3 => |clampK N b q.1 q.2|) h2,
      ← MeasureTheory.integral_prod (μ := cubeμ ℓ) (ν := cubeμ ℓ)
        (f := fun q : E3 × E3 => |b q.1 q.2|) h1]
  exact MeasureTheory.integral_mono h2 h1
    (fun q => by simpa only [Function.uncurry] using clampK_abs_le N b q.1 q.2)

/-- The `kBound` of the clamped kernel is bounded by the `kBound` of the kernel, on the points
where the two one-variable slices of `|b|` are integrable. -/
theorem kBound_clampK_le {ℓ : ℝ} (hℓ : 0 < ℓ) {b : E3 → E3 → ℝ}
    (hbm : Measurable (Function.uncurry b))
    (hbi : Integrable (Function.uncurry b) (acubePair ℓ)) (N : ℕ) {u y : E3}
    (hu : Integrable (fun y' : E3 => |b u y'|) (cubeμ ℓ))
    (hy : Integrable (fun w' : E3 => |b w' y|) (cubeμ ℓ)) :
    kBound ℓ (clampK N b) (u, y) ≤ kBound ℓ b (u, y) := by
  haveI := isFiniteMeasure_cubeμ ℓ hℓ
  have h1 : |clampK N b u y| ≤ |b u y| := clampK_abs_le N b u y
  have h2 : (∫ y' in Submission.BoseGases.acube ℓ, |clampK N b u y'|)
      ≤ ∫ y' in Submission.BoseGases.acube ℓ, |b u y'| := by
    refine MeasureTheory.integral_mono ?_ hu (fun y' => clampK_abs_le N b u y')
    exact Integrable.of_bound
      (((clampK_measurable N hbm).comp (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable
      (N : ℝ) (by
        filter_upwards with y'
        simpa [Function.uncurry] using clampK_abs_le_n N b u y')
  have h3 : (∫ w' in Submission.BoseGases.acube ℓ, |clampK N b w' y|)
      ≤ ∫ w' in Submission.BoseGases.acube ℓ, |b w' y| := by
    refine MeasureTheory.integral_mono ?_ hy (fun w' => clampK_abs_le N b w' y)
    exact Integrable.of_bound
      (((clampK_measurable N hbm).comp (measurable_id.prodMk measurable_const))).norm.aestronglyMeasurable
      (N : ℝ) (by
        filter_upwards with w'
        simpa [Function.uncurry] using clampK_abs_le_n N b w' y)
  have h4 := double_integral_clampK_le hℓ hbm hbi N
  simp only [kBound]
  nlinarith [abs_nonneg ((ℓ ^ 3)⁻¹), sq_nonneg |(ℓ ^ 3)⁻¹|,
    mul_le_mul_of_nonneg_left h2 (abs_nonneg ((ℓ ^ 3)⁻¹)),
    mul_le_mul_of_nonneg_left h3 (abs_nonneg ((ℓ ^ 3)⁻¹)),
    mul_le_mul_of_nonneg_left h4 (sq_nonneg |(ℓ ^ 3)⁻¹|)]

/-- **The a.e. domination of the clamped `qmqKR` by `kBound ℓ b`.** -/
theorem qmqKR_clampK_le_kBound_ae {ℓ : ℝ} (hℓ : 0 < ℓ) {b : E3 → E3 → ℝ}
    (hbm : Measurable (Function.uncurry b))
    (hbi : Integrable (Function.uncurry b) (acubePair ℓ)) :
    ∀ᵐ y ∂(cubeμ ℓ), ∀ᵐ u ∂(cubeμ ℓ),
      ∀ N : ℕ, ‖qmqKR ℓ (clampK N b) u y‖ ≤ kBound ℓ b (u, y) := by
  haveI := isFiniteMeasure_cubeμ ℓ hℓ
  have hu : ∀ᵐ u ∂(cubeμ ℓ), Integrable (fun y' : E3 => |b u y'|) (cubeμ ℓ) := by
    have h := hbi.abs.prod_right_ae
    simpa [acubePair, Function.uncurry, Real.norm_eq_abs] using h
  have hy : ∀ᵐ y ∂(cubeμ ℓ), Integrable (fun w' : E3 => |b w' y|) (cubeμ ℓ) := by
    have h := hbi.abs.prod_left_ae
    simpa [acubePair, Function.uncurry, Real.norm_eq_abs] using h
  filter_upwards [hy] with y hy2
  filter_upwards [hu] with u hu1
  intro N
  refine le_trans (norm_qmqKR_le_kBound (integrable_clampK_pair hℓ N hbm) u y) ?_
  exact kBound_clampK_le hℓ hbm hbi N hu1 hy2

/-- Measurability of `q ↦ qmqKR ℓ b q.1 q.2` for a measurable kernel. -/
theorem measurable_qmqKR {ℓ : ℝ} {b : E3 → E3 → ℝ}
    (hbm : Measurable (Function.uncurry b)) :
    Measurable (fun q : E3 × E3 => qmqKR ℓ b q.1 q.2) := by
  have h1 : Measurable (fun q : E3 × E3 => b q.1 q.2) := hbm
  have h2 : Measurable (fun q : E3 × E3 => ∫ y' in Submission.BoseGases.acube ℓ, b q.1 y') :=
    ((hbm.stronglyMeasurable.integral_prod_right (ν := cubeμ ℓ)).measurable).comp measurable_fst
  have h3 : Measurable (fun q : E3 × E3 => ∫ w' in Submission.BoseGases.acube ℓ, b w' q.2) := by
    have hsw : StronglyMeasurable (Function.uncurry (fun y w' : E3 => b w' y)) := by
      have hsw' : Function.uncurry (fun y w' : E3 => b w' y)
          = (Function.uncurry b) ∘ Prod.swap := rfl
      rw [hsw']
      exact hbm.stronglyMeasurable.comp_measurable measurable_swap
    exact ((hsw.integral_prod_right (ν := cubeμ ℓ)).measurable).comp measurable_snd
  have h4 : Measurable (fun _ : E3 × E3 => ∫ w' in Submission.BoseGases.acube ℓ,
      ∫ y' in Submission.BoseGases.acube ℓ, b w' y') := measurable_const
  have hunfold : (fun q : E3 × E3 => qmqKR ℓ b q.1 q.2)
      = fun q : E3 × E3 => b q.1 q.2
          - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, b q.1 y')
          - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, b w' q.2)
          + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2) * (∫ w' in Submission.BoseGases.acube ℓ,
              ∫ y' in Submission.BoseGases.acube ℓ, b w' y') := by
    funext q
    rw [qmqKR]
  rw [hunfold]
  exact ((h1.sub (measurable_const.mul h2)).sub (measurable_const.mul h3)).add
    (measurable_const.mul h4)

/-- Joint measurability of the `Phi21` integrand in the `(y,u)` variables. -/
theorem measurable_Phi21_joint {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {b : E3 → E3 → ℝ} (hbm : Measurable (Function.uncurry b))
    (p : Fin n × Fin n) (x : Xn n) :
    Measurable (fun q : E3 × E3 => Phi21 ℓ Ψ b p x q.1 q.2) := by
  have hk : Measurable (fun q : E3 × E3 => qmqKR ℓ b q.2 q.1) :=
    (measurable_qmqKR hbm).comp measurable_swap
  have hupd : Continuous (fun q : E3 × E3 =>
      Function.update (Function.update x p.1 q.1) p.2 q.2) :=
    ((continuous_const : Continuous fun _ : E3 × E3 => x).update p.1 continuous_fst).update p.2
      continuous_snd
  have hunfold : (fun q : E3 × E3 => Phi21 ℓ Ψ b p x q.1 q.2)
      = fun q : E3 × E3 => Ψ x * qmqKR ℓ b q.2 q.1
          * Ψ (Function.update (Function.update x p.1 q.1) p.2 q.2) := by
    funext q
    rw [Phi21]
  rw [hunfold]
  exact (measurable_const.mul hk).mul (hΨc.comp hupd).measurable

/-- Measurability of `u ↦ Phi21 ℓ Ψ b p x y u`. -/
theorem measurable_Phi21_left {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {b : E3 → E3 → ℝ} (hbm : Measurable (Function.uncurry b))
    (p : Fin n × Fin n) (x : Xn n) (y : E3) :
    Measurable (fun u : E3 => Phi21 ℓ Ψ b p x y u) :=
  (measurable_Phi21_joint hΨc hbm p x).comp (measurable_const.prodMk measurable_id)

/-- Joint measurability of the `Phi21` integrand in `(x,y,u)`. -/
theorem measurable_Phi21_triple {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {b : E3 → E3 → ℝ} (hbm : Measurable (Function.uncurry b)) (p : Fin n × Fin n) :
    Measurable (fun z : (Xn n × E3) × E3 => Phi21 ℓ Ψ b p z.1.1 z.1.2 z.2) := by
  have hk : Measurable (fun z : (Xn n × E3) × E3 => qmqKR ℓ b z.2 z.1.2) :=
    (measurable_qmqKR hbm).comp (measurable_snd.prodMk measurable_fst.snd)
  have hupd : Continuous (fun z : (Xn n × E3) × E3 =>
      Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2) :=
    ((continuous_fst.fst.update p.1 continuous_fst.snd).update p.2 continuous_snd)
  have hunfold : (fun z : (Xn n × E3) × E3 => Phi21 ℓ Ψ b p z.1.1 z.1.2 z.2)
      = fun z : (Xn n × E3) × E3 => Ψ z.1.1 * qmqKR ℓ b z.2 z.1.2
          * Ψ (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2) := by
    funext z
    rw [Phi21]
  rw [hunfold]
  exact ((hΨc.measurable.comp measurable_fst.fst).mul hk).mul (hΨc.comp hupd).measurable

/-! ## 4. The three-level dominated convergence for `JL21` -/

/-- **The `JL21` limit**: the clamped kernels converge in the block-`II.1` triple integral. -/
theorem tendsto_JL21_clampK {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {f k : E3 → E3 → ℝ} (hfm : Measurable (Function.uncurry f))
    (hkI : Integrable (Function.uncurry k) (volume : Measure (E3 × E3)))
    (hfe : Function.uncurry f =ᵐ[volume] Function.uncurry k)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    Tendsto (fun N : ℕ => JL21 ℓ Ψ (clampK N f) p) atTop (𝓝 (JL21 ℓ Ψ k p)) := by
  haveI hνfin : IsFiniteMeasure (cubeμ ℓ) := isFiniteMeasure_cubeμ ℓ hℓ
  haveI hpairfin : IsFiniteMeasure (acubePair ℓ) := isFiniteMeasure_acubePair ℓ hℓ
  haveI hBfin : IsFiniteMeasure ((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ (le_of_lt hℓ)]
        exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound (n := n) hℓ hΨc
  have hfI : Integrable (Function.uncurry f) (volume : Measure (E3 × E3)) := hkI.congr hfe.symm
  have hfi : Integrable (Function.uncurry f) (acubePair ℓ) := integrable_acubePair_of_integrable hfI
  have hkb : Integrable (kBound ℓ f) (acubePair ℓ) := (dictIIAux.kBoundIntegral hℓ hfi).1
  have hmem_u : ∀ᵐ u ∂(cubeμ ℓ), u ∈ Submission.BoseGases.acube ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)
  have hmem_y : ∀ᵐ y ∂(cubeμ ℓ), y ∈ Submission.BoseGases.acube ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)
  have hmem_x : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)
  have hconv : ∀ᵐ y ∂(cubeμ ℓ), ∀ᵐ u ∂(cubeμ ℓ),
      Tendsto (fun N : ℕ => qmqKR ℓ (clampK N f) u y) atTop (𝓝 (qmqKR ℓ k u y)) :=
    dictIIAux.aeConvClamp (ℓ := ℓ) hkI hfe
  have hdomq : ∀ᵐ y ∂(cubeμ ℓ), ∀ᵐ u ∂(cubeμ ℓ), ∀ N : ℕ,
      ‖qmqKR ℓ (clampK N f) u y‖ ≤ kBound ℓ f (u, y) :=
    qmqKR_clampK_le_kBound_ae hℓ hfm hfi
  have hkbslice : ∀ᵐ y ∂(cubeμ ℓ), Integrable (fun u : E3 => kBound ℓ f (u, y)) (cubeμ ℓ) := by
    have h := hkb.prod_left_ae
    simpa [acubePair] using h
  have hkbuint : Integrable (fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ,
      kBound ℓ f (u, y)) (cubeμ ℓ) := by
    have h := hkb.integral_norm_prod_right
    have h' : (fun y : E3 => ∫ x in Submission.BoseGases.acube ℓ, ‖kBound ℓ f (x, y)‖)
        = fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y) := by
      funext y
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      show ‖kBound ℓ f (u, y)‖ = kBound ℓ f (u, y)
      rw [Real.norm_eq_abs, abs_of_nonneg (kBound_nonneg ℓ f (u, y))]
    rw [h'] at h
    simpa [acubePair] using h
  -- the pointwise bound of the integrand
  have hbnd_pt : ∀ {x : Xn n}, x ∈ Submission.BoseGases.abox n ℓ → ∀ {y u : E3},
      y ∈ Submission.BoseGases.acube ℓ → u ∈ Submission.BoseGases.acube ℓ → ∀ N : ℕ,
      ‖qmqKR ℓ (clampK N f) u y‖ ≤ kBound ℓ f (u, y) →
      ‖Phi21 ℓ Ψ (clampK N f) p x y u‖ ≤ C ^ 2 * kBound ℓ f (u, y) := by
    intro x hx y u hy hu N hk
    have hb1 : ‖Ψ x‖ ≤ C := hCb x hx
    have hb2 : ‖Ψ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ C :=
      hCb _ ((bII_mem_abox_update_update hp hx y u).mpr ⟨hy, hu⟩)
    have hnn : 0 ≤ kBound ℓ f (u, y) := kBound_nonneg ℓ f (u, y)
    rw [Phi21, norm_mul, norm_mul]
    calc ‖Ψ x‖ * ‖qmqKR ℓ (clampK N f) u y‖
            * ‖Ψ (Function.update (Function.update x p.1 y) p.2 u)‖
        ≤ C * kBound ℓ f (u, y) * C :=
          mul_le_mul (mul_le_mul hb1 hk (norm_nonneg _) hC0) hb2 (norm_nonneg _)
            (mul_nonneg hC0 hnn)
      _ = C ^ 2 * kBound ℓ f (u, y) := by ring
  -- the `y`-bound of the middle integral
  have hBbound : ∀ {x : Xn n}, x ∈ Submission.BoseGases.abox n ℓ → ∀ N : ℕ, ∀ᵐ y ∂(cubeμ ℓ),
      ‖∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u‖
        ≤ C ^ 2 * ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y) := by
    intro x hx N
    filter_upwards [hmem_y, hkbslice, hdomq] with y hyac hykb hydom
    calc ‖∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u‖
        ≤ ∫ u in Submission.BoseGases.acube ℓ, ‖Phi21 ℓ Ψ (clampK N f) p x y u‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u in Submission.BoseGases.acube ℓ, C ^ 2 * kBound ℓ f (u, y) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun u => norm_nonneg _) (hykb.const_mul (C ^ 2)) ?_
          filter_upwards [hydom, hmem_u] with u hudom huac
          exact hbnd_pt hx hyac huac N (hudom N)
      _ = C ^ 2 * ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y) :=
          MeasureTheory.integral_const_mul _ _
  have hinner : ∀ {x : Xn n}, x ∈ Submission.BoseGases.abox n ℓ →
      Tendsto (fun N : ℕ => ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u) atTop
        (𝓝 (∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ k p x y u)) := by
    intro x hx
    -- LEVEL A: the u-integral
    have hA : ∀ᵐ y ∂(cubeμ ℓ), Tendsto (fun N : ℕ =>
          ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u) atTop
        (𝓝 (∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ k p x y u)) := by
      filter_upwards [hmem_y, hkbslice, hconv, hdomq] with y hyac hykb hyconv hydom
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun u : E3 => C ^ 2 * kBound ℓ f (u, y))
        (fun N => (measurable_Phi21_left hΨc (clampK_measurable N hfm) p x y).aestronglyMeasurable)
        (hykb.const_mul (C ^ 2)) (fun N => ?_) ?_
      · filter_upwards [hydom, hmem_u] with u hudom huac
        exact hbnd_pt hx hyac huac N (hudom N)
      · filter_upwards [hyconv, hmem_u] with u huconv _
        have h := (tendsto_const_nhds
          (x := Ψ x * Ψ (Function.update (Function.update x p.1 y) p.2 u))).mul huconv
        simpa only [Phi21, mul_assoc, mul_left_comm, mul_comm] using h
    -- LEVEL B: the y-integral
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun y : E3 => C ^ 2 * (∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y)))
      (fun N => ?_) (hkbuint.const_mul (C ^ 2)) (fun N => ?_) hA
    · exact AEStronglyMeasurable.integral_prod_right'
        (μ := cubeμ ℓ) (ν := cubeμ ℓ)
        (f := fun q : E3 × E3 => Phi21 ℓ Ψ (clampK N f) p x q.1 q.2)
        ((measurable_Phi21_joint hΨc (clampK_measurable N hfm) p x).aestronglyMeasurable)
    · exact hBbound hx N
  -- LEVEL C: the x-integral
  have hDCT : Tendsto (fun N : ℕ => ∫ x in Submission.BoseGases.abox n ℓ,
        ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u) atTop
      (𝓝 (∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ k p x y u)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Xn n => C ^ 2 * (∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y)))
      (fun N => ?_) (integrable_const (C ^ 2 * (∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y)))) (fun N => ?_) ?_
    · refine AEStronglyMeasurable.integral_prod_right'
        (μ := (volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ))
        (ν := cubeμ ℓ)
        (f := fun q : Xn n × E3 => ∫ u in Submission.BoseGases.acube ℓ,
          Phi21 ℓ Ψ (clampK N f) p q.1 q.2 u) ?_
      exact AEStronglyMeasurable.integral_prod_right'
        (μ := ((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)).prod (cubeμ ℓ))
        (ν := cubeμ ℓ)
        (f := fun q : (Xn n × E3) × E3 => Phi21 ℓ Ψ (clampK N f) p q.1.1 q.1.2 q.2)
        (measurable_Phi21_triple hΨc (clampK_measurable N hfm) p).aestronglyMeasurable
    · filter_upwards [hmem_x] with x hx
      have hb2 := hBbound hx N
      calc ‖∫ y in Submission.BoseGases.acube ℓ,
              ∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u‖
          ≤ ∫ y in Submission.BoseGases.acube ℓ,
              ‖∫ u in Submission.BoseGases.acube ℓ, Phi21 ℓ Ψ (clampK N f) p x y u‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
              C ^ 2 * (∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y)) := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Eventually.of_forall fun y => norm_nonneg _) (hkbuint.const_mul (C ^ 2)) hb2
        _ = C ^ 2 * (∫ y in Submission.BoseGases.acube ℓ,
              ∫ u in Submission.BoseGases.acube ℓ, kBound ℓ f (u, y)) :=
            MeasureTheory.integral_const_mul _ _
    · filter_upwards [hmem_x] with x hx
      exact hinner hx
  simpa only [JL21, Phi21] using hDCT

/-! ## 5. The `JL23` limit -/

/-- Two one-variable a.e. statements give the joint one. -/
theorem ae_prod_and {ν : Measure E3} [SFinite ν] {P Q : E3 → Prop}
    (hP : ∀ᵐ u ∂ν, P u) (hQ : ∀ᵐ v ∂ν, Q v) :
    ∀ᵐ q ∂(ν.prod ν), P q.1 ∧ Q q.2 := by
  obtain ⟨s, hsP, _hsm, hs0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  obtain ⟨t, htQ, _htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp hQ)
  have hsub : {q : E3 × E3 | ¬ (P q.1 ∧ Q q.2)} ⊆ (s ×ˢ Set.univ) ∪ (Set.univ ×ˢ t) := by
    intro q hq
    rcases Classical.em (P q.1) with h1 | h1
    · refine Or.inr (Set.mem_prod.mpr ⟨Set.mem_univ _, ?_⟩)
      exact htQ fun h2 => hq ⟨h1, h2⟩
    · exact Or.inl (Set.mem_prod.mpr ⟨hsP h1, Set.mem_univ _⟩)
  rw [ae_iff]
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff]
  exact ⟨by rw [Measure.prod_prod, hs0, zero_mul],
    by rw [Measure.prod_prod, ht0, mul_zero]⟩

/-- An a.e. statement on the cube pair pulls back to the centred box along the two slots. -/
theorem ae_pair_eval_of_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {P : E3 → E3 → Prop} (hP : ∀ᵐ q ∂(acubePair ℓ), P q.1 q.2) :
    ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)), P (x p.1) (x p.2) := by
  have hnull : (volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
      {q : E3 × E3 | ¬ P q.1 q.2} = 0 := by
    rw [show (volume : Measure (E3 × E3)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) = acubePair ℓ from
      (Measure.prod_restrict _ _).symm]
    exact ae_iff.mp hP
  have hwae : (fun q : E3 × E3 =>
        ({q : E3 × E3 | ¬ P q.1 q.2}.indicator (fun _ => (1 : ℝ))) q)
      =ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)]
      fun _ => (0 : ℝ) := by
    show ∀ᵐ q ∂(volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)),
      ({q : E3 × E3 | ¬ P q.1 q.2}.indicator (fun _ => (1 : ℝ))) q = (0 : ℝ)
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hnull
    intro q hq
    by_contra hbad
    refine hq ?_
    rw [Set.indicator_of_notMem hbad]
  have hpull := Submission.BoseGases.ae_eq_pair_pullback (N := n) hℓ hp hwae
  filter_upwards [hpull] with x hx
  by_contra hbad
  have hone : ({q : E3 × E3 | ¬ P q.1 q.2}.indicator (fun _ => (1 : ℝ))) (x p.1, x p.2) = 1 :=
    Set.indicator_of_mem (by simpa using hbad) (fun _ => (1 : ℝ))
  rw [hone] at hx
  norm_num at hx

/-- The joint domination of the clamped `qmqKR` by `kBound ℓ f` on the cube pair. -/
theorem qmqKR_clampK_le_kBound_prod {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → E3 → ℝ}
    (hfm : Measurable (Function.uncurry f))
    (hfi : Integrable (Function.uncurry f) (acubePair ℓ)) :
    ∀ᵐ q ∂(acubePair ℓ), ∀ N : ℕ,
      ‖qmqKR ℓ (clampK N f) q.1 q.2‖ ≤ kBound ℓ f (q.1, q.2) := by
  have hu : ∀ᵐ u ∂(cubeμ ℓ), Integrable (fun y' : E3 => |f u y'|) (cubeμ ℓ) := by
    have h := hfi.abs.prod_right_ae
    simpa [acubePair, Function.uncurry, Real.norm_eq_abs] using h
  have hy : ∀ᵐ y ∂(cubeμ ℓ), Integrable (fun w' : E3 => |f w' y|) (cubeμ ℓ) := by
    have h := hfi.abs.prod_left_ae
    simpa [acubePair, Function.uncurry, Real.norm_eq_abs] using h
  haveI : SFinite (cubeμ ℓ) := inferInstance
  have hjoint := ae_prod_and hu hy
  filter_upwards [show ∀ᵐ q ∂(acubePair ℓ),
      Integrable (fun y' : E3 => |f q.1 y'|) (cubeμ ℓ)
        ∧ Integrable (fun w' : E3 => |f w' q.2|) (cubeμ ℓ) from hjoint] with q hq
  intro N
  exact le_trans (norm_qmqKR_le_kBound (integrable_clampK_pair hℓ N hfm) q.1 q.2)
    (kBound_clampK_le hℓ hfm hfi N hq.1 hq.2)

/-- **The a.e. (in the box) convergence of the slot-evaluated `qmqKR`.** -/
theorem ae_tendsto_qmqKR_slots {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f k : E3 → E3 → ℝ}
    (hfm : Measurable (Function.uncurry f))
    (hkI : Integrable (Function.uncurry k) (volume : Measure (E3 × E3)))
    (hfe : Function.uncurry f =ᵐ[volume] Function.uncurry k)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      Tendsto (fun N : ℕ => qmqKR ℓ (clampK N f) (x p.1) (x p.2)) atTop
        (𝓝 (qmqKR ℓ k (x p.1) (x p.2))) := by
  have hfI : Integrable (Function.uncurry f) (volume : Measure (E3 × E3)) := hkI.congr hfe.symm
  have hfi : Integrable (Function.uncurry f) (acubePair ℓ) := integrable_acubePair_of_integrable hfI
  have hkik : Integrable (Function.uncurry k) (acubePair ℓ) := integrable_acubePair_of_integrable hkI
  have hfeP : Function.uncurry f =ᵐ[acubePair ℓ] Function.uncurry k := by
    have h1 : Function.uncurry f =ᵐ[(volume : Measure (E3 × E3)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)] Function.uncurry k :=
      MeasureTheory.ae_restrict_of_ae hfe
    rwa [show (volume : Measure (E3 × E3)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) = acubePair ℓ from
      (Measure.prod_restrict _ _).symm] at h1
  -- the pointwise equality and the slice facts, pulled back to the box
  have hpt : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      f (x p.1) (x p.2) = k (x p.1) (x p.2) :=
    ae_pair_eval_of_ae (P := fun u y => f u y = k u y) hℓ hp hfeP
  have hsegu : ∀ᵐ w ∂(volume : Measure E3),
      (fun y' : E3 => f w y') =ᵐ[volume] (fun y' : E3 => k w y') :=
    Measure.ae_ae_eq_of_ae_eq_uncurry hfe
  have hsegy : ∀ᵐ y ∂(volume : Measure E3),
      (fun w' : E3 => f w' y) =ᵐ[volume] (fun w' : E3 => k w' y) := by
    have hsw : Function.uncurry (fun a b : E3 => f b a)
        =ᵐ[(volume : Measure E3).prod volume] Function.uncurry (fun a b : E3 => k b a) := by
      have h := (Measure.measurePreserving_swap (μ := (volume : Measure E3))
        (ν := (volume : Measure E3))).quasiMeasurePreserving.ae hfe
      filter_upwards [h] with z hz
      simpa [Function.uncurry, Prod.swap] using hz
    exact Measure.ae_ae_eq_of_ae_eq_uncurry hsw
  have hslicef : ∀ᵐ q ∂(acubePair ℓ),
      Integrable (fun y' : E3 => f q.1 y') (cubeμ ℓ)
        ∧ Integrable (fun w' : E3 => f w' q.2) (cubeμ ℓ) := by
    have hu : ∀ᵐ u ∂(cubeμ ℓ), Integrable (fun y' : E3 => f u y') (cubeμ ℓ) := by
      have h := hfi.prod_right_ae
      simpa only [acubePair, Function.uncurry] using h
    have hy : ∀ᵐ y ∂(cubeμ ℓ), Integrable (fun w' : E3 => f w' y) (cubeμ ℓ) := by
      have h := hfi.prod_left_ae
      simpa only [acubePair, Function.uncurry] using h
    exact ae_prod_and hu hy
  have hslicex : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      Integrable (fun y' : E3 => f (x p.1) y') (cubeμ ℓ)
        ∧ Integrable (fun w' : E3 => f w' (x p.2)) (cubeμ ℓ) :=
    ae_pair_eval_of_ae (P := fun u y => Integrable (fun y' : E3 => f u y') (cubeμ ℓ)
        ∧ Integrable (fun w' : E3 => f w' y) (cubeμ ℓ)) hℓ hp hslicef
  have hsegux : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      (fun y' : E3 => f (x p.1) y') =ᵐ[volume] (fun y' : E3 => k (x p.1) y') :=
    ae_pair_eval_of_ae (P := fun u _ => (fun y' : E3 => f u y') =ᵐ[volume]
        (fun y' : E3 => k u y')) hℓ hp
      (Measure.quasiMeasurePreserving_fst.ae (MeasureTheory.ae_restrict_of_ae hsegu))
  have hsegyx : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      (fun w' : E3 => f w' (x p.2)) =ᵐ[volume] (fun w' : E3 => k w' (x p.2)) :=
    ae_pair_eval_of_ae (P := fun _ y => (fun w' : E3 => f w' y) =ᵐ[volume]
        (fun w' : E3 => k w' y)) hℓ hp
      (Measure.quasiMeasurePreserving_snd.ae (MeasureTheory.ae_restrict_of_ae hsegy))
  -- the constant double-box row of `qmqKR`
  have hrow4 : Tendsto (fun N : ℕ => ∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, clampK N f w' y') atTop
      (𝓝 (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, k w' y')) := by
    have hDCT : Tendsto (fun N : ℕ => ∫ q, clampK N f q.1 q.2 ∂(acubePair ℓ)) atTop
        (𝓝 (∫ q, k q.1 q.2 ∂(acubePair ℓ))) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun q : E3 × E3 => |k q.1 q.2|) (fun N => ?_) hkik.abs (fun N => ?_) ?_
      · exact (clampK_measurable N hfm).aestronglyMeasurable
      · filter_upwards [hfeP] with q hq
        have hq' : f q.1 q.2 = k q.1 q.2 := hq
        rw [Real.norm_eq_abs, ← hq']
        exact clampK_abs_le N f q.1 q.2
      · filter_upwards [hfeP] with q hq
        have hq' : f q.1 q.2 = k q.1 q.2 := hq
        have h := clampK_tendsto f q.1 q.2
        rw [hq'] at h
        exact h
    have h1 : ∀ N : ℕ, (∫ q, clampK N f q.1 q.2 ∂(acubePair ℓ))
        = ∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, clampK N f w' y' := by
      intro N
      show (∫ q, clampK N f q.1 q.2 ∂((cubeμ ℓ).prod (cubeμ ℓ)))
        = ∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, clampK N f w' y'
      rw [MeasureTheory.integral_prod (μ := cubeμ ℓ) (ν := cubeμ ℓ)
        (f := fun q : E3 × E3 => clampK N f q.1 q.2) (integrable_clampK_pair hℓ N hfm)]
    have h2 : (∫ q, k q.1 q.2 ∂(acubePair ℓ))
        = ∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y' := by
      show (∫ q, k q.1 q.2 ∂((cubeμ ℓ).prod (cubeμ ℓ)))
        = ∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y'
      rw [MeasureTheory.integral_prod (μ := cubeμ ℓ) (ν := cubeμ ℓ)
        (f := fun q : E3 × E3 => k q.1 q.2) hkik]
    rw [h2] at hDCT
    refine Filter.Tendsto.congr' ?_ hDCT
    filter_upwards with N
    exact h1 N
  filter_upwards [hpt, hslicex, hsegux, hsegyx] with x hptx hsx hsegx hsegy
  have hkix : Integrable (fun y' : E3 => k (x p.1) y') (cubeμ ℓ) :=
    hsx.1.congr (MeasureTheory.ae_restrict_of_ae hsegx)
  have hkiy : Integrable (fun w' : E3 => k w' (x p.2)) (cubeμ ℓ) :=
    hsx.2.congr (MeasureTheory.ae_restrict_of_ae hsegy)
  have hrow1 : Tendsto (fun N : ℕ => clampK N f (x p.1) (x p.2)) atTop
      (𝓝 (k (x p.1) (x p.2))) := by
    have h := clampK_tendsto f (x p.1) (x p.2)
    rw [hptx] at h
    exact h
  have hrow2 : Tendsto (fun N : ℕ => ∫ y' in Submission.BoseGases.acube ℓ,
        clampK N f (x p.1) y') atTop
      (𝓝 (∫ y' in Submission.BoseGases.acube ℓ, k (x p.1) y')) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun y' : E3 => |k (x p.1) y'|) (fun N => ?_) hkix.abs (fun N => ?_) ?_
    · exact ((clampK_measurable N hfm).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_of_ae hsegx] with y' hy'
      rw [Real.norm_eq_abs, ← hy']
      exact clampK_abs_le N f (x p.1) y'
    · filter_upwards [MeasureTheory.ae_restrict_of_ae hsegx] with y' hy'
      have h := clampK_tendsto f (x p.1) y'
      rw [hy'] at h
      exact h
  have hrow3 : Tendsto (fun N : ℕ => ∫ w' in Submission.BoseGases.acube ℓ,
        clampK N f w' (x p.2)) atTop
      (𝓝 (∫ w' in Submission.BoseGases.acube ℓ, k w' (x p.2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun w' : E3 => |k w' (x p.2)|) (fun N => ?_) hkiy.abs (fun N => ?_) ?_
    · exact ((clampK_measurable N hfm).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_of_ae hsegy] with w' hw'
      rw [Real.norm_eq_abs, ← hw']
      exact clampK_abs_le N f w' (x p.2)
    · filter_upwards [MeasureTheory.ae_restrict_of_ae hsegy] with w' hw'
      have h := clampK_tendsto f w' (x p.2)
      rw [hw'] at h
      exact h
  have hcomb := ((hrow1.sub (hrow2.const_mul ((ℓ ^ 3)⁻¹))).sub
    (hrow3.const_mul ((ℓ ^ 3)⁻¹))).add (hrow4.const_mul (((ℓ ^ 3)⁻¹) ^ 2))
  simpa only [qmqKR] using hcomb

/-- Measurability of the two-slot weight `G x = ∫_y ∫_u Ψ(x[p.1↦y][p.2↦u])`. -/
theorem measurable_G {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ) (p : Fin n × Fin n) :
    Measurable (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ u in Submission.BoseGases.acube ℓ,
        Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
  have hcont : Continuous (fun z : (Xn n × E3) × E3 =>
      Ψ (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) :=
    hΨc.comp (((continuous_fst.fst.update p.1 continuous_fst.snd).update p.2 continuous_snd))
  have h1 : StronglyMeasurable (fun q : (Xn n × E3) × E3 =>
      Ψ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) :=
    hcont.stronglyMeasurable
  have h2 : StronglyMeasurable (fun q : Xn n × E3 => ∫ u in Submission.BoseGases.acube ℓ,
      Ψ (Function.update (Function.update q.1 p.1 q.2) p.2 u)) :=
    h1.integral_prod_right' (ν := cubeμ ℓ)
  have h3 : StronglyMeasurable (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ u in Submission.BoseGases.acube ℓ,
        Ψ (Function.update (Function.update x p.1 y) p.2 u)) :=
    h2.integral_prod_right' (ν := cubeμ ℓ)
  exact h3.measurable

/-- **The `JL23` limit**: the clamped kernels converge in the block-`II.2` triple integral. -/
theorem tendsto_JL23_clampK {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} (hΨc : Continuous Ψ)
    {f k : E3 → E3 → ℝ} (hfm : Measurable (Function.uncurry f))
    (hkI : Integrable (Function.uncurry k) (volume : Measure (E3 × E3)))
    (hfe : Function.uncurry f =ᵐ[volume] Function.uncurry k)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    Tendsto (fun N : ℕ => ∫ x in Submission.BoseGases.abox n ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Phi23 ℓ Ψ (clampK N f) p x y u) atTop
      (𝓝 (∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ, Phi23 ℓ Ψ k p x y u)) := by
  haveI hBfin : IsFiniteMeasure ((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume n ℓ (le_of_lt hℓ)]
        exact ENNReal.ofReal_lt_top⟩
  haveI hνfin : IsFiniteMeasure (cubeμ ℓ) := isFiniteMeasure_cubeμ ℓ hℓ
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound (n := n) hℓ hΨc
  set Cg : ℝ := (C * ℓ ^ 3) * ℓ ^ 3 with hCgdef
  have hCg0 : 0 ≤ Cg := by
    rw [hCgdef]
    exact mul_nonneg (mul_nonneg hC0 (pow_nonneg (le_of_lt hℓ) 3)) (pow_nonneg (le_of_lt hℓ) 3)
  have hfI : Integrable (Function.uncurry f) (volume : Measure (E3 × E3)) := hkI.congr hfe.symm
  have hfi : Integrable (Function.uncurry f) (acubePair ℓ) := integrable_acubePair_of_integrable hfI
  have hkb : Integrable (kBound ℓ f) (acubePair ℓ) := (dictIIAux.kBoundIntegral hℓ hfi).1
  have hkbx : IntegrableOn (fun x : Xn n => kBound ℓ f (x p.1, x p.2))
      (Submission.BoseGases.abox n ℓ) (volume : Measure (Xn n)) :=
    dictIIAux.integrableOn_kBound_slots hℓ hp hkb
  -- the pulled-out weight of the two slot integrations
  set G : Xn n → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
    ∫ u in Submission.BoseGases.acube ℓ,
      Ψ (Function.update (Function.update x p.1 y) p.2 u) with hGdef
  have hGm : Measurable G := measurable_G hΨc p
  have hGbound : ∀ x ∈ Submission.BoseGases.abox n ℓ, ‖G x‖ ≤ Cg := by
    intro x hx
    have hinner : ∀ y ∈ Submission.BoseGases.acube ℓ, ‖∫ u in Submission.BoseGases.acube ℓ,
        Ψ (Function.update (Function.update x p.1 y) p.2 u)‖ ≤ C * ℓ ^ 3 := by
      intro y hy
      refine le_trans (norm_integral_le_integral_norm _) ?_
      have hmono : (∫ u in Submission.BoseGases.acube ℓ,
            ‖Ψ (Function.update (Function.update x p.1 y) p.2 u)‖)
          ≤ ∫ u in Submission.BoseGases.acube ℓ, C :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => norm_nonneg _) (integrable_const C)
          (by
            filter_upwards [MeasureTheory.self_mem_ae_restrict
              (Submission.BoseGases.acube_measurable ℓ)] with u hu
            exact hCb _ ((bII_mem_abox_update_update hp hx y u).mpr ⟨hy, hu⟩))
      refine le_trans hmono ?_
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm,
        MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ),
        ENNReal.toReal_ofReal (by positivity)]
    rw [hGdef]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hmono : (∫ y in Submission.BoseGases.acube ℓ,
          ‖∫ u in Submission.BoseGases.acube ℓ,
            Ψ (Function.update (Function.update x p.1 y) p.2 u)‖)
        ≤ ∫ y in Submission.BoseGases.acube ℓ, C * ℓ ^ 3 :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => norm_nonneg _) (integrable_const _)
        (by
          filter_upwards [MeasureTheory.self_mem_ae_restrict
            (Submission.BoseGases.acube_measurable ℓ)] with y hy
          exact hinner y hy)
    refine le_trans hmono ?_
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm,
      MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ),
      ENNReal.toReal_ofReal (by positivity), hCgdef]
  -- the split form of the integrand
  have hsplit : ∀ g : E3 → E3 → ℝ, (∫ x in Submission.BoseGases.abox n ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Phi23 ℓ Ψ g p x y u)
      = ∫ x in Submission.BoseGases.abox n ℓ, (Ψ x * qmqKR ℓ g (x p.1) (x p.2)) * G x := by
    intro g
    have h0 : (fun x : Xn n => ∫ y in Submission.BoseGases.acube ℓ,
          ∫ u in Submission.BoseGases.acube ℓ, Phi23 ℓ Ψ g p x y u)
        = fun x : Xn n => (Ψ x * qmqKR ℓ g (x p.1) (x p.2)) * G x := by
      funext x
      show (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Phi23 ℓ Ψ g p x y u) = (Ψ x * qmqKR ℓ g (x p.1) (x p.2)) * G x
      have h1 : (fun y : E3 => ∫ u in Submission.BoseGases.acube ℓ, Phi23 ℓ Ψ g p x y u)
          = fun y : E3 => (Ψ x * qmqKR ℓ g (x p.1) (x p.2))
              * (∫ u in Submission.BoseGases.acube ℓ,
                  Ψ (Function.update (Function.update x p.1 y) p.2 u)) := by
        funext y
        show (∫ u in Submission.BoseGases.acube ℓ, Phi23 ℓ Ψ g p x y u)
            = (Ψ x * qmqKR ℓ g (x p.1) (x p.2))
              * (∫ u in Submission.BoseGases.acube ℓ,
                  Ψ (Function.update (Function.update x p.1 y) p.2 u))
        simp only [Phi23]
        rw [MeasureTheory.integral_const_mul]
      rw [h1, MeasureTheory.integral_const_mul, hGdef]
    rw [h0]
  -- the a.e. convergence and domination at the slots
  have hconvx := ae_tendsto_qmqKR_slots hℓ hfm hkI hfe hp
  have hdomj := qmqKR_clampK_le_kBound_prod hℓ hfm hfi
  have hdomx : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      ∀ N : ℕ, ‖qmqKR ℓ (clampK N f) (x p.1) (x p.2)‖ ≤ kBound ℓ f (x p.1, x p.2) :=
    ae_pair_eval_of_ae (P := fun u y => ∀ N : ℕ,
      ‖qmqKR ℓ (clampK N f) u y‖ ≤ kBound ℓ f (u, y)) hℓ hp hdomj
  have hmem_x : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (Submission.BoseGases.abox n ℓ)),
      x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)
  have hDCT : Tendsto (fun N : ℕ => ∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x * qmqKR ℓ (clampK N f) (x p.1) (x p.2)) * G x) atTop
      (𝓝 (∫ x in Submission.BoseGases.abox n ℓ,
        (Ψ x * qmqKR ℓ k (x p.1) (x p.2)) * G x)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : Xn n => C * (kBound ℓ f (x p.1, x p.2) * Cg)) (fun N => ?_) ?_ (fun N => ?_) ?_
    · exact ((hΨc.measurable.mul
        ((measurable_qmqKR (clampK_measurable N hfm)).comp
          ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)))).mul hGm).aestronglyMeasurable
    · exact (hkbx.mul_const Cg).const_mul C
    · filter_upwards [hmem_x, hdomx] with x hx hdom
      have h1 : ‖Ψ x‖ ≤ C := hCb x hx
      have h2 : ‖G x‖ ≤ Cg := hGbound x hx
      have h3 : ‖qmqKR ℓ (clampK N f) (x p.1) (x p.2)‖ ≤ kBound ℓ f (x p.1, x p.2) := hdom N
      have h4 : 0 ≤ kBound ℓ f (x p.1, x p.2) := kBound_nonneg ℓ f (x p.1, x p.2)
      rw [norm_mul, norm_mul]
      calc ‖Ψ x‖ * ‖qmqKR ℓ (clampK N f) (x p.1) (x p.2)‖ * ‖G x‖
          ≤ C * kBound ℓ f (x p.1, x p.2) * Cg :=
            mul_le_mul (mul_le_mul h1 h3 (norm_nonneg _) hC0) h2 (norm_nonneg _)
              (mul_nonneg hC0 h4)
        _ = C * (kBound ℓ f (x p.1, x p.2) * Cg) := by ring
    · filter_upwards [hconvx] with x hx
      have h := (tendsto_const_nhds (x := Ψ x * G x)).mul hx
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  rw [hsplit k]
  refine Filter.Tendsto.congr' ?_ hDCT
  filter_upwards with N
  exact (hsplit (clampK N f)).symm

/-! ## 7. The target -/

theorem dictII_L1 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (hΨsym : Submission.BoseGases.PermInvariant n Ψ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : MeasureTheory.AEStronglyMeasurable (Function.uncurry k) MeasureTheory.volume)
    (hkI : MeasureTheory.Integrable (Function.uncurry k) MeasureTheory.volume)
    (hksym : ∀ w y, k w y = k y w)
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((Work.BoseBoxFock.rowShape21 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
            (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (Work.BoseBoxFock.qmqKernel ℓ k) p).re
          + (Work.BoseBoxFock.rowShape23 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (Work.BoseBoxFock.qmqKernel ℓ k) p).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
            * k (x p.1) (x p.2) := by
  obtain ⟨f, hfmeas, hfsym, hfe⟩ := dictIIAux.symmMeasRep (f := k) hkm (fun w y => (hksym w y).symm)
  -- the two row shapes along the clamped kernels
  have h21lim : Tendsto (fun N : ℕ =>
        (rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (qmqKernel ℓ (clampK N f)) p).re) atTop
      (𝓝 ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (qmqKernel ℓ k) p).re)) := by
    have hfun : (fun N : ℕ =>
          (rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ (clampK N f)) p).re)
        = fun N : ℕ => ((ℓ ^ 3)⁻¹ : ℝ) * JL21 ℓ Ψ (clampK N f) p := by
      funext N
      exact rowShape21_re_gen (k := clampK N f) hℓ hΨc hc hr hp
    rw [hfun]
    rw [rowShape21_re_gen (k := k) hℓ hΨc hc hr hp]
    exact (tendsto_JL21_clampK hℓ hΨc hfmeas hkI hfe hp).const_mul ((ℓ ^ 3)⁻¹)
  have h23lim : Tendsto (fun N : ℕ =>
        (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (qmqKernel ℓ (clampK N f)) p).re) atTop
      (𝓝 ((rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (qmqKernel ℓ k) p).re)) := by
    have hfun : (fun N : ℕ =>
          (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ (clampK N f)) p).re)
        = fun N : ℕ => ((ℓ ^ 3)⁻¹ : ℝ) * JL23 ℓ Ψ (clampK N f) p := by
      funext N
      exact rowShape23_re_gen (k := clampK N f) hℓ hΨc hc hr hp
    rw [hfun]
    rw [rowShape23_re_gen (k := k) hℓ hΨc hc hr hp]
    simpa only [JL23, Phi23] using
      (tendsto_JL23_clampK (ℓ := ℓ) hℓ hΨc hfmeas hkI hfe hp).const_mul ((ℓ ^ 3)⁻¹)
  have hLHSlim : Tendsto (fun N : ℕ => (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ (clampK N f)) p).re
          + (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ (clampK N f)) p).re)) atTop
      (𝓝 ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ k) p).re
          + (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ k) p).re))) :=
    Filter.Tendsto.const_mul ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ)) (h21lim.add h23lim)
  have hRHSlim := dictIIAux.tendstoRhsClamp (ℓ := ℓ) hℓ hΨc hkI hfe hp
  have hEq : ∀ N : ℕ, (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ (clampK N f)) p).re
          + (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ (clampK N f)) p).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
            * clampK N f (x p.1) (x p.2) :=
    fun N => blockII_dict hℓ hΨc hΨsym (clampK_measurable N hfmeas)
      ⟨(N : ℝ), fun w y => clampK_abs_le_n N f w y⟩ (clampK_symm hfsym N) hc hr hp
  have hLHSlim' : Tendsto (fun N : ℕ => ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
          * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
          * clampK N f (x p.1) (x p.2)) atTop
      (𝓝 ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
        ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ k) p).re
          + (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ k) p).re))) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun N => hEq N) hLHSlim
  exact tendsto_nhds_unique hLHSlim' hRHSlim

end Work.BoseBoxFock
