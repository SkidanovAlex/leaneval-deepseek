import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockIIDefs
import Submission.Work.BoseBoxFock.pairingP1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxProj_pairing`

The two-variable box projection `boxProj ℓ` of `Submission/Work/BoseBoxFock/blockIIDefs.lean` is
the operator `(1 − P₁)(1 − P₂)` on functions of two box variables, where `P₁`, `P₂` are the
normalised box averages in the first and in the second variable.  Its three factors `P₁`, `P₂`,
`P₁P₂` are each self-adjoint for the box pairing `⟨f, g⟩ = ∫_{Λ}∫_{Λ} f·g`, hence so is the
projection:

  `⟨F, boxProj ℓ k⟩ = ⟨boxProj ℓ F, k⟩`

which is the lemma `boxProj_pairing` below (the `Q M Q` pairing identity for the two-variable
kernel form used by the `blockII` dictionary).

The file is organised in two layers:

* an abstract layer, for an arbitrary finite measure space `(α, μ)` and BOUNDED kernels:
  `integrable_of_abs_le`, `abs_integral_le_of_abs_le`, `integrable_mul_of_abs_le` (the
  bounded-on-a-finite-measure toolbox); `pairingP1` (the first box average is self-adjoint;
  delegated to `Submission/Work/BoseBoxFock/pairingP1.lean`), `pairingP2` (the second box average
  is self-adjoint), `pairingP12` (the product of the two averages is self-adjoint); and
  `boxProj_pairing_general` — the pairing identity for the expanded projection, obtained by
  linearity of the double integral from the three self-adjointness identities;
* the concrete layer: `boxProj_expand` (the definitional expansion of `boxProj`), `boxProj_congr`
  (the projection only depends on the values on the box) and, finally, `boxProj_pairing`, where
  the continuity of `F` supplies the box bound needed by the abstract layer.

Everything is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Bounded kernels on a finite measure space -/

section Abstract

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsFiniteMeasure μ]

/-- A pointwise bounded a.e. strongly measurable real function on a finite measure space is
integrable. -/
theorem integrable_of_abs_le {g : α → ℝ} {C : ℝ} (hC : 0 ≤ C) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)

/-- Integral bound for a pointwise bounded function. -/
theorem abs_integral_le_of_abs_le {g : α → ℝ} {C : ℝ} (hC : 0 ≤ C) (hg : StronglyMeasurable g)
    (hb : ∀ x, |g x| ≤ C) : |∫ x, g x ∂μ| ≤ C * μ.real Set.univ := by
  have hgi : Integrable g μ := integrable_of_abs_le hC hg.aestronglyMeasurable hb
  have hCi : Integrable (fun _ : α => C) μ :=
    integrable_of_abs_le hC stronglyMeasurable_const.aestronglyMeasurable
      (fun _ => by simpa [abs_of_nonneg hC])
  calc |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C ∂μ := integral_mono hgi.abs hCi (fun x => hb x)
    _ = C * μ.real Set.univ := by
        rw [MeasureTheory.integral_const]
        simp [smul_eq_mul, mul_comm]

/-- A product of pointwise bounded a.e. strongly measurable functions is integrable on a finite
measure space. -/
theorem integrable_mul_of_abs_le {f g : α → ℝ} {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ N) : Integrable (fun x => f x * g x) μ :=
  Integrable.of_bound (hf.mul hg) (M * N) (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) hM)

/-- **The second box average is self-adjoint** for the box pairing. -/
theorem pairingP2 {f g : α → α → ℝ} {M N r : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfb : ∀ a b, |f a b| ≤ M) (hgb : ∀ a b, |g a b| ≤ N) :
    (∫ a, ∫ b, f a b * (r * ∫ b', g a b' ∂μ) ∂μ ∂μ)
      = ∫ a, ∫ b, (r * ∫ b', f a b' ∂μ) * g a b ∂μ ∂μ := by
  have h1 : ∀ a, (∫ b, f a b * (r * ∫ b', g a b' ∂μ) ∂μ)
      = (∫ b, f a b ∂μ) * (r * (∫ b', g a b' ∂μ)) := fun a =>
    MeasureTheory.integral_mul_const _ _
  have h2 : ∀ a, (∫ b, (r * ∫ b', f a b' ∂μ) * g a b ∂μ)
      = (r * (∫ b, f a b ∂μ)) * (∫ b, g a b ∂μ) := fun a =>
    MeasureTheory.integral_const_mul _ _
  simp only [h1, h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)

/-- **The product of the two box averages is self-adjoint** for the box pairing. -/
theorem pairingP12 {f g : α → α → ℝ} {r : ℝ} :
    (∫ a, ∫ b, f a b * (r * ∫ a', ∫ b', g a' b' ∂μ ∂μ) ∂μ ∂μ)
      = ∫ a, ∫ b, (r * ∫ a', ∫ b', f a' b' ∂μ ∂μ) * g a b ∂μ ∂μ := by
  have h1 : (∫ a, ∫ b, f a b * (r * (∫ a', ∫ b', g a' b' ∂μ ∂μ)) ∂μ ∂μ)
      = (∫ a, ∫ b, f a b ∂μ ∂μ) * (r * (∫ a', ∫ b', g a' b' ∂μ ∂μ)) := by
    rw [← MeasureTheory.integral_mul_const (r * (∫ a', ∫ b', g a' b' ∂μ ∂μ))
      (fun a => ∫ b, f a b ∂μ)]
    have hpt : ∀ a, (∫ b, f a b * (r * (∫ a', ∫ b', g a' b' ∂μ ∂μ)) ∂μ)
        = (∫ b, f a b ∂μ) * (r * (∫ a', ∫ b', g a' b' ∂μ ∂μ)) := fun a =>
      MeasureTheory.integral_mul_const _ _
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h2 : (∫ a, ∫ b, (r * (∫ a', ∫ b', f a' b' ∂μ ∂μ)) * g a b ∂μ ∂μ)
      = (r * (∫ a', ∫ b', f a' b' ∂μ ∂μ)) * (∫ a, ∫ b, g a b ∂μ ∂μ) := by
    rw [← MeasureTheory.integral_const_mul (r * (∫ a', ∫ b', f a' b' ∂μ ∂μ))
      (fun a => ∫ b, g a b ∂μ)]
    have hpt : ∀ a, (∫ b, (r * (∫ a', ∫ b', f a' b' ∂μ ∂μ)) * g a b ∂μ)
        = (r * (∫ a', ∫ b', f a' b' ∂μ ∂μ)) * (∫ b, g a b ∂μ) := fun a =>
      MeasureTheory.integral_const_mul _ _
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [h1, h2]
  ring

/-- **Self-adjointness of the expanded two-variable box projection** `(1 − P₁)(1 − P₂)`, for
bounded measurable kernels on a finite measure space. -/
theorem boxProj_pairing_general {F k : α → α → ℝ} {MF C r : ℝ} (hMF : 0 ≤ MF) (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hk : Measurable (Function.uncurry k))
    (hFb : ∀ a b, |F a b| ≤ MF) (hkb : ∀ a b, |k a b| ≤ C) :
    (∫ a, ∫ b, F a b * (k a b - r * (∫ a', k a' b ∂μ) - r * (∫ b', k a b' ∂μ)
        + r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)) ∂μ ∂μ)
      = ∫ a, ∫ b, (F a b - r * (∫ a', F a' b ∂μ) - r * (∫ b', F a b' ∂μ)
        + r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k a b ∂μ ∂μ := by
  have hks : StronglyMeasurable (Function.uncurry k) := hk.stronglyMeasurable
  have hFs : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable
  have hVnn : 0 ≤ μ.real Set.univ := MeasureTheory.measureReal_nonneg
  -- ### bounds on the one- and two-variable box averages
  have hbK₂ : ∀ b : α, |∫ a', k a' b ∂μ| ≤ C * μ.real Set.univ := fun b =>
    abs_integral_le_of_abs_le hC (hks.comp_measurable (measurable_id.prodMk measurable_const))
      (fun a' => hkb a' b)
  have hbK₁ : ∀ a : α, |∫ b', k a b' ∂μ| ≤ C * μ.real Set.univ := fun a =>
    abs_integral_le_of_abs_le hC (hks.comp_measurable (measurable_const.prodMk measurable_id))
      (fun b' => hkb a b')
  have hbKK : |∫ a', ∫ b', k a' b' ∂μ ∂μ| ≤ C * (μ.real Set.univ) ^ 2 := by
    have h : |∫ a, ∫ b, k a b ∂μ ∂μ| ≤ (C * μ.real Set.univ) * μ.real Set.univ :=
      abs_integral_le_of_abs_le (μ := μ) (g := fun a => ∫ b, k a b ∂μ)
        (mul_nonneg hC hVnn) hks.integral_prod_right hbK₁
    calc |∫ a', ∫ b', k a' b' ∂μ ∂μ| ≤ (C * μ.real Set.univ) * μ.real Set.univ := h
      _ = C * (μ.real Set.univ) ^ 2 := by ring
  have hbF₂ : ∀ b : α, |∫ a', F a' b ∂μ| ≤ MF * μ.real Set.univ := fun b =>
    abs_integral_le_of_abs_le hMF (hFs.comp_measurable (measurable_id.prodMk measurable_const))
      (fun a' => hFb a' b)
  have hbF₁ : ∀ a : α, |∫ b', F a b' ∂μ| ≤ MF * μ.real Set.univ := fun a =>
    abs_integral_le_of_abs_le hMF (hFs.comp_measurable (measurable_const.prodMk measurable_id))
      (fun b' => hFb a b')
  have hbFF : |∫ a', ∫ b', F a' b' ∂μ ∂μ| ≤ MF * (μ.real Set.univ) ^ 2 := by
    have h : |∫ a, ∫ b, F a b ∂μ ∂μ| ≤ (MF * μ.real Set.univ) * μ.real Set.univ :=
      abs_integral_le_of_abs_le (μ := μ) (g := fun a => ∫ b, F a b ∂μ)
        (mul_nonneg hMF hVnn) hFs.integral_prod_right hbF₁
    calc |∫ a', ∫ b', F a' b' ∂μ ∂μ| ≤ (MF * μ.real Set.univ) * μ.real Set.univ := h
      _ = MF * (μ.real Set.univ) ^ 2 := by ring
  -- ### measurability of the averaged factors
  have hsmA₂ : AEStronglyMeasurable (fun z : α × α => r * (∫ a', k a' z.2 ∂μ)) (μ.prod μ) :=
    AEStronglyMeasurable.mul (f := fun _ : α × α => r)
      (g := fun z : α × α => ∫ a', k a' z.2 ∂μ)
      stronglyMeasurable_const.aestronglyMeasurable
      (hks.integral_prod_left.comp_measurable measurable_snd).aestronglyMeasurable
  have hsmB₂ : AEStronglyMeasurable (fun z : α × α => r * (∫ b', k z.1 b' ∂μ)) (μ.prod μ) :=
    AEStronglyMeasurable.mul (f := fun _ : α × α => r)
      (g := fun z : α × α => ∫ b', k z.1 b' ∂μ)
      stronglyMeasurable_const.aestronglyMeasurable
      (hks.integral_prod_right.comp_measurable measurable_fst).aestronglyMeasurable
  have hsmA₁ : AEStronglyMeasurable (fun z : α × α => r * (∫ a', F a' z.2 ∂μ)) (μ.prod μ) :=
    AEStronglyMeasurable.mul (f := fun _ : α × α => r)
      (g := fun z : α × α => ∫ a', F a' z.2 ∂μ)
      stronglyMeasurable_const.aestronglyMeasurable
      (hFs.integral_prod_left.comp_measurable measurable_snd).aestronglyMeasurable
  have hsmB₁ : AEStronglyMeasurable (fun z : α × α => r * (∫ b', F z.1 b' ∂μ)) (μ.prod μ) :=
    AEStronglyMeasurable.mul (f := fun _ : α × α => r)
      (g := fun z : α × α => ∫ b', F z.1 b' ∂μ)
      stronglyMeasurable_const.aestronglyMeasurable
      (hFs.integral_prod_right.comp_measurable measurable_fst).aestronglyMeasurable
  have hsmD₂ : AEStronglyMeasurable
      (fun _ : α × α => r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)) (μ.prod μ) :=
    stronglyMeasurable_const.aestronglyMeasurable
  have hsmD₁ : AEStronglyMeasurable
      (fun _ : α × α => r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) (μ.prod μ) :=
    stronglyMeasurable_const.aestronglyMeasurable
  -- ### pointwise bounds for the averaged factors
  have hbA₂ : ∀ z : α × α, |r * (∫ a', k a' z.2 ∂μ)| ≤ |r| * (C * μ.real Set.univ) := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbK₂ z.2) (abs_nonneg r)
  have hbB₂ : ∀ z : α × α, |r * (∫ b', k z.1 b' ∂μ)| ≤ |r| * (C * μ.real Set.univ) := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbK₁ z.1) (abs_nonneg r)
  have hbA₁ : ∀ z : α × α, |r * (∫ a', F a' z.2 ∂μ)| ≤ |r| * (MF * μ.real Set.univ) := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbF₂ z.2) (abs_nonneg r)
  have hbB₁ : ∀ z : α × α, |r * (∫ b', F z.1 b' ∂μ)| ≤ |r| * (MF * μ.real Set.univ) := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbF₁ z.1) (abs_nonneg r)
  have hbD₂ : ∀ _ : α × α,
      |r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)| ≤ |r ^ 2| * (C * (μ.real Set.univ) ^ 2) :=
    fun _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hbKK (abs_nonneg (r ^ 2))
  have hbD₁ : ∀ _ : α × α,
      |r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)| ≤ |r ^ 2| * (MF * (μ.real Set.univ) ^ 2) :=
    fun _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hbFF (abs_nonneg (r ^ 2))
  -- ### integrability of the seven integrands
  have hI1 : Integrable (fun z : α × α => F z.1 z.2 * k z.1 z.2) (μ.prod μ) :=
    integrable_mul_of_abs_le hMF hC hFs.aestronglyMeasurable hks.aestronglyMeasurable
      (fun z => hFb z.1 z.2) (fun z => hkb z.1 z.2)
  have hI2 : Integrable (fun z : α × α => F z.1 z.2 * (r * (∫ a', k a' z.2 ∂μ)))
      (μ.prod μ) :=
    integrable_mul_of_abs_le hMF (mul_nonneg (abs_nonneg r) (mul_nonneg hC hVnn))
      hFs.aestronglyMeasurable hsmA₂ (fun z => hFb z.1 z.2) hbA₂
  have hI3 : Integrable (fun z : α × α => F z.1 z.2 * (r * (∫ b', k z.1 b' ∂μ)))
      (μ.prod μ) :=
    integrable_mul_of_abs_le hMF (mul_nonneg (abs_nonneg r) (mul_nonneg hC hVnn))
      hFs.aestronglyMeasurable hsmB₂ (fun z => hFb z.1 z.2) hbB₂
  have hI4 : Integrable
      (fun z : α × α => F z.1 z.2 * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ))) (μ.prod μ) :=
    integrable_mul_of_abs_le hMF
      (mul_nonneg (abs_nonneg (r ^ 2)) (mul_nonneg hC (pow_nonneg hVnn 2)))
      hFs.aestronglyMeasurable hsmD₂ (fun z => hFb z.1 z.2) hbD₂
  have hJ2 : Integrable (fun z : α × α => (r * (∫ a', F a' z.2 ∂μ)) * k z.1 z.2)
      (μ.prod μ) :=
    integrable_mul_of_abs_le (mul_nonneg (abs_nonneg r) (mul_nonneg hMF hVnn)) hC
      hsmA₁ hks.aestronglyMeasurable hbA₁ (fun z => hkb z.1 z.2)
  have hJ3 : Integrable (fun z : α × α => (r * (∫ b', F z.1 b' ∂μ)) * k z.1 z.2)
      (μ.prod μ) :=
    integrable_mul_of_abs_le (mul_nonneg (abs_nonneg r) (mul_nonneg hMF hVnn)) hC
      hsmB₁ hks.aestronglyMeasurable hbB₁ (fun z => hkb z.1 z.2)
  have hJ4 : Integrable
      (fun z : α × α => (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k z.1 z.2) (μ.prod μ) :=
    integrable_mul_of_abs_le
      (mul_nonneg (abs_nonneg (r ^ 2)) (mul_nonneg hMF (pow_nonneg hVnn 2))) hC
      hsmD₁ hks.aestronglyMeasurable hbD₁ (fun z => hkb z.1 z.2)
  -- ### the two linearity expansions
  have hL : (∫ a, ∫ b, F a b * (k a b - r * (∫ a', k a' b ∂μ) - r * (∫ b', k a b' ∂μ)
        + r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)) ∂μ ∂μ)
      = (∫ a, ∫ b, F a b * k a b ∂μ ∂μ)
        - (∫ a, ∫ b, F a b * (r * (∫ a', k a' b ∂μ)) ∂μ ∂μ)
        - (∫ a, ∫ b, F a b * (r * (∫ b', k a b' ∂μ)) ∂μ ∂μ)
        + (∫ a, ∫ b, F a b * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)) ∂μ ∂μ) := by
    have hregroup : (∫ a, ∫ b, F a b * (k a b - r * (∫ a', k a' b ∂μ) - r * (∫ b', k a b' ∂μ)
          + r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)) ∂μ ∂μ)
        = ∫ a, ∫ b, ((F a b * k a b - F a b * (r * (∫ a', k a' b ∂μ)))
            - (F a b * (r * (∫ b', k a b' ∂μ))
              - F a b * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ)))) ∂μ ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun b => by ring)
    rw [hregroup]
    have hs1 : Integrable (fun z : α × α =>
        F z.1 z.2 * k z.1 z.2 - F z.1 z.2 * (r * (∫ a', k a' z.2 ∂μ))) (μ.prod μ) :=
      hI1.sub hI2
    have hs2 : Integrable (fun z : α × α =>
        F z.1 z.2 * (r * (∫ b', k z.1 b' ∂μ))
          - F z.1 z.2 * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ))) (μ.prod μ) :=
      hI3.sub hI4
    rw [MeasureTheory.integral_integral_sub
      (f := fun z : α × α => F z.1 z.2 * k z.1 z.2 - F z.1 z.2 * (r * (∫ a', k a' z.2 ∂μ)))
      (g := fun z : α × α => F z.1 z.2 * (r * (∫ b', k z.1 b' ∂μ))
        - F z.1 z.2 * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ))) hs1 hs2]
    rw [MeasureTheory.integral_integral_sub (f := fun z : α × α => F z.1 z.2 * k z.1 z.2)
      (g := fun z : α × α => F z.1 z.2 * (r * (∫ a', k a' z.2 ∂μ))) hI1 hI2]
    rw [MeasureTheory.integral_integral_sub
      (f := fun z : α × α => F z.1 z.2 * (r * (∫ b', k z.1 b' ∂μ)))
      (g := fun z : α × α => F z.1 z.2 * (r ^ 2 * (∫ a', ∫ b', k a' b' ∂μ ∂μ))) hI3 hI4]
    dsimp only
    ring
  have hR : (∫ a, ∫ b, (F a b - r * (∫ a', F a' b ∂μ) - r * (∫ b', F a b' ∂μ)
        + r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k a b ∂μ ∂μ)
      = (∫ a, ∫ b, F a b * k a b ∂μ ∂μ)
        - (∫ a, ∫ b, (r * (∫ a', F a' b ∂μ)) * k a b ∂μ ∂μ)
        - (∫ a, ∫ b, (r * (∫ b', F a b' ∂μ)) * k a b ∂μ ∂μ)
        + (∫ a, ∫ b, (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k a b ∂μ ∂μ) := by
    have hregroup : (∫ a, ∫ b, (F a b - r * (∫ a', F a' b ∂μ) - r * (∫ b', F a b' ∂μ)
          + r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k a b ∂μ ∂μ)
        = ∫ a, ∫ b, ((F a b * k a b - (r * (∫ a', F a' b ∂μ)) * k a b)
            - ((r * (∫ b', F a b' ∂μ)) * k a b
              - (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k a b)) ∂μ ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun b => by ring)
    rw [hregroup]
    have hs1 : Integrable (fun z : α × α =>
        F z.1 z.2 * k z.1 z.2 - (r * (∫ a', F a' z.2 ∂μ)) * k z.1 z.2) (μ.prod μ) :=
      hI1.sub hJ2
    have hs2 : Integrable (fun z : α × α =>
        (r * (∫ b', F z.1 b' ∂μ)) * k z.1 z.2
          - (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k z.1 z.2) (μ.prod μ) :=
      hJ3.sub hJ4
    rw [MeasureTheory.integral_integral_sub
      (f := fun z : α × α => F z.1 z.2 * k z.1 z.2 - (r * (∫ a', F a' z.2 ∂μ)) * k z.1 z.2)
      (g := fun z : α × α => (r * (∫ b', F z.1 b' ∂μ)) * k z.1 z.2
        - (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k z.1 z.2) hs1 hs2]
    rw [MeasureTheory.integral_integral_sub (f := fun z : α × α => F z.1 z.2 * k z.1 z.2)
      (g := fun z : α × α => (r * (∫ a', F a' z.2 ∂μ)) * k z.1 z.2) hI1 hJ2]
    rw [MeasureTheory.integral_integral_sub
      (f := fun z : α × α => (r * (∫ b', F z.1 b' ∂μ)) * k z.1 z.2)
      (g := fun z : α × α => (r ^ 2 * (∫ a', ∫ b', F a' b' ∂μ ∂μ)) * k z.1 z.2) hJ3 hJ4]
    dsimp only
    ring
  -- ### assembly: the three self-adjointness identities
  rw [hL, hR,
    pairingP1 (f := F) (g := k) (r := r) hMF hC hF hk hFb hkb,
    pairingP2 (f := F) (g := k) (r := r) hMF hC hF hk hFb hkb,
    pairingP12 (f := F) (g := k) (r := r ^ 2)]
  try ring

end Abstract

/-! ## 2. The box projection on the centred cube -/

section Box

variable {ℓ : ℝ}

/-- The defining expansion of `boxProj ℓ`. -/
theorem boxProj_expand (f : E3 → E3 → ℝ) (a b : E3) :
    boxProj ℓ f a b
      = f a b - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ a' in Submission.BoseGases.acube ℓ, f a' b)
        - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ b' in Submission.BoseGases.acube ℓ, f a b')
        + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2) * (∫ a' in Submission.BoseGases.acube ℓ,
            ∫ b' in Submission.BoseGases.acube ℓ, f a' b') := rfl

/-- `boxProj ℓ` only depends on the values of the kernel on the box `Λ × Λ`. -/
theorem boxProj_congr {f g : E3 → E3 → ℝ}
    (h : ∀ a ∈ Submission.BoseGases.acube ℓ, ∀ b ∈ Submission.BoseGases.acube ℓ, f a b = g a b)
    {a b : E3} (ha : a ∈ Submission.BoseGases.acube ℓ)
    (hb : b ∈ Submission.BoseGases.acube ℓ) : boxProj ℓ f a b = boxProj ℓ g a b := by
  have h1 : (∫ a' in Submission.BoseGases.acube ℓ, f a' b)
      = ∫ a' in Submission.BoseGases.acube ℓ, g a' b := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with a' ha'
    exact h a' ha' b hb
  have h2 : (∫ b' in Submission.BoseGases.acube ℓ, f a b')
      = ∫ b' in Submission.BoseGases.acube ℓ, g a b' := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with b' hb'
    exact h a ha b' hb'
  have h3 : (∫ a' in Submission.BoseGases.acube ℓ, ∫ b' in Submission.BoseGases.acube ℓ, f a' b')
      = ∫ a' in Submission.BoseGases.acube ℓ, ∫ b' in Submission.BoseGases.acube ℓ, g a' b' := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with a' ha'
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with b' hb'
    exact h a' ha' b' hb'
  rw [boxProj_expand, boxProj_expand, h a ha b hb, h1, h2, h3]

end Box

/-! ## 3. The pairing identity on the box -/

/-- **The box projection is self-adjoint for the box pairing.** -/
theorem boxProj_pairing {ℓ : ℝ} (hℓ : 0 < ℓ) {F k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFc : Continuous (Function.uncurry F))
    (hkm : Measurable (Function.uncurry k)) {C : ℝ} (hkb : ∀ a b, |k a b| ≤ C) :
    (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        F a b * Work.BoseBoxFock.boxProj ℓ k a b)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFock.boxProj ℓ F a b * k a b := by
  let Λ : Set E3 := Submission.BoseGases.acube ℓ
  change (∫ a in Λ, ∫ b in Λ, F a b * boxProj ℓ k a b)
      = ∫ a in Λ, ∫ b in Λ, boxProj ℓ F a b * k a b
  have hΛm : MeasurableSet Λ := Submission.BoseGases.acube_measurable ℓ
  haveI : MeasureTheory.IsFiniteMeasure ((volume : Measure E3).restrict Λ) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  -- the box bound for the continuous kernel `F`
  obtain ⟨MF, hMF⟩ := ((Submission.BoseGases.acube_compact hℓ).prod
      (Submission.BoseGases.acube_compact hℓ)).exists_bound_of_continuousOn hFc.continuousOn
  have h0Λ : (0 : E3) ∈ Λ :=
    Submission.BoseGases.mem_acube_of_norm_le hℓ.le (by rw [norm_zero]; linarith)
  have hMF0 : 0 ≤ MF := le_trans (norm_nonneg _) (hMF (0, 0) (by
    rw [Set.mem_prod]; exact ⟨h0Λ, h0Λ⟩))
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hkb 0 0)
  -- clamp `F` to the box so that the abstract layer applies
  let g₀ : E3 × E3 → ℝ := (Λ ×ˢ Λ).indicator (fun z => F z.1 z.2)
  have hg₀m : Measurable g₀ := hFc.measurable.indicator (hΛm.prod hΛm)
  let G : E3 → E3 → ℝ := Function.curry g₀
  have hGm : Measurable (Function.uncurry G) := by
    rw [show Function.uncurry G = g₀ from Function.uncurry_curry g₀]
    exact hg₀m
  have hGb : ∀ a b, |G a b| ≤ MF := by
    intro a b
    show |(Λ ×ˢ Λ).indicator (fun z : E3 × E3 => F z.1 z.2) (a, b)| ≤ MF
    by_cases h : (a, b) ∈ Λ ×ˢ Λ
    · rw [Set.indicator_of_mem h]
      have hF' := hMF (a, b) h
      rwa [Real.norm_eq_abs] at hF'
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact hMF0
  have hFG : ∀ a ∈ Λ, ∀ b ∈ Λ, G a b = F a b := by
    intro a ha b hb
    show (Λ ×ˢ Λ).indicator (fun z : E3 × E3 => F z.1 z.2) (a, b) = F a b
    rw [Set.indicator_of_mem (show (a, b) ∈ Λ ×ˢ Λ from ⟨ha, hb⟩)]
  have key := boxProj_pairing_general (μ := (volume : Measure E3).restrict Λ) (F := G) (k := k)
    (MF := MF) (C := C) (r := (ℓ ^ 3)⁻¹) hMF0 hC0 hGm hkm hGb hkb
  have hboxK : (∫ a in Λ, ∫ b in Λ, G a b * boxProj ℓ k a b)
      = ∫ a in Λ, ∫ b in Λ, boxProj ℓ G a b * k a b := by
    simpa only [boxProj_expand] using key
  -- transfer from the clamped kernel back to `F`
  have hμmem : ∀ᵐ a ∂(volume : Measure E3).restrict Λ, a ∈ Λ := ae_restrict_mem hΛm
  have hGF_L : (∫ a in Λ, ∫ b in Λ, F a b * boxProj ℓ k a b)
      = ∫ a in Λ, ∫ b in Λ, G a b * boxProj ℓ k a b := by
    refine integral_congr_ae ?_
    filter_upwards [hμmem] with a ha
    refine integral_congr_ae ?_
    filter_upwards [hμmem] with b hb
    rw [hFG a ha b hb]
  have hGF_R : (∫ a in Λ, ∫ b in Λ, boxProj ℓ G a b * k a b)
      = ∫ a in Λ, ∫ b in Λ, boxProj ℓ F a b * k a b := by
    refine integral_congr_ae ?_
    filter_upwards [hμmem] with a ha
    refine integral_congr_ae ?_
    filter_upwards [hμmem] with b hb
    rw [boxProj_congr hFG ha hb]
  exact hGF_L.trans (hboxK.trans hGF_R)

end Work.BoseBoxFock
