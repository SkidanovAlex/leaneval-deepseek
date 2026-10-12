import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.weakAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairWeightMeas`

The pair weight of the two-particle slot `(i,j)` of a **continuous** state `Ψ` against a
measurable bounded kernel `k`,

  `W(i,j,k) x = ∫_{y ∈ Λ(ℓ)} ∫_{u ∈ Λ(ℓ)} (Qᵢ QⱼΨ)(x[i↦y][j↦u]) · k y u`,

is (a) measurable in `x`, and (b) bounded on the box `Λ(ℓ)ᴺ`.

The two ingredients are

* the *local* sup-norm contraction of the slot projections (`aP_abs_le_abox`,
  `aQ_abs_le_abox` below): `|aP ℓ i Φ x| ≤ C` for `x` in the box whenever `|Φ| ≤ C` on the box.
  No regularity of `Φ` is needed, only the pointwise bound, because the estimate is a pure
  bound on a set-integral (`norm_setIntegral_le_of_norm_le_const`);
* the Fubini-measurability of the partial (Bochner) integral
  (`StronglyMeasurable.integral_prod_right'`), applied twice, once for each slot.  Only the
  *measurability* of `aQ ℓ i (aQ ℓ j Ψ)` enters (weakAux's `Weak.aQ_measurable`), never its
  continuity.

The hypothesis `hij : i ≠ j` is used by neither half; it is carried because that is the form in
which the box ↔ model bridge consumes the statement.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseBoxFock

set_option autoImplicit false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Lebesgue measure of the centred cube, in the `Measure.real` normalisation used by the
`norm_setIntegral_le_of_norm_le_const` bound. -/
theorem volume_real_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (volume : Measure Sp).real (acube ℓ) = ℓ ^ 3 := by
  rw [Measure.real_def, acube_volume ℓ hℓ, ENNReal.toReal_ofReal (by positivity)]

/-- **Local sup-norm contraction of the slot mean.**  If `|Φ| ≤ C` *on the box* `Λ(ℓ)ᴺ` then
`|aP ℓ i Φ| ≤ C` on the box.  No regularity of `Φ` is required: the claim is a bound of a
set-integral against a constant (`norm_setIntegral_le_of_norm_le_const`), and the fibre
`y ↦ Φ (x[i↦y])` of a box point `x` is evaluated at box points only. -/
theorem aP_abs_le_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦB : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) :
    ∀ x ∈ abox n ℓ, |aP ℓ i Φ x| ≤ C := by
  intro x hx
  have hb : ‖∫ y in acube ℓ, Φ (Function.update x i y)‖ ≤ C * ℓ ^ 3 := by
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure Sp))
      (s := acube ℓ) (f := fun y : Sp => Φ (Function.update x i y)) (C := C)
      (acube_lt_top ℓ hℓ.le) (fun y hy => by
        rw [Real.norm_eq_abs]
        exact hΦB _ (update_mem_abox i hx hy))
    rwa [volume_real_acube hℓ.le] at h1
  have hpos : (0 : ℝ) ≤ 1 / ℓ ^ 3 := by positivity
  have h3 : |aP ℓ i Φ x| = (1 / ℓ ^ 3) * ‖∫ y in acube ℓ, Φ (Function.update x i y)‖ := by
    unfold aP
    rw [abs_mul, abs_of_nonneg hpos, Real.norm_eq_abs]
  rw [h3]
  calc (1 / ℓ ^ 3) * ‖∫ y in acube ℓ, Φ (Function.update x i y)‖
      ≤ (1 / ℓ ^ 3) * (C * ℓ ^ 3) := mul_le_mul_of_nonneg_left hb hpos
    _ = C := by field_simp

/-- **Local sup-norm contraction of the complementary slot**: `|aQ ℓ i Φ| ≤ 2C` on the box
whenever `|Φ| ≤ C` there. -/
theorem aQ_abs_le_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦB : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) :
    ∀ x ∈ abox n ℓ, |aQ ℓ i Φ x| ≤ 2 * C := by
  intro x hx
  have hP := aP_abs_le_abox hℓ i hC hΦB x hx
  have h1 : |aQ ℓ i Φ x| ≤ |Φ x| + |aP ℓ i Φ x| := by
    unfold aQ
    exact abs_sub _ _
  have h2 := hΦB x hx
  linarith

theorem pairWeightMeas {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : Measurable (Function.uncurry k)) {Ck : ℝ} (hkb : ∀ y u, |k y u| ≤ Ck)
    {i j : Fin n} (hij : i ≠ j) :
    Measurable (fun x : Submission.BoseGases.X n =>
        ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j Ψ)
            (Function.update (Function.update x i y) j u) * k y u)
    ∧ (∃ CH : ℝ, 0 ≤ CH ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
        |(∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aQ ℓ j Ψ)
            (Function.update (Function.update x i y) j u) * k y u)| ≤ CH) := by
  -- the supremum bound of `Ψ` on the compact box
  obtain ⟨M, hM⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn (f := Ψ) hΨc.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (zero_mem_abox hℓ.le))
  have hΨB : ∀ x ∈ abox n ℓ, |Ψ x| ≤ M := fun x hx => by
    simpa [Real.norm_eq_abs] using hM x hx
  have hCk0 : 0 ≤ Ck := le_trans (abs_nonneg _) (hkb 0 0)
  -- the two slot bounds on the box
  have hQj : ∀ w ∈ abox n ℓ, |aQ ℓ j Ψ w| ≤ 2 * M := aQ_abs_le_abox hℓ j hM0 hΨB
  have hQj0 : 0 ≤ 2 * M := by linarith
  have hQi : ∀ w ∈ abox n ℓ, |aQ ℓ i (aQ ℓ j Ψ) w| ≤ 4 * M := fun w hw => by
    have h := aQ_abs_le_abox hℓ i hQj0 hQj w hw
    linarith
  constructor
  · -- ## Measurability
    haveI : SFinite ((volume : Measure Sp).restrict (acube ℓ)) := inferInstance
    have hJm : Measurable (aQ ℓ i (aQ ℓ j Ψ)) :=
      Weak.aQ_measurable i (Weak.aQ_measurable j hΨc.measurable)
    have hupd : Measurable (fun q : (X n × Sp) × Sp =>
        Function.update (Function.update q.1.1 i q.1.2) j q.2) := by fun_prop
    have h1 : Measurable (fun q : (X n × Sp) × Sp =>
        aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update q.1.1 i q.1.2) j q.2)) :=
      hJm.comp hupd
    have hpair : Measurable (fun q : (X n × Sp) × Sp => (q.1.2, q.2)) := by fun_prop
    have h2 : Measurable (fun q : (X n × Sp) × Sp => k q.1.2 q.2) := by
      show Measurable (fun q : (X n × Sp) × Sp => Function.uncurry k (q.1.2, q.2))
      exact hkm.comp hpair
    have hG : StronglyMeasurable (fun q : (X n × Sp) × Sp =>
        aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update q.1.1 i q.1.2) j q.2)
          * k q.1.2 q.2) := (h1.mul h2).stronglyMeasurable
    have hstep : StronglyMeasurable (fun p : X n × Sp => ∫ u in acube ℓ,
        aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update p.1 i p.2) j u) * k p.2 u) :=
      hG.integral_prod_right' (ν := (volume : Measure Sp).restrict (acube ℓ))
    exact (hstep.integral_prod_right' (ν := (volume : Measure Sp).restrict (acube ℓ))).measurable
  · -- ## The uniform bound on the box
    refine ⟨4 * M * Ck * ℓ ^ 6, by positivity, ?_⟩
    intro x hx
    -- pointwise bound of the integrand for `x` in the box
    have hpt : ∀ y ∈ acube ℓ, ∀ u ∈ acube ℓ,
        |aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u) * k y u|
          ≤ 4 * M * Ck := by
      intro y hy u hu
      have hw : Function.update (Function.update x i y) j u ∈ abox n ℓ :=
        update_mem_abox j (update_mem_abox i hx hy) hu
      have hQ := hQi _ hw
      have hk := hkb y u
      have h4 : 0 ≤ 4 * M := by linarith
      rw [abs_mul]
      calc |aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u)| * |k y u|
          ≤ (4 * M) * Ck := mul_le_mul hQ hk (abs_nonneg _) h4
        _ = 4 * M * Ck := by ring
    -- inner integral
    have hinner : ∀ y ∈ acube ℓ,
        ‖∫ u in acube ℓ, aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u)
          * k y u‖ ≤ (4 * M * Ck) * ℓ ^ 3 := by
      intro y hy
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure Sp))
        (s := acube ℓ)
        (f := fun u : Sp => aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u)
          * k y u) (C := 4 * M * Ck)
        (acube_lt_top ℓ hℓ.le) (fun u hu => by
          rw [Real.norm_eq_abs]
          exact hpt y hy u hu)
      rwa [volume_real_acube hℓ.le] at h1
    -- outer integral
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure Sp))
      (s := acube ℓ)
      (f := fun y : Sp => ∫ u in acube ℓ,
        aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u) * k y u)
      (C := (4 * M * Ck) * ℓ ^ 3) (acube_lt_top ℓ hℓ.le) (fun y hy => by
        simpa [Real.norm_eq_abs] using hinner y hy)
    rw [volume_real_acube hℓ.le] at h2
    have h2b : ‖∫ y in acube ℓ, ∫ u in acube ℓ,
          aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u) * k y u‖
        ≤ 4 * M * Ck * ℓ ^ 6 := by
      calc ‖∫ y in acube ℓ, ∫ u in acube ℓ,
            aQ ℓ i (aQ ℓ j Ψ) (Function.update (Function.update x i y) j u) * k y u‖
          ≤ ((4 * M * Ck) * ℓ ^ 3) * ℓ ^ 3 := h2
        _ = 4 * M * Ck * ℓ ^ 6 := by ring
    simpa [Real.norm_eq_abs] using h2b

end Work.BoseBoxFock
