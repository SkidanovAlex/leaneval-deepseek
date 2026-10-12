import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpA
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxOpG_adjoint_one` — the `h = 1` adjoint identity for `boxOpG`

`boxOpG A f h Ψ x = Σ_i 1_A(x_i)·f(x_i)·∫_{z∈A} h z·Ψ(x_{i←z})`.  For the constant slot weight
`h ≡ 1` the formal adjoint partner `boxOpZ A 1 f` coincides with `boxOpG A 1 f`, and the pairing
identity

  `∫ Φ·(boxOpG A f 1 Ψ) = ∫ (boxOpG A 1 f Φ)·Ψ`

holds on the centred box `abox (N+1) a`.

Both sides are evaluated by the *one-slot peel* `Submission.BoseGases.abox_integral_peel_gen`
together with the indicator collapse `∫_{acube a} 1_A·g = ∫_A g`: with `x = kcInsN N i (y,r)`,

  `Φ x·(boxOpG A f 1 Ψ x) = Σ_i 1_A(y)·f(y)·Φ(kcInsN i (y,r))·(∫_{z∈A}Ψ(kcInsN i (z,r)))`,

so after peeling and pulling the `y`-independent `z`-factor out of the `y`-integral the LHS
becomes `Σ_i ∫_r (∫_A f·Φ(kcInsN i (·,r)))·(∫_A Ψ(kcInsN i (·,r)))`, while the same computation
for the RHS produces the very same expression with the two factors interchanged — hence equal by
`mul_comm`.

The two `peel_*` lemmas are the per-slot analytic ingredients; the two `integrableOn_*` lemmas
supply the integrability that lets the finite sum `Σ_{i : Fin (N+1)}` be moved out of the
integral.
-/

namespace Work.BoseFixB1

open MeasureTheory Filter
open scoped BigOperators Real

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- A slot-updated configuration stays in the box when the new coordinate lies in `A ⊆ acube ℓ`. -/
theorem boxOpG_one_update_mem_abox {n : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ A) : Function.update x i u ∈ Submission.BoseGases.abox n ℓ := by
  intro k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk]; exact hAc hu
  · rw [if_neg hk]; exact hx k

/-! ## 1. The two per-slot peel computations -/

/-- **Peel of the created slot.**  For the integrand whose created slot carries the box
indicator times `f` and whose annihilated slot is integrated against `Ψ`. -/
theorem boxOpG_one_peel_createdSlot {n : ℕ} {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAm : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) a,
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      = ∫ r in Submission.BoseGases.abox n a,
          (∫ y in A, f y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
            * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
  rw [Submission.BoseGases.abox_integral_peel_gen (i := i)
    (F := fun x : Submission.BoseGases.X (n + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
        * (∫ z in A, Ψ (Function.update x i z))) hint]
  apply integral_congr_ae
  filter_upwards with r
  calc (∫ y in Submission.BoseGases.acube a,
        A.indicator (fun _ => (1 : ℝ))
            ((Submission.BoseGases.kcInsN n i (y, r)) i)
          * f ((Submission.BoseGases.kcInsN n i (y, r)) i)
          * Φ (Submission.BoseGases.kcInsN n i (y, r))
          * (∫ z in A, Ψ (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z)))
      = ∫ y in Submission.BoseGases.acube a,
          A.indicator (fun _ => (1 : ℝ)) y * f y * Φ (Submission.BoseGases.kcInsN n i (y, r))
            * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
        apply integral_congr_ae
        filter_upwards with y
        have hupd : (∫ z in A, Ψ (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
            = ∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Submission.BoseGases.update_kcInsN]
        rw [Submission.BoseGases.kc_insN_apply_same, hupd]
    _ = (∫ y in Submission.BoseGases.acube a,
          A.indicator (fun _ => (1 : ℝ)) y * f y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
          * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
        rw [MeasureTheory.integral_mul_const]
    _ = (∫ y in A, f y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
          * (∫ z in A, Ψ (Submission.BoseGases.kcInsN n i (z, r))) := by
        have hfac : (∫ y in Submission.BoseGases.acube a,
              A.indicator (fun _ => (1 : ℝ)) y * f y
                * Φ (Submission.BoseGases.kcInsN n i (y, r)))
            = ∫ y in A, f y * Φ (Submission.BoseGases.kcInsN n i (y, r)) := by
          rw [show (∫ y in Submission.BoseGases.acube a,
                A.indicator (fun _ => (1 : ℝ)) y * f y
                  * Φ (Submission.BoseGases.kcInsN n i (y, r)))
              = ∫ y in Submission.BoseGases.acube a,
                A.indicator (fun _ => (1 : ℝ)) y
                  * (f y * Φ (Submission.BoseGases.kcInsN n i (y, r))) from by
            apply integral_congr_ae
            filter_upwards with y
            ring]
          exact Work.BoseFixB1S.setIntegral_indicator_one_mul hAm hAc
            (fun y => f y * Φ (Submission.BoseGases.kcInsN n i (y, r)))
        rw [hfac]

/-- **Peel of the integrated slot.**  For the integrand whose annihilated slot is integrated
against `f·Φ` and which carries the bulk factor `Ψ`. -/
theorem boxOpG_one_peel_integratedSlot {n : ℕ} {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAm : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) a,
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      = ∫ r in Submission.BoseGases.abox n a,
          (∫ y in A, Ψ (Submission.BoseGases.kcInsN n i (y, r)))
            * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  rw [Submission.BoseGases.abox_integral_peel_gen (i := i)
    (F := fun x : Submission.BoseGases.X (n + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
        * (∫ z in A, f z * Φ (Function.update x i z))) hint]
  apply integral_congr_ae
  filter_upwards with r
  calc (∫ y in Submission.BoseGases.acube a,
        A.indicator (fun _ => (1 : ℝ)) ((Submission.BoseGases.kcInsN n i (y, r)) i)
          * Ψ (Submission.BoseGases.kcInsN n i (y, r))
          * (∫ z in A, f z * Φ (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z)))
      = ∫ y in Submission.BoseGases.acube a,
          A.indicator (fun _ => (1 : ℝ)) y * Ψ (Submission.BoseGases.kcInsN n i (y, r))
            * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
        apply integral_congr_ae
        filter_upwards with y
        have hupd : (∫ z in A, f z * Φ (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
            = ∫ z in A, f z * Φ (Submission.BoseGases.kcInsN n i (z, r)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Submission.BoseGases.update_kcInsN]
        rw [Submission.BoseGases.kc_insN_apply_same, hupd]
    _ = (∫ y in Submission.BoseGases.acube a,
          A.indicator (fun _ => (1 : ℝ)) y * Ψ (Submission.BoseGases.kcInsN n i (y, r)))
          * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
        rw [MeasureTheory.integral_mul_const]
    _ = (∫ y in A, Ψ (Submission.BoseGases.kcInsN n i (y, r)))
          * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
        have hfac : (∫ y in Submission.BoseGases.acube a,
              A.indicator (fun _ => (1 : ℝ)) y * Ψ (Submission.BoseGases.kcInsN n i (y, r)))
            = ∫ y in A, Ψ (Submission.BoseGases.kcInsN n i (y, r)) :=
          Work.BoseFixB1S.setIntegral_indicator_one_mul hAm hAc
            (fun y => Ψ (Submission.BoseGases.kcInsN n i (y, r)))
        rw [hfac]

/-! ## 2. Integrability of the two per-slot integrands -/

/-- Integrability of the created-slot integrand on the box. -/
theorem boxOpG_one_integrableOn_createdSlot {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (n + 1)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume := by
  obtain ⟨Mf, hMf⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hf.continuousOn
  obtain ⟨Mψ, hMψ⟩ := (Submission.BoseGases.abox_compact (n + 1) ha).exists_bound_of_continuousOn
    hΨ.continuousOn
  have hvolA : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hvolA0 : 0 ≤ ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal :=
    ENNReal.toReal_nonneg
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top (n + 1) a ha.le) ?_
    (|Mf| * (|CΦ| * (|Mψ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|))) ?_
  · have h1 : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hAm).comp (measurable_pi_apply i)
    have h2 : Measurable (fun x : Submission.BoseGases.X (n + 1) => f (x i)) :=
      hf.measurable.comp (measurable_pi_apply i)
    have h3 : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
        ∫ z in A, Ψ (Function.update x i z)) :=
      Work.BoseFixB1S.measurable_fibreMean A hAm i hΨ.measurable
    exact (((h1.mul h2).mul hΦm).mul h3).aestronglyMeasurable
  · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) a)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs]
    simp only [abs_mul]
    have hInd : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    have hfbound : |f (x i)| ≤ |Mf| :=
      le_trans (by simpa only [Real.norm_eq_abs] using hMf (x i) (hx i)) (le_abs_self Mf)
    have hΦbound : |Φ x| ≤ |CΦ| := le_trans (hΦb x hx) (le_abs_self CΦ)
    have hInner : |∫ z in A, Ψ (Function.update x i z)|
        ≤ |Mψ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal| := by
      have h1 : ‖∫ z in A, Ψ (Function.update x i z)‖
          ≤ Mψ * (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal) := by
        refine norm_setIntegral_le_of_norm_le_const hvolA ?_
        intro z hz
        have h := hMψ (Function.update x i z) (boxOpG_one_update_mem_abox hAc hx i hz)
        simpa only [Real.norm_eq_abs] using h
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      rw [abs_of_nonneg hvolA0]
      exact mul_le_mul_of_nonneg_right (le_abs_self Mψ) hvolA0
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |f (x i)| * |Φ x|
          * |∫ z in A, Ψ (Function.update x i z)|
        ≤ 1 * |Mf| * |CΦ|
          * (|Mψ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hInd hfbound (abs_nonneg _) (by norm_num))
            hΦbound (abs_nonneg _) (by positivity)) hInner (abs_nonneg _) (by positivity)
      _ = |Mf| * (|CΦ|
          * (|Mψ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|)) := by
          ring

/-- Integrability of the integrated-slot integrand on the box. -/
theorem boxOpG_one_integrableOn_integratedSlot {n : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (n + 1)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (Submission.BoseGases.abox (n + 1) a) MeasureTheory.volume := by
  obtain ⟨Mf, hMf⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hf.continuousOn
  obtain ⟨Mψ, hMψ⟩ := (Submission.BoseGases.abox_compact (n + 1) ha).exists_bound_of_continuousOn
    hΨ.continuousOn
  have hvolA : (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hvolA0 : 0 ≤ ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal :=
    ENNReal.toReal_nonneg
  refine MeasureTheory.IntegrableOn.of_bound
    (Submission.BoseGases.abox_lt_top (n + 1) a ha.le) ?_
    (|Mψ| * (|Mf| * (|CΦ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|))) ?_
  · have h1 : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i)) :=
      (measurable_const.indicator hAm).comp (measurable_pi_apply i)
    have hinner : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
        ∫ z in A, f z * Φ (Function.update x i z)) := by
      have h := Work.BoseFixB1S.measurable_fibreMean A hAm i
        (Ψ := fun y : Submission.BoseGases.X (n + 1) => f (y i) * Φ y)
        ((hf.measurable.comp (measurable_pi_apply i)).mul hΦm)
      have hfun : (fun x : Submission.BoseGases.X (n + 1) =>
            ∫ z in A, f ((Function.update x i z) i) * Φ (Function.update x i z))
          = fun x : Submission.BoseGases.X (n + 1) =>
            ∫ z in A, f z * Φ (Function.update x i z) := by
        funext x
        apply integral_congr_ae
        filter_upwards with z
        rw [Function.update_self]
      rwa [hfun] at h
    exact ((h1.mul hΨ.measurable).mul hinner).aestronglyMeasurable
  · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) a)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs]
    simp only [abs_mul]
    have hInd : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    have hΨbound : |Ψ x| ≤ |Mψ| :=
      le_trans (by simpa only [Real.norm_eq_abs] using hMψ x hx) (le_abs_self Mψ)
    have hInner : |∫ z in A, f z * Φ (Function.update x i z)|
        ≤ |Mf| * (|CΦ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|) := by
      have h1 : ‖∫ z in A, f z * Φ (Function.update x i z)‖
          ≤ (|Mf| * |CΦ|)
            * (((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal) := by
        refine norm_setIntegral_le_of_norm_le_const hvolA (C := |Mf| * |CΦ|) ?_
        intro z hz
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          (le_trans (by simpa only [Real.norm_eq_abs] using hMf z (hAc hz)) (le_abs_self Mf))
          (le_trans (hΦb (Function.update x i z) (boxOpG_one_update_mem_abox hAc hx i hz)) (le_abs_self CΦ))
          (abs_nonneg (Φ (Function.update x i z))) (abs_nonneg Mf)
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      rw [abs_of_nonneg hvolA0]
      exact le_of_eq (mul_assoc _ _ _)
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x|
          * |∫ z in A, f z * Φ (Function.update x i z)|
        ≤ 1 * |Mψ|
          * (|Mf| * (|CΦ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|)) := by
          refine mul_le_mul (mul_le_mul hInd hΨbound (abs_nonneg _) (by norm_num)) hInner
            (abs_nonneg _) (by positivity)
      _ = |Mψ| * (|Mf|
          * (|CΦ| * |((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) A).toReal|)) := by
          ring

/-! ## 3. The adjoint identity -/

theorem boxOpG_adjoint_one {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f)
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    ∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x
      = ∫ x in Submission.BoseGases.abox (N + 1) a,
        Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x := by
  have hLint : ∀ i : Fin (N + 1), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) MeasureTheory.volume :=
    fun i => boxOpG_one_integrableOn_createdSlot ha hAm hAc hf hΦm hΦb hΨ i
  have hRint : ∀ i : Fin (N + 1), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) MeasureTheory.volume :=
    fun i => boxOpG_one_integrableOn_integratedSlot ha hAm hAc hf hΦm hΦb hΨ i
  have hL : (∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in Submission.BoseGases.abox N a,
          (∫ y in A, f y * Φ (Submission.BoseGases.kcInsN N i (y, r)))
            * (∫ z in A, Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
    have hpt : (fun x : Submission.BoseGases.X (N + 1) =>
          Φ x * Work.BoseFixB1.boxOpG A f (fun _ => (1 : ℝ)) Ψ x)
        = fun x : Submission.BoseGases.X (N + 1) =>
          ∑ i : Fin (N + 1), (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
            * (∫ z in A, Ψ (Function.update x i z))) := by
      funext x
      rw [Work.BoseFixB1.boxOpG]
      have hinner : ∀ i : Fin (N + 1),
          (∫ z in A, (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))
            = ∫ z in A, Ψ (Function.update x i z) := by
        intro i
        apply integral_congr_ae
        filter_upwards with z
        simp
      simp only [hinner]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : Submission.BoseGases.X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i) * Φ x
          * (∫ z in A, Ψ (Function.update x i z)))
      (fun i _ => hLint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact boxOpG_one_peel_createdSlot hAm hAc i (hLint i)
  have hR : (∫ x in Submission.BoseGases.abox (N + 1) a,
        Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
      = ∑ i : Fin (N + 1), ∫ r in Submission.BoseGases.abox N a,
          (∫ y in A, Ψ (Submission.BoseGases.kcInsN N i (y, r)))
            * (∫ z in A, f z * Φ (Submission.BoseGases.kcInsN N i (z, r))) := by
    have hpt : (fun x : Submission.BoseGases.X (N + 1) =>
          Work.BoseFixB1.boxOpG A (fun _ => (1 : ℝ)) f Φ x * Ψ x)
        = fun x : Submission.BoseGases.X (N + 1) =>
          ∑ i : Fin (N + 1), (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
            * (∫ z in A, f z * Φ (Function.update x i z))) := by
      funext x
      rw [Work.BoseFixB1.boxOpG, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [mul_one]
      ring
    rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
      (f := fun (i : Fin (N + 1)) (x : Submission.BoseGases.X (N + 1)) =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x
          * (∫ z in A, f z * Φ (Function.update x i z)))
      (fun i _ => hRint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact boxOpG_one_peel_integratedSlot hAm hAc i (hRint i)
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply integral_congr_ae
  filter_upwards with r
  exact mul_comm _ _

end Work.BoseFixB1
