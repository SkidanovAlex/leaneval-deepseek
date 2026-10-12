import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1.boxMuAgreeB1
import Submission.Work.BoseFixB1S.boxPQw_mass_le
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Product integrability on the box with one a.e.-measurable factor -/

/-- A product `f·g·w` of two measurable box-bounded functions and one a.e.-strongly-measurable
box-bounded function is integrable on the box. -/
private lemma integrableOn_mul_mul_of_bound_aesm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g w : X N → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hwm : AEStronglyMeasurable w (volume.restrict (abox N ℓ)))
    {Cf Cg Cw : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf)
    (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg) (hwb : ∀ x ∈ abox N ℓ, |w x| ≤ Cw) :
    IntegrableOn (fun x : X N => f x * g x * w x) (abox N ℓ) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) ?_ (|Cf| * |Cg| * |Cw|) ?_
  · exact (hfm.aestronglyMeasurable.mul hgm.aestronglyMeasurable).mul hwm
  · rw [ae_restrict_iff' (abox_measurable N ℓ)]
    refine ae_of_all _ (fun x hx => ?_)
    have h1 : |f x * g x| ≤ |Cf| * |Cg| := by
      rw [abs_mul]
      exact mul_le_mul (le_trans (hfb x hx) (le_abs_self Cf))
        (le_trans (hgb x hx) (le_abs_self Cg)) (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 (le_trans (hwb x hx) (le_abs_self Cw)) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-! ## The weighted collapse of the projected second factor -/

/-- **The weighted collapse of the second `P_i`-factor.**  For a weight `w` that does not
depend on slot `i`, the box projection `P_i = Work.UBBInputs8.boxPInd volA A i` may be removed
from the second factor of the fibre integral:

    `∫_{abox N ℓ} (P_iΘ)·(P_iΛ)·w = ∫_{abox N ℓ} (P_iΘ)·Λ·w`. -/
theorem boxPInd_mulWeight {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure
      (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Θ Λ : Submission.BoseGases.X N → ℝ}
    (hΘm : Measurable Θ) {CΘ : ℝ} (hΘb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Θ x| ≤ CΘ)
    (hΛm : Measurable Λ) {CΛ : ℝ} (hΛb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Λ x| ≤ CΛ)
    {w : Submission.BoseGases.X N → ℝ}
    (hwm : AEStronglyMeasurable w (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    {Cw : ℝ} (hwb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |w x| ≤ Cw)
    (hw : ∀ (x : Submission.BoseGases.X N) (y : EuclideanSpace ℝ (Fin 3)),
      w (Function.update x i y) = w x) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Θ x * Work.UBBInputs8.boxPInd volA A i Λ x * w x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Θ x * Λ x * w x := by
  cases N with
  | zero => exact i.elim0
  | succ m =>
    have hΘP : ∀ x ∈ abox (m + 1) ℓ, |Work.UBBInputs8.boxPInd volA A i Θ x| ≤ CΘ :=
      Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΘb
    have hΛP : ∀ x ∈ abox (m + 1) ℓ, |Work.UBBInputs8.boxPInd volA A i Λ x| ≤ CΛ :=
      Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΛb
    have hΘPm : Measurable (Work.UBBInputs8.boxPInd volA A i Θ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hA i hΘm
    have hΛPm : Measurable (Work.UBBInputs8.boxPInd volA A i Λ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hA i hΛm
    -- integrability of both integrands on the box
    have hIL : IntegrableOn (fun x : X (m + 1) =>
        Work.UBBInputs8.boxPInd volA A i Θ x * Work.UBBInputs8.boxPInd volA A i Λ x * w x)
        (abox (m + 1) ℓ) volume :=
      integrableOn_mul_mul_of_bound_aesm hℓ hΘPm hΛPm hwm hΘP hΛP hwb
    have hIR : IntegrableOn (fun x : X (m + 1) =>
        Work.UBBInputs8.boxPInd volA A i Θ x * Λ x * w x) (abox (m + 1) ℓ) volume :=
      integrableOn_mul_mul_of_bound_aesm hℓ hΘPm hΛm hwm hΘP hΛb hwb
    -- the fibre identity, pointwise in the remaining coordinates
    have hfib : ∀ r : X m,
        (∫ y in acube ℓ, Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
            * Work.UBBInputs8.boxPInd volA A i Λ (kcInsN m i (y, r))
            * w (kcInsN m i (y, r)))
          = ∫ y in acube ℓ, Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
            * Λ (kcInsN m i (y, r)) * w (kcInsN m i (y, r)) := by
      intro r
      -- the weight is constant along the inserted fibre
      have hWpt : ∀ y : EuclideanSpace ℝ (Fin 3),
          w (kcInsN m i (y, r)) = w (kcInsN m i (0, r)) := by
        intro y
        rw [Submission.BoseGases.kcInsN_update_zero (n := m) i y r]
        exact hw (kcInsN m i (0, r)) y
      have h1A : (∫ y in acube ℓ, A.indicator (fun _ => (1 : ℝ)) y) = volA := by
        have h := Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc
          (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))
        simp only [mul_one] at h
        rw [h, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
        exact hvolA.symm
      -- the peeled left-hand fibre integrand
      have hptL : ∀ y : EuclideanSpace ℝ (Fin 3),
          Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
              * Work.UBBInputs8.boxPInd volA A i Λ (kcInsN m i (y, r))
              * w (kcInsN m i (y, r))
            = ((1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r))))
              * ((1 / volA) * (∫ z in A, Λ (kcInsN m i (z, r))))
              * w (kcInsN m i (0, r))
              * A.indicator (fun _ => (1 : ℝ)) y := by
        intro y
        rw [Work.BoseFixB1S.boxPInd_kcInsN, Work.BoseFixB1S.boxPInd_kcInsN, hWpt y]
        by_cases hy : y ∈ A
        · rw [Set.indicator_of_mem hy]; ring
        · rw [Set.indicator_of_notMem hy]; ring
      -- the peeled right-hand fibre integrand
      have hptR : ∀ y : EuclideanSpace ℝ (Fin 3),
          Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
              * Λ (kcInsN m i (y, r)) * w (kcInsN m i (y, r))
            = ((1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r))))
              * w (kcInsN m i (0, r))
              * (A.indicator (fun _ => (1 : ℝ)) y * Λ (kcInsN m i (y, r))) := by
        intro y
        rw [Work.BoseFixB1S.boxPInd_kcInsN, hWpt y]
        by_cases hy : y ∈ A
        · rw [Set.indicator_of_mem hy]; ring
        · rw [Set.indicator_of_notMem hy]; ring
      have hL : (∫ y in acube ℓ, Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
            * Work.UBBInputs8.boxPInd volA A i Λ (kcInsN m i (y, r))
            * w (kcInsN m i (y, r)))
          = (1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r)))
            * (∫ z in A, Λ (kcInsN m i (z, r))) * w (kcInsN m i (0, r)) := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptL)]
        rw [MeasureTheory.integral_const_mul, h1A]
        have hV1 : (1 / volA) * volA = 1 := by field_simp
        rw [show ((1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r)))
              * ((1 / volA) * (∫ z in A, Λ (kcInsN m i (z, r))))
              * w (kcInsN m i (0, r))) * volA
            = (1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r)))
              * (∫ z in A, Λ (kcInsN m i (z, r))) * w (kcInsN m i (0, r))
              * ((1 / volA) * volA) from by ring]
        rw [hV1, mul_one]
      have hR : (∫ y in acube ℓ, Work.UBBInputs8.boxPInd volA A i Θ (kcInsN m i (y, r))
            * Λ (kcInsN m i (y, r)) * w (kcInsN m i (y, r)))
          = (1 / volA) * (∫ z in A, Θ (kcInsN m i (z, r)))
            * (∫ z in A, Λ (kcInsN m i (z, r))) * w (kcInsN m i (0, r)) := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptR)]
        rw [MeasureTheory.integral_const_mul]
        rw [Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc
          (fun z : EuclideanSpace ℝ (Fin 3) => Λ (kcInsN m i (z, r)))]
        ring
      exact hL.trans hR.symm
    -- peel slot `i` on both sides and compare the fibres
    rw [Submission.BoseGases.abox_integral_peel (n := m) (i := i)
        (F := fun x : X (m + 1) => Work.UBBInputs8.boxPInd volA A i Θ x
          * Work.UBBInputs8.boxPInd volA A i Λ x * w x) hIL,
      Submission.BoseGases.abox_integral_peel (n := m) (i := i)
        (F := fun x : X (m + 1) => Work.UBBInputs8.boxPInd volA A i Θ x * Λ x * w x) hIR]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with r
    exact hfib r

/-! ## The per-pair replacement -/

/-- Per-pair replacement of `P_sP_tΦ` by `P_tΦ` inside the fibre integral.  This is NOT a
pointwise identity: `P_sP_tΦ = 1_A(x s)·1_A(x t)·cc` while `P_tΦ = 1_A(x t)·c_t`, and the
difference is `(1_A(x s)−1)·P_tΦ − P_tQ_sΦ`; the first piece is annihilated by the common
factor `P_sQ_tΦ = 1_A(x s)·1_A(x t)·(c_s − cc)`, and the second integrates to zero because
`P_s` moves off `Q_tΦ` and annihilates `P_tQ_sΦ`.  Formally both sides share the factor
`P_s(Q_tΦ)`, and `boxPInd_mulWeight` above removes `P_s` from the second factor, the weight
`fib(x t)` not depending on slot `s` since `s ≠ t`. -/
theorem boxQ1_pair_replace {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxPInd V A t Φ) x) * fib (x t))
      = (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A s (Work.UBBInputs8.boxQInd V A t Φ) x)
          * (Work.UBBInputs8.boxPInd V A t Φ x) * fib (x t)) := by
  -- a global bound for the continuous state on the compact box
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |B| := by
    intro x hx
    have h1 : |Φ x| ≤ B := by simpa [Real.norm_eq_abs] using hB x hx
    exact le_trans h1 (le_abs_self B)
  have hmΘ : Measurable (Work.UBBInputs8.boxQInd V A t Φ) :=
    Work.BoseFixB1S.measurable_boxQInd V hA t hΦc.measurable
  have hmΛ : Measurable (Work.UBBInputs8.boxPInd V A t Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA t hΦc.measurable
  have hΘb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A t Φ x| ≤ 2 * |B| :=
    Work.BoseFixB1S.abs_boxQInd_le_two hℓ hV hA hVeq hAc t hΦb
  have hΛb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A t Φ x| ≤ |B| :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc t hΦb
  -- the weight `fib (· t)`
  have hwm : MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N => fib (x t))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.aem_comp_coord' (N := N) (ℓ := ℓ) t hFm
  have hwb : ∀ x ∈ abox N ℓ, |(fun x : Submission.BoseGases.X N => fib (x t)) x| ≤ |C| := by
    intro x hx
    exact le_trans (hC (x t) (hx t)) (le_abs_self C)
  have hw : ∀ (x : Submission.BoseGases.X N) (y : EuclideanSpace ℝ (Fin 3)),
      (fun x : Submission.BoseGases.X N => fib (x t)) (Function.update x s y)
        = (fun x : Submission.BoseGases.X N => fib (x t)) x := by
    intro x y
    show fib ((Function.update x s y) t) = fib (x t)
    rw [Function.update_of_ne hst.symm y x]
  exact boxPInd_mulWeight (hℓ := hℓ) (hvol := hV) (hA := hA) (hvolA := hVeq)
    (hAc := hAc) (i := s) (Θ := Work.UBBInputs8.boxQInd V A t Φ)
    (Λ := Work.UBBInputs8.boxPInd V A t Φ) (hΘm := hmΘ) (hΛm := hmΛ)
    (hΘb := hΘb) (hΛb := hΛb) (hwm := hwm) (hwb := hwb) (hw := hw)

end Work.BoseFixB1P
