import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.boxOneValue
import Submission.Work.BoseFixB1S.boxPQw_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 1600000

/-! ## 1. Elementary pieces about the box indicator and the slot mean -/

/-- The box indicator integrated over the cube: `∫_{acube ℓ} 1_A = volA` for `A ⊆ acube ℓ`. -/
theorem aind_integral_acube {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {volA : ℝ}
    (hvolA : volA = MeasureTheory.volume.real A) :
    (∫ t in Submission.BoseGases.acube ℓ, Aind A t) = volA := by
  have h := setIntegral_indicator_one_mul (ℓ := ℓ) hA hAc
    (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))
  simp only [mul_one] at h
  have hfun : (fun t : EuclideanSpace ℝ (Fin 3) => Aind A t)
      = (fun t : EuclideanSpace ℝ (Fin 3) => A.indicator (fun _ => (1 : ℝ)) t) := rfl
  rw [hfun, h, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  exact hvolA.symm

/-- **The pointwise square of the box `Q`-projection** at a configuration with slot `i` inserted:
the box indicator in that slot times the square of `Ψ` minus its slot mean. -/
theorem boxQInd_sq_kcInsN {n : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (i : Fin (n + 1)) (Ψ : Submission.BoseGases.X (n + 1) → ℝ)
    (t : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n) :
    (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
      = Aind A t * (Ψ (Submission.BoseGases.kcInsN n i (t, r))
          - Q0C.oneRest volA A i Ψ r) ^ 2 := by
  simp only [Work.UBBInputs8.boxQInd, Q0C.boxPInd_kcInsN, Submission.BoseGases.kc_insN_apply_same,
    Q0C.oneRest_def, Aind]
  by_cases ht : t ∈ A
  · simp only [Set.indicator_of_mem ht]
    ring
  · simp only [Set.indicator_of_notMem ht, zero_mul]
    ring

/-- The slot mean `oneRest` inherits any bound of `Ψ` on the box. -/
theorem abs_oneRest_le_of_bound {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = MeasureTheory.volume.real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin (n + 1))
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} {B : ℝ}
    (hBb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x| ≤ B) :
    ∀ r ∈ Submission.BoseGases.abox n ℓ, |Q0C.oneRest volA A i Ψ r| ≤ B := by
  intro r hr
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ∞ := volume_A_lt_top hℓ hAc
  have h1 : |∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))| ≤ B * volA := by
    have h := norm_setIntegral_le_of_norm_le_const hAfin (s := A)
      (f := fun t : EuclideanSpace ℝ (Fin 3) =>
        Ψ (Submission.BoseGases.kcInsN n i (t, r))) (C := B) (fun t ht => by
          rw [Real.norm_eq_abs]
          exact hBb _ (kcInsN_mem_abox (ℓ := ℓ) hAc i ht hr))
    rwa [← hvolA] at h
  rw [Q0C.oneRest_def, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
  calc (1 / volA) * |∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))|
      ≤ (1 / volA) * (B * volA) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp

/-- **Bessel's inequality on the `A`-fibre**: subtracting the `A`-mean of a bounded measurable
`f` does not increase the second moment. -/
theorem fibre_sq_sub_mean_le {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {volA : ℝ} (hvolA : volA = (MeasureTheory.volume A).toReal) (hvol : 0 < volA)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable f) {B : ℝ}
    (hfb : ∀ x ∈ A, |f x| ≤ B) :
    (∫ x in A, (f x - (1 / volA) * ∫ y in A, f y) ^ 2) ≤ ∫ x in A, (f x) ^ 2 := by
  have hne : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A ≠ ⊤ :=
    ne_of_lt (ENNReal.toReal_pos_iff.mp (by rw [← hvolA]; exact hvol)).2
  haveI : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hne⟩
  set c : ℝ := (1 / volA) * ∫ y in A, f y with hc
  -- a.e. boundedness and integrability of `f` and `f²` on the fibre
  have hbdd : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A), ‖f x‖ ≤ |B| := by
    rw [ae_restrict_iff' hA]
    exact ae_of_all _ (fun x hx => by
      rw [Real.norm_eq_abs]
      exact le_trans (hfb x hx) (le_abs_self B))
  have hfint : Integrable f ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
    Integrable.of_bound hfm.aestronglyMeasurable |B| hbdd
  have hf2int : Integrable (fun x => (f x) ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) := by
    refine Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (|B| ^ 2) ?_
    filter_upwards [hbdd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) hx 2
  -- the mean identity `c·volA = ∫_A f`
  have hcf : c * volA = ∫ y in A, f y := by
    rw [hc, mul_comm ((1 : ℝ) / volA) (∫ y in A, f y), mul_assoc, one_div,
      inv_mul_cancel₀ (ne_of_gt hvol), mul_one]
  -- expansion of the mean-free second moment
  have hkey : (∫ x in A, (f x - c) ^ 2) = (∫ x in A, (f x) ^ 2) - volA * c ^ 2 := by
    have hpw : (fun x : EuclideanSpace ℝ (Fin 3) => (f x - c) ^ 2)
        = fun x => ((f x) ^ 2 - 2 * c * f x) + c ^ 2 := by
      funext x
      ring
    have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => (f x) ^ 2 - 2 * c * f x)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
      hf2int.sub (hfint.const_mul (2 * c))
    have h2 : Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => c ^ 2)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) := integrable_const (c ^ 2)
    rw [hpw, MeasureTheory.integral_add h1 h2,
      MeasureTheory.integral_sub hf2int (hfint.const_mul (2 * c)),
      MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, smul_eq_mul,
      show (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A = volA from hvolA.symm,
      ← hcf]
    ring
  rw [hkey]
  nlinarith [mul_nonneg hvol.le (sq_nonneg c)]

/-! ## 2. The contraction inequalities -/

theorem boxProj_sq_contraction {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ)
    {B : ℝ} (hB0 : 0 ≤ B) (hBb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) ^ 2)
    ∧
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) ^ 2) := by
  have hN1 : 1 ≤ N := by
    have := i.isLt
    omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hvolA' : volA = MeasureTheory.volume.real A := by
    rw [MeasureTheory.Measure.real_def]
    exact hvolA
  have hAint : (∫ t in Submission.BoseGases.acube ℓ, Aind A t) = volA :=
    aind_integral_acube (ℓ := ℓ) hA hAc hvolA'
  constructor
  · -- the condensate half: `‖P_iΨ‖² ≤ ‖1_A(· i)Ψ‖²`
    calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
        = (∫ t in Submission.BoseGases.acube ℓ, Aind A t)
            * (∫ r in Submission.BoseGases.abox n ℓ, (Q0C.oneRest volA A i Ψ r) ^ 2) :=
          boxPInd_self (m := n) (ℓ := ℓ) (vA := volA) (A := A) hA i Ψ
      _ = volA * (∫ r in Submission.BoseGases.abox n ℓ,
            (Q0C.oneRest volA A i Ψ r) ^ 2) := by
          rw [hAint]
      _ ≤ volA * (volA⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Aind A (x i) * Ψ x) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (oneRest_sq_integral_le_aux (n := n) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA' hAc
              i hΨm hB0 hBb) hvol.le
      _ = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, (Aind A (x i) * Ψ x) ^ 2 := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvol), one_mul]
  · -- the mean-free half: peel the slot `i` and apply Bessel on each fibre
    have hQmeas : Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) :=
      measurable_boxQInd volA hA i hΨm
    have hQbd : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * B :=
      abs_boxQInd_le hℓ hvol hA hvolA' hAc i hBb
    have hIntQ : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
        (Submission.BoseGases.abox (n + 1) ℓ) volume :=
      integrableOn_sq_of_bound hℓ hQmeas hQbd
    have hSmeas : Measurable (fun x : Submission.BoseGases.X (n + 1) => Aind A (x i) * Ψ x) := by
      have h1 : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
          A.indicator (fun _ => (1 : ℝ)) (x i)) :=
        (measurable_const.indicator hA).comp (measurable_pi_apply i)
      exact h1.mul hΨm
    have hSbd : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Aind A (x i) * Ψ x| ≤ B := by
      intro x hx
      show |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x| ≤ B
      rw [abs_mul]
      have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases hxi : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * B :=
            mul_le_mul hσ (hBb x hx) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    have hIntS : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        (Aind A (x i) * Ψ x) ^ 2) (Submission.BoseGases.abox (n + 1) ℓ) volume :=
      integrableOn_sq_of_bound hℓ hSmeas hSbd
    -- the two peels of the slot `i`
    have hQpeel := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n + 1) => (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      hIntQ
    have hSpeel := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
      (fun x : Submission.BoseGases.X (n + 1) => (Aind A (x i) * Ψ x) ^ 2) hIntS
    -- the measure-preserving peel, used only to transport integrability of the fibre integrals
    have hmp : MeasureTheory.MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i))
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube ℓ)).prod
          ((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ)) := by
      have h := MeasureTheory.MeasurePreserving.symm
        (e := MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin 3)) i)
        (Submission.BoseGases.abox_peel_mp n ℓ i)
      simpa [Submission.BoseGases.kcInsN] using h
    have hintQ : Integrable (fun r : Submission.BoseGases.X n =>
        ∫ y in Submission.BoseGases.acube ℓ,
          (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := by
      have hc : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (Work.UBBInputs8.boxQInd volA A i Ψ
            (Submission.BoseGases.kcInsN n i p)) ^ 2)
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) :=
        (hmp.integrable_comp (hg := hIntQ.aestronglyMeasurable)).mpr hIntQ
      exact hc.integral_prod_right
    have hintS : Integrable (fun r : Submission.BoseGases.X n =>
        ∫ y in Submission.BoseGases.acube ℓ,
          (Aind A ((Submission.BoseGases.kcInsN n i (y, r)) i)
            * Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := by
      have hc : Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (Aind A ((Submission.BoseGases.kcInsN n i p) i)
            * Ψ (Submission.BoseGases.kcInsN n i p)) ^ 2)
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
              (Submission.BoseGases.acube ℓ)).prod
            ((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) :=
        (hmp.integrable_comp (hg := hIntS.aestronglyMeasurable)).mpr hIntS
      exact hc.integral_prod_right
    -- the frozen-fibre inequality
    have hfibre : ∀ r ∈ Submission.BoseGases.abox n ℓ,
        (∫ y in A, (Ψ (Submission.BoseGases.kcInsN n i (y, r))
            - Q0C.oneRest volA A i Ψ r) ^ 2)
          ≤ ∫ y in A, (Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 := by
      intro r hr
      have hfm : Measurable (fun y : EuclideanSpace ℝ (Fin 3) =>
          Ψ (Submission.BoseGases.kcInsN n i (y, r))) :=
        hΨm.comp ((Submission.BoseGases.kcInsN n i).measurable.comp (by fun_prop))
      have hfb : ∀ y ∈ A, |Ψ (Submission.BoseGases.kcInsN n i (y, r))| ≤ B := fun y hy =>
        hBb _ (kcInsN_mem_abox (ℓ := ℓ) hAc i hy hr)
      have h := fibre_sq_sub_mean_le (A := A) hA hvolA hvol
        (f := fun y : EuclideanSpace ℝ (Fin 3) =>
          Ψ (Submission.BoseGases.kcInsN n i (y, r))) hfm hfb
      simpa only [Q0C.oneRest_def] using h
    change (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox (n + 1) ℓ, (Aind A (x i) * Ψ x) ^ 2
    rw [hQpeel, hSpeel]
    refine integral_mono_ae hintQ hintS ?_
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with r hr
    calc (∫ y in Submission.BoseGases.acube ℓ,
          (Work.UBBInputs8.boxQInd volA A i Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2)
        = ∫ y in Submission.BoseGases.acube ℓ, Aind A y
            * (Ψ (Submission.BoseGases.kcInsN n i (y, r)) - Q0C.oneRest volA A i Ψ r) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with y
          exact boxQInd_sq_kcInsN volA A i Ψ y r
      _ = ∫ y in A, (Ψ (Submission.BoseGases.kcInsN n i (y, r))
            - Q0C.oneRest volA A i Ψ r) ^ 2 :=
          setIntegral_indicator_one_mul hA hAc _
      _ ≤ ∫ y in A, (Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 := hfibre r hr
      _ = ∫ y in Submission.BoseGases.acube ℓ, Aind A y
            * (Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 :=
          (setIntegral_indicator_one_mul hA hAc _).symm
      _ = ∫ y in Submission.BoseGases.acube ℓ,
          (Aind A ((Submission.BoseGases.kcInsN n i (y, r)) i)
            * Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with y
          rw [Submission.BoseGases.kc_insN_apply_same]
          by_cases hy : y ∈ A
          · simp only [Aind, Set.indicator_of_mem hy, one_mul]
          · simp only [Aind, Set.indicator_of_notMem hy, zero_mul]
            norm_num

end Work.BoseFixB1S
