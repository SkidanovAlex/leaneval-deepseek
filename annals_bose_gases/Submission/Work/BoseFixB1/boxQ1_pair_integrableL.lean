import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A bound of the box projection `PᵢΨ` on the analysis box by a bound `C ≥ 0` of `Ψ`, with **no
positivity hypothesis on the box volume**: the sliding box `dlBox ℓ d u` is empty for most `u`, so
`volA = 0` must be allowed.  In that case `1 / volA = 0` and the projection vanishes identically. -/
private lemma q1_abs_boxPInd_le_of_bound {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure E3).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ C := by
  intro x hx
  have hvol0 : 0 ≤ volA := by
    rw [hvolA, Measure.real_def]; exact ENNReal.toReal_nonneg
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hI : |∫ z in A, Ψ (Function.update x i z)| ≤ C * volA := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3))
      (s := A) (f := fun z : E3 => Ψ (Function.update x i z)) hfin (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hC _ (Submission.BoseGases.update_mem_abox i hx (hAc hz)))
    rw [← hvolA] at h
    simpa only [Real.norm_eq_abs] using h
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A
    · rw [Set.indicator_of_mem hxi]; norm_num
    · rw [Set.indicator_of_notMem hxi]; norm_num
  have hkey : |volA|⁻¹ * (C * volA) ≤ C := by
    rcases eq_or_lt_of_le hvol0 with h0 | hpos
    · rw [← h0, abs_zero, inv_zero, zero_mul]
      exact hC0
    · rw [abs_of_pos hpos]
      have hone : volA⁻¹ * (C * volA) = C := by
        calc volA⁻¹ * (C * volA) = (volA⁻¹ * volA) * C := by ring
          _ = C := by rw [inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      exact le_of_eq hone
  have hfac : Work.UBBInputs8.boxPInd volA A i Ψ x
      = (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) := rfl
  rw [hfac, abs_mul, abs_mul, one_div, abs_inv]
  calc |volA|⁻¹ * |∫ z in A, Ψ (Function.update x i z)|
        * |A.indicator (fun _ => (1 : ℝ)) (x i)|
      ≤ |volA|⁻¹ * (C * volA) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr (abs_nonneg _))) hind
          (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (mul_nonneg hC0 hvol0))
    _ = |volA|⁻¹ * (C * volA) := mul_one _
    _ ≤ C := hkey

/-- Integrability of the peeled pair integrand over the box: the two `P_s`-factors are bounded
(the box projection inherits a bound of its argument, `S` is a.e. strongly measurable and bounded
on the compact box), so `Work.BoseFixB1.integrableOn_slot_wSmallPair` applies with the numerator
`g₂ = g2 v h` (integrable and supported in `ball 0 R0`). -/
theorem boxQ1_pair_integrableL {v : Work.BoseFixB1.E3 → ℝ} {R0 : ℝ}
    (hv_supp : _root_.tsupport v ⊆ Metric.ball (0 : Work.BoseFixB1.E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : Work.BoseFixB1.E3)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1Q ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1P ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1W2 h M ℓ d u (x s) (x t)))
      (Submission.BoseGases.abox N ℓ) := by
  have hA : MeasurableSet (q1Box ℓ d u) := q1Box_measurableSet ℓ d u
  have hAc : q1Box ℓ d u ⊆ Submission.BoseGases.acube ℓ := q1Box_subset_acube ℓ d u
  have hvolA : q1Vol ℓ d u = (volume : Measure E3).real (q1Box ℓ d u) := q1Vol_eq_real ℓ d u
  have hfin : (volume : Measure E3) (q1Box ℓ d u) < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  -- a bound of the state on the compact analysis box
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := Work.BoseFixB1S.exists_abox_bound (N := N) hℓ hΦc
  -- the bound of the `Q`-factor
  have hQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |q1Q ℓ d u t Φ x| ≤ CΦ + |q1Vol ℓ d u|⁻¹ * (CΦ * q1Vol ℓ d u) := by
    intro x hx
    have hx' : ∀ j : Fin N, x j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff N ℓ x).mp hx
    have h := Work.SlotWord.abs_boxQInd_le_of_bound (N := N) ℓ hAc (volA := q1Vol ℓ d u)
      (C := CΦ) hCΦ0 hfin (Ψ := Φ)
      (fun y hy => hCΦ y ((Submission.BoseGases.mem_abox_iff N ℓ y).mpr hy)) t x hx'
    rw [← hvolA] at h
    simpa only [q1Q, q1Vol, q1Box] using h
  have hCq0 : 0 ≤ CΦ + |q1Vol ℓ d u|⁻¹ * (CΦ * q1Vol ℓ d u) :=
    add_nonneg hCΦ0
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (mul_nonneg hCΦ0 (q1Vol_nonneg ℓ d u)))
  -- the bounds of the two `P_s`-factors
  have hPt : ∀ x ∈ Submission.BoseGases.abox N ℓ, |q1P ℓ d u t Φ x| ≤ CΦ := by
    intro x hx
    have h := q1_abs_boxPInd_le_of_bound (ℓ := ℓ) (volA := q1Vol ℓ d u) (A := q1Box ℓ d u)
      hℓ hA hvolA hAc t (Ψ := Φ) hCΦ0 hCΦ x hx
    simpa only [q1P, q1Vol, q1Box] using h
  have hPs1 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |q1P ℓ d u s (q1Q ℓ d u t Φ) x| ≤ CΦ + |q1Vol ℓ d u|⁻¹ * (CΦ * q1Vol ℓ d u) := by
    intro x hx
    have h := q1_abs_boxPInd_le_of_bound (ℓ := ℓ) (volA := q1Vol ℓ d u) (A := q1Box ℓ d u)
      hℓ hA hvolA hAc s (Ψ := q1Q ℓ d u t Φ) hCq0 hQb x hx
    simpa only [q1P, q1Vol, q1Box] using h
  have hPs2 : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |q1P ℓ d u s (q1P ℓ d u t Φ) x| ≤ CΦ := by
    intro x hx
    have h := q1_abs_boxPInd_le_of_bound (ℓ := ℓ) (volA := q1Vol ℓ d u) (A := q1Box ℓ d u)
      hℓ hA hvolA hAc s (Ψ := q1P ℓ d u t Φ) hCΦ0 hPt x hx
    simpa only [q1P, q1Vol, q1Box] using h
  -- measurability of the two `P_s`-factors
  have hΦm : Measurable Φ := hΦc.measurable
  have hQm : Measurable (q1Q ℓ d u t Φ) := by
    have h := Work.SlotWord.measurable_boxQInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA t
      (Ψ := Φ) hΦm
    simpa only [q1Q, q1Vol, q1Box] using h
  have hP1m : Measurable (q1P ℓ d u s (q1Q ℓ d u t Φ)) := by
    have h := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA s
      (Ψ := q1Q ℓ d u t Φ) hQm
    simpa only [q1P, q1Vol, q1Box] using h
  have hP2m : Measurable (q1P ℓ d u s (q1P ℓ d u t Φ)) := by
    have hPt_m : Measurable (q1P ℓ d u t Φ) := by
      have h := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA t
        (Ψ := Φ) hΦm
      simpa only [q1P, q1Vol, q1Box] using h
    have h := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA s
      (Ψ := q1P ℓ d u t Φ) hPt_m
    simpa only [q1P, q1Vol, q1Box] using h
  -- the peeled pair integrand, with the `w₂`-kernel slot
  have hSb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(fun x : Submission.BoseGases.X N =>
          q1P ℓ d u s (q1Q ℓ d u t Φ) x * q1P ℓ d u s (q1P ℓ d u t Φ) x) x|
        ≤ (CΦ + |q1Vol ℓ d u|⁻¹ * (CΦ * q1Vol ℓ d u)) * CΦ := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    refine ae_of_all _ (fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul (hPs1 x hx) (hPs2 x hx) (abs_nonneg _) hCq0
  have hInt := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
    (f := Submission.BoseGases.g2 v h) (M := M) (i := s) (j := t)
    (S := fun x : Submission.BoseGases.X N =>
      q1P ℓ d u s (q1Q ℓ d u t Φ) x * q1P ℓ d u s (q1P ℓ d u t Φ) x)
    (B := (CΦ + |q1Vol ℓ d u|⁻¹ * (CΦ * q1Vol ℓ d u)) * CΦ)
    hℓ hd (Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h)
    (fun z hz => Submission.BoseGases.g2_zero_of_norm_ge hv_supp hz h)
    hM hR hRχ u hst ((hP1m.mul hP2m).aestronglyMeasurable) (mul_nonneg hCq0 hCΦ0) hSb
  simpa only [q1W2] using hInt

end Work.BoseFixB1
