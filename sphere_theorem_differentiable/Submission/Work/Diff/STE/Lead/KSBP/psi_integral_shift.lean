import Mathlib
import Submission.Work.Diff.STE.Lead.KSBP.Defs
import Submission.Work.Diff.STE.Lead.KSBP.four_abs_le_norm_exp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integral of a product of translates of the weight `psi`

`psi ε t = 1` for `‖e^{2πit} - 1‖ < 4ε` and `(4ε/‖e^{2πit} - 1‖)²` otherwise.  Since `psi ε` is
`1`-periodic, the translate `z ↦ ∫_{x ∈ (0,1]ⁿ} ∏ᵢ psi ε (zᵢ - xᵢ)` equals the integral for `z = 0`,
and the integrand factorises over the coordinates:

`∫_{x ∈ unitCube} ∏ᵢ psi ε (zᵢ - xᵢ) = (∫_0^1 psi ε)ⁿ ≤ (4ε)ⁿ`.

The one dimensional input is the pointwise bound

`psi ε t ≤ (if |t| ≤ ε then 1 else (ε/|t|)²)`   for `|t| ≤ 1/2`,

which follows from `4|t| ≤ ‖e^{2πit} - 1‖` on the fundamental domain `|t| ≤ 1/2` (where
`‖e^{2πit} - 1‖ = 2|sin(πt)| ≥ 4|t|`), together with the explicit computation
`∫_{-1/2}^{1/2} (if |t| ≤ ε then 1 else (ε/|t|)²) = 4ε - 4ε² ≤ 4ε` for `ε ≤ 1/2` (for `ε ≥ 1/2`
the weight is identically `1`).

All auxiliary declarations are `private`: the only public name is `psi_integral_shift`.

The one dimensional bound `∫_0^1 psi ε ≤ 4 ε` is proved here from scratch (the pieces
`∫_ε^{1/2} (ε/t)² ≤ ε` and the symmetry `t ↦ -t`); the delegated sibling
`Work.Diff.STE.Lead.KSBP.integral_majorant_half` gives the same half-line estimate in one step and
can be substituted for them.  The norm inequality `4|t| ≤ ‖e^{2πit} - 1‖` is taken from the
delegated module `Work.Diff.STE.Lead.KSBP.four_abs_le_norm_exp`.
-/

noncomputable section

open MeasureTheory

namespace Work.Diff.STE.Lead.KSBP

/-! ## Elementary properties of `psi` -/

/-- The exponential distance `‖exp(2πit) - 1‖` occurring in the definition of `psi`. -/
private abbrev expNormDist (t : ℝ) : ℝ := ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖

private lemma expNormDist_nonneg (t : ℝ) : 0 ≤ expNormDist t := by
  unfold expNormDist; positivity

/-- Unfolding of `psi`. -/
private lemma psi_apply (ε t : ℝ) :
    psi ε t = if expNormDist t < 4 * ε then 1 else (4 * ε / expNormDist t) ^ 2 := by
  unfold psi; rfl

private lemma psi_nonneg_aux (ε t : ℝ) : 0 ≤ psi ε t := by
  rw [psi_apply]; split_ifs <;> positivity

private lemma psi_le_one {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : psi ε t ≤ 1 := by
  rw [psi_apply]
  split_ifs with h
  · exact le_rfl
  · have h4 : 4 * ε ≤ expNormDist t := Std.not_lt.mp h
    have hen : 0 ≤ expNormDist t := expNormDist_nonneg t
    have h0 : 0 ≤ 4 * ε / expNormDist t := div_nonneg (by linarith) hen
    have h1 : 4 * ε / expNormDist t ≤ 1 := by
      rcases eq_or_lt_of_le h4 with h' | h'
      · rw [← h']
        rcases eq_or_ne ε 0 with rfl | hε0
        · norm_num
        · rw [div_self (by positivity : (4 : ℝ) * ε ≠ 0)]
      · rw [div_le_one (by linarith)]; exact h4
    calc (4 * ε / expNormDist t) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 1 := by norm_num

private lemma expNormDist_add_one (t : ℝ) : expNormDist (t + 1) = expNormDist t := by
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((t + 1 : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨1, by push_cast; ring⟩
  unfold expNormDist
  rw [hexp]

private lemma psi_add_one (ε t : ℝ) : psi ε (t + 1) = psi ε t := by
  rw [psi_apply, psi_apply, expNormDist_add_one]

private lemma psi_periodic (ε : ℝ) : Function.Periodic (psi ε) 1 := fun t => psi_add_one ε t

private lemma measurable_expNormDist : Measurable expNormDist := by
  unfold expNormDist; fun_prop

private lemma measurable_psi (ε : ℝ) : Measurable (psi ε) := by
  have h : psi ε = fun t : ℝ =>
      if expNormDist t < 4 * ε then (1 : ℝ) else (4 * ε / expNormDist t) ^ 2 :=
    funext (psi_apply ε)
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_expNormDist measurable_const) measurable_const
    ((measurable_const.div measurable_expNormDist).pow_const 2)

/-! ## The one dimensional majorant -/

/-- The majorant of `psi` on the fundamental domain `|t| ≤ 1/2`. -/
private def psiMaj (ε t : ℝ) : ℝ := if |t| ≤ ε then 1 else (ε / |t|) ^ 2

private lemma psiMaj_nonneg (ε t : ℝ) : 0 ≤ psiMaj ε t := by
  unfold psiMaj; split_ifs <;> positivity

private lemma psiMaj_le_one {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : psiMaj ε t ≤ 1 := by
  unfold psiMaj
  split_ifs with h
  · exact le_rfl
  · have h' : ε < |t| := Std.not_le.mp h
    have ht : 0 < |t| := lt_of_le_of_lt hε h'
    have h0 : 0 ≤ ε / |t| := div_nonneg hε ht.le
    have h1 : ε / |t| ≤ 1 := by
      rw [div_le_one ht]; exact h'.le
    calc (ε / |t|) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 1 := by norm_num

private lemma abs_psiMaj_le_one {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : |psiMaj ε t| ≤ 1 := by
  rw [abs_of_nonneg (psiMaj_nonneg ε t)]; exact psiMaj_le_one hε t

private lemma measurable_psiMaj (ε : ℝ) : Measurable (psiMaj ε) := by
  have h : psiMaj ε = fun t : ℝ => if |t| ≤ ε then (1 : ℝ) else (ε / |t|) ^ 2 :=
    funext fun _ => rfl
  rw [h]
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_const
    ((measurable_const.div continuous_abs.measurable).pow_const 2)

private lemma psiMaj_neg (ε t : ℝ) : psiMaj ε (-t) = psiMaj ε t := by
  unfold psiMaj; rw [abs_neg]

private lemma intervalIntegrable_psiMaj {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    IntervalIntegrable (psiMaj ε) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1 : ℝ))
    (intervalIntegrable_const (c := (1 : ℝ))) (measurable_psiMaj ε).aestronglyMeasurable ?_
  filter_upwards with t
  simpa using abs_psiMaj_le_one hε t

private lemma intervalIntegrable_psi {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    IntervalIntegrable (psi ε) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1 : ℝ))
    (intervalIntegrable_const (c := (1 : ℝ))) (measurable_psi ε).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg_aux ε t)]
  exact psi_le_one hε t

/-! ## The trig/norm inequality `4|t| ≤ ‖exp(2πit) - 1‖` for `|t| ≤ 1/2` -/

/-- The trig inequality `4|t| ≤ ‖exp(2πit) - 1‖` on `|t| ≤ 1/2`.  This is the delegated lemma
`Work.Diff.STE.Lead.KSBP.four_abs_le_norm_exp`, restated in terms of `expNormDist`. -/
private lemma four_abs_le_expNormDist (t : ℝ) (ht : |t| ≤ 1 / 2) : 4 * |t| ≤ expNormDist t :=
  four_abs_le_norm_exp t ht

/-- Pointwise domination of `psi` by its majorant on `|t| ≤ 1/2`. -/
private lemma psi_le_psiMaj {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    psi ε t ≤ psiMaj ε t := by
  unfold psiMaj
  by_cases h : |t| ≤ ε
  · rw [if_pos h]
    exact psi_le_one hε.le t
  · rw [if_neg h]
    have hlt : ε < |t| := Std.not_le.mp h
    have h4 : 4 * |t| ≤ expNormDist t := four_abs_le_expNormDist t ht
    have hfar : ¬ expNormDist t < 4 * ε := by
      intro hc
      have : 4 * |t| < 4 * ε := lt_of_le_of_lt h4 hc
      linarith [abs_nonneg t]
    rw [psi_apply, if_neg hfar]
    have hen : 0 < expNormDist t := lt_of_lt_of_le (by linarith [abs_nonneg t]) h4
    have h0 : 0 ≤ 4 * ε / expNormDist t := div_nonneg (by linarith) hen.le
    have hle : 4 * ε / expNormDist t ≤ ε / |t| := by
      rw [div_le_div_iff₀ hen (by linarith)]
      nlinarith [h4, hε.le, abs_nonneg t]
    calc (4 * ε / expNormDist t) ^ 2 ≤ (ε / |t|) ^ 2 := pow_le_pow_left₀ h0 hle 2
      _ = (ε / |t|) ^ 2 := rfl

/-! ## The one dimensional integral bounds -/

/-- `∫_ε^{1/2} (ε/t)² ≤ ε` for `0 < ε ≤ 1/2`. -/
private lemma integral_inv_sq_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∫ t in ε..(1 / 2 : ℝ), (ε / t) ^ 2 ≤ ε := by
  have hderiv : ∀ t ∈ Set.uIcc ε (1 / 2 : ℝ),
      HasDerivAt (fun s : ℝ => -(ε ^ 2) * s⁻¹) ((ε / t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hε2, Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hε ht.1)
    have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht0
    have h2 := h1.const_mul (-(ε ^ 2))
    have heq : -(ε ^ 2) * (-(t ^ 2)⁻¹) = (ε / t) ^ 2 := by
      rw [div_eq_mul_inv, mul_pow, inv_pow]; ring
    rwa [heq] at h2
  have hint : IntervalIntegrable (fun t : ℝ => (ε / t) ^ 2) volume ε (1 / 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hε2]
    refine (continuousOn_const.div continuousOn_id ?_).pow 2
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hε ht.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  have hval : -(ε ^ 2) * (1 / 2 : ℝ)⁻¹ - -(ε ^ 2) * ε⁻¹ = ε - 2 * ε ^ 2 := by
    field_simp
    ring
  rw [hval]
  nlinarith [sq_nonneg ε]

/-- The integral of the majorant over the symmetric fundamental domain is at most `4ε`. -/
private lemma integral_psiMaj_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∫ t in (-(1 / 2) : ℝ)..(1 / 2), psiMaj ε t ≤ 4 * ε := by
  have hI1 : IntervalIntegrable (psiMaj ε) volume (-(1 / 2) : ℝ) (-ε) :=
    intervalIntegrable_psiMaj hε.le _ _
  have hI2 : IntervalIntegrable (psiMaj ε) volume (-ε) ε := intervalIntegrable_psiMaj hε.le _ _
  have hI3 : IntervalIntegrable (psiMaj ε) volume ε (1 / 2 : ℝ) :=
    intervalIntegrable_psiMaj hε.le _ _
  have hI12 : IntervalIntegrable (psiMaj ε) volume (-(1 / 2) : ℝ) ε :=
    intervalIntegrable_psiMaj hε.le _ _
  have hsplit : ∫ t in (-(1 / 2) : ℝ)..(1 / 2), psiMaj ε t
      = ((∫ t in (-(1 / 2) : ℝ)..(-ε), psiMaj ε t) + (∫ t in (-ε)..ε, psiMaj ε t))
        + (∫ t in ε..(1 / 2 : ℝ), psiMaj ε t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hI12 hI3,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  -- the middle piece
  have hmid : ∫ t in (-ε)..ε, psiMaj ε t = 2 * ε := by
    have hc : ∀ t ∈ Set.uIcc (-ε) ε, psiMaj ε t = (1 : ℝ) := by
      intro t ht
      have ht' : |t| ≤ ε := by
        rw [Set.uIcc_of_le (by linarith : -ε ≤ ε), Set.mem_Icc] at ht
        rw [abs_le]; exact ⟨ht.1, ht.2⟩
      unfold psiMaj; rw [if_pos ht']
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  -- the left piece, by symmetry
  have hleft : ∫ t in (-(1 / 2) : ℝ)..(-ε), psiMaj ε t ≤ ε := by
    have hc : ∀ t ∈ Set.uIcc (-(1 / 2) : ℝ) (-ε), psiMaj ε t = (ε / |t|) ^ 2 := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (-(1 / 2) : ℝ) ≤ -ε), Set.mem_Icc] at ht
      have hge : ε ≤ |t| := by
        rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]; linarith [ht.2]
      unfold psiMaj
      by_cases h : |t| ≤ ε
      · rw [if_pos h]
        have heq : |t| = ε := le_antisymm h hge
        rw [heq, div_self hε.ne']; norm_num
      · rw [if_neg h]
    rw [intervalIntegral.integral_congr hc]
    have hcomp : ∫ t in (-(1 / 2) : ℝ)..(-ε), (ε / |t|) ^ 2
        = ∫ t in ε..(1 / 2 : ℝ), (ε / |t|) ^ 2 := by
      have h := intervalIntegral.integral_comp_neg (f := fun t : ℝ => (ε / |t|) ^ 2)
        (a := ε) (b := (1 / 2 : ℝ))
      simpa only [abs_neg] using h.symm
    rw [hcomp]
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => (ε / t) ^ 2) (fun t ht => by
      rw [Set.uIcc_of_le hε2, Set.mem_Icc] at ht
      rw [abs_of_pos (lt_of_lt_of_le hε ht.1)])]
    exact integral_inv_sq_le hε hε2
  -- the right piece
  have hright : ∫ t in ε..(1 / 2 : ℝ), psiMaj ε t ≤ ε := by
    have hc : ∀ t ∈ Set.uIcc ε (1 / 2 : ℝ), psiMaj ε t = (ε / t) ^ 2 := by
      intro t ht
      rw [Set.uIcc_of_le hε2, Set.mem_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hε ht.1
      unfold psiMaj
      by_cases h : |t| ≤ ε
      · rw [if_pos h]
        have heq : t = ε := le_antisymm (by rw [← abs_of_pos ht0]; exact h) ht.1
        rw [heq, div_self hε.ne']; norm_num
      · rw [if_neg h, abs_of_pos ht0]
    rw [intervalIntegral.integral_congr hc]
    exact integral_inv_sq_le hε hε2
  rw [hsplit, hmid]
  linarith

/-- The one dimensional bound `∫_0^1 psi ε ≤ 4ε`. -/
private lemma integral_psi_Ioc_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1, psi ε t ≤ 4 * ε := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsym : ∫ t in (0 : ℝ)..1, psi ε t = ∫ t in (-(1 / 2) : ℝ)..(1 / 2), psi ε t := by
    have h := (psi_periodic ε).intervalIntegral_add_eq (-(1 / 2)) 0
    rw [show (0 : ℝ) + 1 = 1 by norm_num,
      show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num] at h
    exact h.symm
  rw [hsym]
  rcases lt_or_ge ε (1 / 2) with hε2 | hε2
  · refine le_trans ?_ (integral_psiMaj_le hε hε2.le)
    refine intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_psi hε.le _ _)
      (intervalIntegrable_psiMaj hε.le _ _) ?_
    intro t ht
    exact psi_le_psiMaj hε (by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩)
  · have hpsi : ∀ t, psi ε t = 1 := by
      intro t
      rw [psi_apply]
      by_cases h : expNormDist t < 4 * ε
      · rw [if_pos h]
      · rw [if_neg h]
        have hle : expNormDist t ≤ 2 := by
          unfold expNormDist
          have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
            rw [show 2 * Real.pi * Complex.I * (t : ℂ)
                = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          calc ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖
              ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [h1]; norm_num
        have hge : 4 * ε ≤ expNormDist t := Std.not_lt.mp h
        have h4ε : (4 : ℝ) * ε ≠ 0 := by linarith
        have h2 : expNormDist t = 4 * ε := le_antisymm (by linarith) hge
        rw [h2, div_self h4ε]
        norm_num
    calc ∫ t in (-(1 / 2) : ℝ)..(1 / 2), psi ε t
        = ∫ t in (-(1 / 2) : ℝ)..(1 / 2), (1 : ℝ) :=
          intervalIntegral.integral_congr (fun t _ => hpsi t)
      _ = 1 := by rw [intervalIntegral.integral_const]; norm_num
      _ ≤ 4 * ε := by linarith

/-- The shift of the integrand by a real number does not change its integral over one period. -/
private lemma integral_shift_psi (ε z : ℝ) :
    ∫ t in Set.Ioc (0 : ℝ) 1, psi ε (z - t) = ∫ t in Set.Ioc (0 : ℝ) 1, psi ε t := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_sub_left (fun u => psi ε u) z, sub_zero]
  have h := (psi_periodic ε).intervalIntegral_add_eq (z - 1) 0
  simpa using h

/-! ## The multidimensional statement -/

theorem psi_integral_shift {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Fin n → ℝ) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ∏ i, Work.Diff.STE.Lead.KSBP.psi ε (z i - x i)
      ≤ (4 * ε) ^ n := by
  have hprod : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ∏ i, psi ε (z i - x i)
      = ∏ i : Fin n, ∫ t in Set.Ioc (0 : ℝ) 1, psi ε t := by
    rw [Work.Diff.STE.unitCube, MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
    have hpc : (∏ i : Fin n, ∫ t in Set.Ioc (0 : ℝ) 1, psi ε t)
        = ∏ i : Fin n, ∫ t in Set.Ioc (0 : ℝ) 1, psi ε (z i - t) :=
      Finset.prod_congr rfl (fun i _ => (integral_shift_psi ε (z i)).symm)
    rw [hpc]
    exact MeasureTheory.integral_fintype_prod_eq_prod (fun i t => psi ε (z i - t))
  rw [hprod]
  have hpow : (∏ i : Fin n, ∫ t in Set.Ioc (0 : ℝ) 1, psi ε t)
      = (∫ t in Set.Ioc (0 : ℝ) 1, psi ε t) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow]
  exact pow_le_pow_left₀ (integral_nonneg fun t => psi_nonneg_aux ε t)
    (integral_psi_Ioc_le hε hε1) n

end Work.Diff.STE.Lead.KSBP
