import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EComparison.FubiniZWeight
import Submission.Work.FTS.StrongEps.EComparison.FubiniWeightZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.EComparison

/-! ## The main identity -/

theorem EulerWeakFubini {α L : ℝ} {W : ℝ → ℝ} (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {ρ : ℝ → ℝ} (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hρc : HasCompactSupport ρ) (hsupp : tsupport ρ ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioi 0, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = ∫ t in a..b, deriv (deriv ρ) t *
          (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
            + L * (∫ z in t..b, (z - t) * W z)) := by
  have hab' : a ≤ b := hab.le
  -- 0. `ρ` and its first two derivatives vanish off `(a,b)`
  have hmem : ∀ z : ℝ, z ∉ Set.Ioo a b → ρ z = 0 ∧ deriv ρ z = 0 ∧ deriv (deriv ρ) z = 0 := by
    intro z hz
    have h1 : z ∉ tsupport ρ := fun h => hz (hsupp h)
    have h2 : z ∉ tsupport (deriv ρ) := fun h => h1 (tsupport_deriv_subset h)
    have h3 : z ∉ tsupport (deriv (deriv ρ)) := fun h => h2 (tsupport_deriv_subset h)
    exact ⟨image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2,
      image_eq_zero_of_notMem_tsupport h3⟩
  -- 1. the left-hand side is an integral over `[a,b]`
  have hstep1 : (∫ z in Set.Ioi 0, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = ∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) := by
    rw [intervalIntegral.integral_of_le hab']
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun z hz => lt_trans ha hz.1) (fun z hz => ?_)
    have hznot : z ∉ Set.Ioo a b := fun hcon => hz.2 ⟨hcon.1, hcon.2.le⟩
    obtain ⟨h1, h2, h3⟩ := hmem z hznot
    simp [h1, h2, h3]
  rw [hstep1]
  -- 2. continuity of `ρ`, `ρ'`, `ρ''`
  have hcontρ : ContinuousOn ρ (Set.Icc a b) := (hρ 1).continuous.continuousOn
  have hcontρ1 : ContinuousOn (deriv ρ) (Set.Icc a b) := ((hρ 1).continuous_deriv le_rfl).continuousOn
  have hcontρ2g : Continuous (deriv (deriv ρ)) := by
    have h2 : Continuous (iteratedDeriv 2 ρ) := (hρ 2).continuous_iteratedDeriv 2 (by norm_num)
    convert h2 using 1
    ext t
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hcontρ2 : ContinuousOn (deriv (deriv ρ)) (Set.Icc a b) := hcontρ2g.continuousOn
  -- 3. integrability of `W` and its moments on `[a,b]`
  have hWcc : MeasureTheory.IntegrableOn W (Set.Icc a b) :=
    hW.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le ha hz.1) isCompact_Icc
  have hWzcc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.Icc a b) :=
    hWcc.mul_continuousOn (by fun_prop : ContinuousOn (fun z : ℝ => z) (Set.Icc a b)) isCompact_Icc
  have hWz2cc : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z ^ 2) (Set.Icc a b) :=
    hWcc.mul_continuousOn (by fun_prop : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b)) isCompact_Icc
  have hzWcc : MeasureTheory.IntegrableOn (fun z : ℝ => z * W z) (Set.Icc a b) :=
    hWzcc.congr_fun (fun z _ => mul_comm (W z) z) measurableSet_Icc
  -- 4. the three integrands on the `z`-side
  have hF0 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * ρ z) (Set.Icc a b) :=
    hWcc.mul_continuousOn hcontρ isCompact_Icc
  have hF1 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z * deriv ρ z) (Set.Icc a b) :=
    hWzcc.mul_continuousOn hcontρ1 isCompact_Icc
  have hF2 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z) (Set.Icc a b) :=
    hWz2cc.mul_continuousOn hcontρ2 isCompact_Icc
  have toII : ∀ {f : ℝ → ℝ}, MeasureTheory.IntegrableOn f (Set.Icc a b) → IntervalIntegrable f volume a b := by
    intro f hf
    rw [← Set.uIcc_of_le hab'] at hf
    exact hf.intervalIntegrable
  have iF0 : IntervalIntegrable (fun z : ℝ => W z * ρ z) volume a b := toII hF0
  have iF1 : IntervalIntegrable (fun z : ℝ => W z * z * deriv ρ z) volume a b := toII hF1
  have iF2 : IntervalIntegrable (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z) volume a b := toII hF2
  -- 5. continuity of the two `t`-primitives
  have hAcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z * z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hWzcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hAzcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, z * W z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn (fun z : ℝ => z * W z) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hzWcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hA1cont : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z) (Set.Icc a b) := by
    have h : MeasureTheory.IntegrableOn W (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab']; exact hWcc
    simpa only [Set.uIcc_of_le hab'] using intervalIntegral.continuousOn_primitive_interval_left h
  have hBcont : ContinuousOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z) (Set.Icc a b) := by
    have hcont : ContinuousOn
        (fun t : ℝ => (∫ z in t..b, z * W z) - t * (∫ z in t..b, W z)) (Set.Icc a b) :=
      hAzcont.sub (continuous_id.continuousOn.mul hA1cont)
    refine hcont.congr (fun t ht => ?_)
    have ht1 : a ≤ t := ht.1
    have ht2 : t ≤ b := ht.2
    have hleft : Set.Ioc t b ⊆ Set.Icc a b := fun z hz => ⟨le_trans ht1 hz.1.le, hz.2⟩
    have hright : Set.Ioc b t ⊆ Set.Icc a b :=
      fun z hz => absurd (le_trans hz.2 ht2) (not_le_of_gt hz.1)
    have hi1 : IntervalIntegrable (fun z : ℝ => z * W z) volume t b :=
      ⟨hzWcc.mono_set hleft, hzWcc.mono_set hright⟩
    have hiW : IntervalIntegrable (fun z : ℝ => W z) volume t b :=
      ⟨hWcc.mono_set hleft, hWcc.mono_set hright⟩
    have hi2 : IntervalIntegrable (fun z : ℝ => t * W z) volume t b := hiW.const_mul t
    calc (∫ z in t..b, (z - t) * W z) = ∫ z in t..b, (z * W z - t * W z) :=
          intervalIntegral.integral_congr (fun z _ => by ring)
      _ = (∫ z in t..b, z * W z) - (∫ z in t..b, t * W z) := intervalIntegral.integral_sub hi1 hi2
      _ = (∫ z in t..b, z * W z) - t * (∫ z in t..b, W z) := by
          rw [intervalIntegral.integral_const_mul]
  -- 6. the three integrands on the `t`-side
  have hK1int : MeasureTheory.IntegrableOn (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)) (Set.Icc a b) :=
    hF2.congr_fun (fun z _ => by ring) measurableSet_Icc
  have hK2int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)) (Set.Icc a b) :=
    (hcontρ2.mul hAcont).integrableOn_compact isCompact_Icc
  have hK3int : MeasureTheory.IntegrableOn
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) (Set.Icc a b) :=
    (hcontρ2.mul hBcont).integrableOn_compact isCompact_Icc
  have iK1 : IntervalIntegrable (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)) volume a b := toII hK1int
  have iK2 : IntervalIntegrable
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)) volume a b := toII hK2int
  have iK3 : IntervalIntegrable
      (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) volume a b := toII hK3int
  -- 7. splitting a three-term integrand
  have split3 : ∀ {f1 f2 f3 : ℝ → ℝ}, IntervalIntegrable f1 volume a b →
      IntervalIntegrable f2 volume a b → IntervalIntegrable f3 volume a b →
      (∫ x in a..b, (f1 x + f2 x + f3 x))
        = (∫ x in a..b, f1 x) + (∫ x in a..b, f2 x) + (∫ x in a..b, f3 x) := by
    intro f1 f2 f3 h1 h2 h3
    rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  -- 8. the left-hand side
  have hsplitL : (∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = (∫ z in a..b, L * (W z * ρ z)) + (∫ z in a..b, (-α ^ 2) * (W z * z ^ 2 * deriv (deriv ρ) z))
        + (∫ z in a..b, (-(α * (5 + α))) * (W z * z * deriv ρ z)) := by
    rw [← split3 (f1 := fun z : ℝ => L * (W z * ρ z))
      (f2 := fun z : ℝ => (-α ^ 2) * (W z * z ^ 2 * deriv (deriv ρ) z))
      (f3 := fun z : ℝ => (-(α * (5 + α))) * (W z * z * deriv ρ z))
      (iF0.const_mul L) (iF2.const_mul (-α ^ 2)) (iF1.const_mul (-(α * (5 + α))))]
    exact intervalIntegral.integral_congr (fun z _ => by ring)
  have hLHS2 : (∫ z in a..b, W z * (L * ρ z - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
      = -α ^ 2 * (∫ z in a..b, W z * z ^ 2 * deriv (deriv ρ) z)
        - α * (5 + α) * (∫ z in a..b, W z * z * deriv ρ z)
        + L * (∫ z in a..b, W z * ρ z) := by
    rw [hsplitL,
      intervalIntegral.integral_const_mul L (fun z : ℝ => W z * ρ z),
      intervalIntegral.integral_const_mul (-α ^ 2) (fun z : ℝ => W z * z ^ 2 * deriv (deriv ρ) z),
      intervalIntegral.integral_const_mul (-(α * (5 + α))) (fun z : ℝ => W z * z * deriv ρ z)]
    ring
  -- 9. the right-hand side
  have hsplitR : (∫ t in a..b, deriv (deriv ρ) t *
        (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
          + L * (∫ z in t..b, (z - t) * W z)))
      = (∫ t in a..b, (-α ^ 2) * (deriv (deriv ρ) t * (t ^ 2 * W t)))
        + (∫ t in a..b, (-(α * (5 + α))) * (deriv (deriv ρ) t * (∫ z in t..b, W z * z)))
        + (∫ t in a..b, L * (deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))) := by
    rw [← split3 (f1 := fun t : ℝ => (-α ^ 2) * (deriv (deriv ρ) t * (t ^ 2 * W t)))
      (f2 := fun t : ℝ => (-(α * (5 + α))) * (deriv (deriv ρ) t * (∫ z in t..b, W z * z)))
      (f3 := fun t : ℝ => L * (deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)))
      (iK1.const_mul (-α ^ 2)) (iK2.const_mul (-(α * (5 + α)))) (iK3.const_mul L)]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hRHS2 : (∫ t in a..b, deriv (deriv ρ) t *
        (-(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
          + L * (∫ z in t..b, (z - t) * W z)))
      = -α ^ 2 * (∫ t in a..b, deriv (deriv ρ) t * (t ^ 2 * W t))
        - α * (5 + α) * (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
        + L * (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z)) := by
    rw [hsplitR,
      intervalIntegral.integral_const_mul (-α ^ 2) (fun t : ℝ => deriv (deriv ρ) t * (t ^ 2 * W t)),
      intervalIntegral.integral_const_mul (-(α * (5 + α)))
        (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, W z * z)),
      intervalIntegral.integral_const_mul L
        (fun t : ℝ => deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))]
    ring
  -- 10. the two Fubini steps and the identification of the `t²`-slot
  have hKK : (∫ t in a..b, deriv (deriv ρ) t * (t ^ 2 * W t))
      = ∫ z in a..b, W z * z ^ 2 * deriv (deriv ρ) z :=
    intervalIntegral.integral_congr (fun z _ => by ring)
  have hI2 : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, W z * z))
      = ∫ z in a..b, W z * z * deriv ρ z := FubiniZWeight hW ha hab hρ hρc hsupp
  have hI3 : (∫ t in a..b, deriv (deriv ρ) t * (∫ z in t..b, (z - t) * W z))
      = ∫ z in a..b, W z * ρ z := FubiniWeightZ hW ha hab hρ hρc hsupp
  rw [hLHS2, hRHS2, hKK, hI2, hI3]

end Work.FTS.StrongEps.EComparison
