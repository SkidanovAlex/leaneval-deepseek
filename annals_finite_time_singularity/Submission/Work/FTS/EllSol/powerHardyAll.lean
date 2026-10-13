import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.UopHk.powerHardyFinite

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The power Hardy inequality on `(0,a)` for every exponent `η ≥ 0`

Main statement `Work.FTS.EllSol.powerHardyAll`: there is a universal constant `C > 0` such
that for every `η ≥ 0`, every `a > 0` and every `h` of class `C¹` on `(0,a)` with
`h → 0` at `0⁺`, whose `t^{-η}`-weighted squared derivative is integrable on `(0,a)`,

  `t ↦ h t ^ 2 * t ^ (-(2+η))` is integrable on `(0,a)`, and
  `∫_0^a h² t^{-(2+η)} ≤ C ∫_0^a (h')² t^{-η}`.

The constant `C = 4` works: the auxiliary `powerHardyFiniteAll` below is the sharp bound
`∫_0^a h² t^{-(2+η)} ≤ 4/(1+η)² ∫_0^a (h')² t^{-η}` (the classical integration-by-parts /
weighted Cauchy–Schwarz proof, exactly as in `Work.FTS.EllipticEst.UopHk.powerHardyFinite`,
noting that the hypothesis `η < 1` of that statement is not used by its argument — only
`0 ≤ η` is), and `4/(1+η)² ≤ 4` for `η ≥ 0`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllSol

-- the two general-purpose ingredients of the argument (neither restricts `η`)
open Work.FTS.EllipticEst.UopHk

theorem powerHardyFiniteAll {η a : ℝ} (hη : 0 ≤ η) (ha : 0 < a) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 h (Set.Ioo 0 a))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => h t ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a) ∧
      (∫ t in Set.Ioo 0 a, h t ^ 2 * t ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η) := by
  have hβpos : (0 : ℝ) < 1 + η := by linarith
  have hB_Ioc : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
      (Set.Ioc 0 a) := hB.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hDcont : ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) a) :=
    hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hFcont : ContinuousOn (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η))) (Set.Ioo (0 : ℝ) a) :=
    (hsm.continuousOn.pow 2).mul (fun x hx =>
      (Real.continuousAt_rpow_const x (-(2 + η)) (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
  have hHcont : ContinuousOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η)) (Set.Ioo (0 : ℝ) a) :=
    (hDcont.pow 2).mul (fun x hx =>
      (Real.continuousAt_rpow_const x (-η) (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
  -- the endpoints and inclusions for the family of intervals
  have hεpos : ∀ n : ℕ, (0 : ℝ) < a / 2 ^ (n + 2) := fun n => div_pos ha (by positivity)
  have hεb : ∀ n : ℕ, a / 2 ^ (n + 2) < a - a / 2 ^ (n + 2) := by
    intro n
    have h3 : (0 : ℝ) < 2 ^ (n + 2) := by positivity
    have h4 : (2 : ℝ) < 2 ^ (n + 2) := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 ≤ n + 2)
      have h5 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [h5] at h
      linarith
    have h5 : a / 2 ^ (n + 2) * 2 ^ (n + 2) = a := by field_simp
    have h6 : (a - a / 2 ^ (n + 2)) * 2 ^ (n + 2) = a * 2 ^ (n + 2) - a := by
      rw [sub_mul, h5]
    rw [div_lt_iff₀ h3, h6]
    nlinarith [mul_lt_mul_of_pos_left h4 ha]
  have hb_lt : ∀ n : ℕ, a - a / 2 ^ (n + 2) < a := by
    intro n
    have := hεpos n
    linarith
  have hpow_le : ∀ n : ℕ, a / 2 ^ ((n + 1) + 2) ≤ a / 2 ^ (n + 2) := fun n =>
    div_le_div_of_nonneg_left ha.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hpow_le' : ∀ n : ℕ, a / 2 ^ (n + 2) ≤ a / 2 ^ (0 + 2) := fun n =>
    div_le_div_of_nonneg_left ha.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hsub_s : ∀ n : ℕ, Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
      ⊆ Set.Ioo (0 : ℝ) a := fun n x hx =>
    ⟨lt_trans (hεpos n) hx.1, lt_of_le_of_lt hx.2 (hb_lt n)⟩
  have hsub_Icc : ∀ n : ℕ, Set.Icc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
      ⊆ Set.Ioo (0 : ℝ) a := fun n x hx =>
    ⟨lt_of_lt_of_le (hεpos n) hx.1, lt_of_le_of_lt hx.2 (hb_lt n)⟩
  have hF_int : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))) := fun n =>
    ((hFcont.mono (hsub_Icc n)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hsubIoc0 : Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)) ⊆ Set.Ioc 0 a := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by rw [zero_add]; exact div_le_self ha.le (by norm_num))⟩
  -- the good point in each interval
  have hex : ∀ x ∈ Set.Ioo (0 : ℝ) a, ∃ n : ℕ,
      x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)) := by
    intro x hx
    have hlim1 : Filter.Tendsto (fun n : ℕ => a / 2 ^ (n + 2)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
          (tendsto_add_atTop_nat 2))
    have hlim2 : Filter.Tendsto (fun n : ℕ => a - a / 2 ^ (n + 2)) Filter.atTop (nhds a) := by
      have h := hlim1.const_sub a
      simpa using h
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, a / 2 ^ (n + 2) < x :=
      hlim1.eventually (eventually_lt_nhds hx.1)
    have h2 : ∀ᶠ n : ℕ in Filter.atTop, x < a - a / 2 ^ (n + 2) :=
      hlim2.eventually (eventually_gt_nhds hx.2)
    exact ((h1.and h2).mono (fun n hn => ⟨hn.1, le_of_lt hn.2⟩)).exists
  -- ## Step 1: the slice estimates
  have key : ∀ n : ℕ,
      (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
              (deriv h x) ^ 2 * x ^ (-η)) := by
    intro n
    have hε := hεpos n
    have hsl : (1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          h x ^ 2 * x ^ (-(2 + η)))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η))
          + (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η)) := by
      have hsl' := hardySliceFin (β := 1 + η) hβpos hε (hεb n) (g := h)
        (hsm.continuousOn.mono (hsub_Icc n))
        (fun x hx => ((hsm.differentiableOn one_ne_zero x
          (hsub_Icc n ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).differentiableAt
            (isOpen_Ioo.mem_nhds
              (hsub_Icc n ⟨le_of_lt hx.1, le_of_lt hx.2⟩))).hasDerivAt)
        (hDcont.mono (hsub_Icc n))
      simpa only [show -((1 + η) + 1) = -(2 + η) by ring,
        show (1 - (1 + η)) = -η by ring] using hsl'
    have hcsf : (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η))
        ≤ ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η) := by
      have hlt : a / 2 ^ (n + 2) < a :=
        div_lt_self ha (one_lt_pow₀ (by norm_num) (by omega))
      have hcs := hardyCSBound (a := a) (η := η) (t := a / 2 ^ (n + 2))
        hη hε hlt hsm h0 hB_Ioc
      have hprod : (a / 2 ^ (n + 2)) ^ (1 + η) * (a / 2 ^ (n + 2)) ^ (-(1 + η)) = 1 := by
        rw [← Real.rpow_add hε, show (1 + η) + (-(1 + η)) = 0 by ring, Real.rpow_zero]
      have h2 := mul_le_mul_of_nonneg_right hcs (Real.rpow_pos_of_pos hε (-(1 + η))).le
      calc (h (a / 2 ^ (n + 2))) ^ 2 * (a / 2 ^ (n + 2)) ^ (-(1 + η))
          ≤ (((a / 2 ^ (n + 2)) ^ (1 + η)
              * ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
            * (a / 2 ^ (n + 2)) ^ (-(1 + η)) := h2
        _ = ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η) := by
            rw [show (((a / 2 ^ (n + 2)) ^ (1 + η)
                * ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
                * (a / 2 ^ (n + 2)) ^ (-(1 + η))
                = (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η))
                  * ((a / 2 ^ (n + 2)) ^ (1 + η)
                    * (a / 2 ^ (n + 2)) ^ (-(1 + η))) from by ring,
              hprod, mul_one]
    have hBnd : (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          (deriv h x) ^ 2 * x ^ (-η))
        ≤ ∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η) := by
      refine setIntegral_mono_set hB ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · exact Filter.Eventually.of_forall (fun x hx => hsub_s n hx)
    have hstep : (1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
          h x ^ 2 * x ^ (-(2 + η)))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)) := by
      have h1 : (2 / (1 + η)) * (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η))
          ≤ (2 / (1 + η)) * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)) :=
        mul_le_mul_of_nonneg_left hBnd (by positivity)
      linarith [hsl, h1, hcsf]
    have hne : (1 + η) ≠ 0 := ne_of_gt hβpos
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 / (1 + η))
    have e1 : (2 / (1 + η)) * ((1 + η) / 2 * (∫ x in Set.Ioc (a / 2 ^ (n + 2))
          (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))))
        = (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
      rw [← mul_assoc, mul_comm (2 / (1 + η)) ((1 + η) / 2)]
      field_simp
    have e2 : (2 / (1 + η)) * ((2 / (1 + η)) * (∫ x in Set.Ioo (0 : ℝ) a,
            (deriv h x) ^ 2 * x ^ (-η))
          + (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η)))
        = 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
          + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
              (deriv h x) ^ 2 * x ^ (-η)) := by
      field_simp
      ring
    linarith [hmul, e1, e2]
  -- ## Step 2: monotonicity and boundedness of the sequence of slice integrals
  have hA_mono : Monotone (fun n : ℕ => ∫ x in Set.Ioc (a / 2 ^ (n + 2))
      (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    refine setIntegral_mono_set (hF_int (n + 1)) ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall (fun x hx =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans (hεpos (n + 1)) hx.1).le _)))
    · refine Filter.Eventually.of_forall (fun x hx => ⟨?_, ?_⟩)
      · have h4 := hpow_le n
        linarith [hx.1]
      · have h4 := hpow_le n
        linarith [hx.2]
  have hA_bdd : BddAbove (Set.range (fun n : ℕ => ∫ x in Set.Ioc (a / 2 ^ (n + 2))
      (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η)))) := by
    refine ⟨4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
      + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)),
          (deriv h x) ^ 2 * x ^ (-η)), ?_⟩
    rintro y ⟨n, rfl⟩
    have h1 := key n
    have h2 : (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)), (deriv h x) ^ 2 * x ^ (-η))
        ≤ (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)), (deriv h x) ^ 2 * x ^ (-η)) := by
      refine setIntegral_mono_set (hB_Ioc.mono_set hsubIoc0) ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun x hx =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · refine Filter.Eventually.of_forall (fun x hx => ⟨hx.1, ?_⟩)
        exact le_trans hx.2 (hpow_le' n)
    have h3 : 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
          (deriv h x) ^ 2 * x ^ (-η))
        ≤ 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2)),
            (deriv h x) ^ 2 * x ^ (-η)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith [h1, h3]
  -- ## Step 3: the tails vanish
  have hD_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
      (deriv h x) ^ 2 * x ^ (-η)) Filter.atTop (nhds 0) := by
    have hanti : Antitone (fun n : ℕ => Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2))) := by
      refine antitone_nat_of_succ_le (fun n => ?_)
      exact Set.Ioc_subset_Ioc le_rfl (hpow_le n)
    have h0int : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
        (Set.Ioc (0 : ℝ) (a / 2 ^ (0 + 2))) := hB_Ioc.mono_set hsubIoc0
    have h := hanti.tendsto_setIntegral (fun n => measurableSet_Ioc) h0int
    have hinter : (⋂ n : ℕ, Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2))) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx0 : 0 < x := (Set.mem_iInter.mp hx 0).1
      have hxle : ∀ n : ℕ, x ≤ a / 2 ^ (n + 2) := fun n => (Set.mem_iInter.mp hx n).2
      have hlim : Filter.Tendsto (fun n : ℕ => a / 2 ^ (n + 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
            (tendsto_add_atTop_nat 2))
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hx0)).exists
      exact absurd (lt_of_le_of_lt (hxle n) hn) (lt_irrefl x)
    rw [hinter] at h
    simpa using h
  have hD_lim : Filter.Tendsto
      (fun n : ℕ => 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η))
        + 2 / (1 + η) * (∫ x in Set.Ioc (0 : ℝ) (a / 2 ^ (n + 2)),
            (deriv h x) ^ 2 * x ^ (-η)))
      Filter.atTop
      (nhds (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
        (deriv h x) ^ 2 * x ^ (-η)))) := by
    have h := (hD_tend.const_mul (2 / (1 + η))).const_add
      (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)))
    simpa using h
  have hsup : (⨆ n : ℕ, (∫ x in Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2)),
      h x ^ 2 * x ^ (-(2 + η))))
      ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η)) :=
    le_of_tendsto_of_tendsto' (tendsto_atTop_ciSup hA_mono hA_bdd) hD_lim key
  -- ## Step 4: monotone convergence to the full interval
  have hMCT : ∫⁻ x in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (h x ^ 2 * x ^ (-(2 + η)))
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
          (deriv h x) ^ 2 * x ^ (-η))) := by
    have hsup2 : (⨆ n : ℕ, ENNReal.ofReal (∫ x in Set.Ioc (a / 2 ^ (n + 2))
        (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))))
        ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
            (deriv h x) ^ 2 * x ^ (-η))) :=
      le_trans (iSup_le (fun n => ENNReal.ofReal_le_ofReal (le_ciSup hA_bdd n)))
        (ENNReal.ofReal_le_ofReal hsup)
    have hpoint : ∀ x : ℝ,
        (⨆ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x)
        = (Set.Ioo (0 : ℝ) a).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x := by
      intro x
      by_cases hx : x ∈ Set.Ioo (0 : ℝ) a
      · obtain ⟨N, hN⟩ := hex x hx
        refine le_antisymm (iSup_le (fun n => ?_)) ?_
        · by_cases hxn : x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
          · rw [Set.indicator_of_mem hxn, Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hxn]
            exact zero_le
        · rw [Set.indicator_of_mem hx]
          calc (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x
              = (Set.Ioc (a / 2 ^ (N + 2)) (a - a / 2 ^ (N + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x :=
                (Set.indicator_of_mem hN
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))).symm
            _ ≤ ⨆ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x :=
                le_iSup (fun n : ℕ => (Set.Ioc (a / 2 ^ (n + 2))
                  (a - a / 2 ^ (n + 2))).indicator
                  (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x) N
      · have hzero : ∀ n : ℕ, (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
            (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x = 0 := fun n =>
          Set.indicator_of_notMem (fun hcon => hx (hsub_s n hcon))
            (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))
        rw [Set.indicator_of_notMem hx]
        simp only [hzero]
        simp
    have hmeas_u : ∀ n : ℕ, AEMeasurable ((Set.Ioc (a / 2 ^ (n + 2))
        (a - a / 2 ^ (n + 2))).indicator
        (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η))))) volume := by
      intro n
      rw [aemeasurable_indicator_iff measurableSet_Ioc]
      exact (((hFcont.mono (hsub_s n)).aemeasurable measurableSet_Ioc)).ennreal_ofReal
    have hmono_u : ∀ᵐ x ∂(volume : Measure ℝ), Monotone (fun n : ℕ =>
        (Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))).indicator
          (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))) x) :=
      Filter.Eventually.of_forall (fun x => by
        refine monotone_nat_of_le_succ (fun n => ?_)
        by_cases hxn : x ∈ Set.Ioc (a / 2 ^ (n + 2)) (a - a / 2 ^ (n + 2))
        · have hxn' : x ∈ Set.Ioc (a / 2 ^ ((n + 1) + 2)) (a - a / 2 ^ ((n + 1) + 2)) :=
            ⟨lt_of_le_of_lt (hpow_le n) hxn.1, le_trans hxn.2 (by linarith [hpow_le n])⟩
          rw [Set.indicator_of_mem hxn, Set.indicator_of_mem hxn']
        · rw [Set.indicator_of_notMem hxn]
          exact zero_le)
    calc ∫⁻ x in Set.Ioo (0 : ℝ) a, ENNReal.ofReal (h x ^ 2 * x ^ (-(2 + η)))
        = ⨆ n : ℕ, ENNReal.ofReal (∫ x in Set.Ioc (a / 2 ^ (n + 2))
            (a - a / 2 ^ (n + 2)), h x ^ 2 * x ^ (-(2 + η))) := by
          rw [← lintegral_indicator measurableSet_Ioo
              (fun y : ℝ => ENNReal.ofReal (h y ^ 2 * y ^ (-(2 + η)))),
            ← lintegral_congr hpoint, lintegral_iSup' hmeas_u hmono_u]
          refine iSup_congr (fun n => ?_)
          rw [lintegral_indicator measurableSet_Ioc]
          exact (ofReal_integral_eq_lintegral_ofReal (hF_int n)
            ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun x hx =>
              mul_nonneg (sq_nonneg _)
                (Real.rpow_nonneg (le_trans (hεpos n).le hx.1.le) _))))).symm
      _ ≤ _ := hsup2
  -- ## Step 5: integrability and the real inequality
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) a)]
      (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η))) :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun x hx =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
  have hmeas : AEStronglyMeasurable (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) a)) := hFcont.aestronglyMeasurable measurableSet_Ioo
  have hfin : MeasureTheory.HasFiniteIntegral (fun x : ℝ => h x ^ 2 * x ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) a)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn_ae]
    exact lt_of_le_of_lt hMCT ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have hCnn : (0 : ℝ) ≤ 4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
      (deriv h x) ^ 2 * x ^ (-η)) := by
    have hBnn : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) a, (deriv h x) ^ 2 * x ^ (-η) :=
      setIntegral_nonneg measurableSet_Ioo (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _))
    positivity
  have h2 : ENNReal.ofReal (∫ x in Set.Ioo (0 : ℝ) a, h x ^ 2 * x ^ (-(2 + η)))
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * (∫ x in Set.Ioo (0 : ℝ) a,
          (deriv h x) ^ 2 * x ^ (-η))) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal ⟨hmeas, hfin⟩ hnn_ae]
    exact hMCT
  exact (ENNReal.ofReal_le_ofReal_iff hCnn).mp h2


/-- **The power Hardy inequality on `(0,a)`, uniformly in the exponent `η ≥ 0`.**

For every `η ≥ 0`, `a > 0` and `h ∈ C¹((0,a))` with `h → 0` at `0⁺` whose squared derivative
weighted by `t^{-η}` is integrable on `(0,a)`, the function `t ↦ h t ^ 2 * t ^ (-(2+η))` is
integrable on `(0,a)` and
  `∫_0^a h² t^{-(2+η)} ≤ 4 ∫_0^a (h')² t^{-η}`. -/
theorem powerHardyAll : ∃ C : ℝ, 0 < C ∧ ∀ (η a : ℝ), 0 ≤ η → 0 < a → ∀ h : ℝ → ℝ,
    ContDiffOn ℝ 1 h (Set.Ioo 0 a) →
    Filter.Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a) →
    MeasureTheory.IntegrableOn (fun t : ℝ => (h t) ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a) ∧
    (∫ t in Set.Ioo 0 a, (h t) ^ 2 * t ^ (-(2 + η)))
      ≤ C * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η) := by
  refine ⟨(4 : ℝ), by norm_num, ?_⟩
  intro η a hη ha h hsm h0 hB
  obtain ⟨hint, hle⟩ :=
    powerHardyFiniteAll (η := η) (a := a) hη ha hsm h0 hB
  refine ⟨hint, ?_⟩
  have hXnn : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) a, (deriv h t) ^ 2 * t ^ (-η) :=
    setIntegral_nonneg measurableSet_Ioo fun t ht =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
  have hcoef : 4 / (1 + η) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + η) ^ 2)]
    nlinarith [hη, sq_nonneg (1 + η)]
  calc (∫ t in Set.Ioo 0 a, (h t) ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η) := hle
    _ ≤ 4 * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η) :=
        mul_le_mul_of_nonneg_right hcoef hXnn

end Work.FTS.EllSol
