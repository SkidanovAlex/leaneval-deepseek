import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Hardy transform vanishes at `+∞`

If `|φ| ≤ M` on `(0,∞)` with `∫₀^∞ M² < ∞`, then for `β > 0`

  `z^{-β} ∫₀^z s^{β-1} φ(s) ds → 0`   as `z → ∞`.

The key point is that `M ∈ L²(0,∞)` and `|φ| ≤ M` (so `φ ∈ L²`); Cauchy–Schwarz splits the
integral at `s = 1`, and `∫₁^z s^{2β-2} ds` is `O(z^{2β-1})` (β > 1/2), `= log z` (β = 1/2) or
bounded (β < 1/2), which is exactly what is needed after multiplication by `z^{-β}`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GsingAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary integrability of `s ↦ s ^ r` on `Ioc 1 z` -/

lemma integrableOn_rpow_Ioc (r z : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ r) (Set.Ioc 1 z) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ r) (Set.Icc 1 (max 1 z)) := fun x hx =>
    (Real.continuousAt_rpow_const x r
      (Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).continuousWithinAt
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set
    (fun x hx => ⟨hx.1.le, le_trans hx.2 (le_max_right _ _)⟩)

lemma memLp_rpow_Ioc (r z : ℝ) :
    MemLp (fun s : ℝ => s ^ r) 2 (volume.restrict (Set.Ioc 1 z)) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ r) (Set.Ioc 1 z) := fun x hx =>
    (Real.continuousAt_rpow_const x r
      (Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).continuousWithinAt
  have h1 : AEStronglyMeasurable (fun s : ℝ => s ^ r) (volume.restrict (Set.Ioc 1 z)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  refine (memLp_two_iff_integrable_sq h1).mpr ?_
  refine IntegrableOn.congr_fun (integrableOn_rpow_Ioc (2 * r) z) (fun s hs => ?_)
    measurableSet_Ioc
  have hs0 : 0 ≤ s := by linarith [hs.1]
  rw [show (2 : ℝ) * r = r * 2 by ring, Real.rpow_mul hs0, Real.rpow_two]

lemma memLp_M_Ioc {M : ℝ → ℝ} (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0))) (z : ℝ) :
    MemLp M 2 (volume.restrict (Set.Ioc 1 z)) := by
  have hsub : Set.Ioc 1 z ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    show (0 : ℝ) < x
    linarith [hx.1]
  have h1 : AEStronglyMeasurable M (volume.restrict (Set.Ioc 1 z)) :=
    (hMex.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq h1).mpr (hM2.mono_set hsub)

/-! ## The Cauchy–Schwarz bound on the tail -/

/-- The tail integral `∫_{Ioc 1 z} s^{β-1} φ s` is dominated by
`sqrt (∫_{Ioc 1 z} s^{2β-2}) * sqrt (∫_{Ioc 1 z} M²)`. -/
lemma abs_integral_Ioc_le (β : ℝ) {φ M : ℝ → ℝ}
    (hMnn : ∀ s, 0 ≤ M s)
    (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0)))
    (hφ : ∀ s, 0 < s → |φ s| ≤ M s) (z : ℝ) :
    |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
      ≤ Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
        * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := by
  have hW : MemLp (fun s : ℝ => s ^ (β - 1)) 2 (volume.restrict (Set.Ioc 1 z)) :=
    memLp_rpow_Ioc (β - 1) z
  have hM : MemLp M 2 (volume.restrict (Set.Ioc 1 z)) := memLp_M_Ioc hM2 hMex z
  have hcs := Work.Spaces.cs_integral (s := Set.Ioc 1 z)
    (u := fun s : ℝ => s ^ (β - 1)) (v := M) hW hM
  have hAeq : (∫ s in Set.Ioc 1 z, (s ^ (β - 1)) ^ 2)
      = ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [show (2 : ℝ) * β - 2 = (β - 1) * 2 by ring, Real.rpow_mul hs0, Real.rpow_two]
  rw [hAeq] at hcs
  have hprod : MemLp (fun s : ℝ => s ^ (β - 1) * M s) 1 (volume.restrict (Set.Ioc 1 z)) :=
    hW.mul hM
  have hInt : Integrable (fun s : ℝ => s ^ (β - 1) * M s) (volume.restrict (Set.Ioc 1 z)) :=
    memLp_one_iff_integrable.mp hprod
  have hstep1 : |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
      ≤ ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s := by
    have h1 : |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
        ≤ ∫ s in Set.Ioc 1 z, |s ^ (β - 1) * φ s| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Set.Ioc 1 z)) (fun s : ℝ => s ^ (β - 1) * φ s))
    refine h1.trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun s => abs_nonneg _) hInt ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
    exact mul_le_mul_of_nonneg_left (hφ s hs0) (Real.rpow_nonneg hs0.le _)
  have hnn : 0 ≤ ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s :=
    setIntegral_nonneg measurableSet_Ioc fun s hs =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hs.1]) _) (hMnn s)
  have hA0 : 0 ≤ ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) :=
    setIntegral_nonneg measurableSet_Ioc fun s hs =>
      Real.rpow_nonneg (by linarith [hs.1]) _
  have hstep2 : ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s
      ≤ Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
        * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := by
    calc ∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s
        = Real.sqrt ((∫ s in Set.Ioc 1 z, s ^ (β - 1) * M s) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
            * (∫ s in Set.Ioc 1 z, (M s) ^ 2)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
            * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2) := Real.sqrt_mul hA0 _
  exact hstep1.trans hstep2

/-! ## The tail factor tends to `0` -/

lemma tail_factor_tendsto (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun z : ℝ => z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)))
      atTop (nhds 0) := by
  have hnn : ∀ᶠ z : ℝ in atTop,
      0 ≤ z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz _) (Real.sqrt_nonneg _)
  have hAz : ∀ z : ℝ, 1 ≤ z → β ≠ 1 / 2 → ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2)
      = (z ^ (2 * β - 1) - 1) / (2 * β - 1) := by
    intro z hz hβne
    rw [← intervalIntegral.integral_of_le hz]
    rw [integral_rpow (Or.inr ⟨fun h => hβne (by linarith),
      by rw [Set.uIcc_of_le hz]; rintro ⟨h1, _⟩; linarith⟩)]
    rw [show (2 : ℝ) * β - 2 + 1 = 2 * β - 1 by ring, Real.one_rpow]
  rcases lt_trichotomy β (1 / 2) with hlt | heq | hgt
  · -- β < 1/2 : the integral stays bounded
    have hbd : ∀ᶠ z : ℝ in atTop,
        z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) / Real.sqrt (1 - 2 * β) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hAle : ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) ≤ 1 / (1 - 2 * β) := by
        have hkey : 1 / (1 - 2 * β) = -1 / (2 * β - 1) := by
          rw [div_eq_div_iff (by linarith) (by linarith)]; ring
        have hdiff : -1 / (2 * β - 1) - (z ^ (2 * β - 1) - 1) / (2 * β - 1)
            = z ^ (2 * β - 1) / (1 - 2 * β) := by
          rw [← sub_div, show (1 : ℝ) - 2 * β = -(2 * β - 1) by ring, div_neg, ← neg_div]
          congr 1
          ring
        rw [hAz z hz (by linarith), hkey, ← sub_nonneg, hdiff]
        exact div_nonneg (Real.rpow_nonneg hzpos.le _) (by linarith)
      have hsqrt : Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ Real.sqrt (1 / (1 - 2 * β)) := Real.sqrt_le_sqrt hAle
      calc z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) * Real.sqrt (1 / (1 - 2 * β)) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hzpos.le _)
        _ = z ^ (-β) / Real.sqrt (1 - 2 * β) := by
            rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]; ring
    have hlim : Tendsto (fun z : ℝ => z ^ (-β) / Real.sqrt (1 - 2 * β)) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop hβ).div_const (Real.sqrt (1 - 2 * β))
    exact squeeze_zero' hnn hbd hlim
  · -- β = 1/2 : the integral is `log z`
    subst heq
    rw [show (2 : ℝ) * (1 / 2) - 2 = (-1 : ℝ) by norm_num]
    have hev : (fun z : ℝ =>
          z ^ ((-(1 / 2) : ℝ)) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (-1 : ℝ)))
        =ᶠ[atTop] fun z : ℝ => Real.sqrt (z⁻¹ * Real.log z) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hAz1 : ∫ s in Set.Ioc 1 z, s ^ (-1 : ℝ) = Real.log z := by
        rw [← intervalIntegral.integral_of_le hz]
        rw [show (fun s : ℝ => s ^ (-1 : ℝ)) = fun s => s⁻¹ from funext fun s =>
          Real.rpow_neg_one s]
        rw [integral_inv (by rw [Set.uIcc_of_le hz]; rintro ⟨h1, _⟩; linarith)]
        rw [Real.log_div hzpos.ne' one_ne_zero, Real.log_one, sub_zero]
      have hsqz : Real.sqrt z⁻¹ = z ^ ((-(1 / 2) : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one z, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      rw [hAz1, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ z⁻¹), hsqz]
    refine Filter.Tendsto.congr' hev.symm ?_
    have hlog : Tendsto (fun z : ℝ => Real.log z / z) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun z : ℝ => Real.sqrt (Real.log z / z)) atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hlog
    have hsqrt0 : Tendsto (fun z : ℝ => Real.sqrt (z⁻¹ * Real.log z)) atTop (nhds 0) := by
      rw [← Real.sqrt_zero]
      refine Filter.Tendsto.congr' ?_ h2
      filter_upwards with z
      congr 1
      ring
    exact hsqrt0
  · -- 1/2 < β
    have hbd : ∀ᶠ z : ℝ in atTop,
        z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hzpos : 0 < z := by linarith
      have hden : 0 < 2 * β - 1 := by linarith
      have hAle : ∫ s in Set.Ioc 1 z, s ^ (2 * β - 2) ≤ z ^ (2 * β - 1) / (2 * β - 1) := by
        rw [hAz z hz (by linarith)]
        refine div_le_div_of_nonneg_right ?_ hden.le
        have hzp := Real.rpow_nonneg hzpos.le (2 * β - 1)
        linarith
      have hsqrt : Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (β - 1 / 2) / Real.sqrt (2 * β - 1) := by
        refine (Real.sqrt_le_sqrt hAle).trans (le_of_eq ?_)
        rw [Real.sqrt_div (Real.rpow_nonneg hzpos.le _)]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      calc z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
          ≤ z ^ (-β) * (z ^ (β - 1 / 2) / Real.sqrt (2 * β - 1)) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hzpos.le _)
        _ = z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1) := by
            rw [← mul_div_assoc, ← Real.rpow_add hzpos,
              show -β + (β - 1 / 2) = (-(1 / 2) : ℝ) by ring]
    have hlim : Tendsto (fun z : ℝ => z ^ ((-(1 / 2) : ℝ)) / Real.sqrt (2 * β - 1))
        atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).div_const
        (Real.sqrt (2 * β - 1))
    exact squeeze_zero' hnn hbd hlim

/-! ## The main statement -/

theorem harOp_tendsto_zero (β : ℝ) (hβ : 0 < β) (φ M : ℝ → ℝ)
    (hMnn : ∀ s, 0 ≤ M s)
    (hM2 : IntegrableOn (fun s => (M s) ^ 2) (Set.Ioi 0))
    (hMex : AEMeasurable M (volume.restrict (Set.Ioi 0)))
    (hφ : ∀ s, 0 < s → |φ s| ≤ M s) :
    Filter.Tendsto (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s)
      Filter.atTop (nhds 0) := by
  rcases em (∀ z : ℝ, 0 ≤ z →
      IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 z)) with hgood | hbad
  · -- main case: `s^{β-1}φ` is locally integrable
    set C : ℝ := ∫ s in Set.Ioc 0 1, s ^ (β - 1) * φ s with hC
    have hCint : IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 1) :=
      hgood 1 zero_le_one
    have hev : (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s) =ᶠ[atTop]
        fun z : ℝ => z ^ (-β) * (C + ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      have hz0 : (0 : ℝ) ≤ z := by linarith
      have hunion : Set.Ioc 0 1 ∪ Set.Ioc 1 z = Set.Ioc 0 z :=
        Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz
      have hdisj : Disjoint (Set.Ioc 0 1) (Set.Ioc 1 z) :=
        Set.disjoint_left.mpr fun x hx1 hx2 => by linarith [hx1.2, hx2.1]
      have h2int : IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 1 z) :=
        (hgood z hz0).mono_set fun x hx => ⟨by linarith [hx.1], hx.2⟩
      rw [intervalIntegral.integral_of_le hz0, ← hunion,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hCint h2int]
      try ring
    refine Filter.Tendsto.congr' hev.symm ?_
    have h1 : Tendsto (fun z : ℝ => z ^ (-β) * C) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop hβ).mul_const C
    have h2 : Tendsto (fun z : ℝ => z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s)
        atTop (nhds 0) := by
      have hB : 0 ≤ ∫ s in Set.Ioi 0, (M s) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
      have hbd2 : ∀ᶠ z : ℝ in atTop,
          |z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
            ≤ z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
              * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
        have hz0 : (0 : ℝ) < z := by linarith
        have hbd := abs_integral_Ioc_le β hMnn hM2 hMex hφ z
        have hMz : ∫ s in Set.Ioc 1 z, (M s) ^ 2 ≤ ∫ s in Set.Ioi 0, (M s) ^ 2 :=
          MeasureTheory.setIntegral_mono_set hM2
            (Eventually.of_forall fun s => sq_nonneg _)
            (Eventually.of_forall fun s hs => by show (0 : ℝ) < s; linarith [hs.1])
        have hMsq : Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2)
            ≤ Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := Real.sqrt_le_sqrt hMz
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hz0.le _)]
        calc z ^ (-β) * |∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|
            ≤ z ^ (-β) * (Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioc 1 z, (M s) ^ 2)) :=
              mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hz0.le _)
          _ ≤ z ^ (-β) * (Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hMsq (Real.sqrt_nonneg _))
                (Real.rpow_nonneg hz0.le _)
          _ = z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z, s ^ (2 * β - 2))
                * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2) := by ring
      have hlim2 : Tendsto (fun z : ℝ => z ^ (-β) * Real.sqrt (∫ s in Set.Ioc 1 z,
          s ^ (2 * β - 2)) * Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2)) atTop (nhds 0) := by
        simpa using (tail_factor_tendsto β hβ).mul_const
          (Real.sqrt (∫ s in Set.Ioi 0, (M s) ^ 2))
      have hsq : Tendsto (fun z : ℝ =>
          |z ^ (-β) * ∫ s in Set.Ioc 1 z, s ^ (β - 1) * φ s|) atTop (nhds 0) :=
        squeeze_zero' (Eventually.of_forall fun z => abs_nonneg _) hbd2 hlim2
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [Real.norm_eq_abs] using hsq
    have hsum : Tendsto (fun z : ℝ => z ^ (-β) * (C + ∫ s in Set.Ioc 1 z,
        s ^ (β - 1) * φ s)) atTop (nhds 0) := by
      simpa [mul_add] using h1.add h2
    exact hsum
  · -- degenerate case: the integral is `0` from some point on
    simp only [not_forall] at hbad
    obtain ⟨z0, hz0nn, hz0bad⟩ := hbad
    have hz0pos : 0 < z0 := by
      rcases lt_or_eq_of_le hz0nn with h | h
      · exact h
      · exfalso
        apply hz0bad
        rw [← h, Set.Ioc_self]
        exact integrableOn_empty
    have hev : (fun z : ℝ => z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * φ s) =ᶠ[atTop]
        fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_ge_atTop z0] with z hz
      have hz0le : (0 : ℝ) ≤ z := le_trans hz0pos.le hz
      have hni : ¬ IntegrableOn (fun s : ℝ => s ^ (β - 1) * φ s) (Set.Ioc 0 z) :=
        fun hc => hz0bad (hc.mono_set (Set.Ioc_subset_Ioc_right hz))
      rw [intervalIntegral.integral_of_le hz0le, MeasureTheory.integral_undef hni, mul_zero]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

end Work.FTS.EllipticEst.GsingAux
