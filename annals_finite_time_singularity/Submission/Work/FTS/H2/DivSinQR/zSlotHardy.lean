import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.power_hardy
import Submission.Work.FTS.EllipticEst.remov.sin_weight_compare
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
import Submission.Work.FTS.EllipticEst.remov.interval_integral_mono_limit
import Submission.Work.FTS.EllipticEst.H2W.hardy_boundary_clean
import Submission.Work.FTS.EllipticEst.H2W.AeWAux.powerHardyOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivSinQR

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The honest power-weight Hardy inequality (delegated) -/

/-! ## The honest power-weight Hardy inequality on the open interval `(0,a)` -/

/-- Reflection of a set integral on `(0,t)` about the midpoint. -/
private lemma integral_Ioo_comp_sub_self (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x in Set.Ioo 0 t, F (t - x)) = ∫ x in Set.Ioo 0 t, F x := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht.le]
  rw [intervalIntegral.integral_comp_sub_left F t]
  rw [show t - t = 0 by ring, show t - 0 = t by ring]

/-- Integrability transfer under reflection about the midpoint of `(0,t)`. -/
private lemma integrableOn_comp_sub_self {Φ : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Φ (t - x)) (Set.Ioo 0 t) ↔
      MeasureTheory.IntegrableOn Φ (Set.Ioo 0 t) := by
  have hiff : ∀ {Ψ : ℝ → ℝ}, MeasureTheory.IntegrableOn Ψ (Set.Ioo 0 t) ↔
      MeasureTheory.IntegrableOn Ψ (Set.Ioc 0 t) := fun {Ψ} =>
    MeasureTheory.integrableOn_congr_set_ae (μ := volume) MeasureTheory.Ioo_ae_eq_Ioc
  rw [hiff, hiff, ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  constructor
  · intro h
    have h2 : IntervalIntegrable (fun x : ℝ => Φ (t - (t - x))) volume (t - 0) (t - t) :=
      h.comp_sub_left t
    have hfun : (fun x : ℝ => Φ (t - (t - x))) = Φ := by
      funext x; rw [show t - (t - x) = x by ring]
    rw [hfun] at h2
    rw [show t - 0 = t by ring, show t - t = 0 by ring] at h2
    exact h2.symm
  · intro h
    have h2 : IntervalIntegrable (fun x : ℝ => Φ (t - x)) volume (t - 0) (t - t) :=
      h.comp_sub_left t
    rw [show t - 0 = t by ring, show t - t = 0 by ring] at h2
    exact h2.symm

/-- Pointwise Cauchy–Schwarz: `|u| ≤ (1/2) (u² x^{-η} + x^{η})` for `x > 0`. -/
private lemma abs_le_half_weight {η x u : ℝ} (hx : 0 < x) :
    |u| ≤ 1 / 2 * (u ^ 2 * x ^ (-η) + x ^ η) := by
  have hp : x ^ (-η / 2) * x ^ (-η / 2) = x ^ (-η) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hq : x ^ (η / 2) * x ^ (η / 2) = x ^ η := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hpq : x ^ (-η / 2) * x ^ (η / 2) = 1 := by
    rw [← Real.rpow_add hx, show -η / 2 + η / 2 = 0 by ring, Real.rpow_zero]
  have hp2 : (x ^ (-η / 2)) ^ 2 = x ^ (-η) := by rw [pow_two, hp]
  have hq2 : (x ^ (η / 2)) ^ 2 = x ^ η := by rw [pow_two, hq]
  have hsq : (u * x ^ (-η / 2)) ^ 2 = u ^ 2 * x ^ (-η) := by
    have h2 : (u * x ^ (-η / 2)) ^ 2 = u ^ 2 * (x ^ (-η / 2) * x ^ (-η / 2)) := by ring
    rw [h2, hp]
  have hmul : u * x ^ (-η / 2) * x ^ (η / 2) = u := by rw [mul_assoc, hpq, mul_one]
  have hsqu : ((-u) * x ^ (-η / 2)) ^ 2 = u ^ 2 * x ^ (-η) := by
    have h2 : ((-u) * x ^ (-η / 2)) ^ 2 = u ^ 2 * (x ^ (-η / 2) * x ^ (-η / 2)) := by ring
    rw [h2, hp]
  have hmulu : (-u) * x ^ (-η / 2) * x ^ (η / 2) = -u := by rw [mul_assoc, hpq, mul_one]
  have h5 : 2 * u ≤ u ^ 2 * x ^ (-η) + x ^ η := by
    have h := two_mul_le_add_sq (u * x ^ (-η / 2)) (x ^ (η / 2))
    rw [mul_assoc, hmul, hsq, hq2] at h
    exact h
  have h6 : -(2 * u) ≤ u ^ 2 * x ^ (-η) + x ^ η := by
    have h := two_mul_le_add_sq ((-u) * x ^ (-η / 2)) (x ^ (η / 2))
    rw [mul_assoc, hmulu, hsqu, hq2] at h
    linarith [h]
  have habs : |2 * u| ≤ u ^ 2 * x ^ (-η) + x ^ η := abs_le.mpr ⟨by linarith [h6], h5⟩
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  linarith [habs]

/-- The endpoint rate forced by the finiteness of the weighted energy: for `g` of class `C¹` on
`(0,a)` with `g → 0` at `0⁺` and `∫_{(0,a)} (g')² x^{-η} < ∞` one has
`g(t)² t^{-(1+η)} ≤ ∫_{(0,a)} (g')² x^{-η}` for every `t ∈ (0,a)`. -/
private lemma rateBound {a η : ℝ} (_ha : 0 < a) (hη0 : 0 ≤ η) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 a))
    (hg0 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv g x) ^ 2 * x ^ (-η)) (Set.Ioo 0 a)) :
    ∀ t ∈ Set.Ioo 0 a, (g t) ^ 2 * t ^ (-(1 + η))
      ≤ ∫ x in Set.Ioo 0 a, (deriv g x) ^ 2 * x ^ (-η) := by
  intro t ht
  obtain ⟨ht0, hta⟩ := ht
  have hWoc : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv g x) ^ 2 * x ^ (-η))
      (Set.Ioc 0 t) :=
    (hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)).congr_set_ae
      MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hpow : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ η) (Set.Ioc 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).1
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t) (r := η) (by linarith))
  have hRinv : MeasureTheory.IntegrableOn (fun x : ℝ => (x ^ (-η))⁻¹) (Set.Ioc 0 t) := by
    refine hpow.congr_fun (fun x hx => ?_) measurableSet_Ioc
    rw [← Real.rpow_neg hx.1.le (-η)]
    ring_nf
  -- interval integrability of `deriv g` on `(0,t)`
  have hdfint : IntervalIntegrable (deriv g) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le]
    have hdom : MeasureTheory.IntegrableOn
        (fun s : ℝ => (1 / 2) * ((deriv g s) ^ 2 * s ^ (-η) + s ^ η)) (Set.Ioc 0 t) :=
      (hWoc.add hpow).const_mul (1 / 2)
    refine hdom.mono' ?_ ?_
    · exact ((hg.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono
        (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)).aestronglyMeasurable measurableSet_Ioc
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      rw [Real.norm_eq_abs]
      exact abs_le_half_weight hx.1
  -- the fundamental theorem of calculus at `0⁺`
  have hFTC : ∫ s in (0 : ℝ)..t, deriv g s = g t - 0 := by
    have h : ∫ s in (0 : ℝ)..t, deriv g s = g t - 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht0
        (f := g) (f' := deriv g) ?_ hdfint hg0 ?_
    · simpa using h
    · intro x hx
      exact ((hg.contDiffAt (isOpen_Ioo.mem_nhds ⟨hx.1, by linarith [hx.2, hta]⟩)).differentiableAt
        one_ne_zero).hasDerivAt
    · exact ((hg.contDiffAt (isOpen_Ioo.mem_nhds ⟨ht0, hta⟩)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
  -- Cauchy–Schwarz
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul (f := deriv g)
    (σ := fun x : ℝ => x ^ (-η)) (a := (0 : ℝ)) (b := t) ht0.le
    (fun s hs => Real.rpow_pos_of_pos hs.1 (-η)) hWoc hRinv
  have hFTC' : ∫ s in (0 : ℝ)..t, deriv g s = g t := by rw [hFTC, sub_zero]
  have hsq : (g t) ^ 2 ≤ (∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η))
      * (∫ s in (0 : ℝ)..t, (s ^ (-η))⁻¹) := by
    rw [← hFTC']
    exact hcs
  -- the second factor is at most `t ^ (1+η)`
  have hsmall : (∫ s in (0 : ℝ)..t, (s ^ (-η))⁻¹) ≤ t ^ (1 + η) := by
    have hid : (∫ s in (0 : ℝ)..t, (s ^ (-η))⁻¹) = ∫ s in (0 : ℝ)..t, s ^ η := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le ht0.le] at hs
      rw [← Real.rpow_neg hs.1 (-η)]
      congr 1; ring
    rw [hid]
    have h1 : IntervalIntegrable (fun s : ℝ => s ^ η) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < η)
    have h2 : IntervalIntegrable (fun _ : ℝ => t ^ η) volume 0 t := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo ht0.le h1 h2
      (fun s hs => Real.rpow_le_rpow (le_of_lt hs.1) hs.2.le hη0)
    rw [intervalIntegral.integral_const] at hmono
    have hval : (t - 0) • (t ^ η) = t ^ (1 + η) := by
      rw [sub_zero, smul_eq_mul]
      calc t * t ^ η = t ^ (1 : ℝ) * t ^ η := by rw [Real.rpow_one]
        _ = t ^ ((1 : ℝ) + η) := (Real.rpow_add ht0 1 η).symm
        _ = t ^ (1 + η) := by norm_num
    rwa [hval] at hmono
  -- assemble
  have hWset : (∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η))
      = ∫ s in Set.Ioo 0 t, (deriv g s) ^ 2 * s ^ (-η) :=
    Work.FTS.EllipticEst.remov.intervalIntegral_eq_setIntegral_Ioo ht0.le _
  have hJnn : 0 ≤ ∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η) := by
    rw [hWset]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun s hs => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.1.le _))
  have hmono2 : (∫ s in Set.Ioo 0 t, (deriv g s) ^ 2 * s ^ (-η))
      ≤ ∫ x in Set.Ioo 0 a, (deriv g x) ^ 2 * x ^ (-η) := by
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
        (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
    · exact Filter.Eventually.of_forall (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  calc (g t) ^ 2 * t ^ (-(1 + η))
      ≤ ((∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η))
          * (∫ s in (0 : ℝ)..t, (s ^ (-η))⁻¹)) * t ^ (-(1 + η)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg ht0.le _)
    _ = (∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η))
          * ((∫ s in (0 : ℝ)..t, (s ^ (-η))⁻¹) * t ^ (-(1 + η))) := by ring
    _ ≤ (∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η)) * (t ^ (1 + η) * t ^ (-(1 + η))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg ht0.le _))
          hJnn
    _ = (∫ s in (0 : ℝ)..t, (deriv g s) ^ 2 * s ^ (-η)) := by
        rw [← Real.rpow_add ht0, show (1 + η) + (-(1 + η)) = 0 by ring, Real.rpow_zero, mul_one]
    _ = ∫ s in Set.Ioo 0 t, (deriv g s) ^ 2 * s ^ (-η) := hWset
    _ ≤ ∫ x in Set.Ioo 0 a, (deriv g x) ^ 2 * x ^ (-η) := hmono2

/-- **The sharp power-weight Hardy inequality on the open interval `(0,a)`.**  For `a > 0`,
`0 ≤ η < 1` and `g` of class `C¹` on `(0,a)` with `g → 0` at `0⁺` and
`∫_{(0,a)} (g')² x^{-η} < ∞`, the weighted energy `∫_{(0,a)} g² x^{-(2+η)}` is finite and
`∫ g² x^{-(2+η)} ≤ 4/(1+η)² ∫ (g')² x^{-η}`. -/
theorem powerHardyOpenAux {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Set.Ioo 0 a))
    (hg0 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv g x) ^ 2 * x ^ (-η)) (Set.Ioo 0 a)) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (g x) ^ 2 * x ^ (-(2 + η))) (Set.Ioo 0 a) ∧
    (∫ x in Set.Ioo 0 a, (g x) ^ 2 * x ^ (-(2 + η)))
      ≤ (4 / (1 + η) ^ 2) * ∫ x in Set.Ioo 0 a, (deriv g x) ^ 2 * x ^ (-η) := by
  set W : ℝ → ℝ := fun x => (deriv g x) ^ 2 * x ^ (-η) with hW
  set F : ℝ → ℝ := fun x => (g x) ^ 2 * x ^ (-(2 + η)) with hFdef
  have hFnn : ∀ x ∈ Set.Ioo (0 : ℝ) a, 0 ≤ F x := by
    intro x hx
    rw [hFdef]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)
  have hFcont : ContinuousOn F (Set.Ioo 0 a) := by
    rw [hFdef]
    exact (hg.continuousOn.pow 2).mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne'))
  have hKnn : 0 ≤ ∫ x in Set.Ioo 0 a, W x :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => by rw [hW]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _))
  have hrate := rateBound ha hη0 hg hg0 hint
  -- the uniform truncation bound
  have htrunc : ∀ t ∈ Set.Ioo (0 : ℝ) a, ∀ ε ∈ Set.Ioo (0 : ℝ) t,
      (∫ s in ε..t, F s) ≤ 8 * (∫ x in Set.Ioo 0 a, W x) / (1 + η) ^ 2 := by
    intro t ht ε hε
    obtain ⟨ht0, hta⟩ := ht
    obtain ⟨hε0, hεt⟩ := hε
    have hbc := Work.FTS.EllipticEst.H2W.hardy_boundary_clean (q := η) hη0 hη1
      (U := g) (a := ε) (b := t) hε0 hεt.le ht0
      (hg.mono (fun x hx => ⟨lt_of_lt_of_le hε0 hx.1, lt_of_le_of_lt hx.2 hta⟩))
    have hJle : (∫ s in ε..t, W s) ≤ ∫ x in Set.Ioo 0 a, W x := by
      rw [Work.FTS.EllipticEst.remov.intervalIntegral_eq_setIntegral_Ioo hεt.le W]
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
          (fun x hx => by rw [hW]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)))
      · exact Filter.Eventually.of_forall
          (fun x hx => ⟨lt_trans hε0 hx.1, lt_trans hx.2 hta⟩)
    have hGe : (g ε) ^ 2 * ε ^ (-(1 + η)) ≤ ∫ x in Set.Ioo 0 a, W x :=
      hrate ε ⟨hε0, lt_trans hεt hta⟩
    have hGt : 0 ≤ (g t) ^ 2 * t ^ (-(1 + η)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _)
    have hcoef : (0 : ℝ) < (1 + η) ^ 2 / 4 := by positivity
    have hkey : (1 + η) ^ 2 / 4 * (∫ s in ε..t, F s)
        ≤ 2 * (∫ x in Set.Ioo 0 a, W x) := by
      nlinarith [hbc, hJle, hGe, hGt, hKnn]
    have hpos2 : (0 : ℝ) < (1 + η) ^ 2 := by positivity
    rw [le_div_iff₀ hpos2]
    nlinarith [hkey, hcoef]
  -- integrability and the bound on every `(0,t)`, `t < a`
  have hH : ∀ t ∈ Set.Ioo (0 : ℝ) a,
      MeasureTheory.IntegrableOn F (Set.Ioo 0 t) ∧
      (∫ x in Set.Ioo 0 t, F x) ≤ 8 * (∫ x in Set.Ioo 0 a, W x) / (1 + η) ^ 2 := by
    intro t ht
    obtain ⟨ht0, hta⟩ := ht
    -- the reflection of `F` about the midpoint of `(0,t)`
    have hGcont : ContinuousOn (fun x : ℝ => F (t - x)) (Set.Ioo 0 t) := by
      have hmap : Set.MapsTo (fun x : ℝ => t - x) (Set.Ioo 0 t) (Set.Ioo 0 a) :=
        fun x hx => ⟨by linarith [hx.2], by linarith [hx.1, hta]⟩
      have hcomp := hFcont.comp (continuousOn_const.sub continuousOn_id) hmap
      simpa [Function.comp_def, Pi.sub_apply] using hcomp
    have hGnn : ∀ x ∈ Set.Ioo (0 : ℝ) t, 0 ≤ F (t - x) :=
      fun x hx => hFnn _ ⟨by linarith [hx.2], by linarith [hx.1, hta]⟩
    have hGint : ∀ b ∈ Set.Ioo (0 : ℝ) t,
        MeasureTheory.IntegrableOn (fun x : ℝ => F (t - x)) (Set.Ioo 0 b) := by
      intro b hb
      obtain ⟨hb0, hbt⟩ := hb
      have hFicc : ContinuousOn F (Set.Icc (t - b) t) :=
        hFcont.mono (fun x hx => ⟨lt_of_lt_of_le (by linarith [hbt]) hx.1,
          by linarith [hx.2, hta]⟩)
      have hmap : Set.MapsTo (fun x : ℝ => t - x) (Set.Icc 0 b) (Set.Icc (t - b) t) :=
        fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have hcomp := hFicc.comp (continuousOn_const.sub continuousOn_id) hmap
      have hcont : ContinuousOn (fun x : ℝ => F (t - x)) (Set.Icc 0 b) := by
        simpa [Function.comp_def, Pi.sub_apply] using hcomp
      have hii : IntervalIntegrable (fun x : ℝ => F (t - x)) volume 0 b :=
        ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hb0.le hcont
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le] at hii
      exact hii.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc
    have hGbound : ∀ b ∈ Set.Ioo (0 : ℝ) t,
        (∫ x in (0 : ℝ)..b, F (t - x)) ≤ 8 * (∫ x in Set.Ioo 0 a, W x) / (1 + η) ^ 2 := by
      intro b hb
      obtain ⟨hb0, hbt⟩ := hb
      have hid : (∫ x in (0 : ℝ)..b, F (t - x)) = ∫ x in (t - b)..t, F x := by
        rw [intervalIntegral.integral_comp_sub_left F t]
        rw [show t - 0 = t by ring]
      rw [hid]
      exact htrunc t ⟨ht0, hta⟩ (t - b) ⟨by linarith [hbt], by linarith [hb0]⟩
    have hmono := Work.FTS.EllipticEst.remov.interval_integral_mono_limit (a := (0 : ℝ))
      (β := t) ht0 hGcont hGnn hGint hGbound
    refine ⟨?_, ?_⟩
    · exact (integrableOn_comp_sub_self (Φ := F) ht0).mp hmono.1
    · rw [← integral_Ioo_comp_sub_self F ht0]
      exact hmono.2
  -- pass to `(0,a)`
  have hmain := Work.FTS.EllipticEst.remov.interval_integral_mono_limit (a := (0 : ℝ))
    (β := a) ha hFcont hFnn (fun b hb => (hH b hb).1)
    (fun b hb => by
      rw [Work.FTS.EllipticEst.remov.intervalIntegral_eq_setIntegral_Ioo hb.1.le F]
      exact (hH b hb).2)
  refine ⟨hmain.1, ?_⟩
  exact Work.FTS.EllipticEst.H2W.AeWAux.powerHardyOpen ha hη0 hη1 hg hmain.1 hint

/-! ## Reflection and splitting bookkeeping -/

/-- Reflection of integrals on the right half to the left half. -/
private lemma integral_Ioo_comp_sub (Φ : ℝ → ℝ) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), Φ θ)
      = ∫ x in Set.Ioo 0 (Real.pi / 4), Φ (Real.pi / 2 - x) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h4le, ← intervalIntegral.integral_of_le h4]
  rw [intervalIntegral.integral_comp_sub_left Φ (Real.pi / 2)]
  rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
      show Real.pi / 2 - 0 = Real.pi / 2 by ring]

/-- Integrability transfer under reflection. -/
private lemma integrableOn_comp_sub_left_iff {Φ : ℝ → ℝ} :
    MeasureTheory.IntegrableOn (fun x : ℝ => Φ (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4)) ↔
      MeasureTheory.IntegrableOn Φ (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hiff1 : MeasureTheory.IntegrableOn (fun x : ℝ => Φ (Real.pi / 2 - x)) (Set.Ioo 0 (Real.pi / 4))
      ↔ MeasureTheory.IntegrableOn (fun x : ℝ => Φ (Real.pi / 2 - x)) (Set.Ioc 0 (Real.pi / 4)) :=
    MeasureTheory.integrableOn_congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc
  have hiff2 : MeasureTheory.IntegrableOn Φ (Set.Ioo (Real.pi / 4) (Real.pi / 2))
      ↔ MeasureTheory.IntegrableOn Φ (Set.Ioc (Real.pi / 4) (Real.pi / 2)) :=
    MeasureTheory.integrableOn_congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc
  rw [hiff1, hiff2, ← intervalIntegrable_iff_integrableOn_Ioc_of_le h4,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le h4le]
  constructor
  · intro h
    have h' : IntervalIntegrable (fun x : ℝ => Φ (Real.pi / 2 - x)) volume 0 (Real.pi / 4) := h
    have h2 : IntervalIntegrable (fun x : ℝ => Φ (Real.pi / 2 - (Real.pi / 2 - x)))
        volume (Real.pi / 2 - Real.pi / 4) (Real.pi / 2 - 0) :=
      h'.symm.comp_sub_left (Real.pi / 2)
    have hfun : (fun x : ℝ => Φ (Real.pi / 2 - (Real.pi / 2 - x))) = Φ := by
      funext x; rw [show Real.pi / 2 - (Real.pi / 2 - x) = x by ring]
    rw [hfun] at h2
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
        show Real.pi / 2 - 0 = Real.pi / 2 by ring] at h2
    exact h2
  · intro h
    have h' : IntervalIntegrable Φ volume (Real.pi / 4) (Real.pi / 2) := h
    have h3 := h'.comp_sub_left (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
        show Real.pi / 2 - Real.pi / 2 = 0 by ring] at h3
    exact h3.symm

/-- Splitting an integral over `Iθ` into the two halves. -/
private lemma integral_Iθ_split {G : ℝ → ℝ} (h1 : IntervalIntegrable G volume 0 (Real.pi / 4))
    (h2 : IntervalIntegrable G volume (Real.pi / 4) (Real.pi / 2)) :
    (∫ θ in Work.Spaces.Iθ, G θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
        + ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h2le : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le h2le]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h4, ← intervalIntegral.integral_of_le h4le]
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

private lemma intervalIntegrable_half_left {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G Work.Spaces.Iθ) :
    IntervalIntegrable G volume 0 (Real.pi / 4) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 4)]
  exact hG.mono_set (by intro x hx; exact ⟨hx.1.le, by linarith [hx.2, Real.pi_pos]⟩)

private lemma intervalIntegrable_half_right {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G Work.Spaces.Iθ) :
    IntervalIntegrable G volume (Real.pi / 4) (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2)]
  exact hG.mono_set (by intro x hx; exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)

private lemma integrableOn_of_le {s : Set ℝ} {f g : ℝ → ℝ} (hms : MeasurableSet s)
    (hg : MeasureTheory.IntegrableOn g s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ x ∈ s, 0 ≤ f x) (hle : ∀ x ∈ s, f x ≤ g x) : MeasureTheory.IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := hg
  refine hg'.mono' hf ?_
  rw [MeasureTheory.ae_restrict_iff' hms]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]
  exact hle x hx

/-! ## The target theorem -/

theorem zSlotHardy : ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
    ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ,
        (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ C * (∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  refine ⟨2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta) * (4 / (1 + Work.Spaces.eta) ^ 2)
      * 2 ^ Work.Spaces.eta, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (by norm_num)
        (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _))
        (div_pos (by norm_num) (pow_pos (by linarith [Work.Spaces.eta_nonneg]) 2)))
        (Real.rpow_pos_of_pos (by norm_num) _)
  · intro h hsm h0 hpi hI
    set η : ℝ := Work.Spaces.eta with hηdef
    have hη0 : 0 ≤ η := Work.Spaces.eta_nonneg
    have hη1 : η < 1 := Work.Spaces.eta_lt_one
    have h4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h2pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    -- constants
    have hcπ : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + η) := (Real.rpow_pos_of_pos h4pos _).le
    have hc4 : (0 : ℝ) ≤ 4 / (1 + η) ^ 2 :=
      (div_pos (by norm_num) (pow_pos (by linarith) 2)).le
    have hc2 : (0 : ℝ) ≤ 2 ^ η := (Real.rpow_pos_of_pos (by norm_num) _).le
    -- abbreviations
    set Fi : ℝ → ℝ := fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) with hFi
    set Gi : ℝ → ℝ := fun θ : ℝ => (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η) with hGi
    set G : ℝ → ℝ := fun θ : ℝ => (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) with hG
    -- sin facts
    have hsinpos : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
      intro x hx
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
    have hsinnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * x) :=
      fun x hx => (hsinpos x hx).le
    -- smoothness
    have hsm1 : ContDiffOn ℝ 1 h (Set.Ioo 0 (Real.pi / 2)) := hsm.of_le (by simp)
    have hsmL : ContDiffOn ℝ 1 h (Set.Ioo 0 (Real.pi / 4)) :=
      hsm1.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
    have hderL : ContinuousOn (deriv h) (Set.Ioo 0 (Real.pi / 4)) :=
      hsmL.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    -- ## the power weight on the left half
    have hFcompL : ∀ x ∈ Set.Ioo 0 (Real.pi / 4),
        (deriv h x) ^ 2 * x ^ (-η) ≤ 2 ^ η * Fi x := by
      intro x hx
      have hxI : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4) := ⟨hx.1, hx.2.le⟩
      have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare η hη0).2.1 x hxI
      have hmul := mul_le_mul_of_nonneg_left hcmp (sq_nonneg (deriv h x))
      calc (deriv h x) ^ 2 * x ^ (-η)
          ≤ (deriv h x) ^ 2 * (2 ^ η * (Real.sin (2 * x)) ^ (-η)) := hmul
        _ = 2 ^ η * Fi x := by rw [hFi]; ring
    have hint1 : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
        (Set.Ioo 0 (Real.pi / 4)) :=
      integrableOn_of_le (f := fun x : ℝ => (deriv h x) ^ 2 * x ^ (-η))
        (g := fun x : ℝ => 2 ^ η * Fi x) measurableSet_Ioo
        ((hI.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)).const_mul _)
        (((hderL.pow 2).mul
          (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne'))).aestronglyMeasurable
            measurableSet_Ioo)
        (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _))
        hFcompL
    obtain ⟨hGL1, hGL2⟩ := powerHardyOpenAux (a := Real.pi / 4) (η := η) h4pos hη0 hη1 hsmL h0 hint1
    -- ## the reflected function
    set gr : ℝ → ℝ := fun u : ℝ => h (Real.pi / 2 - u) with hgr
    have hgr_sm : ContDiffOn ℝ 1 gr (Set.Ioo 0 (Real.pi / 4)) := by
      have hinner : ContDiffOn ℝ 1 (fun u : ℝ => Real.pi / 2 - u) (Set.Ioo 0 (Real.pi / 4)) := by
        have h1 : ContDiffOn ℝ 1 (fun _ : ℝ => Real.pi / 2) (Set.Ioo 0 (Real.pi / 4)) :=
          contDiffOn_const
        have h2 : ContDiffOn ℝ 1 (fun u : ℝ => u) (Set.Ioo 0 (Real.pi / 4)) := contDiffOn_id
        simpa using h1.sub h2
      have hmap : Set.MapsTo (fun u : ℝ => Real.pi / 2 - u) (Set.Ioo 0 (Real.pi / 4))
          (Set.Ioo 0 (Real.pi / 2)) := fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have hcomp := hsm1.comp hinner hmap
      rw [hgr]
      simpa only [Function.comp_def] using hcomp
    have hgr0 : Filter.Tendsto gr (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hmap : Filter.Tendsto (fun u : ℝ => Real.pi / 2 - u) (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hc : ContinuousAt (fun u : ℝ => Real.pi / 2 - u) 0 := by fun_prop
          have := hc.tendsto
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          rw [Set.mem_Ioi] at hu
          exact sub_lt_self _ hu
      have hcomp := hpi.comp hmap
      rw [hgr]
      simpa only [Function.comp_def] using hcomp
    have hgrd : ∀ u : ℝ, deriv gr u = -deriv h (Real.pi / 2 - u) := by
      intro u
      rw [hgr, deriv_comp_const_sub]
    -- gradient weight on the right half, dominated by the sin weight
    have hgradRle : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (deriv h x) ^ 2 * (Real.pi / 2 - x) ^ (-η) ≤ 2 ^ η * Fi x := by
      intro x hx
      have hxI : x ∈ Set.Ioc (Real.pi / 4) (Real.pi / 2) := ⟨hx.1, hx.2.le⟩
      have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare η hη0).2.2.2.1 x hxI
      have hmul := mul_le_mul_of_nonneg_left hcmp (sq_nonneg (deriv h x))
      calc (deriv h x) ^ 2 * (Real.pi / 2 - x) ^ (-η)
          ≤ (deriv h x) ^ 2 * (2 ^ η * (Real.sin (2 * x)) ^ (-η)) := hmul
        _ = 2 ^ η * Fi x := by rw [hFi]; ring
    have hgradR : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      refine integrableOn_of_le (f := fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))
        (g := fun θ : ℝ => 2 ^ η * Fi θ) measurableSet_Ioo
        ((hI.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)).const_mul _)
        ?_ ?_ hgradRle
      · have hcont : ContinuousOn (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))
            (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
          have hd : ContinuousOn (deriv h) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
            (hsm1.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono
              (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
          have h1 : ContinuousOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-η))
              (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
            refine ContinuousOn.rpow_const ?_ ?_
            · fun_prop
            · intro x hx
              exact Or.inl (by linarith [hx.2])
          exact (hd.pow 2).mul h1
        exact hcont.aestronglyMeasurable measurableSet_Ioo
      · intro x hx
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (le_of_lt (by linarith [hx.2])) _)
    have hgrint : MeasureTheory.IntegrableOn (fun u : ℝ => (deriv gr u) ^ 2 * u ^ (-η))
        (Set.Ioo 0 (Real.pi / 4)) := by
      have h1 : MeasureTheory.IntegrableOn
          (fun u : ℝ => (deriv h (Real.pi / 2 - u)) ^ 2 * u ^ (-η)) (Set.Ioo 0 (Real.pi / 4)) := by
        have h2 := (integrableOn_comp_sub_left_iff
          (Φ := fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))).mpr hgradR
        refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioo
        show (deriv h (Real.pi / 2 - u)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - u)) ^ (-η)
            = (deriv h (Real.pi / 2 - u)) ^ 2 * u ^ (-η)
        rw [show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
      exact h1.congr_fun (fun u _ => by rw [hgrd u, neg_sq]) measurableSet_Ioo
    obtain ⟨hGR1, hGR2⟩ := powerHardyOpenAux (a := Real.pi / 4) (η := η) h4pos hη0 hη1 hgr_sm hgr0 hgrint
    -- ## integrability of `G = h² sin(2θ)^{-(2+η)}` on the two halves
    have hGcont : ContinuousOn G (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ => (h θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
        hsm.continuousOn.pow 2
      have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + η)))
          (Set.Ioo 0 (Real.pi / 2)) := by
        refine ContinuousOn.rpow_const ?_ ?_
        · fun_prop
        · intro x hx
          exact Or.inl (hsinpos x hx).ne'
      rw [hG]
      exact h1.mul h2
    have hGRbase : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      have hgr1' : MeasureTheory.IntegrableOn
          (fun u : ℝ => (h (Real.pi / 2 - u)) ^ 2 * u ^ (-(2 + η)))
          (Set.Ioo 0 (Real.pi / 4)) := by
        rw [hgr] at hGR1
        simpa only using hGR1
      refine (integrableOn_comp_sub_left_iff
        (Φ := fun θ : ℝ => (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)))).mp ?_
      refine hgr1'.congr_fun (fun u _ => ?_) measurableSet_Ioo
      show (h (Real.pi / 2 - u)) ^ 2 * u ^ (-(2 + η))
          = (h (Real.pi / 2 - u)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - u)) ^ (-(2 + η))
      rw [show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
    have hGL : MeasureTheory.IntegrableOn G (Set.Ioo 0 (Real.pi / 4)) := by
      refine integrableOn_of_le (f := G)
        (g := fun x : ℝ => (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * x ^ (-(2 + η))))
        measurableSet_Ioo (hGL1.const_mul _)
        ((hGcont.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)).aestronglyMeasurable
          measurableSet_Ioo) ?_ ?_
      · intro x hx
        rw [hG]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinnn x ⟨hx.1, by linarith [hx.2]⟩) _)
      · intro x hx
        rw [hG]
        have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare (2 + η) (by linarith)).1 x
          ⟨hx.1, hx.2.le⟩
        calc (h x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            ≤ (h x) ^ 2 * ((Real.pi / 4) ^ (2 + η) * x ^ (-(2 + η))) :=
              mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
          _ = (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * x ^ (-(2 + η))) := by ring
    have hGR : MeasureTheory.IntegrableOn G (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      refine integrableOn_of_le (f := G)
        (g := fun x : ℝ => (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * (Real.pi / 2 - x) ^ (-(2 + η))))
        measurableSet_Ioo (hGRbase.const_mul _)
        ((hGcont.mono (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)).aestronglyMeasurable
          measurableSet_Ioo) ?_ ?_
      · intro x hx
        rw [hG]
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (hsinnn x ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩) _)
      · intro x hx
        rw [hG]
        have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare (2 + η) (by linarith)).2.2.1 x
          ⟨hx.1, hx.2.le⟩
        calc (h x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            ≤ (h x) ^ 2 * ((Real.pi / 4) ^ (2 + η) * (Real.pi / 2 - x) ^ (-(2 + η))) :=
              mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
          _ = (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * (Real.pi / 2 - x) ^ (-(2 + η))) := by ring
    have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iθ := by
      have hGL' : MeasureTheory.IntegrableOn G (Set.Ioc 0 (Real.pi / 4)) :=
        (MeasureTheory.integrableOn_congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc
          (a := (0 : ℝ)) (b := Real.pi / 4))).mp hGL
      have hGR' : MeasureTheory.IntegrableOn G (Set.Ioc (Real.pi / 4) (Real.pi / 2)) :=
        (MeasureTheory.integrableOn_congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc
          (a := Real.pi / 4) (b := Real.pi / 2))).mp hGR
      have hU : MeasureTheory.IntegrableOn G
          (Set.Ioc 0 (Real.pi / 4) ∪ Set.Ioc (Real.pi / 4) (Real.pi / 2)) := hGL'.union hGR'
      have hset : (Set.Ioc 0 (Real.pi / 4) ∪ Set.Ioc (Real.pi / 4) (Real.pi / 2))
          = Set.Ioc 0 (Real.pi / 2) := by
        ext x; constructor
        · rintro (hx | hx)
          · exact ⟨hx.1, by linarith [hx.2]⟩
          · exact ⟨by linarith [hx.1], hx.2⟩
        · intro hx
          rcases lt_or_ge (Real.pi / 4) x with hx4 | hx4
          · exact Or.inr ⟨hx4, hx.2⟩
          · exact Or.inl ⟨hx.1, hx4⟩
      rw [hset] at hU
      exact (MeasureTheory.integrableOn_congr_set_ae
        (MeasureTheory.Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).mp hU
    -- ## `Gi = G` a.e. on `Iθ`
    have hGiaeq : Gi =ᵐ[volume.restrict Work.Spaces.Iθ] G := by
      have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
      rw [hμ]
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      rw [hGi, hG]
      change (h x / Real.sin (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-η)
        = (h x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
      have hsp : 0 < Real.sin (2 * x) := hsinpos x hx
      have h1 : (Real.sin (2 * x)) ^ (-(2 : ℝ)) = ((Real.sin (2 * x)) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hsp.le, Real.rpow_ofNat]
      have h2 : (Real.sin (2 * x)) ^ (-(2 + η))
          = (Real.sin (2 * x)) ^ (-(2 : ℝ)) * (Real.sin (2 * x)) ^ (-η) := by
        rw [show -(2 + η) = -(2 : ℝ) + (-η) by ring, Real.rpow_add hsp]
      rw [div_pow, h2, h1]
      ring
    -- ## the two halves of the `G`-integral
    have hFi_nn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] Fi := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      rw [hFi]
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos])) _)
    have hleft : (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
        ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
            * (∫ θ in Work.Spaces.Iθ, Fi θ) := by
      have step1 : (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
          ≤ (Real.pi / 4) ^ (2 + η)
              * ∫ θ in Set.Ioo 0 (Real.pi / 4), (h θ) ^ 2 * θ ^ (-(2 + η)) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_mono_on hGL (hGL1.const_mul _) measurableSet_Ioo ?_
        intro x hx
        rw [hG]
        have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare (2 + η) (by linarith)).1 x
          ⟨hx.1, hx.2.le⟩
        calc (h x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            ≤ (h x) ^ 2 * ((Real.pi / 4) ^ (2 + η) * x ^ (-(2 + η))) :=
              mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
          _ = (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * x ^ (-(2 + η))) := by ring
      have step3 : (∫ x in Set.Ioo 0 (Real.pi / 4), (deriv h x) ^ 2 * x ^ (-η))
          ≤ 2 ^ η * ∫ x in Set.Ioo 0 (Real.pi / 4), Fi x := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_mono_on hint1
          ((hI.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)).const_mul _) measurableSet_Ioo ?_
        intro x hx
        exact hFcompL x hx
      have step4 : (∫ x in Set.Ioo 0 (Real.pi / 4), Fi x)
          ≤ ∫ θ in Work.Spaces.Iθ, Fi θ :=
        MeasureTheory.setIntegral_mono_set hI hFi_nn
          (Filter.Eventually.of_forall (fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩))
      calc (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
          ≤ (Real.pi / 4) ^ (2 + η)
              * ∫ θ in Set.Ioo 0 (Real.pi / 4), (h θ) ^ 2 * θ ^ (-(2 + η)) := step1
        _ ≤ (Real.pi / 4) ^ (2 + η) * ((4 / (1 + η) ^ 2)
              * ∫ x in Set.Ioo 0 (Real.pi / 4), (deriv h x) ^ 2 * x ^ (-η)) :=
              mul_le_mul_of_nonneg_left hGL2 hcπ
        _ = (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2)
              * ∫ x in Set.Ioo 0 (Real.pi / 4), (deriv h x) ^ 2 * x ^ (-η) := by ring
        _ ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2)
              * (2 ^ η * ∫ x in Set.Ioo 0 (Real.pi / 4), Fi x) :=
              mul_le_mul_of_nonneg_left step3 (mul_nonneg hcπ hc4)
        _ = (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * ∫ x in Set.Ioo 0 (Real.pi / 4), Fi x := by ring
        _ ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * ∫ θ in Work.Spaces.Iθ, Fi θ :=
              mul_le_mul_of_nonneg_left step4 (mul_nonneg (mul_nonneg hcπ hc4) hc2)
    have hright : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ)
        ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
            * (∫ θ in Work.Spaces.Iθ, Fi θ) := by
      have step1 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ)
          ≤ (Real.pi / 4) ^ (2 + η)
              * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
                  (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_mono_on hGR (hGRbase.const_mul _) measurableSet_Ioo ?_
        intro x hx
        rw [hG]
        have hcmp := (Work.FTS.EllipticEst.remov.sin_weight_compare (2 + η) (by linarith)).2.2.1 x
          ⟨hx.1, hx.2.le⟩
        calc (h x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + η))
            ≤ (h x) ^ 2 * ((Real.pi / 4) ^ (2 + η) * (Real.pi / 2 - x) ^ (-(2 + η))) :=
              mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
          _ = (Real.pi / 4) ^ (2 + η) * ((h x) ^ 2 * (Real.pi / 2 - x) ^ (-(2 + η))) := by ring
      have step2 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
              (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)))
          = ∫ u in Set.Ioo 0 (Real.pi / 4), (gr u) ^ 2 * u ^ (-(2 + η)) := by
        rw [integral_Ioo_comp_sub (fun θ : ℝ => (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)))]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
        show (h (Real.pi / 2 - u)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - u)) ^ (-(2 + η))
            = (gr u) ^ 2 * u ^ (-(2 + η))
        rw [hgr, show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
      have step3 : (∫ u in Set.Ioo 0 (Real.pi / 4), (deriv gr u) ^ 2 * u ^ (-η))
          = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
              (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η) := by
        rw [integral_Ioo_comp_sub (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
        show (deriv gr u) ^ 2 * u ^ (-η)
            = (deriv h (Real.pi / 2 - u)) ^ 2 * (Real.pi / 2 - (Real.pi / 2 - u)) ^ (-η)
        rw [hgrd u, neg_sq, show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
      have step4 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
              (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η))
          ≤ 2 ^ η * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), Fi θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_mono_on hgradR
          ((hI.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩)).const_mul _)
          measurableSet_Ioo ?_
        intro x hx
        exact hgradRle x hx
      have step5 : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), Fi θ)
          ≤ ∫ θ in Work.Spaces.Iθ, Fi θ :=
        MeasureTheory.setIntegral_mono_set hI hFi_nn
          (Filter.Eventually.of_forall (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩))
      calc (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ)
          ≤ (Real.pi / 4) ^ (2 + η)
              * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
                  (h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) := step1
        _ = (Real.pi / 4) ^ (2 + η)
              * ∫ u in Set.Ioo 0 (Real.pi / 4), (gr u) ^ 2 * u ^ (-(2 + η)) := by rw [step2]
        _ ≤ (Real.pi / 4) ^ (2 + η) * ((4 / (1 + η) ^ 2)
              * ∫ u in Set.Ioo 0 (Real.pi / 4), (deriv gr u) ^ 2 * u ^ (-η)) :=
              mul_le_mul_of_nonneg_left hGR2 hcπ
        _ = (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2)
              * ∫ u in Set.Ioo 0 (Real.pi / 4), (deriv gr u) ^ 2 * u ^ (-η) := by ring
        _ = (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2)
              * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
                  (deriv h θ) ^ 2 * (Real.pi / 2 - θ) ^ (-η) := by rw [step3]
        _ ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2)
              * (2 ^ η * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), Fi θ) :=
              mul_le_mul_of_nonneg_left step4 (mul_nonneg hcπ hc4)
        _ = (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), Fi θ := by ring
        _ ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * ∫ θ in Work.Spaces.Iθ, Fi θ :=
              mul_le_mul_of_nonneg_left step5 (mul_nonneg (mul_nonneg hcπ hc4) hc2)
    refine ⟨?_, ?_⟩
    · exact hGint.congr hGiaeq.symm
    · have hsplit := integral_Iθ_split (G := G) (intervalIntegrable_half_left hGint)
        (intervalIntegrable_half_right hGint)
      calc (∫ θ in Work.Spaces.Iθ, Gi θ)
          = ∫ θ in Work.Spaces.Iθ, G θ := MeasureTheory.integral_congr_ae hGiaeq
        _ = (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
              + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ) := hsplit
        _ ≤ (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * (∫ θ in Work.Spaces.Iθ, Fi θ)
            + (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * (∫ θ in Work.Spaces.Iθ, Fi θ) := add_le_add hleft hright
        _ = 2 * (Real.pi / 4) ^ (2 + η) * (4 / (1 + η) ^ 2) * 2 ^ η
              * (∫ θ in Work.Spaces.Iθ, Fi θ) := by ring

end Work.FTS.H2.DivSinQR
