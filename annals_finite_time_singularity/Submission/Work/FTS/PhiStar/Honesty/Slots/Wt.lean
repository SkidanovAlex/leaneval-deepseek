import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## 1. Elementary integrability of the angular `rpow` weight -/

/-- `sin(2θ)^e` is integrable on `Iθ` for every `e > -1`. -/
theorem sin_rpow_integrableOn_Iθ {e : ℝ} (he : -1 < e) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ e) Work.Spaces.Iθ := by
  by_cases h : e ≤ 0
  · exact (Work.Spaces.sin_two_rpow e he h).1
  · have hcont : Continuous (fun θ : ℝ => Real.sin (2 * θ) ^ e) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr (le_of_lt (not_le.mp h)))
    have hIcc : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    rw [hIcc]
    refine MeasureTheory.Integrable.mono'
      (g := fun _ : ℝ => (1 : ℝ)) (integrableOn_const ?_) ?_ ?_
    · rw [Real.volume_Icc]; simp
    · exact hcont.continuousOn.aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 e)]
      exact Real.rpow_le_one h0 (Real.sin_le_one _) (le_of_lt (not_le.mp h))

/-! ## 2. The weight profile `Φ z = z^{2/α}/(1+z)^{7/α}` and the integrability of `(Φ w)²` -/

/-- The weight profile singled out by the radial mode bounds. -/
noncomputable def phiWt (α : ℝ) (z : ℝ) : ℝ := z ^ (2 / α) / (1 + z) ^ (7 / α)

theorem phiWt_nonneg {α z : ℝ} (hz : 0 ≤ z) : 0 ≤ phiWt α z :=
  div_nonneg (Real.rpow_nonneg hz _) (Real.rpow_nonneg (by linarith) _)

/-- The pointwise identity `(Φ z · w z)² = z^{4/α-4}·(1+z)^{4-14/α}` for `z > 0`. -/
theorem phiWt_mul_w_sq {α : ℝ} (_hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    (phiWt α z * Work.Spaces.w z) ^ 2 = z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α) := by
  have h1 : 0 < 1 + z := by linarith
  have hwr : z ^ (2:ℝ) = z ^ 2 := Real.rpow_natCast z 2
  have h1r : (1 + z) ^ (2:ℝ) = (1 + z) ^ 2 := Real.rpow_natCast (1 + z) 2
  have hw1 : (z ^ 2)⁻¹ = z ^ (-(2 : ℝ)) := by rw [← hwr, ← Real.rpow_neg hz.le (2 : ℝ)]
  have hw2 : Work.Spaces.w z = (1 + z) ^ (2:ℝ) * z ^ (-(2 : ℝ)) := by
    rw [Work.Spaces.w, div_eq_mul_inv, hw1, h1r.symm]
  have hphi : phiWt α z = z ^ (2 / α) * (1 + z) ^ (-(7 / α)) := by
    rw [phiWt, div_eq_mul_inv, ← Real.rpow_neg h1.le (7 / α)]
  have hlin : phiWt α z * Work.Spaces.w z
      = z ^ (2 / α - 2) * (1 + z) ^ (2 - 7 / α) := by
    rw [hw2, hphi]
    rw [show z ^ (2 / α) * (1 + z) ^ (-(7 / α))
          * ((1 + z) ^ (2:ℝ) * z ^ (-(2 : ℝ)))
        = (z ^ (2 / α) * z ^ (-(2 : ℝ)))
          * ((1 + z) ^ (2:ℝ) * (1 + z) ^ (-(7 / α))) by ring]
    rw [← Real.rpow_add hz (2 / α) (-(2:ℝ)), ← Real.rpow_add h1 (2:ℝ) (-(7/α))]
    ring_nf
  rw [hlin, mul_pow, sq, sq,
    (Real.rpow_add hz (2 / α - 2) (2 / α - 2)).symm,
    (Real.rpow_add h1 (2 - 7 / α) (2 - 7 / α)).symm]
  ring_nf

theorem integrableOn_phiWt_mul_w_sq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  have hα16 : (16 : ℝ) ≤ 4 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  have hα56 : (56 : ℝ) ≤ 14 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  have hexp1 : -1 < 4 / α - 4 := by linarith
  have hexp2 : -10 / α < -1 := by
    rw [div_lt_iff₀ hα]
    nlinarith [hα4, hα]
  have hexp3 : 4 - 14 / α ≤ 0 := by linarith
  -- the two dominating functions
  have hg1 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (4 / α - 4)) (Set.Ioo 0 1) := by
    have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (4 / α - 4)) (Set.Icc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
        (intervalIntegral.intervalIntegrable_rpow' hexp1)
    exact hIcc.mono_set Set.Ioo_subset_Icc_self
  have hg2 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-10 / α)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (show (0:ℝ) < 1 by norm_num)).mpr hexp2
  have hca : ContinuousOn (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
      (Set.Ioi 0) := by
    have h2 : ContinuousOn (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
      continuousOn_const.add continuousOn_id
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).mul
      (h2.rpow_const (fun x hx => Or.inl (ne_of_gt (by linarith [show (0:ℝ) < x from hx]))))
  -- the small part
  have hsmall : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
    refine MeasureTheory.Integrable.mono' hg1 ?_ ?_
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
          (MeasureTheory.volume.restrict (Set.Ioo 0 1)) :=
        (hca.mono (fun x hx => hx.1)).aestronglyMeasurable measurableSet_Ioo
      refine haesm.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      exact (phiWt_mul_w_sq hα hz.1).symm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), phiWt_mul_w_sq hα hz.1]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (le_of_lt hz.1) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz.1]) hexp3)
  -- the large part
  have hbig : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    refine MeasureTheory.Integrable.mono' hg2 ?_ ?_
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α))
          (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
        (hca.mono (fun x hx => lt_trans zero_lt_one (show (1:ℝ) < x from hx))).aestronglyMeasurable
          measurableSet_Ioi
      refine haesm.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact (phiWt_mul_w_sq hα (lt_trans zero_lt_one (show (1:ℝ) < z from hz))).symm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : (1:ℝ) < z := hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), phiWt_mul_w_sq hα (by linarith)]
      have h2z : (1 + z) ^ (4 - 14 / α) ≤ z ^ (4 - 14 / α) :=
        Real.rpow_le_rpow_of_nonpos (x := z) (y := 1 + z) (z := 4 - 14 / α)
          (by linarith [hz1]) (by linarith) hexp3
      calc z ^ (4 / α - 4) * (1 + z) ^ (4 - 14 / α)
          ≤ z ^ (4 / α - 4) * z ^ (4 - 14 / α) :=
            mul_le_mul_of_nonneg_left h2z (Real.rpow_nonneg (by linarith) _)
        _ = z ^ (-10 / α) := by
            rw [← Real.rpow_add (by linarith : (0:ℝ) < z),
              show 4 / α - 4 + (4 - 14 / α) = -10 / α by ring]
  -- combine
  have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => (phiWt α z * Work.Spaces.w z) ^ 2)
      (Set.Icc 0 1) := hsmall.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  have hcomb := hIcc.union hbig
  rwa [Set.Icc_union_Ioi_eq_Ici (show (0:ℝ) ≤ 1 by norm_num)] at hcomb

/-! ## 3. Weighted-square integrability from a separable pointwise bound -/

/-- **Integrability of `θ ↦ (F z θ · w z)² sin(2θ)^e` and of its `θ`-integral.**
`F` is continuous on the open quadrant and bounded there by `K · φ(z)`, `φ` is nonnegative on
`Iz` with `(φ · w)²` integrable, and `e > -1` so that the angular weight is integrable. -/
theorem integrableOn_sq_mul_sin_rpow_of_bound {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {K e : ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)))
    (hK : 0 ≤ K) (hφnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ φ z)
    (hbdd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → |F z θ| ≤ K * φ z)
    (hφ : MeasureTheory.IntegrableOn (fun z : ℝ => (φ z * Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (he : -1 < e) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iz := by
  have hsinIoo : MeasureTheory.IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ e)
      (Set.Ioo 0 (π/2)) :=
    (sin_rpow_integrableOn_Iθ he).mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  -- the angular weight is nonnegative on the open interval
  have hsin0 : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) → 0 ≤ Real.sin (2 * θ) ^ e := fun θ hθ =>
    Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) e
  -- the pointwise domination (on the open quadrant)
  have hpt : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π/2) →
      (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e
        ≤ (K * φ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e := by
    intro z hz θ hθ
    have hKphi : 0 ≤ K * φ z := mul_nonneg hK (hφnn z (le_of_lt hz))
    have hF2 : (F z θ) ^ 2 ≤ (K * φ z) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hKphi]; exact hbdd z hz θ hθ
    have h1 : (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (K * φ z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hF2 (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (hsin0 θ hθ)
    nlinarith [h2, sq_nonneg (Work.Spaces.w z), hsin0 θ hθ]
  -- continuity of the uncurried integrand on the open quadrant
  have hwq : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
    unfold Work.Spaces.w
    exact ((continuousOn_const.add continuousOn_fst).pow 2).div (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinc : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := by
    refine (Real.continuous_sin.comp_continuousOn
      (continuousOn_const.mul continuousOn_snd)).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo ?_))
    exact ⟨by show (0:ℝ) < 2 * p.2; linarith [hp.2.1],
      by show 2 * p.2 < Real.pi; linarith [hp.2.2]⟩
  have hGcont : ContinuousOn
      (fun p : ℝ × ℝ => (F p.1 p.2 * Work.Spaces.w p.1) ^ 2 * Real.sin (2 * p.2) ^ e)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)) := ((hF.mul hwq).pow 2).mul hsinc
  -- the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with rfl | hz0
    · have hzero : (fun θ : ℝ => (F 0 θ * Work.Spaces.w 0) ^ 2 * Real.sin (2 * θ) ^ e)
          = fun _ => (0:ℝ) := by
        funext θ; simp [Work.Spaces.w]
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · have hsl : ContinuousOn
          (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
          (Set.Ioo 0 (π/2)) := by
        refine ((hF.comp (continuousOn_const.prodMk continuousOn_id)
          (fun p hp => ⟨hz0, hp⟩)).mul continuousOn_const).pow 2 |>.mul ?_
        refine (Real.continuous_sin.comp_continuousOn
          (continuousOn_const.mul continuousOn_id)).rpow_const ?_
        intro θ hθ
        refine Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo ?_))
        exact ⟨by show (0:ℝ) < 2 * θ; linarith [hθ.1],
          by show 2 * θ < Real.pi; linarith [hθ.2]⟩
      have hIoo : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
          (Set.Ioo 0 (π/2)) := by
        refine MeasureTheory.Integrable.mono'
          (hsinIoo.const_mul ((K * φ z * Work.Spaces.w z) ^ 2)) ?_ ?_
        · exact hsl.aestronglyMeasurable measurableSet_Ioo
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hsin0 θ hθ))]
          exact hpt z hz0 θ hθ
      exact hIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  refine ⟨hslice, ?_⟩
  -- the outer integral
  set S : ℝ := ∫ θ in Set.Ioo (0:ℝ) (π/2), Real.sin (2 * θ) ^ e with hS
  have hdom : MeasureTheory.IntegrableOn
      (fun z : ℝ => (K * φ z * Work.Spaces.w z) ^ 2 * S) Work.Spaces.Iz := by
    have h := hφ.const_mul (K ^ 2 * S)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hGae : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ =>
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioo 0 (π/2)))) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact hGcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have haesm1 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hGae.integral_prod_right'
  have haesm2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0:ℝ))]
    exact haesm1
  have haesm3 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine haesm2.congr ?_
    filter_upwards with z
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc)
  refine MeasureTheory.Integrable.mono' hdom haesm3 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) e)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with rfl | hz0
  · have hzero : (fun θ : ℝ => (F 0 θ * Work.Spaces.w 0) ^ 2 * Real.sin (2 * θ) ^ e)
        = fun _ => (0:ℝ) := by
      funext θ; simp [Work.Spaces.w]
    rw [hzero]
    simp [Work.Spaces.w]
  · rw [show (∫ θ in Work.Spaces.Iθ, (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e)
        = ∫ θ in Set.Ioo (0:ℝ) (π/2),
            (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e from
      MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc.symm)]
    calc ∫ θ in Set.Ioo (0:ℝ) (π/2),
          (F z θ * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e
        ≤ ∫ θ in Set.Ioo (0:ℝ) (π/2),
            (K * φ z * Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ e :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ =>
              mul_nonneg (sq_nonneg _) (hsin0 θ hθ))
            (hsinIoo.const_mul ((K * φ z * Work.Spaces.w z) ^ 2))
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => hpt z hz0 θ hθ)
      _ = (K * φ z * Work.Spaces.w z) ^ 2 * S := by
          rw [hS, ← MeasureTheory.integral_const_mul]

/-! ## Angular smoothness facts -/

/-- The Gegenbauer polynomials are `C^∞`. -/
theorem contDiff_gC_all : ∀ k : ℕ, ∀ n : ℕ,
    ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro n
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      exact contDiff_const
  | one =>
      intro n
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
      exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
      intro m
      rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x
        * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
        - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
      exact (((contDiff_const.mul contDiff_id).mul (ih2 m)).sub
        (contDiff_const.mul (ih1 m))).div_const _

/-- The angular modes `eFam j` are `C^∞`. -/
theorem contDiff_eFam_all (j : ℕ) : ∀ n : ℕ,
    ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam j) := by
  intro n
  have h2 : ContDiff ℝ n (Work.FTS.PhiStar.Gegenbauer.gC (2 * j + 1)) :=
    contDiff_gC_all (2 * j + 1) n
  exact Real.contDiff_cos.mul (h2.comp Real.contDiff_sin)

/-- Every iterated derivative of an angular mode is continuous. -/
theorem continuous_iteratedDeriv_eFam (m j : ℕ) :
    Continuous (iteratedDeriv m (Work.FTS.PhiStar.Gegenbauer.eFam j)) :=
  (contDiff_infty.mpr (contDiff_eFam_all j)).continuous_iteratedDeriv m
    (by show ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact_mod_cast le_top)

end Work.FTS.PhiStar.Honesty
