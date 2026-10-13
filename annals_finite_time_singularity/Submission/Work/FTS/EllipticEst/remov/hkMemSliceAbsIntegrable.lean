import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.FTS.EllipticEst.remov.sliceAbsSinCos2CS
import Submission.Work.FTS.EllipticEst.remov.pzIter2WeightedSqIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/

private lemma sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  show Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `(A * (b / s^{η/2}))² = A² b² s^{-η}` for `s ≥ 0`. -/
private lemma mul_div_rpow_sq (A b s : ℝ) (hs : 0 ≤ s) :
    (A * (b / s ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * b ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have h2 : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [mul_pow, div_pow, h2, Real.rpow_neg hs, div_eq_mul_inv]
  ring

/-! ## The main lemma -/

theorem hkMemSliceAbsIntegrable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    {z₀ z₁ : ℝ} (hz₀ : 0 < z₀) (hzlt : z₀ < z₁) :
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ) ∧
    (MeasureTheory.IntegrableOn
        (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
        (Set.Icc z₀ z₁)) ∧
    (MeasureTheory.Integrable
        (Function.uncurry (fun s θ : ℝ =>
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.uIoc z₀ z₁)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
    (∀ z ∈ Set.Icc z₀ z₁, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
  := by
  have hk1 : 1 ≤ k := hk
  have hA : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont_abs : ContinuousOn (fun p : ℝ × ℝ =>
      |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (continuous_sinCos2.comp continuous_snd).continuousOn
    exact ((hA.pzIter 2).continuousOn.abs).mul h2
  -- ## Conjunct 1
  have hconc1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have hmem := h.memA.1 z hzIz
    have hdom : MeasureTheory.IntegrableOn (fun θ : ℝ => (1 / z ^ 4) * Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ + 1) Work.Spaces.Iθ :=
      (hmem.const_mul (1 / z ^ 4)).add
        (MeasureTheory.integrableOn_const (C := (1 : ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    refine hdom.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        hcont_abs hz
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have h1 : |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
          ≤ (Work.Spaces.pzIter 2 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hh := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
          (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ) hz hθ
        rwa [abs_mul, abs_of_nonneg (sinCos2_nonneg_Iθ hθ)] at hh
      have h2 : (Work.Spaces.pzIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (1 / z ^ 4) * Work.Spaces.HkIntegrand α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
        have h3 := Work.Spaces.sq_le_HkIntegrand_z α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
        simp only [Work.Spaces.DzIter_zero] at h3
        have hkey : ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
        rw [hkey] at h3
        have hX : (Work.Spaces.pzIter 2 Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = (z ^ 4)⁻¹ * (z ^ 4 * ((Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [inv_mul_cancel_left₀ (pow_ne_zero 4 (ne_of_gt hz))]
        rw [hX, one_div]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ))]
      linarith
  -- ## Conjunct 4 (the pointwise weighted bound)
  have hconc4 : ∀ z ∈ Set.Icc z₀ z₁, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hS : MeasureTheory.Integrable (fun θ : ℝ =>
        (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := pzIter2WeightedSqIntegrable hk1 h z hzpos
    have hcs := sliceAbsSinCos2CS (f := fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (hA.aesm_slice_pzIter 2 hzpos) hS
    have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
          = z ^ 4 * (Work.Spaces.w z) ^ 2
              * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      intro θ hθ
      rw [mul_div_rpow_sq (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.w z)
        (Real.sin (2 * θ)) (sin_two_nonneg_Iθ hθ)]
      ring
    have hQz : (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        = z ^ 4 * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      have hae : (fun θ : ℝ => ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => z ^ 4 * (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpoint
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
    have hQ2 : Real.sqrt (∫ θ in Work.Spaces.Iθ,
          ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        = z ^ 2 * Work.Spaces.w z * Real.sqrt
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      rw [hQz, show z ^ 4 * (Work.Spaces.w z) ^ 2 = (z ^ 2 * Work.Spaces.w z) ^ 2 by ring]
      have hwz : (0 : ℝ) ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w]; positivity
      rw [Real.sqrt_mul (x := (z ^ 2 * Work.Spaces.w z) ^ 2) (by positivity),
        Real.sqrt_sq (mul_nonneg (by positivity) hwz)]
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := hcs
      _ ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [hQ2]
          have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := Work.FTS.EllipticEst.one_le_w hzpos
          have hzw : (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
                * (z ^ 2 * Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              = Work.Spaces.w z * (Real.sqrt (Real.pi / 2) * Real.sqrt
                  (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
            have h1 : (1 / z ^ 2) * Real.sqrt (Real.pi / 2)
                  * (z ^ 2 * Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
                = ((1 / z ^ 2) * z ^ 2) * (Real.sqrt (Real.pi / 2)
                    * (Work.Spaces.w z * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by ring
            rw [h1, one_div, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hzpos)), one_mul]
            ring
          rw [hzw]
          exact le_mul_of_one_le_left
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hw1
  -- ## The `z`-weighted integral `J` and the domination `Q ≤ J`
  set J : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ with hJdef
  have hJIz : MeasureTheory.IntegrableOn J Work.Spaces.Iz := by
    simpa only [hJdef] using h.memA.2
  have hJint : MeasureTheory.IntegrableOn J (Set.Icc z₀ z₁) :=
    hJIz.mono_set (fun z hz => le_trans (le_of_lt hz₀) hz.1)
  have hJnn : ∀ z : ℝ, 0 ≤ J z := by
    intro z
    rw [hJdef]
    exact MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
  have hQJ : ∀ z ∈ Set.Icc z₀ z₁,
      (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ J z := by
    intro z hz
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have hmem := h.memA.1 z hzIz
    have hintL : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
      refine hmem.mono' ?_ ?_
      · refine (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (fun p : ℝ × ℝ => (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (((continuousOn_fst.pow 2).mul (hA.pzIter 2).continuousOn).mul
            Work.FTS.EllipticEst.continuousOn_wdivsin_Q0) hzpos).pow 2
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k)
    rw [hJdef]
    exact MeasureTheory.integral_mono hintL hmem (fun θ =>
      Work.Spaces.sq_le_HkIntegrand_z α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (Nat.zero_le k))
  -- ## Conjunct 2
  have hconc2 : MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ z₁) := by
    have hDint : MeasureTheory.IntegrableOn
        (fun z : ℝ => (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2) * (1 + J z))
        (Set.Icc z₀ z₁) := by
      have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => (1 : ℝ) + J z) (Set.Icc z₀ z₁) :=
        (MeasureTheory.integrableOn_const (C := (1 : ℝ))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).add hJint
      exact h1.const_mul _
    have haesmF : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict (Set.Icc z₀ z₁)) := by
      have hprod : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          ((MeasureTheory.volume.restrict (Set.Ioc z₀ z₁)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.FTS.EllipticEst.aesm_uncurry_restrict_open
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
          hcont_abs hz₀.le
      have h4 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∫ θ : ℝ,
          |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict (Set.Ioc z₀ z₁)) :=
        hprod.integral_prod_right'
      rw [← MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (a := z₀) (b := z₁))]
      exact h4
    refine hDint.mono' haesmF ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun z hz => ?_)
    have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz.1
    have hFnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    have hcs := hconc4 z hz
    have h1 : (1 / z ^ 2) ≤ 1 / z₀ ^ 2 :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < z₀ ^ 2)
        (pow_le_pow_left₀ hz₀.le hz.1 2)
    have h3 : Real.sqrt (J z) ≤ 1 + J z := by
      have hJ0 := hJnn z
      nlinarith [Real.sq_sqrt hJ0, Real.sqrt_nonneg (J z)]
    have hc0 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
    have hz0inv : (0 : ℝ) ≤ 1 / z₀ ^ 2 := by positivity
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
        ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := hcs
      _ ≤ (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hc0) (Real.sqrt_nonneg _)
      _ ≤ (1 / z₀ ^ 2) * Real.sqrt (Real.pi / 2) * (1 + J z) :=
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQJ z hz))
            (mul_nonneg hz0inv hc0)).trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hz0inv hc0))
  -- ## Conjunct 3
  have hconc3 : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae
      (G := fun s θ : ℝ => |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) ?_ ?_ ?_ ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun a _ =>
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun b hb =>
          mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ hb)))
    · rw [Set.uIoc_of_le hzlt.le]
      exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open
        (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2| * Work.Elliptic.sinCos2 p.2)
        hcont_abs hz₀.le
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun a ha => ?_)
      rw [Set.uIoc_of_le hzlt.le] at ha
      exact hconc1 a (lt_trans hz₀ ha.1)
    · have hsub : Set.uIoc z₀ z₁ ⊆ Set.Icc z₀ z₁ := by
        rw [Set.uIoc_of_le hzlt.le]; exact Set.Ioc_subset_Icc_self
      exact hconc2.mono_set hsub
  exact ⟨hconc1, hconc2, hconc3, hconc4⟩

end Work.FTS.EllipticEst.remov
