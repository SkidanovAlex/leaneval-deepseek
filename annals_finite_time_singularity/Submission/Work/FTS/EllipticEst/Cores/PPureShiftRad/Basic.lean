/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial difference quotient `dq c g` and its `ℋ⁰`-weighted majorant

For `c > 1` the radial difference quotient of `g` is

  `dq c g z θ = (g (c z) θ - g z θ)/(c-1)`.

This module collects the elementary analysis needed to compare its weighted level-`0`
`ℋ`-integrand with that of `D_z g = z ∂_z g`:

* `hk_zero_eq` : the level-`0` `ℋ`-integrand is the single weighted squared slot, written
  with the angular weight `sin(2θ)^{-η}` so that the three factors separate;
* `hk_zero_of_sin_eq_zero` : it vanishes at the angular boundary;
* `w_le_mul_sq`, `w_sq_le_mul` : the pointwise weight comparison `w z ≤ u² w (z u)`
  (hence `(w z)² ≤ u⁴ (w (z u))²`) for `z > 0`, `u ≥ 1`;
* `dq_eq_intervalIntegral` : the fundamental theorem of calculus in the form
  `dq c g z θ = (c-1)⁻¹ ∫_1^c u⁻¹ (D_z g) (z u) θ du` (the `u⁻¹` is the Jacobian of
  `u ↦ z u`);
* `interval_sq_le_mul_sub` : the Cauchy–Schwarz instance used below;
* `HkIntegrand_dq_le` : the pointwise domination
  `HkIntegrand α 0 (dq c g) z θ ≤ (c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.PPureShiftRad

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The level-`0` `ℋ`-integrand -/

/-- The level-`0` `ℋ`-integrand is the single weighted squared slot; writing the angular
weight as `sin(2θ)^{-η}` separates the three factors. -/
theorem hk_zero_eq (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 h z θ
      = (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.EllipticEst.Cores.Dil.HkIntegrand_zero_apply]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0,
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0)]
    ring
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      norm_num
    rw [mul_pow, div_pow, hsq, Real.rpow_neg hs]
    ring

/-- The level-`0` `ℋ`-integrand of any function vanishes where `sin(2θ) = 0`. -/
theorem hk_zero_of_sin_eq_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 h z θ = 0 := by
  rw [Work.FTS.EllipticEst.Cores.Dil.HkIntegrand_zero_apply, hs,
    Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0),
    div_zero, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-! ## The pointwise comparison of the radial weight `w` -/

/-- `w` is nonnegative (it is a quotient of squares). -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- For `z > 0` and `u ≥ 1`, `w z ≤ u² w (z u)`: both sides are `((1+z)/z)²` resp.
`((1+zu)/z)²`, and `1 + z ≤ 1 + z u`. -/
theorem w_le_mul_sq {z u : ℝ} (hz : 0 < z) (hu : 1 ≤ u) :
    Work.Spaces.w z ≤ u ^ 2 * Work.Spaces.w (z * u) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have h1 : (1 + z) ^ 2 ≤ (1 + z * u) ^ 2 := by
    have h : 1 + z ≤ 1 + z * u := by nlinarith [hz, hu]
    exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + z) h 2
  have hw : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  have hw2 : u ^ 2 * Work.Spaces.w (z * u) = (1 + z * u) ^ 2 / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  rw [hw, hw2]
  exact div_le_div_of_nonneg_right h1 (le_of_lt hz2)

/-- For `z > 0` and `u ≥ 1`, `(w z)² ≤ u⁴ (w (z u))²`. -/
theorem w_sq_le_mul {z u : ℝ} (hz : 0 < z) (hu : 1 ≤ u) :
    (Work.Spaces.w z) ^ 2 ≤ u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by
  have h := w_le_mul_sq hz hu
  have h4 : (u ^ 2 * Work.Spaces.w (z * u)) ^ 2
      = u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by ring
  have hzu : 0 < z * u := mul_pos hz (lt_of_lt_of_le zero_lt_one hu)
  calc (Work.Spaces.w z) ^ 2 ≤ (u ^ 2 * Work.Spaces.w (z * u)) ^ 2 :=
        pow_le_pow_left₀ (w_nonneg z) h 2
    _ = u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := h4

/-! ## The difference quotient as an interval integral -/

/-- **The fundamental theorem of calculus for the difference quotient.**  For `g` of class
`C^∞` on the open quadrant, `c > 1`, `z > 0` and `θ ∈ (0,π/2)`,

  `dq c g z θ = (c-1)⁻¹ ∫_1^c u⁻¹ (D_z g) (z u) θ du`. -/
theorem dq_eq_intervalIntegral {c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.EllipticEst.Cores.Dil.dq c g z θ
        = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ := by
  intro z θ hz hθ
  have hderiv : ∀ u ∈ Set.uIcc (1 : ℝ) c,
      HasDerivAt (fun u' : ℝ => g (z * u') θ) (u⁻¹ * Work.Spaces.Dz g (z * u) θ) u := by
    intro u hu
    rw [Set.uIcc_of_le (le_of_lt hc)] at hu
    have hu1 : (1 : ℝ) ≤ u := hu.1
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hzu : 0 < z * u := mul_pos hz hu0
    have hsl := hg.hasDerivAt_slice hθ hzu
    have hlin : HasDerivAt (fun u' : ℝ => z * u') z u := by
      simpa using (hasDerivAt_id u).const_mul z
    have hcomp := hsl.comp u hlin
    have hcoe : Work.Spaces.pz g (z * u) θ * z = u⁻¹ * Work.Spaces.Dz g (z * u) θ := by
      rw [Work.Spaces.Dz]
      field_simp
    rw [hcoe] at hcomp
    simpa only [Function.comp_def] using hcomp
  have hcont : ContinuousOn (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ)
      (Set.uIcc (1 : ℝ) c) := by
    rw [Set.uIcc_of_le (le_of_lt hc)]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.comp continuousOn_id (fun u hu => by
        simp only [Set.mem_Icc] at hu
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
    · exact ((hg.Dz).curry_z hθ).continuousOn.comp (by fun_prop) (fun u hu => by
        simp only [Set.mem_Icc] at hu
        simp only [Set.mem_Ioi]
        nlinarith [hu.1, hz])
  have hint : IntervalIntegrable (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ) volume
      (1 : ℝ) c := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC, Work.FTS.EllipticEst.Cores.Dil.dq_apply, div_eq_inv_mul, mul_one]
  rw [show c * z = z * c by ring]

/-! ## The weighted Cauchy–Schwarz instance -/

/-- Weighted Cauchy–Schwarz with weight `σ ≡ 1` and constant interval: for `f` continuous on
`[a,b]`, `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
theorem interval_sq_le_mul_sub {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * ∫ u in a..b, (f u) ^ 2 := by
  have hf2 : MeasureTheory.IntegrableOn (fun s : ℝ => (f s) ^ 2 * (1 : ℝ)) (Set.Ioc a b) := by
    have h : MeasureTheory.IntegrableOn (f ^ 2) (Set.Ioc a b) :=
      ((hf.pow 2).integrableOn_compact (μ := volume) isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have h2 : (fun s : ℝ => (f s) ^ 2 * (1 : ℝ)) = f ^ 2 := by
      funext s; simp
    rw [h2]
    exact h
  have hσi : MeasureTheory.IntegrableOn (fun s : ℝ => ((fun _ : ℝ => (1 : ℝ)) s)⁻¹)
      (Set.Ioc a b) := by
    have h : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
      MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp)
    have h' : (fun s : ℝ => ((fun _ : ℝ => (1 : ℝ)) s)⁻¹) = fun _ : ℝ => (1 : ℝ) := by
      funext s; simp
    rw [h']
    exact h
  have hcs := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul (f := f)
    (σ := fun _ : ℝ => (1 : ℝ)) hab (fun s _ => one_pos) hf2 hσi
  have h1 : (∫ u in a..b, ((fun _ : ℝ => (1 : ℝ)) u)⁻¹) = b - a := by
    rw [intervalIntegral.integral_const]
    norm_num
  have h2 : (∫ u in a..b, (f u) ^ 2 * (fun _ : ℝ => (1 : ℝ)) u) = ∫ u in a..b, (f u) ^ 2 := by
    simp
  rw [h1, h2] at hcs
  calc (∫ u in a..b, f u) ^ 2 ≤ (∫ u in a..b, (f u) ^ 2) * (b - a) := hcs
    _ = (b - a) * ∫ u in a..b, (f u) ^ 2 := by ring

/-! ## The pointwise domination by the majorant -/

/-- The majorant integrand of the difference quotient: `u² · HkIntegrand α 0 (D_z g) (z u) θ`,
continuous in `u` on `[1,c]` for every point of the closed quadrant. -/
theorem continuousOn_u_majorant {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn
        (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
        (Set.Icc 1 c) := by
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ u : ℝ,
        u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ = 0 := by
      intro u
      rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
    simp only [h0]
    exact continuousOn_const
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have hs : Real.sin (2 * θ) = 0 := by rw [← hθ0]; simp
      have h0 : ∀ u : ℝ,
          u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
        intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
      simp only [h0]
      exact continuousOn_const
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · -- the interior case: a composition of continuous maps
        have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
        have hmap : Set.MapsTo (fun u : ℝ => (z * u, θ)) (Set.Icc 1 c)
            (Work.FTS.EllipticEst.Q0) := by
          intro u hu
          simp only [Set.mem_Icc] at hu
          exact Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨mul_pos hzpos (lt_of_lt_of_le zero_lt_one hu.1), hθ'⟩
        have hDz : ContinuousOn (fun u : ℝ => Work.Spaces.Dz g (z * u) θ) (Set.Icc 1 c) :=
          (hg.Dz).continuousOn.comp
            ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn hmap
        have hwcont : ContinuousOn (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2) (Set.Icc 1 c) := by
          have hcoe : (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2)
              = fun u : ℝ => ((1 + z * u) ^ 2 / (z * u) ^ 2) ^ 2 := by
            funext u; rw [Work.Spaces.w]
          rw [hcoe]
          refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
          · have h1 : ContinuousOn (fun u : ℝ => 1 + z * u) (Set.Icc 1 c) :=
              continuous_const.continuousOn.add
                ((continuous_const.mul continuous_id).continuousOn)
            exact h1.pow 2
          · exact ((continuous_const.mul continuous_id).continuousOn).pow 2
          · intro u hu
            simp only [Set.mem_Icc] at hu
            exact pow_ne_zero 2 (mul_ne_zero (ne_of_gt hzpos)
              (ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)))
        have hcoe : ∀ u : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ
            = (Work.Spaces.Dz g (z * u) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w (z * u)) ^ 2 :=
          fun u => hk_zero_eq α (Work.Spaces.Dz g) (z * u) θ hθ
        simp only [hcoe]
        exact (continuousOn_id.pow 2).mul (((hDz.pow 2).mul continuousOn_const).mul hwcont)
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [hθpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have h0 : ∀ u : ℝ,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
          intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
        simp only [h0]
        exact continuousOn_const

/-- **The pointwise domination.**  For every `z ∈ Iz`, `θ ∈ Iθ`,

  `HkIntegrand α 0 (dq c g) z θ ≤ (c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du`. -/
theorem HkIntegrand_dq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
        ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
  intro z hz θ hθ
  have hc1 : 1 ≤ c := le_of_lt hc
  -- degenerate cases: everything vanishes
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ u : ℝ,
        u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ = 0 := by
      intro u; rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
    rw [Work.FTS.LocData.HkIntegrand_zero_fst α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) θ]
    refine le_of_eq ?_
    simp only [h0, intervalIntegral.integral_zero, mul_zero]
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have hs : Real.sin (2 * θ) = 0 := by rw [← hθ0]; simp
      have h0 : ∀ u : ℝ,
          u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
        intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
      rw [hk_zero_of_sin_eq_zero α (Work.FTS.EllipticEst.Cores.Dil.dq c g) hs z]
      refine le_of_eq ?_
      simp only [h0, intervalIntegral.integral_zero, mul_zero]
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · -- the interior case
        have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
        have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Real.rpow_nonneg
            (Real.sin_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
        have hwznn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        -- continuity of `u ↦ u⁻¹ D_z g (z u) θ` on `[1,c]`
        have hcont : ContinuousOn (fun u : ℝ => u⁻¹ * Work.Spaces.Dz g (z * u) θ)
            (Set.Icc 1 c) := by
          refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_id.inv₀ (fun u hu => by
              simp only [Set.mem_Icc] at hu
              exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))
          · exact ((hg.Dz).curry_z hθ').continuousOn.comp (by fun_prop) (fun u hu => by
              simp only [Set.mem_Icc] at hu
              simp only [Set.mem_Ioi]
              nlinarith [hu.1, hzpos])
        -- the fundamental theorem of calculus
        have hftc := dq_eq_intervalIntegral hg hc z θ hzpos hθ'
        -- the Cauchy–Schwarz step
        have hcs := interval_sq_le_mul_sub hc1 hcont
        have hcne : (c - 1) ≠ 0 := by linarith
        have hA : (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
            ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
          rw [hftc]
          calc ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              = (c - 1)⁻¹ ^ 2
                  * (∫ u in (1 : ℝ)..c, u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by ring
            _ ≤ (c - 1)⁻¹ ^ 2 * ((c - 1) * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
            _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                calc (c - 1)⁻¹ ^ 2 * ((c - 1) * ∫ u in (1 : ℝ)..c,
                      (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2)
                    = (c - 1)⁻¹ * ((c - 1)⁻¹ * (c - 1)) * ∫ u in (1 : ℝ)..c,
                        (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by ring
                  _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                        (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                      rw [inv_mul_cancel₀ hcne, mul_one]
        -- multiply by the angular weight and the radial weight
        have hB : (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
            ≤ (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
          have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2 :=
            mul_nonneg hsnn hwznn
          calc (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
              ≤ ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                  (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2)
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2) :=
                mul_le_mul_of_nonneg_right hA h2
            _ = (c - 1)⁻¹ * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w z) ^ 2)
                  * ∫ u in (1 : ℝ)..c, (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) := by ring
            _ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c,
                ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 := by
                rw [intervalIntegral.integral_const_mul]
        -- the pointwise comparison of the integrands
        have hpt : ∀ u ∈ Set.Icc (1 : ℝ) c,
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
          intro u hu
          have hu1 : (1 : ℝ) ≤ u := hu.1
          have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          have hw := w_sq_le_mul hzpos hu1
          have hune : u ≠ 0 := ne_of_gt hu0
          have halg : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2))
              = u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w (z * u)) ^ 2) := by
            field_simp
          have hKeq := hk_zero_eq α (Work.Spaces.Dz g) (z * u) θ hθ
          have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2)) := by
            have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                  * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
              ring
            rw [h1]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hw (sq_nonneg _)) hsnn
          calc ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
              ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                * ((u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2)) := hstep
            _ = u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  * (Work.Spaces.w (z * u)) ^ 2) := halg
            _ = u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
                rw [hKeq]
        -- assemble
        have hInt1 : IntervalIntegrable (fun u : ℝ =>
            ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
              * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) volume (1 : ℝ) c := by
          have hc' : ContinuousOn (fun u : ℝ =>
              ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2)
                * (u⁻¹ * Work.Spaces.Dz g (z * u) θ) ^ 2) (Set.uIcc (1 : ℝ) c) := by
            rw [Set.uIcc_of_le hc1]
            exact (hcont.pow 2).const_mul _
          exact hc'.intervalIntegrable
        have hInt2 : IntervalIntegrable (fun u : ℝ => u ^ 2 *
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) volume (1 : ℝ) c := by
          have hc' : ContinuousOn (fun u : ℝ => u ^ 2 *
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) (Set.uIcc (1 : ℝ) c) := by
            rw [Set.uIcc_of_le hc1]
            exact continuousOn_u_majorant hg hc z hz θ hθ
          exact hc'.intervalIntegrable
        have hmono := intervalIntegral.integral_mono_on hc1 hInt1 hInt2 hpt
        have hQQ : Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
            = (Work.FTS.EllipticEst.Cores.Dil.dq c g z θ) ^ 2
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Work.Spaces.w z) ^ 2) := by
          rw [hk_zero_eq α (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ hθ]
          ring
        rw [hQQ]
        exact hB.trans (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (by linarith)))
      · have hs : Real.sin (2 * θ) = 0 := by
          rw [hθpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have h0 : ∀ u : ℝ,
            u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ = 0 := by
          intro u; rw [hk_zero_of_sin_eq_zero α _ hs, mul_zero]
        rw [hk_zero_of_sin_eq_zero α (Work.FTS.EllipticEst.Cores.Dil.dq c g) hs z]
        refine le_of_eq ?_
        simp only [h0, intervalIntegral.integral_zero, mul_zero]

end Work.FTS.EllipticEst.Cores.PPureShiftRad
