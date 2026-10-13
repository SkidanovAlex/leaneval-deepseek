/-
The one-dimensional angular slice inequality underlying the mixed weighted interpolation
estimate.

`slice_key`: there is `c₁ > 0` such that for every real function `f` of class `C²` on an open
neighbourhood of the angular interval `[0,π/2]` with `f 0 = f (π/2) = 0`,

  `((1-η)/(1+η)) ∫_{Iθ} (f')² sin(2θ)^{-η}
      ≤ -∫_{Iθ} f f'' sin(2θ)^{-η} + c₁ ∫_{Iθ} f² sin(2θ)^{-η}`,

where `η = 99/100 = Work.Spaces.eta` and `Iθ = [0,π/2]`.

## Route

* `ThetaU.ang_ibp_eta` (angular integration by parts with the singular weight `sin(2θ)^{-η}`)
  gives `I = J + 2η K` with `I = ∫(f')²σ`, `J = -∫f f''σ`, `K = ∫ f f' cot(2θ) σ`;
* the pointwise AM–GM inequality `2|ab| ≤ ε a² + b²/ε` applied with
  `a = f' σ^{1/2}`, `b = f cot(2θ) σ^{1/2}` and `ε = 1/(1+η)` bounds
  `2η|K| ≤ η ε I + (η/ε) ∫ f² cot²(2θ) σ`;
* `cot²(2θ) σ = cos²(2θ) sin(2θ)^{-(2+η)} ≤ sin(2θ)^{-(2+η)}`, and the *sharp* Hardy
  inequality `hardy_shift_two_same_weight` (applied to `f`, which vanishes at both endpoints)
  bounds `∫ f² sin(2θ)^{-(2+η)} ≤ (1/(1+η)²) I + C_H ∫ f² σ`;
* the arithmetic `1 - η ε - η/(ε(1+η)²) = (1-η)/(1+η)` at `ε = 1/(1+η)` gives the claim with
  `c₁ = η(1+η) C_H`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ThetaU.AngIbp
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- On `Iθ`, division by `s ^ p` (`s ≥ 0`, `p > 0`) is multiplication by `s ^ (-p)`. -/
theorem div_eq_mul_rpow_neg {a s p : ℝ} (hs : 0 ≤ s) (hp : 0 < p) :
    a / s ^ p = a * s ^ (-p) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow (ne_of_gt hp), Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt hp)),
      div_zero, mul_zero]
  · rw [div_eq_mul_inv, Real.rpow_neg h.le]

/-- `x ^ 2 * x ^ (-(2+p)) = x ^ (-p)` for `x > 0`. -/
theorem sq_mul_rpow_neg_two_add {x p : ℝ} (hx : 0 < x) :
    x ^ 2 * x ^ (-(2 + p)) = x ^ (-p) := by
  have hx2 : x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
  rw [hx2, ← Real.rpow_add hx]
  ring_nf

/-- On the open interval `(0,π/2)`, `cot(2θ)² σ = cos²(2θ) sin(2θ)^{-(2+η)}`. -/
theorem cot_sq_mul_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
      = (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_pos_of_mem_Ioo hθ
  have hkey : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      = ((Real.sin (2 * θ)) ^ 2)⁻¹ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [show -(2 + Work.Spaces.eta) = (-2 : ℝ) + (-Work.Spaces.eta) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le]
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 from
      Real.rpow_natCast _ 2]
  rw [hkey, Real.cot_eq_cos_div_sin, div_pow, Work.FTS.EllipticEst.thEta, div_eq_mul_inv,
    Real.rpow_neg hs.le]
  ring

theorem slice_key : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (f : ℝ → ℝ),
      ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + c₁ * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  obtain ⟨C_H, hC_H_pos, hC_H⟩ := Work.FTS.EllipticEst.hardy_shift_two_same_weight
    Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  have hη : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have h1η : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith
  refine ⟨Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H, by positivity, ?_⟩
  intro f hf hf0 hf1
  -- the four angular integrals
  set I : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hIdef
  set J : ℝ := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
      * Work.FTS.EllipticEst.thEta θ with hJdef
  set K : ℝ := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
      * Work.FTS.EllipticEst.thEta θ with hKdef
  set V : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hVdef
  set Y : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) with hYdef
  set W : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ with hWdef
  -- the angular integration by parts
  have hAng : I = -J + 2 * Work.Spaces.eta * K := by
    rw [hIdef, hJdef, hKdef]
    exact Work.FTS.EllipticEst.ThetaU.ang_ibp_eta hf hf0 hf1
  -- integrability of the three pieces of the IBP
  obtain ⟨hIint, hJint, hKint⟩ :=
    Work.FTS.EllipticEst.ThetaU.integrableOn_ang_pieces hf hf0 hf1
  -- the slice bounds
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ :=
    Work.FTS.EllipticEst.ThetaU.slice_bounds hf hf0 hf1
  -- continuity of the pieces on the open interval
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hIooIθ : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  have hcont_f : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hf.continuousOn.mono hsub
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (sin_pos_of_mem_Ioo hθ)
  have hcont_th : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
  -- the pointwise majorant for the singular weight, reused below
  have hmaj : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-(2 + Work.Spaces.eta))
              + (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi (2 + Work.Spaces.eta) θ (by positivity) (hIooIθ hθ)
    have hmin0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIooIθ hθ)
    have hf2 : (f θ) ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg (f θ)) hfa 2
    have hspos : 0 < (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
      Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _
    have hmin_le1 : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hmin_le2 : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hsq1 : (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
        ≤ θ ^ (-Work.Spaces.eta) := by
      have h2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ θ ^ 2 :=
        pow_le_pow_left₀ hmin0 hmin_le1 2
      calc (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
          ≤ θ ^ 2 * θ ^ (-(2 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hθ.1.le _)
        _ = θ ^ (-(Work.Spaces.eta)) := sq_mul_rpow_neg_two_add hθ.1
    have hsq2 : (min θ (Real.pi / 2 - θ)) ^ 2
          * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-Work.Spaces.eta) := by
      have h2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hmin0 hmin_le2 2
      have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
      calc (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))
          ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hpos.le _)
        _ = (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := sq_mul_rpow_neg_two_add hpos
    calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right hf2 hspos.le
      _ ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2
            * ((Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (θ ^ (-(2 + Work.Spaces.eta))
                + (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + Work.Spaces.eta))
              + (min θ (Real.pi / 2 - θ)) ^ 2
                * (Real.pi / 2 - θ) ^ (-(2 + Work.Spaces.eta))) := by ring
      _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add hsq1 hsq2
  -- nonnegativity of the weighted `cot²` integrand on `Iθ`
  have hpt_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h1 : 0 ≤ Work.FTS.EllipticEst.thEta θ := by
      rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
      · rw [Work.FTS.EllipticEst.thEta, ← h, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      · exact (Real.rpow_pos_of_pos h _).le
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
  -- the pointwise comparison `f² cot²(2θ) σ ≤ f² sin(2θ)^{-(2+η)}` on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ
      ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    intro θ hθ
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hsin | hsin
    · have hσ : Work.FTS.EllipticEst.thEta θ = 0 := by
        rw [Work.FTS.EllipticEst.thEta, hsin, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      have h2 : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) = 0 := by
        rw [hsin, Real.zero_rpow (neg_ne_zero.mpr (by positivity : (2 + Work.Spaces.eta) ≠ 0))]
      rw [hσ, h2]
      simp
    · have hs : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (sin_nonneg_of_mem_Iθ hθ) (Ne.symm hsin)
      have hθ0 : θ ≠ 0 := by
        intro h; exact hsin (by rw [h]; norm_num)
      have hθ1 : θ ≠ Real.pi / 2 := by
        intro h
        apply hsin
        rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ1⟩
      have hcos : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
        have h := Real.sin_sq_add_cos_sq (2 * θ)
        nlinarith [sq_nonneg (Real.sin (2 * θ))]
      calc (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (f θ) ^ 2 * ((Real.cos (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
            rw [show (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
                = (f θ) ^ 2 * ((Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) by ring,
              cot_sq_mul_thEta hθ']
        _ ≤ (f θ) ^ 2 * (1 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcos (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
        _ = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by ring
  -- the same bound with the majorant
  have hpt_maj : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
    exact le_trans (hpt θ hθI) (hmaj θ hθ)
  -- integrability of the three `θ`-integrals
  have hYint : IntegrableOn (fun θ => (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Work.Spaces.Iθ := by
    refine Work.Elliptic.integrableOn_of_rpow_majorant hη.le hη1
      (by positivity : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)) ?_ ?_
    · exact (hcont_f.pow 2).mul hcont_th
    · intro θ hθ
      have hnn : 0 ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _).le
      calc ‖(f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))‖
          = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + Work.Spaces.eta)
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := hmaj θ hθ
  have hVint : IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := by
    have hcont_thη : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
    refine Work.Elliptic.integrableOn_of_rpow_majorant hη.le hη1
      (by positivity : (0 : ℝ) ≤ C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta)
      ?_ ?_
    · exact (hcont_f.pow 2).mul hcont_thη
    · intro θ hθ
      have hs : Work.FTS.EllipticEst.thEta θ
          ≤ (Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) :=
        Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ hη (hIooIθ hθ)
      have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIooIθ hθ)
      have hminl : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 :=
        le_trans (min_le_left _ _) hθ.2.le
      have hfb' : |f θ| ≤ C * (Real.pi / 2) := by
        calc |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfa
          _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hminl hC0
      have hf2 : (f θ) ^ 2 ≤ (C * (Real.pi / 2)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hfb' 2
      have hth_nn : 0 ≤ Work.FTS.EllipticEst.thEta θ :=
        (Real.rpow_pos_of_pos (sin_pos_of_mem_Ioo hθ) _).le
      have hnn : 0 ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        mul_nonneg (sq_nonneg _) hth_nn
      calc ‖(f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ‖
          = (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ (C * (Real.pi / 2)) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
            mul_le_mul_of_nonneg_right hf2 hth_nn
        _ ≤ (C * (Real.pi / 2)) ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
              * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by ring
  -- integrability of `f² cot²(2θ) σ`, obtained from `hYint` by comparison
  have hWint : IntegrableOn (fun θ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hcont_cot : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      rw [show (fun θ : ℝ => Real.cot (2 * θ))
          = fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ) from by
        funext θ; rw [Real.cot_eq_cos_div_sin]]
      exact ContinuousOn.div
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)
        hcont_sin (fun θ hθ => hsinn θ hθ)
    have hcont_g : ContinuousOn (fun θ : ℝ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine ContinuousOn.mul (ContinuousOn.mul (hcont_f.pow 2) (hcont_cot.pow 2)) ?_
      exact hcont_sin.rpow_const (fun θ hθ => Or.inl (hsinn θ hθ))
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (volume.restrict Work.Spaces.Iθ) := by
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
      rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ))
        (b := Real.pi / 2))]
      exact hcont_g.aestronglyMeasurable measurableSet_Ioo
    refine hYint.mono' haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hnn := hpt_nn θ hθ
    calc ‖(f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ‖
        = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      _ ≤ (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := hpt θ hθ
  -- `W ≤ Y`
  have hWY : W ≤ Y := by
    rw [hWdef, hYdef]
    refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact hpt_nn θ hθ) ?_ ?_
    · exact hYint
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hpt θ hθ
  -- the pointwise AM–GM bound
  have hAM : ∀ θ ∈ Work.Spaces.Iθ,
      |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|
        ≤ (1 / (2 * (1 + Work.Spaces.eta))) * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + ((1 + Work.Spaces.eta) / 2)
            * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    intro θ hθ
    rcases eq_or_ne (Real.sin (2 * θ)) 0 with hsin | hsin
    · have hσ : Work.FTS.EllipticEst.thEta θ = 0 := by
        rw [Work.FTS.EllipticEst.thEta, hsin, Real.zero_rpow (neg_ne_zero.mpr hη.ne')]
      rw [hσ]
      simp
    · have hs : 0 < Real.sin (2 * θ) :=
        lt_of_le_of_ne (sin_nonneg_of_mem_Iθ hθ) (Ne.symm hsin)
      have hsq : Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
          = Work.FTS.EllipticEst.thEta θ := by
        rw [← Real.rpow_add hs]
        have : -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -Work.Spaces.eta := by ring
        rw [this, Work.FTS.EllipticEst.thEta]
      set A : ℝ := deriv f θ * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) with hA
      set B : ℝ := f θ * Real.cot (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) with hB
      have hAB : f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ = A * B := by
        rw [hA, hB, ← hsq]
        ring
      have hA2 : A ^ 2 = (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
        rw [hA, show (deriv f θ * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
            = (deriv f θ) ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
              * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) by ring, hsq]
      have hB2 : B ^ 2 = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
        rw [hB, show (f θ * Real.cot (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
            = (f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
              * (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))
                * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) by ring, hsq]
      have hg : |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|
          = |A| * |B| := by
        rw [hAB, abs_mul]
      rw [hg]
      have hsq0 := sq_nonneg (|A| - (1 + Work.Spaces.eta) * |B|)
      have hpos : (0 : ℝ) < 2 * (1 + Work.Spaces.eta) := by positivity
      have h2 : 2 * (1 + Work.Spaces.eta) * (|A| * |B|) ≤ A ^ 2
          + (1 + Work.Spaces.eta) ^ 2 * B ^ 2 := by
        have hsqA : |A| ^ 2 = A ^ 2 := sq_abs A
        have hsqB : |B| ^ 2 = B ^ 2 := sq_abs B
        nlinarith [hsq0, hsqA, hsqB]
      have h3 := div_le_div_of_nonneg_right h2 hpos.le
      rw [mul_div_cancel_left₀ _ (ne_of_gt hpos)] at h3
      rw [hA2, hB2] at h3
      have h4 : ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            + (1 + Work.Spaces.eta) ^ 2
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ))
            / (2 * (1 + Work.Spaces.eta))
          = (1 / (2 * (1 + Work.Spaces.eta)))
              * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + ((1 + Work.Spaces.eta) / 2)
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        field_simp
        try ring
      rw [h4] at h3
      exact h3
  -- the bound on `K`
  have hKbound : 2 * Work.Spaces.eta * K
      ≤ (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
        + (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W := by
    have hKabs : K ≤ ∫ θ in Work.Spaces.Iθ,
        |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ| := by
      rw [hKdef]
      calc (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
              * Work.FTS.EllipticEst.thEta θ)
          ≤ |∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ)
              * Work.FTS.EllipticEst.thEta θ| := le_abs_self _
        _ ≤ _ := MeasureTheory.abs_integral_le_integral_abs
    have hsum_eq : (∫ θ in Work.Spaces.Iθ,
          ((1 / (2 * (1 + Work.Spaces.eta)))
              * ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + ((1 + Work.Spaces.eta) / 2)
              * ((f θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)))
        = (1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W := by
      rw [MeasureTheory.integral_add (hIint.const_mul _) (hWint.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hIdef, ← hWdef]
    have hmono : (∫ θ in Work.Spaces.Iθ,
          |f θ * deriv f θ * Real.cot (2 * θ) * Work.FTS.EllipticEst.thEta θ|) ≤
        (1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W := by
      rw [← hsum_eq]
      refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
        (Filter.Eventually.of_forall fun θ => abs_nonneg _)
        ((hIint.const_mul _).add (hWint.const_mul _)) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact hAM θ hθ
    have hfin : K ≤ (1 / (2 * (1 + Work.Spaces.eta))) * I
        + ((1 + Work.Spaces.eta) / 2) * W := le_trans hKabs hmono
    have h2 : 2 * Work.Spaces.eta * K ≤ 2 * Work.Spaces.eta
        * ((1 / (2 * (1 + Work.Spaces.eta))) * I + ((1 + Work.Spaces.eta) / 2) * W) :=
      mul_le_mul_of_nonneg_left hfin (by positivity)
    have hrw : 2 * Work.Spaces.eta * ((1 / (2 * (1 + Work.Spaces.eta))) * I
          + ((1 + Work.Spaces.eta) / 2) * W)
        = (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
          + (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W := by
      field_simp
      try ring
    rwa [hrw] at h2
  -- the sharp Hardy inequality applied to `f`
  have hconvI : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 / Real.sin (2 * θ) ^ Work.Spaces.eta)
      = I := by
    rw [hIdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) hη
  have hconvV : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / Real.sin (2 * θ) ^ Work.Spaces.eta) = V := by
    rw [hVdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) hη
  have hconvY : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 / Real.sin (2 * θ) ^ (2 + Work.Spaces.eta))
      = Y := by
    rw [hYdef]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact div_eq_mul_rpow_neg (sin_nonneg_of_mem_Iθ hθ) (by positivity)
  have hsubIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hHardy : Y ≤ (1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V := by
    have h := hC_H f ((hf.mono hsubIcc).of_le (by norm_num)) hf0 hf1
    rw [hconvY, hconvI, hconvV] at h
    simpa [add_comm] using h
  -- assembling
  have h3 : (Work.Spaces.eta * (1 + Work.Spaces.eta)) * W
      ≤ (Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V) :=
    mul_le_mul_of_nonneg_left (le_trans hWY hHardy) (by positivity)
  have h4 : (Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((1 / (1 + Work.Spaces.eta) ^ 2) * I + C_H * V)
      = (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
        + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    field_simp
    try ring
  have h5 : 2 * Work.Spaces.eta * K ≤ (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    rw [h4] at h3
    have h := hKbound
    linarith
  have h6 : I ≤ -J + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta / (1 + Work.Spaces.eta)) * I
      + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    have h := h5
    linarith [hAng, h]
  have h8 : I - (2 * (Work.Spaces.eta / (1 + Work.Spaces.eta))) * I
      = ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * I := by
    field_simp
    try ring
  have h7 : I - (2 * (Work.Spaces.eta / (1 + Work.Spaces.eta))) * I
      ≤ -J + (Work.Spaces.eta * (1 + Work.Spaces.eta) * C_H) * V := by
    linarith [h6]
  rw [h8] at h7
  exact h7

end Work.FTS.EllipticEst.Alpha4
