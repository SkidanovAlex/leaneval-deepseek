import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

/-!
# The Cesàro profile: Stieltjes representation, weight bound, and lacunary tail summability

This file establishes the three elementary analytic facts about the Cesàro profile `cesH`,
its Stieltjes density `cesHd` and its tail `cesH2` that the lacunary oscillation argument
needs:

* **(Stieltjes representation)** for every `u > 0`,
  `cesH1 u = -∫_0^1 cesHd t · 1_{u ≤ t} dt`.
  Equivalently, on `(0,1]` the profile is the negative primitive of its density, which is the
  Fundamental Theorem of Calculus for `cesH`, together with `cesH 1 = 0`.

* **(Boundedness of the density)** `‖cesHd t‖ ≤ π` on `(0,1]` (`cesHd_norm_le`).

* **(Lacunary tail summability)** for `ρ > 1` and `θ ∈ (0,1]` the square sum
  `Σ_i ‖cesH2 (⌊ρ^i⌋ θ)‖²` is summable with a bound *uniform in* `θ`.  This is because `cesH2`
  vanishes for arguments `≤ 1`, so only the lacunary tail `⌊ρ^i⌋ θ > 1` contributes, and there the
  profile decays like `1/(πu)`; this is exactly the `d = 1` profile-replacement error of
  `Submission/Work/BourgainPlan/Oscillation/lacScale_error_tsum_le.lean`.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## The derivative of the profile -/

/-- `c(u) = 2πi u`, the argument of the numerator and denominator of the Cesàro profile. -/
noncomputable def cesC (u : ℝ) : ℂ := 2 * Real.pi * Complex.I * (u : ℂ)

lemma cesC_ne_zero {u : ℝ} (hu : u ≠ 0) : cesC u ≠ 0 := by
  simp only [cesC]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
  · exact_mod_cast Real.pi_ne_zero
  · exact_mod_cast hu

/-- An antiderivative of `s ↦ s · e^{cs}`:  `F(s) = e^{cs}·(s/c - 1/c²)`. -/
private lemma hasDerivAt_antideriv (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (c * (s:ℂ)) * ((s:ℂ) * c⁻¹ - (c^2)⁻¹))
      ((x:ℂ) * Complex.exp (c * (x:ℂ))) x := by
  have hA : HasDerivAt (fun s : ℝ => c * (s:ℂ)) c x := by
    simpa only [mul_one] using! ((hasDerivAt_id (x:ℂ)).const_mul c).comp_ofReal
  have hE : HasDerivAt (fun s : ℝ => Complex.exp (c * (s:ℂ))) (Complex.exp (c*(x:ℂ)) * c) x :=
    (Complex.hasDerivAt_exp (c * (x:ℂ))).comp x hA
  have h1 : HasDerivAt (fun s : ℝ => (s:ℂ)) (1:ℂ) x := by
    simpa only [id_eq] using! (hasDerivAt_id (x:ℂ)).comp_ofReal
  have hB : HasDerivAt (fun s : ℝ => (s:ℂ) * c⁻¹ - (c^2)⁻¹) (c⁻¹) x := by
    simpa only [one_mul] using! (h1.mul_const (c⁻¹)).sub_const ((c^2)⁻¹)
  have hval : (Complex.exp (c*(x:ℂ)) * c) * ((x:ℂ) * c⁻¹ - (c^2)⁻¹) + Complex.exp (c*(x:ℂ)) * c⁻¹
      = (x:ℂ) * Complex.exp (c * (x:ℂ)) := by
    field_simp
    ring
  exact hval ▸ hE.mul hB

/-- `∫_0^1 s e^{cs} ds = e^c (c⁻¹ - (c²)⁻¹) + (c²)⁻¹` for `c ≠ 0`. -/
private lemma integral_smul_exp (c : ℂ) (hc : c ≠ 0) :
    (∫ s in (0:ℝ)..1, (s:ℂ) * Complex.exp (c * (s:ℂ)))
      = Complex.exp c * (c⁻¹ - (c^2)⁻¹) + (c^2)⁻¹ := by
  have hint : IntervalIntegrable (fun s : ℝ => (s:ℂ) * Complex.exp (c * (s:ℂ))) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => (s:ℂ) * Complex.exp (c * (s:ℂ))).intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_antideriv c hc x) hint
  rw [h]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    zero_mul]
  ring

/-- The Stieltjes density evaluated in closed form. -/
lemma cesHd_closed (u : ℝ) (hu : u ≠ 0) :
    cesHd u = 2 * Real.pi * Complex.I *
      (Complex.exp (cesC u) * ((cesC u)⁻¹ - ((cesC u)^2)⁻¹) + ((cesC u)^2)⁻¹) := by
  have hc : cesC u ≠ 0 := cesC_ne_zero hu
  rw [show cesHd u = ∫ s in (0:ℝ)..1,
        (2*Real.pi*Complex.I) * ((s:ℂ) * Complex.exp (cesC u * (s:ℂ))) from by
    rw [cesHd]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [cesC]; ring_nf]
  rw [intervalIntegral.integral_const_mul, integral_smul_exp (cesC u) hc]

/-- `cesHd` is the derivative of the profile at every `x ≠ 0`. -/
lemma cesH_hasDerivAt (x : ℝ) (hx : x ≠ 0) : HasDerivAt cesH (cesHd x) x := by
  have hc : cesC x ≠ 0 := cesC_ne_zero hx
  have hA : HasDerivAt (fun s : ℝ => cesC s) (2 * Real.pi * Complex.I) x := by
    simp only [cesC]
    simpa only [mul_one, mul_assoc] using!
      ((hasDerivAt_id (x:ℂ)).const_mul (2 * Real.pi * Complex.I)).comp_ofReal
  have hq : HasDerivAt (fun s : ℝ => (Complex.exp (cesC s) - 1)/cesC s)
      ((Complex.exp (cesC x) * (2*Real.pi*Complex.I) * cesC x
        - (Complex.exp (cesC x) - 1) * (2*Real.pi*Complex.I))/cesC x^2) x :=
    (((Complex.hasDerivAt_exp (cesC x)).comp x hA).sub_const 1).div hA hc
  rw [cesHd_closed x hx]
  convert hq using 1
  · ext s; simp only [cesH, cesC]
  · field_simp
    ring

/-- The Stieltjes density is continuous. -/
lemma cesHd_continuous : Continuous cesHd := by
  show Continuous (fun u : ℝ => ∫ s in (0:ℝ)..1,
    2 * Real.pi * Complex.I * (s:ℂ) * Complex.exp (2 * Real.pi * Complex.I * (u:ℂ) * (s:ℂ)))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1

/-! ## The Stieltjes representation of `cesH1` -/

/-- **Stieltjes representation.**  For `u > 0`,
`cesH1 u = -∫_0^1 cesHd t · 1_{u ≤ t} dt`, i.e. `cesH u = -∫_u^1 cesHd t dt` on `(0,1]`. -/
lemma cesH1_eq_stieltjes (u : ℝ) (hu : 0 < u) :
    cesH1 u = -∫ t in (0:ℝ)..1, cesHd t * (if u ≤ t then (1:ℂ) else 0) := by
  by_cases hu1 : u ≤ 1
  · have hcesH1 : cesH1 u = cesH u := by rw [cesH1, if_pos hu1]
    rw [hcesH1]
    set f : ℝ → ℂ := fun t => cesHd t * (if u ≤ t then (1:ℂ) else 0) with hf
    have hint_0u : IntervalIntegrable f volume 0 u := by
      refine (IntervalIntegrable.zero (μ := volume) (a := 0) (b := u)).congr_uIoo ?_
      intro x hx
      rw [Set.uIoo_of_le hu.le] at hx
      show (0:ℂ) = f x
      rw [hf]
      simp only
      rw [if_neg (not_le.mpr hx.2), mul_zero]
    have hint_u1 : IntervalIntegrable f volume u 1 := by
      refine (cesHd_continuous.intervalIntegrable u 1).congr_uIoo ?_
      intro x hx
      rw [Set.uIoo_of_le hu1] at hx
      show cesHd x = f x
      rw [hf]
      simp only
      rw [if_pos (le_of_lt hx.1), mul_one]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_0u hint_u1
    have h0u : (∫ t in (0:ℝ)..u, f t) = 0 := by
      have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) u → f t = 0 := by
        rw [MeasureTheory.ae_iff]
        apply measure_mono_null _ (measure_singleton u)
        intro x hx
        have hxmem : x ∈ Set.uIoc (0:ℝ) u := by
          by_contra hc
          exact hx (fun h => absurd h hc)
        have hxf : f x ≠ 0 := by
          intro hc
          exact hx (fun _ => hc)
        simp only [Set.mem_singleton_iff]
        have hxle : x ≤ u := by
          rcases (Set.mem_uIoc.mp hxmem) with ⟨_, h⟩ | ⟨h1, h2⟩
          · exact h
          · linarith [hu, h1, h2]
        by_contra hne
        have h1 : ¬ (u ≤ x) := fun hle => hne (le_antisymm hxle hle)
        rw [hf] at hxf
        simp only at hxf
        exact hxf (by rw [if_neg h1, mul_zero])
      rw [intervalIntegral.integral_congr_ae hae]
      simp
    have hu1' : (∫ t in u..1, f t) = ∫ t in u..1, cesHd t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hu1] at ht
      rw [hf]
      simp only
      rw [if_pos ht.1, mul_one]
    have hftc : (∫ t in u..1, cesHd t) = cesH 1 - cesH u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => cesH_hasDerivAt x (by
          rw [Set.uIcc_of_le hu1] at hx
          exact ne_of_gt (lt_of_lt_of_le hu hx.1)))
        (cesHd_continuous.intervalIntegrable u 1)
    have hgoal : (∫ t in (0:ℝ)..1, f t) = -cesH u := by
      rw [← hsplit, h0u, hu1', hftc, cesH_one]
      ring
    rw [hgoal]
    ring
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have hcesH1 : cesH1 u = 0 := by rw [cesH1, if_neg (not_le.mpr hu1')]
    rw [hcesH1]
    have hzero : (∫ t in (0:ℝ)..1, cesHd t * (if u ≤ t then (1:ℂ) else 0)) = 0 := by
      rw [show (∫ t in (0:ℝ)..1, cesHd t * (if u ≤ t then (1:ℂ) else 0))
            = ∫ _ in (0:ℝ)..1, (0:ℂ) from by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        change cesHd t * (if u ≤ t then (1:ℂ) else 0) = 0
        rw [if_neg (by intro hle; linarith [ht.2, hle, hu1']), mul_zero]]
      simp
    rw [hzero]
    ring

/-! ## The summability of the lacunary tail -/

/-- The pointwise domination of the tail square by the profile-replacement error. -/
lemma cesH2_sq_le (x : ℝ) (hx : 0 < x) :
    ‖cesH2 x‖ ^ 2 ≤ (if x ≤ 1 then x ^ 2 else (x⁻¹) ^ 2) := by
  by_cases h : x ≤ 1
  · rw [if_pos h]
    have hz : cesH2 x = 0 := by rw [cesH2, if_neg (not_lt.mpr h)]
    rw [hz, norm_zero]
    simpa using sq_nonneg x
  · rw [if_neg h]
    have hx1 : 1 < x := lt_of_not_ge h
    have hc : cesH2 x = cesH x := by rw [cesH2, if_pos hx1]
    rw [hc]
    have hb : ‖cesH x‖ ≤ 1 / (Real.pi * x) := cesH_norm_le x hx
    have hpi1 : (1:ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
    have hle' : ‖cesH x‖ ≤ x⁻¹ := by
      calc ‖cesH x‖ ≤ 1 / (Real.pi * x) := hb
        _ ≤ 1 / x := one_div_le_one_div_of_le hx (by nlinarith [hpi1, hx])
        _ = x⁻¹ := one_div x
    exact pow_le_pow_left₀ (norm_nonneg _) hle' 2

/-- The tail square at the lacunary scale is dominated by the `d = 1` profile-replacement error. -/
lemma cesH2_sq_le_lac (ρ : ℝ) (hρ : 1 ≤ ρ) (θ : ℝ) (hθ : 0 < θ) (i : ℕ) :
    ‖cesH2 ((lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤
      (if |θ| * (lacScale ρ i : ℝ) ≤ 1 then (|θ| * (lacScale ρ i : ℝ)) ^ 2
        else ((|θ| * (lacScale ρ i : ℝ)) ^ (-(1 : ℝ))) ^ 2) := by
  have hL : (1:ℝ) ≤ (lacScale ρ i : ℝ) := by
    have := one_le_lacScale ρ hρ i
    exact_mod_cast this
  have hLpos : (0:ℝ) < (lacScale ρ i : ℝ) := lt_of_lt_of_le zero_lt_one hL
  have hx : 0 < (lacScale ρ i : ℝ) * θ := mul_pos hLpos hθ
  have h := cesH2_sq_le ((lacScale ρ i : ℝ) * θ) hx
  rw [abs_of_pos hθ, Real.rpow_neg_one]
  simp only [mul_comm θ]
  exact h

/-! ## The packaged data -/

theorem cesaro_profile_data (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧
      (∀ u : ℝ, 0 < u →
        Work.BourgainPlan.Oscillation.Lacunary.cesH1 u
          = -∫ t in (0:ℝ)..1,
              Work.BourgainPlan.Oscillation.Lacunary.cesHd t * (if u ≤ t then (1:ℂ) else 0)) ∧
      (∀ t ∈ Set.Ioc (0:ℝ) 1, ‖Work.BourgainPlan.Oscillation.Lacunary.cesHd t‖ ≤ M) ∧
      (∀ θ ∈ Set.Ioc (0:ℝ) 1,
        Summable (fun i : ℕ => ‖Work.BourgainPlan.Oscillation.Lacunary.cesH2
            ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
        ∑' i : ℕ, ‖Work.BourgainPlan.Oscillation.Lacunary.cesH2
            ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := lacScale_error_tsum_le ρ hρ 1 le_rfl
  refine ⟨Real.sqrt C, Real.pi, Real.sqrt_pos.mpr hCpos, Real.pi_pos, ?_, ?_, ?_⟩
  · exact cesH1_eq_stieltjes
  · intro t _; exact cesHd_norm_le t
  · intro θ hθ
    obtain ⟨hsumF, hboundF⟩ := hC θ (ne_of_gt hθ.1)
    simp only [Nat.cast_one, div_one, pow_one] at hsumF hboundF
    have hpt : ∀ i : ℕ,
        ‖cesH2 ((lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤
          (if |θ| * (lacScale ρ i : ℝ) ≤ 1 then (|θ| * (lacScale ρ i : ℝ)) ^ 2
            else ((|θ| * (lacScale ρ i : ℝ)) ^ (-(1 : ℝ))) ^ 2) :=
      fun i => cesH2_sq_le_lac ρ hρ.le θ hθ.1 i
    have hsum : Summable (fun i : ℕ => ‖cesH2 ((lacScale ρ i : ℝ) * θ)‖ ^ 2) :=
      hsumF.of_nonneg_of_le (fun i => sq_nonneg _) hpt
    refine ⟨hsum, ?_⟩
    calc ∑' i : ℕ, ‖cesH2 ((lacScale ρ i : ℝ) * θ)‖ ^ 2
        ≤ ∑' i : ℕ, (if |θ| * (lacScale ρ i : ℝ) ≤ 1
            then (|θ| * (lacScale ρ i : ℝ)) ^ 2
            else ((|θ| * (lacScale ρ i : ℝ)) ^ (-(1 : ℝ))) ^ 2) :=
          Summable.tsum_le_tsum hpt hsum hsumF
      _ ≤ C := hboundF
      _ = (Real.sqrt C) ^ 2 := (Real.sq_sqrt hCpos.le).symm

end

end Work.BourgainPlan.Oscillation.Lacunary
