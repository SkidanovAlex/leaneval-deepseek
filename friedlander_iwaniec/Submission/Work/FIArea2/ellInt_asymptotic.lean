import Mathlib
import Submission.Work.FIArea2.sinhIntegral_asymptotic

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

/-! ## Auxiliary rpow algebra -/

lemma rp_half_helper (E : ℝ) (hE : 0 < E) :
    2*E*E^(-(1:ℝ)/2)*(4*E)^(-(1:ℝ)/2) = 1 := by
  have h4 : (4:ℝ)^(-(1:ℝ)/2) = 1/2 := by
    rw [show (-(1:ℝ)/2) = -(1/2) by norm_num]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4) (1/2), ← Real.sqrt_eq_rpow]
    norm_num
  have hsq : E^(-(1:ℝ)/2) * E^(-(1:ℝ)/2) = E⁻¹ := by
    rw [show (-(1:ℝ)/2) = -(1/2) by norm_num]
    rw [← Real.rpow_add (hE) (-(1/2)) (-(1/2))]
    norm_num
    exact Real.rpow_neg_one E
  calc 2*E*E^(-(1:ℝ)/2)*(4*E)^(-(1:ℝ)/2)
      = 2*E*(4*E)^(-(1:ℝ)/2)*E^(-(1:ℝ)/2) := by ring
    _ = 2*E*((4:ℝ)^(-(1:ℝ)/2)*E^(-(1:ℝ)/2))*E^(-(1:ℝ)/2) := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (le_of_lt hE)]
    _ = 2*E*((1/2)*E^(-(1:ℝ)/2))*E^(-(1:ℝ)/2) := by rw [h4]
    _ = 2*E*(1/2)*(E^(-(1:ℝ)/2)*E^(-(1:ℝ)/2)) := by ring
    _ = 2*E*(1/2)*E⁻¹ := by rw [hsq]
    _ = 1 := by field_simp

lemma rp_half_helper2 (E G : ℝ) (hE : 0 < E) (_hG : 0 < G) :
    2*E * (((4*E)^(-(1:ℝ)/2) * G^(-(1:ℝ)/2)) * E^(-(1:ℝ)/2)) = G^(-(1:ℝ)/2) := by
  rw [show 2*E * (((4*E)^(-(1:ℝ)/2) * G^(-(1:ℝ)/2)) * E^(-(1:ℝ)/2))
        = (2*E*E^(-(1:ℝ)/2)*(4*E)^(-(1:ℝ)/2))*G^(-(1:ℝ)/2) from by ring]
  rw [rp_half_helper E hE, one_mul]

lemma ellInt_key (γ : ℝ) (hγ : γ < 1) (x : ℝ) :
    |2*Real.exp (2*x)| * (((Real.exp (2*x))^2 - 2*γ*Real.exp (2*x) + 1)^(-(1:ℝ)/2) * (Real.exp (2*x))^(-(1:ℝ)/2))
      = (((1-γ)/2) + (Real.sinh x)^2)^(-(1:ℝ)/2) := by
  have hE : 0 < Real.exp (2*x) := Real.exp_pos _
  have hcp : 0 < ((1-γ)/2) + (Real.sinh x)^2 := by
    have : 0 < (1-γ)/2 := by linarith
    nlinarith [sq_nonneg (Real.sinh x)]
  rw [abs_of_pos (by positivity : (0:ℝ) < 2*Real.exp (2*x))]
  have hbase : (Real.exp (2*x))^2 - 2*γ*Real.exp (2*x) + 1 = 4*Real.exp (2*x)*(((1-γ)/2) + (Real.sinh x)^2) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (2*x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
    rw [h1, h2]
    have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
    field_simp
    ring
  rw [hbase]
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ 4*Real.exp (2*x)) (le_of_lt hcp)]
  exact rp_half_helper2 (Real.exp (2*x)) (((1-γ)/2) + (Real.sinh x)^2) hE hcp

/-- The original elliptic integral, written on the positive half-line, equals twice the
`sinh`-integral: `t = exp(2v)` turns it into `∫_ℝ (c + sinh²v)^{-1/2}` with `c = (1-γ)/2`. -/
theorem ellInt_eq_sinhIntegral (γ : ℝ) (hγ : γ < 1) :
    (∫ t in Set.Ioi 0, (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
      = 2 * (∫ v in Set.Ioi 0, (((1 - γ) / 2) + (Real.sinh v) ^ 2) ^ (-(1 : ℝ) / 2)) := by
  have himg : (fun v : ℝ => Real.exp (2*v)) '' Set.univ = Set.Ioi 0 := by
    rw [Set.image_univ]
    rw [show (Set.range fun v : ℝ => Real.exp (2*v)) = Set.range Real.exp from by
      ext y; constructor
      · rintro ⟨v, rfl⟩; exact ⟨2*v, rfl⟩
      · rintro ⟨u, rfl⟩; exact ⟨u/2, by ring_nf⟩]
    exact Real.range_exp
  have hcv : (∫ x in (fun v : ℝ => Real.exp (2*v)) '' Set.univ, (x ^ 2 - 2*γ*x + 1) ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2))
      = ∫ x in Set.univ, |2*Real.exp (2*x)| * (((Real.exp (2*x))^2 - 2*γ*Real.exp (2*x) + 1)^(-(1:ℝ)/2) * (Real.exp (2*x))^(-(1:ℝ)/2)) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
        (f := fun v => Real.exp (2*v)) (f' := fun v => 2*Real.exp (2*v)) MeasurableSet.univ
        (fun v _ => (by
          have h := (Real.hasDerivAt_exp (2*v)).comp v (hasDerivAt_const_mul (x := v) 2)
          have h2 : Real.exp (2*v) * 2 = 2 * Real.exp (2*v) := by ring
          rw [← h2]; exact h.hasDerivWithinAt))
        (fun a _ b _ h => by
          have h' : 2*a = 2*b := Real.exp_injective h
          linarith)
        (fun x => (x ^ 2 - 2*γ*x + 1) ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2))
  rw [himg] at hcv
  rw [hcv]
  rw [MeasureTheory.setIntegral_univ]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ellInt_key γ hγ x))]
  rw [← integral_comp_abs (f := fun x => (((1-γ)/2) + (Real.sinh x)^2)^(-(1:ℝ)/2))]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  show (((1-γ)/2) + (Real.sinh x)^2)^(-(1:ℝ)/2) = (((1-γ)/2) + (Real.sinh (|x|))^2)^(-(1:ℝ)/2)
  rcases lt_or_ge x 0 with hx | hx
  · rw [abs_of_neg hx, Real.sinh_neg]; ring_nf
  · rw [abs_of_nonneg hx]

/-- The elliptic-integral asymptotics of FI §7, eq. (7.9), with the leading constant corrected.
For `γ → 1⁻`, writing `δ² = 1 - γ²`,

  `∫₀^∞ (t² - 2γt + 1)^{-1/2} t^{-1/2} dt = log(64/δ²) + O(δ² log(64/δ²))`.

(The paper prints `log 4δ^{-2}`, off by the additive `log 16`; that constant is exactly what fixes
the leading coefficient of the main term, so we state the correct value.  Only `γ ∈ [1/2,1)` is
needed.)  Route: `t = tan θ` gives `∫₀^{π/2} dθ/√((1-γ sin2θ) sinθcosθ)`; alternatively
`t = e^{2u}` and `s = sinh(u/2)` give `2K(√((1+γ)/2))` with `K` the complete elliptic integral of
the first kind, whose asymptotics give the claim.  A route avoiding elliptic functions: split
`∫₀^1 + ∫_1^∞` and use `t²-2γt+1 = (t-1)² + 2(1-γ)t`. -/
theorem ellInt_asymptotic (γ : ℝ) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    |(∫ t in Set.Ioi 0, (t ^ 2 - 2 * γ * t + 1) ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 2))
        - Real.log (64 / (1 - γ ^ 2))| ≤ 64 * (1 - γ ^ 2) * Real.log (64 / (1 - γ ^ 2)) := by
  rw [ellInt_eq_sinhIntegral γ hγ1]
  set c : ℝ := (1-γ)/2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hc14 : c ≤ 1/4 := by rw [hcdef]; linarith
  set S : ℝ := (∫ v in Set.Ioi 0, (c + (Real.sinh v)^2)^(-(1:ℝ)/2)) with hSdef
  have hcore' : |2*S - Real.log (16/c)| ≤ 8*c*Real.log (1/c)+8*c :=
    sinhIntegral_asymptotic c hc hc14
  have hc1 : (0:ℝ) < 1-c := by linarith
  have hd : (0:ℝ) < 1 - γ^2 := by nlinarith
  have hcnz : c ≠ 0 := ne_of_gt hc
  have h1cnz : (1-c) ≠ 0 := ne_of_gt hc1
  have hdelta : 1 - γ^2 = 4*c*(1-c) := by rw [hcdef]; ring
  have hlog : Real.log (64/(1-γ^2)) = Real.log (16/c) - Real.log (1-c) := by
    have h4 : (64:ℝ)/(1-γ^2) = (16/c)/(1-c) := by rw [hdelta]; field_simp; ring
    rw [h4, Real.log_div (div_ne_zero (by norm_num) hcnz) h1cnz]
  have hb1 : |2*S - Real.log (64/(1-γ^2))| ≤ |2*S - Real.log (16/c)| + |Real.log (1-c)| := by
    rw [hlog]
    have hh : 2*S - (Real.log (16/c) - Real.log (1-c)) = (2*S - Real.log (16/c)) + Real.log (1-c) := by ring
    rw [hh]; exact abs_add_le _ _
  have hlogm : |Real.log (1-c)| ≤ (4/3)*c := by
    rw [abs_of_nonpos (Real.log_nonpos (le_of_lt hc1) (by linarith))]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hc1)
    rw [Real.log_inv] at h
    have hsub : (1-c)⁻¹ - 1 = c/(1-c) := by field_simp; ring
    rw [hsub] at h
    have hc4' : c/(1-c) ≤ (4/3)*c := by rw [div_le_iff₀ hc1]; nlinarith
    linarith
  have hL1 : 1 ≤ Real.log (1/c) := by
    have h4c : (4:ℝ) ≤ 1/c := by rw [le_div_iff₀ hc]; linarith
    calc (1:ℝ) ≤ Real.log 4 := by
            rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
            linarith [Real.exp_one_lt_three]
        _ ≤ Real.log (1/c) := Real.log_le_log (by norm_num) h4c
  have hL0 : 0 ≤ Real.log (1/c) := le_trans zero_le_one hL1
  have hfin : 8*c*Real.log (1/c) + 8*c + (4/3)*c ≤ 192*c*Real.log (1/c) := by
    have hLc : (184:ℝ)*c*1 ≤ 184*c*Real.log (1/c) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    nlinarith [hLc, hc]
  have hkey : (192:ℝ)*c*Real.log (1/c) ≤ 64*(1-γ^2)*Real.log (64/(1-γ^2)) := by
    have hcoef : (192:ℝ)*c ≤ 64*(1-γ^2) := by rw [hdelta]; nlinarith
    have harg : (1:ℝ)/c ≤ 64/(1-γ^2) := by
      rw [div_le_iff₀ hc, div_mul_eq_mul_div, le_div_iff₀ hd, one_mul, hdelta]
      nlinarith
    have hlogarg : Real.log (1/c) ≤ Real.log (64/(1-γ^2)) :=
      Real.log_le_log (by positivity) harg
    calc (192:ℝ)*c*Real.log (1/c) ≤ (64*(1-γ^2))*Real.log (1/c) :=
            mul_le_mul_of_nonneg_right hcoef hL0
      _ ≤ (64*(1-γ^2))*Real.log (64/(1-γ^2)) :=
            mul_le_mul_of_nonneg_left hlogarg (by linarith)
  calc |2*S - Real.log (64/(1-γ^2))|
      ≤ |2*S - Real.log (16/c)| + |Real.log (1-c)| := hb1
    _ ≤ (8*c*Real.log (1/c)+8*c) + (4/3)*c := by linarith [hcore', hlogm]
    _ ≤ 64*(1-γ^2)*Real.log (64/(1-γ^2)) := by linarith [hfin, hkey]

end

end Work.FIArea2
