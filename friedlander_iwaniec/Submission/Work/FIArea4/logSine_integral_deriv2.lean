import Mathlib
import Submission.Work.FIArea4.logSine_defs
import Submission.Work.FIArea4.logSine_psi_deriv
import Submission.Work.FIArea4.logSine_tau_bound
import Submission.Work.FIArea4.logSine_psi_global_bound
import Submission.Work.FIArea4.one_sub_cos_ge_two_div_sq
import Submission.Work.FIArea4.logSine_deriv2_base
import Submission.Work.FIArea4.logSine_deriv2_le_general
import Submission.Work.FIArea4.logSine_deriv2_le_regionB

namespace Work.FIArea4

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped ContDiff
open MeasureTheory intervalIntegral

noncomputable section

/-- **Reduction of the integral to `[0, π/2]`.**  `u_N''` is even and satisfies
`u_N''(π - α) = u_N''(α)`, so the integral over `[-π, π]` is `4` times the integral over
`[0, π/2]`. -/
lemma integral_abs_deriv2_eq (N : ℕ) (hN : 1 ≤ N) :
    ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α|
      = 4 * ∫ α in (0:ℝ)..(Real.pi/2), |deriv (deriv (ufun N)) α| := by
  set f : ℝ → ℝ := fun α => |deriv (deriv (ufun N)) α| with hf
  have hcont : Continuous f := (contDiff_deriv2_ufun N hN).continuous.abs
  have heven : ∀ α, f (-α) = f α := by
    intro α; simp only [hf, deriv_deriv_ufun_neg N hN α]
  have hsymm : ∀ α, f (Real.pi - α) = f α := by
    intro α; simp only [hf, deriv_deriv_ufun_pi_sub N hN α]
  have hA : ∫ x in (-Real.pi)..(0:ℝ), f x = ∫ x in (0:ℝ)..Real.pi, f x := by
    have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := (0:ℝ)) f
    rw [show -(0:ℝ) = 0 by ring, neg_neg] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun x _ => (heven x).symm)
  have hD : ∫ x in (Real.pi/2)..Real.pi, f x = ∫ x in (0:ℝ)..(Real.pi/2), f x := by
    have h := intervalIntegral.integral_comp_sub_left (a := Real.pi/2) (b := Real.pi) f Real.pi
    rw [show Real.pi - Real.pi = (0:ℝ) by ring,
        show Real.pi - Real.pi/2 = Real.pi/2 by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun x _ => (hsymm x).symm)
  have hAB := intervalIntegral.integral_add_adjacent_intervals (a := -Real.pi) (b := (0:ℝ))
    (c := Real.pi) (μ := volume) (hcont.intervalIntegrable (μ := volume) _ _)
    (hcont.intervalIntegrable (μ := volume) _ _)
  have hCD := intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := Real.pi/2)
    (c := Real.pi) (μ := volume) (hcont.intervalIntegrable (μ := volume) _ _)
    (hcont.intervalIntegrable (μ := volume) _ _)
  rw [← hAB, hA, ← hCD, hD]
  ring

/-! ### Elementary integral identities -/

/-- `∫_a^b dx/x² = 1/a - 1/b` for `0 < a`, `0 < b`. -/
lemma integral_one_div_sq_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, (1:ℝ)/x^2 = 1/a - 1/b := by
  have h0 : (0:ℝ) ∉ Set.uIcc a b := Set.notMem_uIcc_of_lt ha hb
  rw [show ∫ x in a..b, (1:ℝ)/x^2 = ∫ x in a..b, x^(-2:ℤ) from
    intervalIntegral.integral_congr fun _ _ => by simp [one_div]]
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  rw [show (-2:ℤ) + 1 = -1 by norm_num, zpow_neg_one, zpow_neg_one]
  rw [inv_eq_one_div, inv_eq_one_div]
  ring

/-- `x ↦ 1/x²` is interval integrable on `[a,b]` when `a,b > 0`. -/
lemma intervalIntegrable_one_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (1:ℝ)/x^2) volume a b := by
  have hne : ∀ x ∈ Set.uIcc a b, x ^ 2 ≠ 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha h1))
    · exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hb h1))
  have h := intervalIntegral.intervalIntegrable_inv (μ := volume)
    (f := fun x : ℝ => x^2) hne (continuousOn_id.pow 2)
  simpa [one_div] using h

/-- The integral of the region-`B` majorant `(144/43)(1/x²+1)+1` over `[5/(2N), π/2]`. -/
lemma integral_regionB_majorant (N : ℕ) (hN : 2 ≤ N) :
    ∫ x in (5/(2*(N:ℝ)))..(Real.pi/2), ((144/43)*(1/x^2 + 1) + 1)
      = (144/43)*(5/(2*(N:ℝ)))⁻¹ - (144/43)*(2/Real.pi)
        + (187/43)*(Real.pi/2 - 5/(2*(N:ℝ))) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set a : ℝ := 5/(2*(N:ℝ)) with ha_def
  have ha : 0 < a := by positivity
  have hapi : a ≤ Real.pi/2 := by
    have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
    rw [ha_def, div_le_iff₀ (by positivity)]
    have h1 : (3:ℝ) * 2 ≤ Real.pi * N :=
      mul_le_mul hpi3.le hN2 (by norm_num) (by linarith)
    have h2 : Real.pi/2 * (2*(N:ℝ)) = Real.pi * N := by ring
    rw [h2]; linarith
  have hb : (0:ℝ) < Real.pi/2 := by positivity
  have hI1 : IntervalIntegrable (fun x : ℝ => (1:ℝ)/x^2) volume a (Real.pi/2) :=
    intervalIntegrable_one_div_sq ha hb
  have hI2 : IntervalIntegrable (fun x : ℝ => (1:ℝ)) volume a (Real.pi/2) :=
    continuous_const.intervalIntegrable a (Real.pi/2)
  have hI3 : IntervalIntegrable (fun x : ℝ => (144/43)*(1/x^2 + 1)) volume a (Real.pi/2) :=
    (hI1.add hI2).const_mul (144/43)
  have h1 : ∫ x in a..(Real.pi/2), ((144/43)*(1/x^2 + 1) + 1)
      = (144/43) * (∫ x in a..(Real.pi/2), (1/x^2 + 1)) + ∫ x in a..(Real.pi/2), (1:ℝ) := by
    rw [intervalIntegral.integral_add hI3 hI2, intervalIntegral.integral_const_mul]
  have h2 : ∫ x in a..(Real.pi/2), (1/x^2 + 1)
      = (∫ x in a..(Real.pi/2), (1:ℝ)/x^2) + (Real.pi/2 - a) := by
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1, h2, intervalIntegral.integral_const, smul_eq_mul,
    integral_one_div_sq_pos ha hb]
  ring

/-- Bound for the region-`B` majorant integral: `≤ 288N/215 + (187/43)(π/2)`. -/
lemma integral_regionB_majorant_le (N : ℕ) (hN : 2 ≤ N) :
    ∫ x in (5/(2*(N:ℝ)))..(Real.pi/2), ((144/43)*(1/x^2 + 1) + 1)
      ≤ 288*(N:ℝ)/215 + (187/43)*(Real.pi/2) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [integral_regionB_majorant N hN]
  have hinv : (5/(2*(N:ℝ)))⁻¹ = 2*(N:ℝ)/5 := by field_simp
  rw [hinv]
  have hA : (0:ℝ) < (144:ℝ)/43*(2/Real.pi) := by positivity
  have hB : (0:ℝ) < (187:ℝ)/43*(5/(2*(N:ℝ))) := by positivity
  have hX : (144:ℝ)/43*(2*(N:ℝ)/5) = 288*(N:ℝ)/215 := by ring
  rw [hX]
  nlinarith [hA, hB]

/-- The region-`A` constant majorant integral: `∫_0^{5/(2N)} c = 135 K N (log N + 1) + 5/(2N)`. -/
lemma integral_regionA_const (N : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    ∫ x in (0:ℝ)..(5/(2*(N:ℝ))), (4*K*(N:ℝ)^2*(Real.log N + 1)
        + 8*K*(N:ℝ)^4*(Real.log N + 1)*(5/(2*(N:ℝ)))^2 + 1)
      = 135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring


/-- `IntervalIntegrable` of the region-`B` majorant. -/
lemma intervalIntegrable_regionB_majorant {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (144/43)*(1/x^2 + 1) + 1) volume a b := by
  have hI1 : IntervalIntegrable (fun x : ℝ => (1:ℝ)/x^2) volume a b :=
    intervalIntegrable_one_div_sq ha hb
  have hI2 : IntervalIntegrable (fun x : ℝ => (1:ℝ)) volume a b :=
    continuous_const.intervalIntegrable a b
  exact ((hI1.add hI2).const_mul (144/43)).add hI2

/-! ### The two pointwise bounds, integrated over the two ranges -/

/-- Region `[0, 5/(2N)]`: integrate the (constant) majorant
`4KN²(log N+1) + 8KN⁴(log N+1)(5/(2N))² + 1`. -/
lemma integral_regionA_le {N : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (hbd : ∀ α ∈ Set.Icc (0:ℝ) (5/(2*(N:ℝ))),
        |deriv (deriv (ufun N)) α| ≤ 4*K*(N:ℝ)^2*(Real.log N + 1)
          + 8*K*(N:ℝ)^4*(Real.log N + 1)*(5/(2*(N:ℝ)))^2 + 1) :
    ∫ α in (0:ℝ)..(5/(2*(N:ℝ))), |deriv (deriv (ufun N)) α|
      ≤ 135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have ha0 : (0:ℝ) ≤ 5/(2*(N:ℝ)) := by positivity
  have hcont : Continuous (fun α => |deriv (deriv (ufun N)) α|) :=
    (contDiff_deriv2_ufun N hN1).continuous.abs
  have hmaj : IntervalIntegrable (fun _ : ℝ => 4*K*(N:ℝ)^2*(Real.log N + 1)
      + 8*K*(N:ℝ)^4*(Real.log N + 1)*(5/(2*(N:ℝ)))^2 + 1) volume
      (0:ℝ) (5/(2*(N:ℝ))) := continuous_const.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on ha0
    (hcont.intervalIntegrable (μ := volume) _ _) hmaj hbd
  exact hmono.trans (le_of_eq (integral_regionA_const N hN K))

/-- Region `[5/(2N), π/2]`: integrate the majorant `(144/43)(1/α²+1)+1`. -/
lemma integral_regionB_le {N : ℕ} (hN : 3 ≤ N)
    (hbd : ∀ α ∈ Set.Icc (5/(2*(N:ℝ))) (Real.pi/2),
        |deriv (deriv (ufun N)) α| ≤ (144/43)*(1/α^2 + 1) + 1) :
    ∫ α in (5/(2*(N:ℝ)))..(Real.pi/2), |deriv (deriv (ufun N)) α|
      ≤ 288*(N:ℝ)/215 + (187/43)*(Real.pi/2) := by
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have ha : (0:ℝ) < 5/(2*(N:ℝ)) := by positivity
  have hb : (0:ℝ) < Real.pi/2 := by positivity
  have hab : 5/(2*(N:ℝ)) ≤ Real.pi/2 := by
    have hN2' : (2:ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
    rw [div_le_iff₀ (by positivity)]
    have h1 : (3:ℝ) * 2 ≤ Real.pi * N :=
      mul_le_mul hpi3.le hN2' (by norm_num) (by linarith)
    have h2 : Real.pi/2 * (2*(N:ℝ)) = Real.pi * N := by ring
    rw [h2]; linarith
  have hcont : Continuous (fun α => |deriv (deriv (ufun N)) α|) :=
    (contDiff_deriv2_ufun N hN1).continuous.abs
  have hmaj : IntervalIntegrable (fun x : ℝ => (144/43)*(1/x^2 + 1) + 1) volume
      (5/(2*(N:ℝ))) (Real.pi/2) := intervalIntegrable_regionB_majorant ha hb
  have hmono := intervalIntegral.integral_mono_on hab
    (hcont.intervalIntegrable (μ := volume) _ _) hmaj hbd
  exact hmono.trans (integral_regionB_majorant_le N hN2)

set_option maxHeartbeats 800000 in
/-- **Crude global bound** for `u_N''`: using the global bounds for all four `Ψ` terms. -/
lemma abs_deriv2_ufun_le_crude (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) (α : ℝ) :
    |deriv (deriv (ufun N)) α| ≤ 8*K*(N:ℝ)^2*(Real.log N + 1)
      + 16*K*(N:ℝ)^4*(Real.log N + 1) := by
  obtain ⟨hPsi1, hPsi2⟩ := logSine_psi_global_bound N hN K hK hK1 hK2
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hg0 : 0 ≤ 1 - Real.cos α := by linarith [Real.cos_le_one α]
  have hh0 : 0 ≤ 1 + Real.cos α := by linarith [Real.neg_one_le_cos α]
  have hB : |deriv (Psi N) (1 - Real.cos α)| ≤ 4*K*(N:ℝ)^2*(Real.log N + 1) :=
    hPsi1 _ hg0
  have hA : |deriv (Psi N) (1 + Real.cos α)| ≤ 4*K*(N:ℝ)^2*(Real.log N + 1) :=
    hPsi1 _ hh0
  have hC : |deriv (deriv (Psi N)) (1 - Real.cos α)| ≤ 8*K*(N:ℝ)^4*(Real.log N + 1) :=
    hPsi2 _ hg0
  have hD : |deriv (deriv (Psi N)) (1 + Real.cos α)| ≤ 8*K*(N:ℝ)^4*(Real.log N + 1) :=
    hPsi2 _ hh0
  have hcos : |Real.cos α| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos α, Real.cos_le_one α⟩
  have hsinn : 0 ≤ Real.sin α ^ 2 := sq_nonneg _
  have hsin1 : Real.sin α ^ 2 ≤ 1 := Real.sin_sq_le_one α
  rw [deriv_deriv_ufun_eq N hN1]
  have hX : |Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))|
      ≤ 8*K*(N:ℝ)^2*(Real.log N + 1) := by
    rw [abs_mul]
    have h1 : |deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)|
        ≤ |deriv (Psi N) (1 + Real.cos α)| + |deriv (Psi N) (1 - Real.cos α)| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (deriv (Psi N) (1 + Real.cos α))
        (-(deriv (Psi N) (1 - Real.cos α)))
    calc |Real.cos α| * |deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)|
        ≤ 1 * (|deriv (Psi N) (1 + Real.cos α)| + |deriv (Psi N) (1 - Real.cos α)|) :=
          mul_le_mul hcos h1 (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (4*K*(N:ℝ)^2*(Real.log N + 1) + 4*K*(N:ℝ)^2*(Real.log N + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hA, hB]
      _ = 8*K*(N:ℝ)^2*(Real.log N + 1) := by ring
  have hY : |Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
        + deriv (deriv (Psi N)) (1 + Real.cos α))| ≤ 16*K*(N:ℝ)^4*(Real.log N + 1) := by
    rw [abs_mul, abs_of_nonneg hsinn]
    have h1 : |deriv (deriv (Psi N)) (1 - Real.cos α) + deriv (deriv (Psi N)) (1 + Real.cos α)|
        ≤ |deriv (deriv (Psi N)) (1 - Real.cos α)| + |deriv (deriv (Psi N)) (1 + Real.cos α)| :=
      abs_add_le _ _
    calc Real.sin α ^ 2 * |deriv (deriv (Psi N)) (1 - Real.cos α)
          + deriv (deriv (Psi N)) (1 + Real.cos α)|
        ≤ 1 * (|deriv (deriv (Psi N)) (1 - Real.cos α)|
            + |deriv (deriv (Psi N)) (1 + Real.cos α)|) :=
          mul_le_mul hsin1 h1 (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (8*K*(N:ℝ)^4*(Real.log N + 1) + 8*K*(N:ℝ)^4*(Real.log N + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hC, hD]
      _ = 16*K*(N:ℝ)^4*(Real.log N + 1) := by ring
  have hsub : |Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))
        - Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
            + deriv (deriv (Psi N)) (1 + Real.cos α))|
      ≤ |Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))|
        + |Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
            + deriv (deriv (Psi N)) (1 + Real.cos α))| := by
    rw [sub_eq_add_neg]
    simpa only [abs_neg] using abs_add_le
      (Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)))
      (-(Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
          + deriv (deriv (Psi N)) (1 + Real.cos α))))
  linarith [hsub, hX, hY]

/-- **`L¹` bound for `u_N''(α)`.**  `u_N = ufun N = -Ψ_N(1-cos α) - Ψ_N(1+cos α) + 2 log 2`
(`Work.FIArea4.logSine_defs`), and the claim is `∫_{-π}^{π} |u_N''(α)| dα ≪ N log N`. -/
theorem logSine_integral_deriv2 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α| ≤ C * (N:ℝ) * Real.log N := by
  obtain ⟨⟨K₀, hK₀pos, hK₀⟩, _, _⟩ := logSine_tau_bound
  set K : ℝ := max K₀ 1 with hKdef
  have hKge : 1 ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hKge
  have hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K :=
    fun x => le_trans (hK₀ x).1 (le_max_left _ _)
  have hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K :=
    fun x => le_trans (hK₀ x).2 (le_max_left _ _)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C1 : ℝ := 135*K*(1 + 1/Real.log 3) + (5/6)/(3*Real.log 3) + (288/215)/Real.log 3
      + ((187/43)*(Real.pi/2))/(3*Real.log 3) with hC1def
  set C2 : ℝ := 576*Real.pi*K*(Real.log 2 + 1)/Real.log 2 with hC2def
  set C : ℝ := 4*C1 + C2 + 1 with hCdef
  have hC1pos : 0 < C1 := by rw [hC1def]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2def]; positivity
  refine ⟨C, by rw [hCdef]; linarith, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  by_cases hN3 : 3 ≤ N
  · have hN3' : (3:ℝ) ≤ N := by exact_mod_cast hN3
    have hNpos : (0:ℝ) < N := by linarith
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hlogNge : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hN3'
    have hNlog : 3 * Real.log 3 ≤ (N:ℝ) * Real.log N := by
      have h := mul_le_mul hN3' hlogNge (le_of_lt hlog3) (by positivity)
      simpa [mul_comm] using h
    have hapi : 5/(2*(N:ℝ)) ≤ Real.pi/2 := by
      have hN2' : (2:ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
      have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
      rw [div_le_iff₀ (by positivity)]
      have h1 : (3:ℝ) * 2 ≤ Real.pi * N := mul_le_mul hpi3.le hN2' (by norm_num) (by linarith)
      have h2 : Real.pi/2 * (2*(N:ℝ)) = Real.pi * N := by ring
      rw [h2]; linarith
    -- pointwise bounds
    have hbdA : ∀ α ∈ Set.Icc (0:ℝ) (5/(2*(N:ℝ))),
        |deriv (deriv (ufun N)) α| ≤ 4*K*(N:ℝ)^2*(Real.log N + 1)
          + 8*K*(N:ℝ)^4*(Real.log N + 1)*(5/(2*(N:ℝ)))^2 + 1 := by
      intro α hα
      rw [Set.mem_Icc] at hα
      have hgen := logSine_deriv2_le_general N hN K hKge hK1 hK2 hα.1
        (le_trans hα.2 hapi)
      have hα2 : α^2 ≤ (5/(2*(N:ℝ)))^2 := by nlinarith [hα.1, hα.2]
      have hcoef : (0:ℝ) ≤ 8*K*(N:ℝ)^4*(Real.log N + 1) := by
        have : (0:ℝ) < Real.log N + 1 := by linarith
        positivity
      have := mul_le_mul_of_nonneg_left hα2 hcoef
      linarith [hgen, this]
    have hbdB : ∀ α ∈ Set.Icc (5/(2*(N:ℝ))) (Real.pi/2),
        |deriv (deriv (ufun N)) α| ≤ (144/43)*(1/α^2 + 1) + 1 := by
      intro α hα
      rw [Set.mem_Icc] at hα
      exact logSine_deriv2_le_regionB N hN3 K hKge hK1 hK2 hα.1 hα.2
    have hA := integral_regionA_le hN K hbdA
    have hB := integral_regionB_le hN3 hbdB
    have hcont : Continuous (fun α => |deriv (deriv (ufun N)) α|) :=
      (contDiff_deriv2_ufun N hN1).continuous.abs
    have hsplit : ∫ α in (0:ℝ)..(Real.pi/2), |deriv (deriv (ufun N)) α|
        = (∫ α in (0:ℝ)..(5/(2*(N:ℝ))), |deriv (deriv (ufun N)) α|)
          + (∫ α in (5/(2*(N:ℝ)))..(Real.pi/2), |deriv (deriv (ufun N)) α|) :=
      (intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := 5/(2*(N:ℝ)))
        (c := Real.pi/2) (μ := volume) (hcont.intervalIntegrable (μ := volume) _ _)
        (hcont.intervalIntegrable (μ := volume) _ _)).symm
    have hsum2 : (∫ α in (0:ℝ)..(5/(2*(N:ℝ))), |deriv (deriv (ufun N)) α|)
        + (∫ α in (5/(2*(N:ℝ)))..(Real.pi/2), |deriv (deriv (ufun N)) α|)
        ≤ 135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) + 288*(N:ℝ)/215
          + (187/43)*(Real.pi/2) := by linarith [hA, hB]
    rw [integral_abs_deriv2_eq N hN1, hsplit]
    have harith : 4*(135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) + 288*(N:ℝ)/215
        + (187/43)*(Real.pi/2)) ≤ C * (N:ℝ) * Real.log N := by
      set X : ℝ := (N:ℝ) * Real.log N with hXdef
      have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hNpos hlogN
      have h1 : Real.log N + 1 ≤ Real.log N * (1 + 1/Real.log 3) := by
        have hlt : (1:ℝ) ≤ Real.log N / Real.log 3 := by rw [le_div_iff₀ hlog3]; linarith
        have hc : (1:ℝ) ≤ Real.log N * (1/Real.log 3) := by
          simpa [one_div, div_eq_mul_inv] using hlt
        rw [mul_add, mul_one]; linarith
      have t1 : 4 * (135*K*(N:ℝ)*(Real.log N + 1))
          ≤ 4*(135*K*(1 + 1/Real.log 3)) * X := by
        have hh := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4*135*K*(N:ℝ))
        rw [hXdef]; nlinarith [hh]
      have t2 : 4 * (5/(2*(N:ℝ))) ≤ 4*((5/6)/(3*Real.log 3)) * X := by
        have h53 : 5/(2*(N:ℝ)) ≤ (5:ℝ)/6 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith [hN3']
        have h56 : (5:ℝ)/6 ≤ (5/6)/(3*Real.log 3) * X := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 3*Real.log 3), hXdef]
          nlinarith [hNlog]
        nlinarith [h53, h56]
      have t3 : 4 * (288*(N:ℝ)/215) ≤ 4*((288/215)/Real.log 3) * X := by
        have hNle : (N:ℝ) ≤ X / Real.log 3 := by
          rw [hXdef, le_div_iff₀ hlog3]; nlinarith [hlogNge, hNpos]
        have hre : 4*((288/215)/Real.log 3) * X = (1152/215) * (X/Real.log 3) := by ring
        rw [hre]; nlinarith [hNle]
      have t4 : 4 * ((187/43)*(Real.pi/2))
          ≤ 4*(((187/43)*(Real.pi/2))/(3*Real.log 3)) * X := by
        have hX1 : (1:ℝ) ≤ X/(3*Real.log 3) := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 3*Real.log 3), hXdef]; linarith [hNlog]
        have hre : 4*(((187/43)*(Real.pi/2))/(3*Real.log 3)) * X
            = 4*((187/43)*(Real.pi/2)) * (X/(3*Real.log 3)) := by ring
        rw [hre]
        have hpos : (0:ℝ) ≤ 4*((187/43)*(Real.pi/2)) := by positivity
        nlinarith [hX1, hpos]
      have hsum := add_le_add (add_le_add (add_le_add t1 t2) t3) t4
      have hL : 4*(135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) + 288*(N:ℝ)/215
          + (187/43)*(Real.pi/2))
          = 4 * (135*K*(N:ℝ)*(Real.log N + 1)) + 4*(5/(2*(N:ℝ))) + 4*(288*(N:ℝ)/215)
            + 4*((187/43)*(Real.pi/2)) := by ring
      have hR : 4*(135*K*(1 + 1/Real.log 3)) * X + 4*((5/6)/(3*Real.log 3)) * X
          + 4*((288/215)/Real.log 3) * X + 4*(((187/43)*(Real.pi/2))/(3*Real.log 3)) * X
          = 4*C1 * X := by rw [hC1def]; ring
      have hmid : 4*(135*K*(N:ℝ)*(Real.log N + 1) + 5/(2*(N:ℝ)) + 288*(N:ℝ)/215
          + (187/43)*(Real.pi/2)) ≤ 4*C1 * X := by linarith [hL, hsum, hR]
      have hCX : 4*C1 * X ≤ C * (N:ℝ) * Real.log N := by
        have hCX' : 4*C1 * X ≤ (4*C1 + C2 + 1) * X :=
          mul_le_mul_of_nonneg_right (by linarith [hC2nn]) (le_of_lt hXpos)
        rw [hCdef]
        rw [hXdef] at hCX'
        linarith [hCX']
      linarith [hmid, hCX]
    linarith [hsum2, harith]
  · -- N = 2
    have hN2 : N = 2 := by omega
    subst hN2
    have hcont : Continuous (fun α => |deriv (deriv (ufun 2)) α|) :=
      (contDiff_deriv2_ufun 2 (by norm_num)).continuous.abs
    have hbd : ∀ α ∈ Set.Icc (-Real.pi) Real.pi,
        |deriv (deriv (ufun 2)) α| ≤ 8*K*(2:ℝ)^2*(Real.log 2 + 1)
          + 16*K*(2:ℝ)^4*(Real.log 2 + 1) :=
      fun α _ => abs_deriv2_ufun_le_crude 2 (by norm_num) K hKge hK1 hK2 α
    have hmono := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (hcont.intervalIntegrable (μ := volume) _ _)
      (continuous_const.intervalIntegrable _ _) hbd
    have hconst : ∫ α in (-Real.pi)..Real.pi, (8*K*(2:ℝ)^2*(Real.log 2 + 1)
          + 16*K*(2:ℝ)^4*(Real.log 2 + 1))
        = (Real.pi - (-Real.pi)) * (8*K*(2:ℝ)^2*(Real.log 2 + 1)
            + 16*K*(2:ℝ)^4*(Real.log 2 + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have hbound : ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun 2)) α|
        ≤ 576*Real.pi*K*(Real.log 2 + 1) := by
      refine hmono.trans ?_
      rw [hconst, show Real.pi - (-Real.pi) = 2*Real.pi by ring]
      nlinarith [Real.pi_pos, hKpos]
    have hZnn : (0:ℝ) ≤ 576*Real.pi*K*(Real.log 2 + 1) := by
      have h1 : (0:ℝ) < Real.log 2 + 1 := by linarith
      positivity
    have hkey : 576*Real.pi*K*(Real.log 2 + 1) ≤ C * (2:ℝ) * Real.log 2 := by
      have hC2le : C2 ≤ C := by rw [hCdef]; linarith [hC1pos, hC2nn]
      have h1 : C2 * (2*Real.log 2) ≤ C * (2*Real.log 2) :=
        mul_le_mul_of_nonneg_right hC2le (by positivity)
      have h2 : C2 * (2*Real.log 2) = 2 * (576*Real.pi*K*(Real.log 2 + 1)) := by
        rw [hC2def]; field_simp
      nlinarith [h1, h2, hZnn]
    exact le_trans hbound hkey

end

end Work.FIArea4
