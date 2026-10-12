import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open Real Complex

noncomputable section

lemma summable_exp_neg_mul_sq_nat {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  have hbase : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg : Summable fun n : ℕ => (Real.exp (-c))^n :=
    summable_geometric_of_lt_one (le_of_lt (Real.exp_pos (-c))) hbase
  refine hg.of_nonneg_of_le (fun n => le_of_lt (Real.exp_pos _)) (fun n => ?_)
  have hn : (n:ℝ) ≤ (n:ℝ)^2 := by
    rcases Nat.eq_zero_or_pos n with h|h
    · simp [h]
    · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
      nlinarith
  have hle : -c * (n:ℝ)^2 ≤ -c * (n:ℝ) := mul_le_mul_of_nonpos_left hn (by linarith)
  calc Real.exp (-c * (n:ℝ)^2) ≤ Real.exp (-c * (n:ℝ)) := Real.exp_le_exp.mpr hle
    _ = (Real.exp (-c))^n := by rw [mul_comm, Real.exp_nat_mul]

lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨summable_exp_neg_mul_sq_nat hc,
    by simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using summable_exp_neg_mul_sq_nat hc⟩

lemma summable_theta_shift {a c : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ =>
      cexp ((( -(Real.pi*(n:ℝ))^2/a : ℝ) : ℂ)) * cexp (2*Real.pi*I*(n:ℂ)*(c:ℂ))) := by
  apply Summable.of_norm_bounded (g := fun n : ℤ => Real.exp (-(Real.pi^2/a) * (n:ℝ)^2))
  · exact summable_exp_neg_mul_sq_int (by positivity)
  · intro n
    have hW : (2*Real.pi*I*(n:ℂ)*(c:ℂ)) = (((2*Real.pi*(n:ℝ)*c : ℝ)) : ℂ) * I := by
      push_cast
      ring
    have hexp : (↑(-(Real.pi*(n:ℝ))^2/a) : ℂ).re = -(Real.pi^2/a)*(n:ℝ)^2 := by
      rw [Complex.ofReal_re]
      ring_nf
    have hexp2 : (2*Real.pi*I*(n:ℂ)*(c:ℂ)).re = 0 := by
      rw [hW, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp, hexp, hexp2]
    simp

theorem theta_shift_real {a c : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-(a * ((n : ℝ) + c) ^ 2)))
      = Real.sqrt (Real.pi / a) *
        (∑' n : ℤ, Real.exp (-((Real.pi * (n : ℝ)) ^ 2) / a)
          * Real.cos (2 * Real.pi * (n : ℝ) * c)) := by
  set L : ℝ := ∑' n : ℤ, Real.exp (-(a * ((n : ℝ) + c) ^ 2)) with hLdef
  set R : ℝ := ∑' n : ℤ, Real.exp (-((Real.pi * (n : ℝ)) ^ 2) / a)
      * Real.cos (2 * Real.pi * (n : ℝ) * c) with hRdef
  set T : ℂ := ∑' n : ℤ, cexp (-(a:ℂ) * ((n:ℂ) + (c:ℂ))^2) with hTdef
  set U : ℂ := ∑' n : ℤ, cexp ((( -(Real.pi*(n:ℝ))^2/a : ℝ) : ℂ))
      * cexp (2*Real.pi*I*(n:ℂ)*(c:ℂ)) with hUdef
  set A : ℂ := ((a / Real.pi : ℝ) : ℂ) with hAdef
  set B : ℂ := ((-(a * c) / Real.pi : ℝ) : ℂ) with hBdef
  have hAre : 0 < A.re := by rw [hAdef]; simp only [ofReal_re]; positivity
  have hq := Complex.tsum_exp_neg_quadratic hAre B
  -- Termwise identities
  have h1 : ∀ n : ℤ, cexp (-(Real.pi:ℂ) * A * (n:ℂ)^2 + 2*(Real.pi:ℂ)*B*(n:ℂ))
      = ((Real.exp (a*c^2) : ℝ) : ℂ) * cexp (-(a:ℂ)*((n:ℂ)+(c:ℂ))^2) := by
    intro n
    rw [hAdef, hBdef, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have h2 : ∀ n : ℤ, cexp (-(Real.pi:ℂ)/A * ((n:ℂ) + Complex.I*B)^2)
      = ((Real.exp (a*c^2):ℝ):ℂ)
        * (cexp ((( -(Real.pi*(n:ℝ))^2/a : ℝ) : ℂ)) * cexp (2*Real.pi*I*(n:ℂ)*(c:ℂ))) := by
    intro n
    have ha' : (a:ℂ) ≠ 0 := by simp [ne_of_gt ha]
    rw [hAdef, hBdef, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hL : (∑' n : ℤ, cexp (-(Real.pi:ℂ) * A * (n:ℂ)^2 + 2*(Real.pi:ℂ)*B*(n:ℂ)))
      = ((Real.exp (a*c^2):ℝ):ℂ) * T := by
    rw [tsum_congr h1, tsum_mul_left, hTdef]
  have hR : (∑' n : ℤ, cexp (-(Real.pi:ℂ)/A * ((n:ℂ) + Complex.I*B)^2))
      = ((Real.exp (a*c^2):ℝ):ℂ) * U := by
    rw [tsum_congr h2, tsum_mul_left, hUdef]
  have hcoef : (1:ℂ) / A^(1/2:ℂ) = ((Real.sqrt (Real.pi/a) : ℝ):ℂ) := by
    rw [hAdef]
    have hcpow : (((a/Real.pi:ℝ):ℂ))^(1/2:ℂ) = (((a/Real.pi)^(1/2:ℝ) : ℝ):ℂ) := by
      rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
          ← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ a/Real.pi) (1/2)]
    rw [hcpow]
    rw [show (1:ℂ) = ((1:ℝ):ℂ) by simp, ← Complex.ofReal_div]
    congr 1
    rw [Real.sqrt_eq_rpow]
    rw [show Real.pi/a = (a/Real.pi)⁻¹ by rw [inv_div]]
    rw [Real.inv_rpow (by positivity : (0:ℝ) ≤ a/Real.pi)]
    rw [one_div]
  have hCT : ((Real.exp (a*c^2):ℝ):ℂ) * T
      = ((Real.sqrt (Real.pi/a):ℝ):ℂ) * (((Real.exp (a*c^2):ℝ):ℂ) * U) := by
    rw [hL, hR, hcoef] at hq
    exact hq
  have hCne : ((Real.exp (a*c^2):ℝ):ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact Real.exp_ne_zero _
  have hTU : T = ((Real.sqrt (Real.pi/a):ℝ):ℂ) * U := by
    have h := hCT
    rw [← mul_assoc ((Real.sqrt (Real.pi/a):ℝ):ℂ) ((Real.exp (a*c^2):ℝ):ℂ) U] at h
    rw [mul_comm ((Real.sqrt (Real.pi/a):ℝ):ℂ) ((Real.exp (a*c^2):ℝ):ℂ)] at h
    rw [mul_assoc] at h
    exact mul_left_cancel₀ hCne h
  have hTL : (∑' n : ℤ, (Real.exp (-(a * ((n : ℝ) + c) ^ 2)) : ℂ)) = T := by
    rw [hTdef]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hUsum : Summable (fun n : ℤ => cexp ((( -(Real.pi*(n:ℝ))^2/a : ℝ) : ℂ))
      * cexp (2*Real.pi*I*(n:ℂ)*(c:ℂ))) := summable_theta_shift ha
  have hre : ∀ n : ℤ, (cexp ((( -(Real.pi*(n:ℝ))^2/a : ℝ) : ℂ))
      * cexp (2*Real.pi*I*(n:ℂ)*(c:ℂ))).re
      = Real.exp (-((Real.pi*(n:ℝ))^2)/a) * Real.cos (2*Real.pi*(n:ℝ)*c) := by
    intro n
    rw [← Complex.ofReal_exp]
    rw [show (2*Real.pi*I*(n:ℂ)*(c:ℂ)) = ((2*Real.pi*(n:ℝ)*c : ℝ):ℂ) * I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    rw [Complex.re_ofReal_mul]
    congr 1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hUR : U.re = R := by
    rw [hUdef, Complex.re_tsum hUsum]
    exact tsum_congr hre
  have hmain : (L : ℂ) = ((Real.sqrt (Real.pi/a):ℝ):ℂ) * U := by
    rw [hLdef, Complex.ofReal_tsum]
    rw [hTL, hTU]
  have hre2 := congrArg Complex.re hmain
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre2
  rw [hUR] at hre2
  exact hre2

end

end Commons.Analysis.Fourier