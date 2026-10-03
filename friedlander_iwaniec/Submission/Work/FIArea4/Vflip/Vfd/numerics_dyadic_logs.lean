import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.Vfd.log_growth
import Submission.Work.FIArea4.Vflip.Vfd.rpow_dyadic_ident
import Submission.Work.FIArea4.Vflip.Vfd.Hpow_le_xpow
import Submission.Work.FIArea4.Vflip.Vfd.log_pow4_ge

namespace Work.FIArea4.Vflip.Vfd

set_option maxHeartbeats 1000000

/-- **Dyadic numerics with logarithmic factors.**  In the range `D ≤ RS < D²` and with the
near-diagonal scale `H = (RS/D)^{1/3}`, the four terms of the near-diagonal contribution of
Friedlander–Iwaniec Proposition 12.1 are bounded by a constant (depending only on `ε > 0`)
times the bracket `p14T12 D R S ε`.

The proof rewrites every term using the single relation `x = RS = d·H³` (`d = D`):
* `(d·H·x)^{1/2} = d^{1/3} x^{2/3} = d·H²`, so the first two summands are dominated by the
  middle summand `d^{1/3} x^{2/3}(log 2x + 1)^4` of `p14T12` (using `log(2H) ≤ log(2x)`,
  `H² ≤ x` and `log t + 2 ≤ (log t + 1)^4` for `t ≥ 2`);
* the third summand is at most `x^{3/2}/d ≤ SE (≤ SE·x^ε)`;
* the last summand needs `(log 2H + 1)^4 ≤ K H^{3ε} ≤ K x^{ε/2}`, i.e. the logarithmic growth
  bound combined with `x ≥ H^6` (which follows from `x ≤ d²`). -/
theorem numerics_dyadic_logs (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H : ℝ), 1 ≤ D → 1 ≤ R → 1 ≤ S → R * S < D * D →
      D ≤ R * S → H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      (Real.log (2 * H) + 1) ^ 2 * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ 2 *
          ((D : ℝ) * H * (R : ℝ) * (S : ℝ)) ^ ((1 : ℝ) / 2)
      + ((R : ℝ) * (S : ℝ) / H) * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
      + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)
      + (Real.log (2 * H) + 1) ^ 4 * ((R : ℝ) * (S : ℝ)) ^ (ε / 2)
          * (((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / (D : ℝ)
              + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
      ≤ C * Work.FIArea4.p14T12 D R S ε := by
  obtain ⟨K, hKpos, hKbd⟩ := log_growth (3*ε) (by linarith)
  refine ⟨3 + K, by linarith, ?_⟩
  intro D R S H hD hR hS hlt hle hH
  unfold Work.FIArea4.p14T12
  have e1 : (2:ℝ)*(R:ℝ)*(S:ℝ) = 2*((R:ℝ)*(S:ℝ)) := by ring
  have e2 : (D:ℝ)*H*(R:ℝ)*(S:ℝ) = (D:ℝ)*H*((R:ℝ)*(S:ℝ)) := by ring
  rw [e1, e2]
  set d : ℝ := (D:ℝ) with hddef
  set x : ℝ := (R:ℝ)*(S:ℝ) with hxdef
  have hd1 : (1:ℝ) ≤ d := by rw [hddef]; exact_mod_cast hD
  have hx1 : (1:ℝ) ≤ x := by
    rw [hxdef]
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have := mul_le_mul hR1 hS1 (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hR1])
    simpa using this
  have hdpos : (0:ℝ) < d := by linarith only [hd1]
  have hxpos : (0:ℝ) < x := by linarith only [hx1]
  have hd_le_x : d ≤ x := by rw [hddef, hxdef]; exact_mod_cast hle
  have hH1 : (1:ℝ) ≤ H := by
    rw [hH]
    apply Real.one_le_rpow
    · rw [le_div_iff₀ hdpos]; linarith only [hd_le_x]
    · norm_num
  have hHpos : (0:ℝ) < H := by linarith only [hH1]
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hxd0 : (0:ℝ) ≤ x/d := by positivity
  have hHx : H^3 = x/d := by
    rw [hH, ← Real.rpow_natCast ((x/d)^((1:ℝ)/3)) 3, ← Real.rpow_mul hxd0 ((1:ℝ)/3) ((3:ℕ):ℝ)]
    rw [show ((1:ℝ)/3) * ((3:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
  have hxd : x ≤ d*d := by rw [hddef, hxdef]; exact_mod_cast (le_of_lt hlt)
  have hH3_le_x : H^3 ≤ x := by
    rw [hHx, div_le_iff₀ hdpos]
    exact le_mul_of_one_le_right (le_of_lt hxpos) hd1
  have hH_le_x : H ≤ x := by
    have h1 : H ≤ H^3 := by
      have := pow_le_pow_right₀ hH1 (show (1:ℕ) ≤ 3 by norm_num)
      simpa using this
    linarith only [h1, hH3_le_x]
  have hH2_le_x : H^2 ≤ x := by
    have h1 : H^2 ≤ H^3 := by
      have := pow_le_pow_right₀ hH1 (show (2:ℕ) ≤ 3 by norm_num)
      simpa using this
    linarith only [h1, hH3_le_x]
  have hR34 : (0:ℝ) ≤ (R:ℝ)*(S:ℝ)^((3:ℝ)/4) :=
    mul_nonneg (Nat.cast_nonneg R) (Real.rpow_nonneg (Nat.cast_nonneg S) _)
  have hS34 : (0:ℝ) ≤ (S:ℝ)*(R:ℝ)^((3:ℝ)/4) :=
    mul_nonneg (Nat.cast_nonneg S) (Real.rpow_nonneg (Nat.cast_nonneg R) _)
  have hG0eq : d⁻¹ * x^((3:ℝ)/2) + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)
      = x^((3:ℝ)/2)/d + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4) := by
    rw [div_eq_mul_inv]; ring
  rw [hG0eq]
  set T2 : ℝ := d^((1:ℝ)/3) * x^((2:ℝ)/3) * (Real.log (2*x)+1)^4 with hT2def
  set A : ℝ := (Real.log (2*H)+1)^2 * (Real.log (2*x)+1)^2 * (d*H*x)^((1:ℝ)/2) with hAdef
  set B : ℝ := (x/H) * (Real.log (2*x/(d*H)) + 2) with hBdef
  set Cc : ℝ := x^((3:ℝ)/2)/(d*H) with hCcdef
  set SE : ℝ := x^((3:ℝ)/2)/d + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4) with hSEdef
  set E : ℝ := (Real.log (2*H)+1)^4 * x^(ε/2) * SE with hEdef
  set Gx : ℝ := SE * x^ε with hGxdef
  have hSE0 : (0:ℝ) ≤ SE := by
    rw [hSEdef]
    have h1 : (0:ℝ) ≤ x^((3:ℝ)/2)/d := div_nonneg (Real.rpow_nonneg (by linarith only [hx1]) _) (by linarith only [hd1])
    linarith only [h1, hR34, hS34]
  have hx_eq : x = d * H^3 := by
    rw [hHx]; exact (mul_div_cancel₀ x (ne_of_gt hdpos)).symm
  have hA : A ≤ T2 := by
    rw [hAdef, hT2def]
    rw [rpow_dyadic_ident d H x hdpos hHpos hx_eq]
    have hlog : Real.log (2*H) ≤ Real.log (2*x) :=
      Real.log_le_log (by linarith only [hH1]) (by linarith only [hH_le_x])
    have hlog0 : (0:ℝ) ≤ Real.log (2*H) + 1 := by
      have h := Real.log_nonneg (show (1:ℝ) ≤ 2*H by linarith only [hH1]); linarith only [h]
    have hsq : (Real.log (2*H)+1)^2 ≤ (Real.log (2*x)+1)^2 :=
      pow_le_pow_left₀ hlog0 (by linarith only [hlog]) 2
    have hpx : (0:ℝ) ≤ d^((1:ℝ)/3) * x^((2:ℝ)/3) :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hd1]) _) (Real.rpow_nonneg (by linarith only [hx1]) _)
    calc (Real.log (2*H)+1)^2 * (Real.log (2*x)+1)^2 * (d^((1:ℝ)/3)*x^((2:ℝ)/3))
        = (Real.log (2*H)+1)^2 * (d^((1:ℝ)/3)*x^((2:ℝ)/3)) * (Real.log (2*x)+1)^2 := by ring
      _ ≤ (Real.log (2*x)+1)^2 * (d^((1:ℝ)/3)*x^((2:ℝ)/3)) * (Real.log (2*x)+1)^2 := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hpx) (sq_nonneg _)
      _ = d^((1:ℝ)/3)*x^((2:ℝ)/3) * (Real.log (2*x)+1)^4 := by ring
  have hid2 : d^((1:ℝ)/3)*x^((2:ℝ)/3) = d*H^2 := by
    rw [← rpow_dyadic_ident d H x hdpos hHpos hx_eq, hx_eq, ← Real.sqrt_eq_rpow,
        show d*H*(d*H^3) = (d*H^2)^2 by ring, Real.sqrt_sq (by positivity)]
  have hB : B ≤ T2 := by
    rw [hBdef, hT2def, hid2]
    have hx_div : x / H = d * H^2 := by rw [hx_eq, div_eq_iff hHne]; ring
    have harg : 2*x/(d*H) = 2*H^2 := by rw [hx_eq, div_eq_iff (mul_ne_zero (ne_of_gt hdpos) hHne)]; ring
    rw [hx_div, harg]
    have hlog : Real.log (2*H^2) + 2 ≤ (Real.log (2*x)+1)^4 := by
      have h1 : Real.log (2*H^2) ≤ Real.log (2*x) := Real.log_le_log (by positivity) (by linarith only [hH2_le_x])
      have hu : (1:ℝ)/3 ≤ Real.log (2*x) := by
        have h2x : (2:ℝ) ≤ 2*x := by linarith only [hx1]
        have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2x
        have h13 : (1:ℝ)/3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
        linarith only [h, h13]
      linarith only [h1, log_pow4_ge (Real.log (2*x)) hu]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hxε : (1:ℝ) ≤ x^ε := Real.one_le_rpow hx1 hε.le
  have hC : Cc ≤ Gx := by
    rw [hCcdef, hGxdef]
    have ha : (0:ℝ) ≤ x^((3:ℝ)/2) := Real.rpow_nonneg (by linarith only [hx1]) _
    have hstep1 : x^((3:ℝ)/2)/(d*H) ≤ x^((3:ℝ)/2)/d := by
      rw [div_le_iff₀ (mul_pos hdpos hHpos),
          ← mul_assoc, div_mul_cancel₀ (x^((3:ℝ)/2)) (ne_of_gt hdpos)]
      exact le_mul_of_one_le_right ha hH1
    have hstep2 : x^((3:ℝ)/2)/d ≤ SE := by rw [hSEdef]; linarith only [hR34, hS34]
    have hstep3 : SE ≤ SE * x^ε := le_mul_of_one_le_right hSE0 hxε
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  have hE : E ≤ K * Gx := by
    rw [hEdef, hGxdef]
    have hxhalf : (0:ℝ) ≤ x^(ε/2) := Real.rpow_nonneg (by linarith only [hx1]) _
    have hK' : (Real.log (2*H)+1)^4 ≤ K * x^(ε/2) := by
      have h1 := hKbd H hH1
      have h2 : H^(3*ε) ≤ x^(ε/2) := Hpow_le_xpow d x H ε hd1 hH1 hε hHx hxd
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hKpos))
    have hxx : x^(ε/2) * x^(ε/2) = x^ε := by
      rw [← Real.rpow_add hxpos (ε/2) (ε/2)]; congr 1; ring
    have heq : K * x^(ε/2) * x^(ε/2) * SE = K * (SE * x^ε) := by
      rw [show K * x^(ε/2) * x^(ε/2) * SE = K * (x^(ε/2)*x^(ε/2)) * SE by ring, hxx]; ring
    calc (Real.log (2*H)+1)^4 * x^(ε/2) * SE
        ≤ (K * x^(ε/2)) * x^(ε/2) * SE :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK' hxhalf) hSE0
      _ = K * (SE * x^ε) := heq
  have hT2nn : (0:ℝ) ≤ T2 := by
    rw [hT2def]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith only [hd1]) _) (Real.rpow_nonneg (by linarith only [hx1]) _)) (by positivity)
  have hGxnn : (0:ℝ) ≤ Gx := by
    rw [hGxdef]; exact mul_nonneg hSE0 (Real.rpow_nonneg (by linarith only [hx1]) _)
  have hdnn : (0:ℝ) ≤ d := by linarith only [hd1]
  have h1 : A + B + Cc + E ≤ T2 + T2 + Gx + K * Gx :=
    add_le_add (add_le_add (add_le_add hA hB) hC) hE
  refine le_trans h1 ?_
  rw [show (3+K)*(d+T2+Gx) = (3+K)*d + (3+K)*T2 + (3+K)*Gx by ring]
  have e1 : (2:ℝ)*T2 ≤ (3+K)*T2 := mul_le_mul_of_nonneg_right (by linarith only [hKpos]) hT2nn
  have e2 : Gx + K*Gx ≤ (3+K)*Gx := by
    rw [show Gx + K*Gx = (1+K)*Gx by ring]
    exact mul_le_mul_of_nonneg_right (by linarith only [hKpos]) hGxnn
  have e3 : (0:ℝ) ≤ (3+K)*d := mul_nonneg (by linarith only [hKpos]) hdnn
  linarith only [e1, e2, e3]

end Work.FIArea4.Vflip.Vfd
