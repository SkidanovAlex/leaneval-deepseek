import Mathlib
open scoped FourierTransform
open Filter Asymptotics

/-!
# 1-D Poisson summation for a shifted Gaussian with a linear phase

`Σ_k exp(-π a (k+w)² + 2π i c (k+w)) = a^{-1/2} Σ_m exp(-π (m-c)²/a) exp(2π i m w)`
for real `a > 0`, `c`, `w`.  This is the base case of the `R`-dimensional Gaussian Poisson
summation used for Banaszczyk's transference theorem.
-/


noncomputable section

namespace Work.HP.Sig2

lemma summable_gauss_nat (A : ℝ) (hA : 0 < A) :
    Summable (fun n : ℕ => Real.exp (-A * (n : ℝ) ^ 2)) := by
  have hg : Summable (fun n : ℕ => (Real.exp (-A)) ^ n) := by
    rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_) hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h2 : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    calc Real.exp (-A * (n:ℝ)^2) ≤ Real.exp (-A * (n:ℝ)) :=
          Real.exp_le_exp.mpr (by nlinarith [hA.le])
      _ = (Real.exp (-A))^n := by rw [← Real.exp_nat_mul]; ring_nf

lemma summable_gauss_int (A : ℝ) (hA : 0 < A) :
    Summable (fun n : ℤ => Real.exp (-A * (n : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact summable_gauss_nat A hA
  · simpa using summable_gauss_nat A hA

/-- The 1-D Gaussian with a linear phase. -/
def gf (a c : ℝ) : ℝ → ℂ := fun x => Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2
    + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ))

lemma reArg2 (A x : ℝ) : (-(A:ℂ) * (x:ℂ)^2).re = -A*x^2 := by
  have h1 : -(A:ℂ)*(x:ℂ)^2 = -((A*x^2:ℝ):ℂ) := by push_cast; ring
  rw [h1, Complex.neg_re, Complex.ofReal_re]; ring

lemma reArg3 (A x y : ℝ) : (-(A:ℂ) * ((x:ℂ)-(y:ℂ))^2).re = -A*(x-y)^2 := by
  have h1 : -(A:ℂ)*((x:ℂ)-(y:ℂ))^2 = -((A*(x-y)^2:ℝ):ℂ) := by push_cast; ring
  rw [h1, Complex.neg_re, Complex.ofReal_re]; ring

lemma reArg (a c x : ℝ) :
    (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ)).re = -(Real.pi*a) * x^2 := by
  have h1 : -(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2 = -((Real.pi * a * x^2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ)
      = Complex.I * ((2*Real.pi*c*x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_im]; ring

lemma gf_continuous (a c : ℝ) : Continuous (gf a c) := by
  rw [show gf a c = (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2
      + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ))) from rfl]
  fun_prop

theorem poisson_shift_gaussian (a : ℝ) (ha : 0 < a) (c w : ℝ) :
    (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((k : ℂ) + (w : ℂ)) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * ((k : ℂ) + (w : ℂ))))
      = 1 / ((a : ℂ) ^ (1 / 2 : ℂ)) *
        ∑' m : ℤ, Complex.exp (-(Real.pi : ℂ) / (a : ℂ) * ((m : ℂ) - (c : ℂ)) ^ 2)
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (w : ℂ)) := by
  have hcont : Continuous (gf a c) := gf_continuous a c
  have hfourier : 𝓕 (gf a c) = fun t : ℝ => 1 / ((a:ℂ) ^ (1/2:ℂ)) *
      Complex.exp (-(Real.pi:ℂ)/(a:ℂ) * ((t:ℂ) - (c:ℂ))^2) := by
    have hfe : gf a c = (fun x : ℝ => Complex.exp (-(Real.pi:ℂ) * (a:ℂ) * (x:ℂ)^2
        + 2*(Real.pi:ℂ) * (Complex.I * (c:ℂ)) * (x:ℂ))) := by
      rw [show gf a c = fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ)) from rfl]
      congr 1 with x; ring_nf
    have h := fourier_gaussian_pi' (b := (a:ℂ)) (by simpa using ha) (Complex.I * (c:ℂ))
    rw [hfe, h]
    ext t
    have hI : Complex.I * (Complex.I * (c:ℂ)) = -(c:ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    rw [hI]
    ring_nf
  have hdec : gf a c =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) := by
    have h1' : (fun x : ℝ => Real.exp (-(Real.pi*a) * x^2)) =o[cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) := by
      have h1 : (fun x : ℝ => Complex.exp (-((Real.pi*a : ℝ) : ℂ) * (x:ℂ)^2))
          =o[cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) :=
        isLittleO_exp_neg_mul_sq_cocompact (a := ((Real.pi*a : ℝ) : ℂ))
          (by simpa using (by positivity : 0 < Real.pi*a)) (-2)
      have := h1.norm_left
      simpa only [Complex.norm_exp, reArg2] using this
    have h2 : (fun x : ℝ => ‖gf a c x‖) = fun x : ℝ => Real.exp (-(Real.pi*a) * x^2) := by
      funext x
      rw [show gf a c x = Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (x : ℂ)) from rfl]
      rw [Complex.norm_exp, reArg]
    have h3 : (fun x : ℝ => ‖gf a c x‖) =o[cocompact ℝ] (fun x : ℝ => |x| ^ (-2:ℝ)) := by
      rw [h2]; exact h1'
    exact IsBigO.of_norm_left h3.isBigO
  have hbase : Summable (fun n : ℤ => Complex.exp (-(Real.pi:ℂ)/(a:ℂ) * (((n:ℝ):ℂ) - (c:ℂ))^2)) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℤ => Real.exp (2*Real.pi*c^2/a) * Real.exp (-(Real.pi/(2*a)) * (n:ℝ)^2)) ?_ (fun n => ?_)
    · exact (summable_gauss_int (Real.pi/(2*a)) (by positivity)).mul_left (Real.exp (2*Real.pi*c^2/a))
    · rw [Complex.norm_exp]
      have hre : (-(Real.pi:ℂ)/(a:ℂ) * (((n:ℝ):ℂ) - (c:ℂ))^2).re = -(Real.pi/a) * ((n:ℝ)-c)^2 := by
        have h1 : -(Real.pi:ℂ)/(a:ℂ) = -((Real.pi/a : ℝ) : ℂ) := by push_cast; ring
        rw [h1, reArg3]
      rw [hre]
      have ham : -(((n:ℝ)-c))^2 ≤ -((n:ℝ))^2/2 + 2*c^2 := by
        nlinarith [sq_nonneg ((n:ℝ)-c), sq_nonneg c, sq_nonneg (n:ℝ)]
      have hc2 : 0 < Real.pi/a := by positivity
      have hle : -(Real.pi/a) * ((n:ℝ)-c)^2 ≤ -(Real.pi/(2*a)) * (n:ℝ)^2 + 2*Real.pi*c^2/a := by
        have hstep := mul_le_mul_of_nonneg_left ham hc2.le
        have e1 : -(Real.pi/a) * ((n:ℝ)-c)^2 = (Real.pi/a) * (-(((n:ℝ)-c)^2)) := by ring
        have e2 : (Real.pi/a) * (-(n:ℝ)^2/2 + 2*c^2)
            = -(Real.pi/(2*a)) * (n:ℝ)^2 + 2*Real.pi*c^2/a := by field_simp <;> ring
        rw [e1]; exact hstep.trans (le_of_eq e2)
      calc Real.exp (-(Real.pi/a) * ((n:ℝ)-c)^2)
          ≤ Real.exp (-(Real.pi/(2*a)) * (n:ℝ)^2 + 2*Real.pi*c^2/a) := Real.exp_le_exp.mpr hle
        _ = Real.exp (2*Real.pi*c^2/a) * Real.exp (-(Real.pi/(2*a)) * (n:ℝ)^2) := by
              rw [← Real.exp_add]; ring_nf
  have hsumF : Summable fun n : ℤ => 𝓕 (gf a c) n := by
    rw [hfourier]
    exact hbase.mul_left _
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont one_lt_two hdec hsumF w
  rw [hfourier] at hpois
  have hL : (∑' k : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((k : ℂ) + (w : ℂ)) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * ((k : ℂ) + (w : ℂ))))
      = ∑' k : ℤ, gf a c (w + (k:ℝ)) := by
    apply tsum_congr; intro k
    rw [show gf a c (w + (k:ℝ)) = Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * ((w + (k:ℝ) : ℝ) : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * ((w + (k:ℝ) : ℝ) : ℂ)) from rfl]
    congr 1; push_cast; ring
  rw [hL, hpois]
  have hfw : ∀ n : ℤ, (fourier n) ((w:ℝ) : UnitAddCircle)
      = Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(w:ℂ)) := by
    intro n; rw [fourier_coe_apply]; norm_num
  have hR : (∑' n : ℤ, (fun t : ℝ => 1 / ((a:ℂ)^(1/2:ℂ)) *
        Complex.exp (-(Real.pi:ℂ)/(a:ℂ) * ((t:ℂ) - (c:ℂ))^2)) (n:ℝ)
        * (fourier n) ((w:ℝ) : UnitAddCircle))
      = 1 / ((a:ℂ)^(1/2:ℂ)) *
        ∑' m : ℤ, Complex.exp (-(Real.pi:ℂ)/(a:ℂ) * ((m:ℂ) - (c:ℂ))^2)
          * Complex.exp (2*(Real.pi:ℂ)*Complex.I*(m:ℂ)*(w:ℂ)) := by
    simp_rw [hfw, mul_assoc]
    rw [tsum_mul_left]
    congr 1
  exact hR

end Work.HP.Sig2
