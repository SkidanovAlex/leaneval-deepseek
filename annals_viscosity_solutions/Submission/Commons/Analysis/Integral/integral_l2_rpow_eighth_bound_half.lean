import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Bound on the integral `∫_{1}^{√2} (1 - (1/x)²)^(-1/8) √(2/(1+√(1-(1/x)²))) (√x)⁻¹ ≤ 0.6`

This file proves the numerical estimate requested by the `annals_viscosity_solutions`
development.  The proof proceeds by the change of variables `x = (1 - y²)^(-1/2)`
(so that `y = √(1 - (1/x)²)` ranges over `[0, 1/√2]`), which turns the integrand into
`√2 · y^{3/4} (1-y)^{-5/4} (1+y)^{-7/4}`.  The resulting elementary integral is then
bounded by a Riemann-sum style argument on four sub-intervals, whose terms are majorised
by explicit rational numbers.
-/

namespace Commons.Analysis.Integral

open Real MeasureTheory

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

private noncomputable def Fint (x : ℝ) : ℝ :=
  (1 - (1/x)^2)^(-(1/8:ℝ)) * Real.sqrt (2/(1+Real.sqrt (1-(1/x)^2))) * (Real.sqrt x)⁻¹

private noncomputable def Gg (y : ℝ) : ℝ := (1 - y^2)^(-(1/2:ℝ))
private noncomputable def Gg' (y : ℝ) : ℝ := y * (1 - y^2)^(-(3/2:ℝ))
private noncomputable def R : ℝ := 1/Real.sqrt 2
private noncomputable def fmono (y : ℝ) : ℝ := y^(3/4:ℝ) * (1+y)^(-(7/4:ℝ))
private noncomputable def PsiR (y : ℝ) : ℝ := Real.sqrt 2 * fmono y * (1-y)^(-(5/4:ℝ))
private noncomputable def Psi (y : ℝ) : ℝ :=
  Real.sqrt 2 * y^(3/4:ℝ) * (1-y)^(-(5/4:ℝ)) * (1+y)^(-(7/4:ℝ))

private lemma Psi_eq_PsiR (y : ℝ) : Psi y = PsiR y := by rw [Psi, PsiR, fmono]; ring

/-! ## Elementary power-function comparisons

We shall bound real powers by rationals by raising to the fourth power. -/

private lemma rpow_three_quarters_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^(3/4:ℝ) ≤ b ↔ a^3 ≤ b^4 := by
  have h4 : (a^(3/4:ℝ))^4 = a^3 := by
    rw [← Real.rpow_natCast (a^(3/4:ℝ)) 4, ← Real.rpow_mul ha (3/4:ℝ) ((4:ℕ):ℝ)]
    norm_num
  rw [← h4]
  exact (pow_le_pow_iff_left₀ (n:=4) (Real.rpow_nonneg ha _) hb (by norm_num)).symm

private lemma rpow_neg_quarter_le_iff {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    a^(-(1/4:ℝ)) ≤ q ↔ 1 ≤ q^4 * a := by
  have h4 : (a^(-(1/4:ℝ)))^4 = a⁻¹ := by
    rw [← Real.rpow_natCast (a^(-(1/4:ℝ))) 4, ← Real.rpow_mul ha.le (-(1/4:ℝ)) ((4:ℕ):ℝ)]
    norm_num
    exact Real.rpow_neg_one a
  have ht : 0 ≤ a^(-(1/4:ℝ)) := Real.rpow_nonneg ha.le _
  rw [← pow_le_pow_iff_left₀ (n:=4) ht hq (by norm_num), h4, inv_le_iff_one_le_mul₀ ha]

private lemma le_rpow_neg_quarter_iff {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    q ≤ a^(-(1/4:ℝ)) ↔ q^4 * a ≤ 1 := by
  have h4 : (a^(-(1/4:ℝ)))^4 = a⁻¹ := by
    rw [← Real.rpow_natCast (a^(-(1/4:ℝ))) 4, ← Real.rpow_mul ha.le (-(1/4:ℝ)) ((4:ℕ):ℝ)]
    norm_num
    exact Real.rpow_neg_one a
  have ht : 0 ≤ a^(-(1/4:ℝ)) := Real.rpow_nonneg ha.le _
  rw [← pow_le_pow_iff_left₀ (n:=4) hq ht (by norm_num), h4, inv_eq_one_div, le_div_iff₀ ha]

private lemma rpow_neg_seven_quarters_le_iff {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    a^(-(7/4:ℝ)) ≤ b ↔ 1 ≤ b^4 * a^7 := by
  have h4 : (a^(-(7/4:ℝ)))^4 = (a^7)⁻¹ := by
    rw [← Real.rpow_natCast (a^(-(7/4:ℝ))) 4, ← Real.rpow_mul ha.le (-(7/4:ℝ)) ((4:ℕ):ℝ)]
    norm_num
  have ht : 0 ≤ a^(-(7/4:ℝ)) := Real.rpow_nonneg ha.le _
  rw [← pow_le_pow_iff_left₀ (n:=4) ht hb (by norm_num), h4,
      inv_le_iff_one_le_mul₀ (pow_pos ha 7)]

/-! ## The real numbers `R = 1/√2` -/

private lemma R_pos : 0 < R := by rw [R]; positivity
private lemma R_sq : R^2 = 1/2 := by
  rw [R, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
private lemma R_le : R ≤ 71/100 := by nlinarith [R_sq, R_pos]
private lemma R_le34 : R ≤ 3/4 := by nlinarith [R_sq, R_pos]

private lemma Gg_zero : Gg 0 = 1 := by rw [Gg]; norm_num
private lemma Gg_R : Gg R = Real.sqrt 2 := by
  rw [Gg, R_sq, show (1 - 1/2:ℝ) = 1/2 by norm_num,
      show (-(1/2:ℝ)) = (-1:ℝ) * (1/2) by norm_num,
      Real.rpow_mul (by norm_num : (0:ℝ)≤1/2), Real.rpow_neg_one]
  norm_num
  rw [← Real.sqrt_eq_rpow]

/-! ## The change of variables -/

private lemma Gg_deriv (y : ℝ) (hy : y^2 < 1) : HasDerivAt Gg (Gg' y) y := by
  have hne : (1:ℝ) - y^2 ≠ 0 := by nlinarith
  have hp : HasDerivAt (fun x:ℝ => x^2) (2*y) y := by
    have h := hasDerivAt_pow (2:ℕ) y
    convert h using 1 <;> (first | rfl | (ext z; ring) | ring_nf)
  have hbase : HasDerivAt (fun y:ℝ => 1 - y^2) (-2*y) y := by
    have h := (hasDerivAt_const y (1:ℝ)).sub hp
    convert h using 1 <;> (first | rfl | (ext z; ring) | ring_nf)
  have h2 := hbase.rpow_const (p := -(1/2:ℝ)) (Or.inl hne)
  unfold Gg Gg'
  convert h2 using 1 <;>
    (first | rfl | (rw [show (-(1/2:ℝ)) - 1 = -(3/2) by norm_num]; ring) | ring_nf)

private lemma Gg_cont : ContinuousOn Gg (Set.uIcc 0 R) := by
  apply ContinuousOn.rpow_const
  · fun_prop
  · intro x hx
    rw [Set.uIcc_of_le R_pos.le] at hx
    exact Or.inl (by
      have : x^2 ≤ 1/2 := by nlinarith [R_sq, hx.1, hx.2, sq_nonneg x]
      nlinarith)

private lemma Gg_nn : ∀ x ∈ Set.Ioo 0 R, 0 ≤ Gg' x := by
  intro x hx
  rw [Gg']
  have h1 : (0:ℝ) < 1 - x^2 := by
    have : x^2 ≤ 1/2 := by nlinarith [R_sq, R_pos, hx.1, hx.2]
    nlinarith
  exact mul_nonneg (le_of_lt hx.1) (le_of_lt (Real.rpow_pos_of_pos h1 _))

private lemma sqrt_two_div (y : ℝ) (hy : 0≤y) :
    Real.sqrt (2/(1+y)) = Real.sqrt 2 * (1+y)^(-(1/2:ℝ)) := by
  have h1p : (0:ℝ) < 1+y := by linarith
  rw [Real.sqrt_div (x:=2) (by norm_num) (1+y), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      div_eq_mul_inv, ← Real.rpow_neg h1p.le (1/2:ℝ)]

private lemma Gg_invsq (y : ℝ) (hy : y^2 ≤ 1/2) : (1 / Gg y)^2 = 1 - y^2 := by
  have ha : (0:ℝ) < 1 - y^2 := by nlinarith
  have h1 : (1 / Gg y) = (1 - y^2)^(1/2:ℝ) := by
    rw [Gg, Real.rpow_neg ha.le (1/2:ℝ)]; field_simp
  rw [h1, ← Real.rpow_natCast ((1-y^2)^(1/2:ℝ)) 2,
      ← Real.rpow_mul ha.le (1/2:ℝ) ((2:ℕ):ℝ),
      show (1/2:ℝ)*((2:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]

private lemma Fint_Gg (y : ℝ) (hy0 : 0≤y) (hy : y^2 ≤ 1/2) :
    Fint (Gg y) * Gg' y = Psi y := by
  have ha : (0:ℝ) < 1 - y^2 := by nlinarith
  have h1m : (0:ℝ) < 1 - y := by nlinarith [hy, sq_nonneg y]
  have h1p : (0:ℝ) < 1 + y := by linarith
  have h4 : (1 - (1 / Gg y)^2)^(-(1/8:ℝ)) = y^(-(1/4:ℝ)) := by
    rw [Gg_invsq y hy, show (1 - (1 - y^2)) = y^2 by ring, ← Real.rpow_natCast (y:ℝ) 2,
        ← Real.rpow_mul hy0 ((2:ℕ):ℝ) (-(1/8:ℝ))]
    norm_num
  have h5 : Real.sqrt (1 - (1 / Gg y)^2) = y := by
    rw [Gg_invsq y hy, show (1 - (1 - y^2)) = y^2 by ring, Real.sqrt_sq hy0]
  have h6 : (Real.sqrt (Gg y))⁻¹ = (1 - y^2)^(1/4:ℝ) := by
    have hGg : 0 ≤ Gg y := by rw [Gg]; positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hGg (1/2:ℝ) (-1:ℝ),
        show (1/2:ℝ)*(-1) = -(1/2) by norm_num, Gg,
        ← Real.rpow_mul ha.le (-(1/2:ℝ)) (-(1/2:ℝ))]
    norm_num
  have hy3 : y^(-(1/4:ℝ)) * y = y^(3/4:ℝ) := by
    rw [show (3/4:ℝ) = -(1/4) + 1 by norm_num, Real.rpow_add' hy0 (by norm_num), Real.rpow_one]
  have ha5 : (1-y^2)^(1/4:ℝ) * (1-y^2)^(-(3/2:ℝ)) = (1-y^2)^(-(5/4:ℝ)) := by
    rw [show (-(5/4:ℝ)) = (1/4) + (-(3/2)) by norm_num, Real.rpow_add' ha.le (by norm_num)]
  have ha' : (1-y^2)^(-(5/4:ℝ)) = (1-y)^(-(5/4:ℝ)) * (1+y)^(-(5/4:ℝ)) := by
    rw [show (1 - y^2) = (1-y)*(1+y) by ring, Real.mul_rpow h1m.le h1p.le]
  have hp7 : (1+y)^(-(5/4:ℝ)) * (1+y)^(-(1/2:ℝ)) = (1+y)^(-(7/4:ℝ)) := by
    rw [show (-(7/4:ℝ)) = (-(5/4)) + (-(1/2)) by norm_num, Real.rpow_add' h1p.le (by norm_num)]
  unfold Fint Gg' Psi
  rw [h4, h5, h6, sqrt_two_div y hy0]
  rw [show y ^ (-(1/4:ℝ)) * (Real.sqrt 2 * (1+y)^(-(1/2:ℝ))) * (1-y^2)^(1/4:ℝ)
        * (y * (1-y^2)^(-(3/2:ℝ)))
        = Real.sqrt 2 * (y ^ (-(1/4:ℝ)) * y) * ((1-y^2)^(1/4:ℝ) * (1-y^2)^(-(3/2:ℝ)))
          * (1+y)^(-(1/2:ℝ)) by ring]
  rw [hy3, ha5, ha']
  rw [show Real.sqrt 2 * y^(3/4:ℝ) * ((1-y)^(-(5/4:ℝ))*(1+y)^(-(5/4:ℝ))) * (1+y)^(-(1/2:ℝ))
        = Real.sqrt 2 * y^(3/4:ℝ) * (1-y)^(-(5/4:ℝ))
          * ((1+y)^(-(5/4:ℝ))*(1+y)^(-(1/2:ℝ))) by ring]
  rw [hp7]

/-! ## The explicit numerical bound on `∫₀^{R} PsiR` -/

private lemma sqrt2_le : Real.sqrt 2 ≤ 14143/10000 := by
  have h : (Real.sqrt 2)^2 ≤ (14143/10000:ℝ)^2 := by
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; norm_num
  nlinarith [Real.sqrt_nonneg 2]

private lemma fmono_le {y A B : ℝ} (hy : 0 ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA' : y^3 ≤ A^4) (hB' : 1 ≤ B^4 * (1+y)^7) : fmono y ≤ A * B := by
  rw [fmono]
  have h1 : y^(3/4:ℝ) ≤ A := (rpow_three_quarters_le_iff hy hA).mpr hA'
  have h2 : (1+y)^(-(7/4:ℝ)) ≤ B := (rpow_neg_seven_quarters_le_iff (by linarith) hB).mpr hB'
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) hA

private lemma dicalg (y : ℝ) (hy : 0<y) :
    (3/4:ℝ) * y ^ ((3/4:ℝ)-1) * (1 + y) ^ (-(7/4:ℝ))
      + y ^ (3/4:ℝ) * (1 * -(7/4:ℝ) * (1 + y) ^ (-(7/4:ℝ) - 1))
    = 1/4 * y ^ (-(1/4:ℝ)) * (1 + y) ^ (-(11/4:ℝ)) * (3 - 4*y) := by
  rw [show ((3:ℝ)/4) - 1 = -(1/4) by norm_num,
      show (-(7/4:ℝ)) - 1 = -(11/4) by norm_num]
  rw [show (3:ℝ)/4 = 1 + (-(1/4)) by norm_num, Real.rpow_add hy]
  rw [show (-(7/4:ℝ)) = (-(11/4:ℝ)) + 1 by norm_num, Real.rpow_add (by positivity : (0:ℝ)<1+y)]
  simp only [Real.rpow_one]
  ring

private lemma fmono_hasDeriv (y : ℝ) (hy : 0<y) :
    HasDerivAt fmono ((1/4)*y^(-(1/4:ℝ))*(1+y)^(-(11/4:ℝ))*(3-4*y)) y := by
  unfold fmono
  have h1 : HasDerivAt (fun y:ℝ => y^(3/4:ℝ)) ((3/4:ℝ) * y^((3/4:ℝ)-1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hy))
  have h2 : HasDerivAt (fun y:ℝ => (1+y)^(-(7/4:ℝ)))
      ((1:ℝ) * (-(7/4:ℝ)) * (1+y)^((-(7/4:ℝ))-1)) y := by
    apply HasDerivAt.rpow_const
    · simpa using (hasDerivAt_id y).const_add (1:ℝ)
    · exact Or.inl (by positivity)
  exact (h1.mul h2).congr_deriv (dicalg y hy)

private lemma fmono_mono : MonotoneOn fmono (Set.Icc 0 (3/4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const
      · exact continuousOn_id
      · intro x hx; right; norm_num
    · apply ContinuousOn.rpow_const
      · fun_prop
      · intro x hx; exact Or.inl (ne_of_gt (by linarith [hx.1] : (0:ℝ) < 1+x))
  · rw [interior_Icc]
    intro x hx
    exact (fmono_hasDeriv x hx.1).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(fmono_hasDeriv x hx.1).deriv]
    have hy1 : 0 ≤ x^(-(1/4:ℝ)) := Real.rpow_nonneg (le_of_lt hx.1) _
    have hy2 : 0 ≤ (1+x)^(-(11/4:ℝ)) := Real.rpow_nonneg (by linarith [hx.1]) _
    have h3 : 0 ≤ 3 - 4*x := by linarith [hx.2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy1) hy2) h3

private lemma integral_weight (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    ∫ y in a..b, (1-y)^(-(5/4:ℝ)) = 4*((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ))) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y:ℝ => 4*(1-y)^(-(1/4:ℝ))) ((1-x)^(-(5/4:ℝ))) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : (1:ℝ) - x ≠ 0 := by linarith [hx.2, hb]
    have hbase : HasDerivAt (fun y:ℝ => 1-y) (-1) x := by
      have h := (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
      convert h using 1 <;> (first | rfl | ring_nf)
    have h1 : HasDerivAt (fun y:ℝ => (1-y)^(-(1/4:ℝ)))
        ((-1) * (-(1/4:ℝ)) * (1-x)^((-(1/4:ℝ))-1)) x :=
      hbase.rpow_const (p := -(1/4:ℝ)) (Or.inl hx1)
    have h2 := h1.const_mul (4:ℝ)
    convert h2 using 1 <;>
      (first | rfl | (rw [show (-(1/4:ℝ))-1 = -(5/4) by norm_num]; ring) | ring_nf)
  have hint : IntervalIntegrable (fun y => (1-y)^(-(5/4:ℝ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact Or.inl (by linarith [hx.2, hb])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y:ℝ => 4*(1-y)^(-(1/4:ℝ)))
        (f' := fun y:ℝ => (1-y)^(-(5/4:ℝ))) hderiv hint]
  ring

private lemma piece_bound (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3/4) :
    ∫ y in a..b, PsiR y ≤ Real.sqrt 2 * fmono b * (4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ)))) := by
  have hb1 : b < 1 := by linarith
  have hmono_cont : ContinuousOn fmono (Set.uIcc a b) := by
    unfold fmono
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const (f := fun y => y)
      · exact continuousOn_id
      · intro x hx; right; norm_num
    · apply ContinuousOn.rpow_const (f := fun y => 1+y)
      · fun_prop
      · intro x hx; rw [Set.uIcc_of_le hab] at hx; exact Or.inl (by linarith [hx.1, ha])
  have hcont : ContinuousOn (fun y => fmono y * (1-y)^(-(5/4:ℝ))) (Set.uIcc a b) := by
    apply ContinuousOn.mul hmono_cont
    apply ContinuousOn.rpow_const (f := fun y => 1-y)
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact Or.inl (by linarith [hx.2, hb1])
  have hcont2 : ContinuousOn (fun y => fmono b * (1-y)^(-(5/4:ℝ))) (Set.uIcc a b) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.rpow_const (f := fun y => 1-y)
    · fun_prop
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact Or.inl (by linarith [hx.2, hb1])
  have hint1 : IntervalIntegrable (fun y => fmono y * (1-y)^(-(5/4:ℝ))) volume a b :=
    hcont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun y => fmono b * (1-y)^(-(5/4:ℝ))) volume a b :=
    hcont2.intervalIntegrable
  have h1 : ∫ y in a..b, PsiR y = Real.sqrt 2 * ∫ y in a..b, fmono y * (1-y)^(-(5/4:ℝ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy; rw [PsiR]; ring
  rw [h1]
  have h2 : ∫ y in a..b, fmono y * (1-y)^(-(5/4:ℝ))
      ≤ fmono b * (4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ)))) := by
    calc ∫ y in a..b, fmono y * (1-y)^(-(5/4:ℝ))
        ≤ ∫ y in a..b, fmono b * (1-y)^(-(5/4:ℝ)) := by
          apply intervalIntegral.integral_mono_on hab hint1 hint2
          intro y hy
          have hy' : fmono y ≤ fmono b :=
            fmono_mono ⟨by linarith [hy.1, ha], by linarith [hy.2, hb]⟩
              ⟨by linarith [ha, hab], hb⟩ hy.2
          exact mul_le_mul_of_nonneg_right hy' (Real.rpow_nonneg (by linarith [hy.2, hb1]) _)
      _ = fmono b * ∫ y in a..b, (1-y)^(-(5/4:ℝ)) := intervalIntegral.integral_const_mul _ _
      _ = fmono b * (4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ)))) := by
          rw [integral_weight a b ha hab hb1]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)

private lemma PsiR_cont {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3/4) :
    ContinuousOn PsiR (Set.uIcc a b) := by
  have h1 : ContinuousOn fmono (Set.uIcc a b) := by
    unfold fmono
    apply ContinuousOn.mul
    · apply ContinuousOn.rpow_const (f := fun y => y)
      · exact continuousOn_id
      · intro x hx; right; norm_num
    · apply ContinuousOn.rpow_const (f := fun y => 1+y)
      · fun_prop
      · intro x hx; rw [Set.uIcc_of_le hab] at hx; exact Or.inl (by linarith [hx.1, ha])
  unfold PsiR
  apply ContinuousOn.mul
  · exact ContinuousOn.mul continuousOn_const h1
  · apply ContinuousOn.rpow_const (f := fun y => 1-y)
    · fun_prop
    · intro x hx; rw [Set.uIcc_of_le hab] at hx; exact Or.inl (by linarith [hx.2, hb])

private lemma piece_num {a b A B Q P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hP : 0 ≤ P)
    (hab : a ≤ b) (hb34 : b ≤ 3/4)
    (hA' : b^3 ≤ A^4) (hB' : 1 ≤ B^4 * (1+b)^7)
    (hQ' : 1 ≤ Q^4 * (1-b)) (hP' : P^4 * (1-a) ≤ 1) :
    Real.sqrt 2 * fmono b * (4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ))))
      ≤ (14143/10000) * (A*B) * (4*(Q-P)) := by
  have hb1 : b < 1 := by linarith
  have hf : fmono b ≤ A*B := fmono_le hb hA hB hA' hB'
  have hfb : 0 ≤ fmono b := by
    rw [fmono]; exact mul_nonneg (Real.rpow_nonneg hb _) (Real.rpow_nonneg (by linarith) _)
  have hqa : (1-b)^(-(1/4:ℝ)) ≤ Q := (rpow_neg_quarter_le_iff (by linarith) hQ).mpr hQ'
  have hpb : P ≤ (1-a)^(-(1/4:ℝ)) := (le_rpow_neg_quarter_iff (by linarith) hP).mpr hP'
  have hdiff : (1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ)) ≤ Q - P := sub_le_sub hqa hpb
  have hX : 0 ≤ 4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ))) := by
    rw [← integral_weight a b ha hab hb1]
    apply intervalIntegral.integral_nonneg hab
    intro u hu; exact Real.rpow_nonneg (by linarith [hu.2, hb1]) _
  have h1 : Real.sqrt 2 * fmono b ≤ (14143/10000) * (A*B) :=
    mul_le_mul sqrt2_le hf hfb (by norm_num)
  have hw : 4 * ((1-b)^(-(1/4:ℝ)) - (1-a)^(-(1/4:ℝ))) ≤ 4*(Q-P) := by linarith
  have hAB : 0 ≤ (14143/10000) * (A*B) := mul_nonneg (by norm_num) (mul_nonneg hA hB)
  simpa [mul_assoc] using mul_le_mul h1 hw hX hAB

private theorem integral_psi_bound : ∫ y in (0:ℝ)..R, PsiR y ≤ 3/5 := by
  have i_R : IntervalIntegrable PsiR volume (0:ℝ) R :=
    (PsiR_cont le_rfl R_pos.le R_le34).intervalIntegrable
  have i_2 : IntervalIntegrable PsiR volume R (71/100) :=
    (PsiR_cont R_pos.le R_le (by norm_num)).intervalIntegrable
  have hExt : ∫ y in (0:ℝ)..R, PsiR y ≤ ∫ y in (0:ℝ)..(71/100), PsiR y := by
    have e := intervalIntegral.integral_add_adjacent_intervals i_R i_2
    have hpos : 0 ≤ ∫ y in R..(71/100), PsiR y := by
      apply intervalIntegral.integral_nonneg R_le
      intro u hu
      rw [PsiR, fmono]
      have hu1 : (0:ℝ) ≤ u := le_trans R_pos.le hu.1
      have hu2 : (0:ℝ) < 1 - u := by linarith [hu.2]
      have h2 : (0:ℝ) < 1 + u := by linarith
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
        (mul_nonneg (Real.rpow_nonneg hu1 _) (Real.rpow_nonneg (le_of_lt h2) _)))
        (Real.rpow_nonneg (le_of_lt hu2) _)
    linarith [e, hpos]
  set c1 : ℝ := (14143/10000) * ((341829/1250000) * (7513087/10000000))
    * (4*(10500647/10000000 - 1)) with hc1
  set c2 : ℝ := (14143/10000) * ((1149771/2500000) * (5876331/10000000))
    * (4*(1115861/1000000 - 5250323/5000000)) with hc2
  set c3 : ℝ := (14143/10000) * ((1558403/2500000) * (379/800))
    * (4*(12093573/10000000 - 11158609/10000000)) with hc3
  set c4 : ℝ := (14143/10000) * ((3867353/5000000) * (3910721/10000000))
    * (4*(106461/78125 - 3023393/2500000)) with hc4
  have i0 : ∫ y in (0:ℝ)..(71/400), PsiR y ≤ c1 := by
    rw [hc1]
    exact le_trans (piece_bound 0 (71/400) (by norm_num) (by norm_num) (by norm_num))
      (piece_num (a:=0) (b:=71/400) (A:=341829/1250000) (B:=7513087/10000000)
        (Q:=10500647/10000000) (P:=1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
  have i1 : ∫ y in (71/400:ℝ)..(71/200), PsiR y ≤ c2 := by
    rw [hc2]
    exact le_trans (piece_bound (71/400) (71/200) (by norm_num) (by norm_num) (by norm_num))
      (piece_num (a:=71/400) (b:=71/200) (A:=1149771/2500000) (B:=5876331/10000000)
        (Q:=1115861/1000000) (P:=5250323/5000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
  have i2 : ∫ y in (71/200:ℝ)..(213/400), PsiR y ≤ c3 := by
    rw [hc3]
    exact le_trans (piece_bound (71/200) (213/400) (by norm_num) (by norm_num) (by norm_num))
      (piece_num (a:=71/200) (b:=213/400) (A:=1558403/2500000) (B:=379/800)
        (Q:=12093573/10000000) (P:=11158609/10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
  have i3 : ∫ y in (213/400:ℝ)..(71/100), PsiR y ≤ c4 := by
    rw [hc4]
    exact le_trans (piece_bound (213/400) (71/100) (by norm_num) (by norm_num) (by norm_num))
      (piece_num (a:=213/400) (b:=71/100) (A:=3867353/5000000) (B:=3910721/10000000)
        (Q:=106461/78125) (P:=3023393/2500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num))
  have e1 : (∫ y in (0:ℝ)..(71/400), PsiR y) + (∫ y in (71/400:ℝ)..(71/200), PsiR y)
      = ∫ y in (0:ℝ)..(71/200), PsiR y :=
    intervalIntegral.integral_add_adjacent_intervals
      ((PsiR_cont le_rfl (by norm_num) (by norm_num)).intervalIntegrable)
      ((PsiR_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
  have e2 : (∫ y in (71/200:ℝ)..(213/400), PsiR y) + (∫ y in (213/400:ℝ)..(71/100), PsiR y)
      = ∫ y in (71/200:ℝ)..(71/100), PsiR y :=
    intervalIntegral.integral_add_adjacent_intervals
      ((PsiR_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
      ((PsiR_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
  have e3 : (∫ y in (0:ℝ)..(71/200), PsiR y) + (∫ y in (71/200:ℝ)..(71/100), PsiR y)
      = ∫ y in (0:ℝ)..(71/100), PsiR y :=
    intervalIntegral.integral_add_adjacent_intervals
      ((PsiR_cont le_rfl (by norm_num) (by norm_num)).intervalIntegrable)
      ((PsiR_cont (by norm_num) (by norm_num) (by norm_num)).intervalIntegrable)
  have hA : ∫ y in (0:ℝ)..(71/200), PsiR y ≤ c1 + c2 := by
    rw [← e1]; exact add_le_add i0 i1
  have hB : ∫ y in (71/200:ℝ)..(71/100), PsiR y ≤ c3 + c4 := by
    rw [← e2]; exact add_le_add i2 i3
  have hC : ∫ y in (0:ℝ)..(71/100), PsiR y ≤ c1 + c2 + c3 + c4 := by
    rw [← e3]; simpa [add_assoc] using add_le_add hA hB
  have hnum : c1 + c2 + c3 + c4 ≤ 3/5 := by rw [hc1, hc2, hc3, hc4]; norm_num
  linarith [hExt, hC, hnum]

/-! ## The target theorem -/

theorem integral_l2_rpow_eighth_bound_half :
    ∫ x in Set.Ioc (1:ℝ) (Real.sqrt 2),
        (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2)))
          * (Real.sqrt x)⁻¹
      ≤ 0.6 := by
  have hle : (1:ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  rw [← intervalIntegral.integral_of_le hle]
  change ∫ x in (1:ℝ)..(Real.sqrt 2), Fint x ≤ 0.6
  have hderiv : ∀ x ∈ Set.Ioo (min 0 R) (max 0 R), HasDerivAt Gg (Gg' x) x := by
    intro x hx
    rw [min_eq_left R_pos.le, max_eq_right R_pos.le] at hx
    exact Gg_deriv x (by nlinarith [R_sq, sq_nonneg x, le_of_lt hx.1, hx.2])
  have hnn : ∀ x ∈ Set.Ioo (min 0 R) (max 0 R), 0 ≤ Gg' x := by
    intro x hx
    rw [min_eq_left R_pos.le, max_eq_right R_pos.le] at hx
    exact Gg_nn x hx
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f:=Gg) (f':=Gg')
      (g:=Fint) (a:=0) (b:=R) Gg_cont hderiv hnn
  rw [Gg_zero, Gg_R] at hsub
  rw [← hsub]
  have hcongr : ∫ y in (0:ℝ)..R, (Fint ∘ Gg) y * Gg' y = ∫ y in (0:ℝ)..R, Psi y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le R_pos.le] at hy
    exact Fint_Gg y hy.1 (by nlinarith [R_sq, hy.1, hy.2, sq_nonneg y])
  rw [hcongr]
  have hPS : ∫ y in (0:ℝ)..R, Psi y = ∫ y in (0:ℝ)..R, PsiR y :=
    intervalIntegral.integral_congr (fun y _ => Psi_eq_PsiR y)
  rw [hPS]
  linarith [integral_psi_bound]

end Commons.Analysis.Integral