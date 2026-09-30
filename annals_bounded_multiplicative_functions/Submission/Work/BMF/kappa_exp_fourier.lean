import Mathlib
import Submission.Work.BMF.parseval.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory intervalIntegral

/-!
# The exponential Fourier transform of the trapezoid weight `κ` on `[0,4]`

`κ` is the trapezoid weight defined in `Submission/Work/BMF/parseval/Defs.lean`:
it equals `w` on `[0,1]`, `1` on `[1,3]`, `4 - w` on `[3,4]` and `0` outside `[0,4]`.
Its exponential Fourier transform on `[0,4]` is elementary:

`∫_0^4 κ(u) e^{Zu} du = (e^{4Z} - e^{3Z} - e^{Z} + 1) / Z^2` for `Z ≠ 0`.

This file proves that identity by splitting the integral at `1` and `3` and applying
the Newton–Leibniz formula with the explicit antiderivatives of `u e^{Zu}`,
`e^{Zu}` and `(4-u) e^{Zu}`.
-/

/-- On `[0,1]`, the trapezoid weight `κ` is the identity. -/
lemma kappa_eq_self_of_mem {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : kappa w = w := by
  unfold kappa; split_ifs <;> linarith

/-- On `[3,4]`, the trapezoid weight `κ` is `w ↦ 4 - w`. -/
lemma kappa_eq_four_sub_of_mem {w : ℝ} (h3 : 3 ≤ w) (h4 : w ≤ 4) : kappa w = 4 - w := by
  unfold kappa; split_ifs <;> linarith

theorem kappa_exp_fourier (Z : ℂ) (hZ : Z ≠ 0) :
    (∫ u in (0:ℝ)..4, ((Work.BMF.kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ)))
      = (Complex.exp (4*Z) - Complex.exp (3*Z) - Complex.exp Z + 1) / Z^2 := by
  have hZ2 : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  -- continuity of the three "nice" integrands, used for interval integrability
  have hg1c : Continuous (fun u : ℝ => (u:ℂ) * Complex.exp (Z * (u:ℂ))) := by fun_prop
  have hg2c : Continuous (fun u : ℝ => Complex.exp (Z * (u:ℂ))) := by fun_prop
  have hg3c : Continuous (fun u : ℝ => ((4:ℂ) - (u:ℂ)) * Complex.exp (Z * (u:ℂ))) := by fun_prop
  -- Step 1: rewrite the integrand `κ u * e^{Zu}` on each of the three pieces
  have h01 : (∫ u in (0:ℝ)..1, ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ)))
      = ∫ u in (0:ℝ)..1, (u:ℂ) * Complex.exp (Z * (u:ℂ)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro u hu
    dsimp only
    rw [kappa_eq_self_of_mem hu.1 hu.2]
  have h13 : (∫ u in (1:ℝ)..3, ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ)))
      = ∫ u in (1:ℝ)..3, Complex.exp (Z * (u:ℂ)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    intro u hu
    dsimp only
    rw [kappa_eq_one hu.1 hu.2]
    simp
  have h34 : (∫ u in (3:ℝ)..4, ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ)))
      = ∫ u in (3:ℝ)..4, ((4:ℂ) - (u:ℂ)) * Complex.exp (Z * (u:ℂ)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 4)]
    intro u hu
    dsimp only
    rw [kappa_eq_four_sub_of_mem hu.1 hu.2]
    push_cast
    ring
  -- Step 2: interval integrability of `κ u * e^{Zu}` on each piece
  have hf01 : IntervalIntegrable
      (fun u : ℝ => ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))) volume (0:ℝ) 1 := by
    refine (hg1c.intervalIntegrable (0:ℝ) 1).congr ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro u hu
    dsimp only
    show (u:ℂ) * Complex.exp (Z * (u:ℂ)) = ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))
    rw [kappa_eq_self_of_mem hu.1.le hu.2]
  have hf13 : IntervalIntegrable
      (fun u : ℝ => ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))) volume (1:ℝ) 3 := by
    refine (hg2c.intervalIntegrable (1:ℝ) 3).congr ?_
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    intro u hu
    dsimp only
    show Complex.exp (Z * (u:ℂ)) = ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))
    rw [kappa_eq_one hu.1.le hu.2]
    simp
  have hf34 : IntervalIntegrable
      (fun u : ℝ => ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))) volume (3:ℝ) 4 := by
    refine (hg3c.intervalIntegrable (3:ℝ) 4).congr ?_
    rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)]
    intro u hu
    dsimp only
    show ((4:ℂ) - (u:ℂ)) * Complex.exp (Z * (u:ℂ)) =
      ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))
    rw [kappa_eq_four_sub_of_mem hu.1.le hu.2]
    push_cast
    ring
  have hf03 : IntervalIntegrable
      (fun u : ℝ => ((kappa u : ℝ) : ℂ) * Complex.exp (Z * (u:ℂ))) volume (0:ℝ) 3 :=
    hf01.trans hf13
  -- Step 3: the three elementary integrals, by Newton–Leibniz
  have hJ1 : (∫ u in (0:ℝ)..1, (u:ℂ) * Complex.exp (Z * (u:ℂ)))
      = ((1:ℂ)/Z - 1/Z^2) * Complex.exp Z + 1/Z^2 := by
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun u : ℝ => ((u:ℂ)/Z - 1/Z^2) * Complex.exp (Z * (u:ℂ)))
          ((x:ℂ) * Complex.exp (Z * (x:ℂ))) x := by
      intro x hx
      have hlin : HasDerivAt (fun u : ℝ => (u:ℂ)) (1:ℂ) x := Complex.ofRealCLM.hasDerivAt
      have hlinZ : HasDerivAt (fun u : ℝ => Z * (u:ℂ)) Z x := by
        simpa using hlin.const_mul Z
      have hexp : HasDerivAt (fun u : ℝ => Complex.exp (Z * (u:ℂ)))
          (Complex.exp (Z * (x:ℂ)) * Z) x :=
        (Complex.hasDerivAt_exp (Z * (x:ℂ))).comp x hlinZ
      have hquo : HasDerivAt (fun u : ℝ => (u:ℂ)/Z - 1/Z^2) (1/Z) x := by
        have h := hlin.div_const Z
        simpa using h.sub_const (1/Z^2)
      have hprod := hquo.mul hexp
      convert hprod using 1
      field_simp
      ring
    have hint : IntervalIntegrable (fun u : ℝ => (u:ℂ) * Complex.exp (Z * (u:ℂ)))
        volume (0:ℝ) 1 := hg1c.intervalIntegrable 0 1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) hd hint
    rw [hftc]
    have e1 : Complex.exp (Z * ((1:ℝ):ℂ)) = Complex.exp Z := by congr 1; push_cast; ring
    have e2 : Complex.exp (Z * ((0:ℝ):ℂ)) = 1 := by
      rw [show Z * ((0:ℝ):ℂ) = 0 by push_cast; ring, Complex.exp_zero]
    rw [e1, e2]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_div]
    field_simp
    ring
  have hJ2 : (∫ u in (1:ℝ)..3, Complex.exp (Z * (u:ℂ)))
      = Complex.exp (3*Z)/Z - Complex.exp Z/Z := by
    have hd : ∀ x ∈ Set.uIcc (1:ℝ) 3,
        HasDerivAt (fun u : ℝ => Complex.exp (Z*(u:ℂ))/Z) (Complex.exp (Z*(x:ℂ))) x := by
      intro x hx
      have hlin : HasDerivAt (fun u : ℝ => (u:ℂ)) (1:ℂ) x := Complex.ofRealCLM.hasDerivAt
      have hlinZ : HasDerivAt (fun u : ℝ => Z*(u:ℂ)) Z x := by simpa using hlin.const_mul Z
      have hexp : HasDerivAt (fun u : ℝ => Complex.exp (Z*(u:ℂ)))
          (Complex.exp (Z*(x:ℂ))*Z) x :=
        (Complex.hasDerivAt_exp (Z*(x:ℂ))).comp x hlinZ
      have h := hexp.div_const Z
      convert h using 1
      rw [mul_div_cancel_right₀ _ hZ]
    have hint : IntervalIntegrable (fun u : ℝ => Complex.exp (Z * (u:ℂ))) volume (1:ℝ) 3 :=
      hg2c.intervalIntegrable 1 3
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (1:ℝ)) (b := 3) hd hint
    rw [hftc]
    have e1 : Complex.exp (Z * ((3:ℝ):ℂ)) = Complex.exp (3*Z) := by congr 1; push_cast; ring
    have e2 : Complex.exp (Z * ((1:ℝ):ℂ)) = Complex.exp Z := by congr 1; push_cast; ring
    rw [e1, e2]
  have hJ3 : (∫ u in (3:ℝ)..4, ((4:ℂ) - (u:ℂ)) * Complex.exp (Z * (u:ℂ)))
      = Complex.exp (4*Z)/Z^2 - (1/Z + 1/Z^2) * Complex.exp (3*Z) := by
    have hd : ∀ x ∈ Set.uIcc (3:ℝ) 4,
        HasDerivAt (fun u : ℝ => (((4:ℂ) - (u:ℂ))/Z + 1/Z^2) * Complex.exp (Z*(u:ℂ)))
          (((4:ℂ) - (x:ℂ)) * Complex.exp (Z*(x:ℂ))) x := by
      intro x hx
      have hlin : HasDerivAt (fun u : ℝ => (u:ℂ)) (1:ℂ) x := Complex.ofRealCLM.hasDerivAt
      have hlinZ : HasDerivAt (fun u : ℝ => Z*(u:ℂ)) Z x := by simpa using hlin.const_mul Z
      have hexp : HasDerivAt (fun u : ℝ => Complex.exp (Z*(u:ℂ)))
          (Complex.exp (Z*(x:ℂ))*Z) x :=
        (Complex.hasDerivAt_exp (Z*(x:ℂ))).comp x hlinZ
      have hnum : HasDerivAt (fun u : ℝ => (4:ℂ) - (u:ℂ)) (-1) x := by
        simpa using hlin.const_sub (4:ℂ)
      have hquo : HasDerivAt (fun u : ℝ => ((4:ℂ) - (u:ℂ))/Z) (-(1/Z)) x := by
        have h := hnum.div_const Z
        simpa [neg_div] using h
      have hc : HasDerivAt (fun u : ℝ => ((4:ℂ) - (u:ℂ))/Z + 1/Z^2) (-(1/Z)) x := by
        simpa using hquo.add_const (1/Z^2)
      have hprod := hc.mul hexp
      convert hprod using 1
      field_simp
      ring
    have hint : IntervalIntegrable (fun u : ℝ => ((4:ℂ) - (u:ℂ)) * Complex.exp (Z * (u:ℂ)))
        volume (3:ℝ) 4 := hg3c.intervalIntegrable 3 4
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (3:ℝ)) (b := 4) hd hint
    rw [hftc]
    have e1 : Complex.exp (Z * ((4:ℝ):ℂ)) = Complex.exp (4*Z) := by congr 1; push_cast; ring
    have e2 : Complex.exp (Z * ((3:ℝ):ℂ)) = Complex.exp (3*Z) := by congr 1; push_cast; ring
    rw [e1, e2]
    norm_num
    ring
  -- Step 4: reassemble the three pieces and simplify
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hf01 hf13
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hf03 hf34
  rw [← hsplit2, ← hsplit1, h01, h13, h34, hJ1, hJ2, hJ3]
  field_simp
  ring

end Work.BMF
