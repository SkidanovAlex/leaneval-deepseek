/-
# `Work.FIArea5.S16Hecke.heckeFE_of_theta`

Hecke's functional equation for the completed `L`-function of the Grössencharacter
`ψ(z) = χ(z)(z/|z|)^m` of `ℚ(i)`, deduced from the theta transformation law (Friedlander–Iwaniec
§16).  The analytic ingredients are built in `heckeFE_defs` and the auxiliary modules
`mellin_cut_props`, `thetaHol_bound_of_summable`, `thetaCut_low_mellin`,
`mellinConvergent_thetaCutLow`, `mellin_cut_facts`, `heckeXi_reflect_of_const`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.mellin_cut_props
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.integral_inv_scale
import Submission.Work.FIArea5.S16Hecke.cpow_inv_scale
import Submission.Work.FIArea5.S16Hecke.mellin_cut_facts

set_option maxHeartbeats 1000000

namespace Work.FIArea5.S16Hecke

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate Topology
open Work.FIPlan

noncomputable section


/-! ## The master lemma: from the theta law and the cuts to Hecke's functional equation -/

/-- Entireness of `t ↦ B^{m+1-t}`. -/
lemma analyticOn_thetaB_cpow (d : ℕ) (hd : 1 ≤ d) (m : ℕ) :
    AnalyticOn ℂ (fun t : ℂ => (thetaB d : ℂ) ^ ((m : ℂ) + 1 - t)) Set.univ := by
  have hB : (thetaB d : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]; exact ne_of_gt (thetaB_pos hd)
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  intro t _
  exact (DifferentiableAt.const_cpow (c := (thetaB d : ℂ))
      ((differentiableAt_const _).sub differentiableAt_id) (Or.inl hB)).differentiableWithinAt

/-- Entireness of `t ↦ (4d)^t`. -/
lemma analyticOn_fourd_cpow (d : ℕ) (hd : 1 ≤ d) :
    AnalyticOn ℂ (fun t : ℂ => (((4 * d : ℕ)) : ℂ) ^ t) Set.univ := by
  have hB : (((4 * d : ℕ)) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (4 * d : ℕ) ≠ 0)
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  intro t _
  exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hB)).differentiableWithinAt

/-- `(x^2)^z = x^{2z}` for `x ≥ 0` real. -/
lemma ofReal_sq_cpow (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    (((x ^ 2 : ℝ)) : ℂ) ^ z = ((x : ℂ)) ^ (((2 : ℕ) : ℂ) * z) := by
  rw [Complex.ofReal_pow, ← Complex.cpow_natCast]
  rw [← Complex.cpow_mul (x := ((x : ℂ))) (y := ((2 : ℕ) : ℂ)) z]
  · rw [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hx, Complex.natCast_im,
      Complex.natCast_re]
    linarith [Real.pi_pos]
  · rw [Complex.mul_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hx, Complex.natCast_im,
      Complex.natCast_re]
    linarith [Real.pi_pos]

/-- `B^{m+1-t} = (4d)^{2(m+1-t)}`. -/
lemma thetaB_cpow_eq (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (t : ℂ) :
    (thetaB d : ℂ) ^ ((m : ℂ) + 1 - t)
      = (((4 * d : ℕ)) : ℂ) ^ (((2 : ℕ) : ℂ) * ((m : ℂ) + 1 - t)) := by
  have hB : thetaB d = (4 * (d : ℝ)) ^ 2 := by rw [thetaB]; ring
  rw [hB]
  rw [ofReal_sq_cpow (4 * (d : ℝ)) (by positivity)]
  rw [show (((4 * (d : ℝ)) : ℝ) : ℂ) = (((4 * d : ℕ)) : ℂ) by push_cast; ring]

/-- The `π`-bookkeeping of the Mellin identity: `(4d)^s π^{m/2} π^{-(s+m/2)} = ((4d)/π)^s`. -/
lemma fourd_pow_pi_pow (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (s : ℂ) :
    (((4 * d : ℕ)) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
        ((Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2))) = ((((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ)) ^ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * ((Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)))
      = (Real.pi : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have h2 : ((((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ)) ^ s
      = (((4 * d : ℕ)) : ℂ) ^ s * (Real.pi : ℂ) ^ (-s) := by
    rw [show ((((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) *
        (((Real.pi⁻¹ : ℝ)) : ℂ) by
      rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv]; ring]
    rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [show (((Real.pi⁻¹ : ℝ)) : ℂ) ^ s = ((Real.pi : ℂ) ^ s)⁻¹ by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _
        (by rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]
            exact Real.pi_ne_zero.symm)]]
    rw [Complex.cpow_neg]
    rw [show (((4 * (d : ℝ)) : ℝ) : ℂ) = (((4 * d : ℕ)) : ℂ) by push_cast; ring]
  rw [h2]
  rw [mul_assoc, h1]

/-- The `m`-bookkeeping of the theta law in `conj Λ(conj(1-s))`. -/
lemma star_heckeLambda (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ) (U A : ℂ) (s : ℂ) :
    star (heckeLambda d chi m U A (star (1 - s)))
      = (((4 * d : ℕ)) : ℂ) ^ (1 - s) * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
          star (heckeXi d chi m U A ((m : ℂ) + 1 - star (s + (m : ℂ) / 2))) := by
  have hm2 : (m : ℂ) / 2 = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hmm : star ((m : ℂ) / 2) = (m : ℂ) / 2 := by
    rw [hm2, Complex.star_def, Complex.conj_ofReal]
  have harg : star (1 - s) + (m : ℂ) / 2 = (m : ℂ) + 1 - star (s + (m : ℂ) / 2) := by
    rw [star_add, hmm, star_sub, star_one]
    ring
  rw [heckeLambda, harg]
  have h1 : star ((((4 * d : ℕ)) : ℂ) ^ (star (1 - s))) = (((4 * d : ℕ)) : ℂ) ^ (1 - s) := by
    rw [show star ((((4 * d : ℕ)) : ℂ) ^ (star (1 - s)))
        = (starRingEnd ℂ) ((((4 * d : ℕ)) : ℂ) ^ (star (1 - s))) from rfl]
    rw [← Complex.ofReal_natCast (4 * d),
      starRingEnd_cpow_ofReal (u := (((4 * d : ℕ)) : ℝ)) (by positivity) (star (1 - s))]
    rw [← Complex.star_def, star_star]
  have h2 : star ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) = (Real.pi : ℂ) ^ ((m : ℂ) / 2) := by
    rw [hm2, ← Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
    exact Complex.conj_ofReal _
  rw [star_mul, star_mul, h1, h2]
  ring

/-! ## The master lemma -/

/-! ## The zero cases -/

/-- If `thetaHol` vanishes, then so does `heckeA`. -/
lemma heckeA_eq_zero_of_thetaHol_zero (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ)
    (h : ∀ u : ℝ, 0 < u → thetaHol chi m u = 0) (t : ℂ) : heckeA d chi m t = 0 := by
  rw [heckeA, mellin]
  rw [show (∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (t - 1) • thetaCut d chi m u)
      = ∫ u in Set.Ioi (0 : ℝ), (0 : ℂ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
      rw [thetaCut]
      split
      · rw [h u hu, smul_zero]
      · rw [smul_zero])]
  simp

/-- If `thetaHol` vanishes, then so does `heckeE`. -/
lemma heckeE_eq_zero_of_thetaHol_zero (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ)
    (h : ∀ u : ℝ, 0 < u → thetaHol chi m u = 0) (t : ℂ) : heckeE d chi m t = 0 := by
  rw [heckeE, mellin]
  rw [show (∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ ((m : ℂ) + 1 - t - 1) • thetaCutStar d chi m u)
      = ∫ u in Set.Ioi (0 : ℝ), (0 : ℂ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
      rw [thetaCutStar]
      split
      · rw [h u hu, star_zero, smul_zero]
      · rw [smul_zero])]
  simp

/-- If `thetaHol` vanishes, then the Mellin integral of `thetaHol` vanishes. -/
lemma mellin_eq_zero_of_thetaHol_zero (chi : GaussianInt → ℂ) (m : ℕ)
    (h : ∀ u : ℝ, 0 < u → thetaHol chi m u = 0) (t : ℂ) : mellin (thetaHol chi m) t = 0 := by
  rw [mellin]
  rw [show (∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (t - 1) • thetaHol chi m u)
      = ∫ u in Set.Ioi (0 : ℝ), (0 : ℂ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => by rw [h u hu, smul_zero])]
  simp

/-! ## The three cases -/

/-- **The theorem when `heckeLSeries` vanishes on `re > 1`**: `Λ := 0` works. -/
theorem heckeFE_of_theta_of_Lzero (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (U : ℂ) (hU : U ≠ 0) (A : ℂ)
    (hL : ∀ z : ℂ, 1 < z.re → heckeLSeries chi (m : ℤ) z = 0) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s) ∧
      (∀ s : ℂ, Lam s = A * (((4 * d : ℕ)) : ℂ) ^ ((m : ℤ) + 1) * (star U / U) *
          star (Lam (star (1 - s)))) := by
  refine ⟨fun _ => 0, analyticOn_const, ?_, ?_⟩
  · intro s hs
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
    rw [LambdaHecke, hL s (lt_of_le_of_lt (le_add_of_nonneg_right (a := (1 : ℝ)) hm0) hs)]
    simp
  · intro s
    simp

/-- **The theorem when `thetaHol` vanishes**: `Λ := 0` works, using the Mellin identity. -/
theorem heckeFE_of_theta_of_theta_zero (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (U : ℂ) (hU : U ≠ 0) (A : ℂ)
    (hmellin : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
        mellin (thetaHol chi m) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
              heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2))
    (hzero : ∀ u : ℝ, 0 < u → thetaHol chi m u = 0) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → Lam s = LambdaHecke d chi m s) ∧
      (∀ s : ℂ, Lam s = A * (((4 * d : ℕ)) : ℂ) ^ ((m : ℤ) + 1) * (star U / U) *
          star (Lam (star (1 - s)))) := by
  refine ⟨fun _ => 0, analyticOn_const, ?_, ?_⟩
  · intro s hs
    have hm2 : (m : ℂ) / 2 = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    have ht : 1 + (m : ℝ) / 2 < (s + (m : ℂ) / 2).re := by
      have hre : (s + (m : ℂ) / 2).re = s.re + (m : ℝ) / 2 := by simp [Complex.add_re]
      rw [hre]
      exact lt_of_lt_of_le hs (le_add_of_nonneg_right (by positivity))
    rw [LambdaHecke]
    rcases eq_or_ne (Complex.Gamma (s + (m : ℂ) / 2)) 0 with h | h
    · rw [h]
      simp
    · have hm := hmellin (s + (m : ℂ) / 2) ht
      rw [mellin_eq_zero_of_thetaHol_zero chi m hzero] at hm
      have hpi : (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) ≠ 0 := by
        rw [ne_eq, Complex.cpow_eq_zero_iff]
        exact fun hh => Complex.ofReal_ne_zero.mpr Real.pi_ne_zero hh.1
      have hL0 : heckeLSeries chi (m : ℤ) (s + (m : ℂ) / 2 - (m : ℂ) / 2) = 0 := by
        have h0 := hm.symm
        exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero h hpi)
      rw [show s + (m : ℂ) / 2 - (m : ℂ) / 2 = s by ring] at hL0
      rw [hL0, mul_zero]
  · intro s
    rw [star_zero, mul_zero]

end

end Work.FIArea5.S16Hecke
