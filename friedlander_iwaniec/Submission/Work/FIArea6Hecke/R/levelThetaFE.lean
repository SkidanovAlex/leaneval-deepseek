import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea6Hecke.R.levelHeckeDefs
import Submission.Work.FIArea6Hecke.R.levCutFacts
import Submission.Work.FIArea6Hecke.R.levLowConv
import Submission.Work.FIArea6Hecke.R.levLowMellin
import Submission.Work.FIArea6Hecke.R.levMellinSplit
import Submission.Work.FIArea6Hecke.R.levXiReflect
import Submission.Work.FIArea6Hecke.R.thetaHol_meas_li

set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped ComplexConjugate Topology

noncomputable section

open Work.FIArea5.S16Hecke

/-! ## Auxiliary computations -/

/-- The `π`-bookkeeping of the Mellin identity at scale `R`:
`(√R)^s π^{m/2} π^{-(s+m/2)} = (√R/π)^s`. -/
lemma levelPiBoot (R : ℝ) (m : ℕ) (s : ℂ) :
    (((Real.sqrt R : ℝ)) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
        ((Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2))) =
      (((Real.sqrt R / Real.pi : ℝ)) : ℂ) ^ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * ((Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)))
      = (Real.pi : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have h2 : (((Real.sqrt R / Real.pi : ℝ)) : ℂ) ^ s
      = (((Real.sqrt R : ℝ)) : ℂ) ^ s * (Real.pi : ℂ) ^ (-s) := by
    rw [show (((Real.sqrt R / Real.pi : ℝ)) : ℂ) =
        (((Real.sqrt R : ℝ)) : ℂ) * (((Real.pi⁻¹ : ℝ)) : ℂ) by
      rw [Complex.ofReal_div, Complex.ofReal_inv, div_eq_mul_inv]]
    rw [Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg R) (le_of_lt (inv_pos.mpr Real.pi_pos))]
    rw [show (((Real.pi⁻¹ : ℝ)) : ℂ) ^ s = ((Real.pi : ℂ) ^ s)⁻¹ by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _
        (by rw [Complex.arg_ofReal_of_nonneg (le_of_lt Real.pi_pos)]; exact Real.pi_ne_zero.symm)]]
    rw [Complex.cpow_neg]
  rw [h2]
  rw [mul_assoc, h1]

/-- The scaling identity behind the reflection: `(√R)^s R^{m+1-(s+m/2)} = (√R)^{m+1}(√R)^{1-s}`. -/
lemma levelSqrtRCpowMul (R : ℝ) (hR : 0 < R) (m : ℕ) (s : ℂ) :
    (((Real.sqrt R : ℝ)) : ℂ) ^ s * (R : ℂ) ^ ((m : ℂ) + 1 - (s + (m : ℂ) / 2)) =
      (((Real.sqrt R : ℝ)) : ℂ) ^ (m + 1) * (((Real.sqrt R : ℝ)) : ℂ) ^ (1 - s) := by
  have hS : (((Real.sqrt R : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hR).ne'
  have hRz : (R : ℂ) ^ ((m : ℂ) + 1 - (s + (m : ℂ) / 2))
      = (((Real.sqrt R : ℝ)) : ℂ) ^ ((m : ℂ) + 2 - 2 * s) := by
    rw [show (R : ℂ) = (((Real.sqrt R)^2 : ℝ) : ℂ) by rw [Real.sq_sqrt hR.le]]
    rw [ofReal_sq_cpow (Real.sqrt R) (Real.sqrt_nonneg R)]
    congr 1
    push_cast
    ring
  rw [hRz]
  have step1 : (((Real.sqrt R : ℝ)) : ℂ) ^ s * (((Real.sqrt R : ℝ)) : ℂ) ^ ((m : ℂ) + 2 - 2 * s)
      = (((Real.sqrt R : ℝ)) : ℂ) ^ (s + ((m : ℂ) + 2 - 2 * s)) := by
    rw [Complex.cpow_add _ _ hS]
  rw [step1, show s + ((m : ℂ) + 2 - 2 * s) = ((m : ℂ) + 1) + (1 - s) by ring,
    Complex.cpow_add _ _ hS]
  congr 1
  rw [show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]

/-- The Mellin identity of `mellin_thetaHol`, written with `mellin`. -/
lemma levelMellinForm {chi : GaussianInt → ℂ} {m : ℕ} (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
      mellin (thetaHol chi m) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
        heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2) := by
  intro s hs
  rw [mellin]
  rw [← mellin_thetaHol chi m hb hs]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [smul_eq_mul]; ring

/-- Twice the theta law: if the theta series is not identically zero, then
`A·conj A·R^{m+1} = 1`. -/
lemma levelConstOfLaw (R : ℝ) (hR : 0 < R) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → f u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (f (1 / (R * u))))
    (hne : ∃ u : ℝ, 0 < u ∧ f u ≠ 0) :
    A * star A * ((R : ℂ) ^ ((m : ℂ) + 1)) = 1 := by
  obtain ⟨u, hu, hu0⟩ := hne
  set v : ℝ := 1 / (R * u) with hvdef
  have hv : 0 < v := by rw [hvdef]; positivity
  have hvu : 1 / (R * v) = u := by rw [hvdef]; field_simp
  have huv : u * v = 1 / R := by rw [hvdef]; field_simp
  have h1 := hlaw u hu
  have h2 := hlaw v hv
  rw [hvu] at h2
  have h3 : star (f v) = star A * ((v : ℂ) ^ (-(m : ℤ) - 1)) * f u := by
    rw [h2, star_mul, star_mul, star_star, star_ofReal_zpow]
    ring
  have h4 : f u = A * star A *
          (((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))) * f u := by
    calc f u
        = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (f v) := h1
      _ = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
            (star A * ((v : ℂ) ^ (-(m : ℤ) - 1)) * f u) := by rw [h3]
      _ = A * star A *
            (((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))) * f u := by ring
  have hreal : u ^ (-(m : ℤ) - 1) * v ^ (-(m : ℤ) - 1) = R ^ (m + 1) := by
    rw [← mul_zpow, huv, one_div, inv_zpow, ← zpow_neg]
    rw [show (-(-(m : ℤ) - 1)) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hpow : ((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))
      = (((R) ^ (m + 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_zpow, ← Complex.ofReal_zpow, ← Complex.ofReal_mul, hreal]
  have h5 : (A * star A * (((R) ^ (m + 1) : ℝ) : ℂ)) * f u = 1 * f u := by
    rw [← hpow, ← h4]; ring
  have h6 := mul_right_cancel₀ hu0 h5
  rw [show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
  rw [Complex.ofReal_pow] at h6
  exact h6

/-- On the whole plane, `Ξ` agrees with the Mellin transform of `f`. -/
lemma levelXi_eq_mellin (R : ℝ) (hR : 0 < R) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → f u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (f (1 / (R * u))))
    (hmeas : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hli : MeasureTheory.LocallyIntegrableOn f (Set.Ioi (0 : ℝ)))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ‖f u‖ ≤ C * Real.exp (-Real.pi * u)) :
    ∀ t : ℂ, thetaXi R f m A t = mellin f t := by
  intro t
  obtain ⟨hconvHi, hconvStar, _hAan, _hEan⟩ := levCutFacts R hR f m hmeas hli hdec
  have hconvLo : MellinConvergent (thetaCutLo R f) t :=
    levLowConv R hR f m A hlaw t (hconvStar ((m : ℂ) + 1 - t))
  have hsplit := levMellinSplit R hR f t hconvLo (hconvHi t)
  rw [hsplit, levLowMellin R hR f m A hlaw t]
  simp only [thetaXi, thetaA, thetaE]
  ring

/-- The agreement of `thetaLam` with `(√R/π)^s Γ(s+m/2) L(s)` on the half-plane
`re s > 1 + m/2`. -/
lemma levelLam_eq (R : ℝ) (hR : 0 < R) (chi : GaussianInt → ℂ) (m : ℕ) (A : ℂ)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hlaw : ∀ u : ℝ, 0 < u → thetaHol chi m u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (thetaHol chi m (1 / (R * u))))
    (hmeas : AEMeasurable (thetaHol chi m) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hli : MeasureTheory.LocallyIntegrableOn (thetaHol chi m) (Set.Ioi (0 : ℝ)))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖thetaHol chi m u‖ ≤ C * Real.exp (-Real.pi * u)) :
    ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
      thetaLam R (thetaHol chi m) m A s = ((Real.sqrt R / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + (m : ℂ) / 2) * heckeLSeries chi (m : ℤ) s := by
  intro s hs
  have ht : 1 + (m : ℝ) / 2 < (s + (m : ℂ) / 2).re := by
    have hre : (s + (m : ℂ) / 2).re = s.re + (m : ℝ) / 2 := by
      rw [Complex.add_re, show (m : ℂ) / 2 = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [hre]; linarith [show (0 : ℝ) ≤ (m : ℝ) / 2 by positivity]
  have hXi := levelXi_eq_mellin R hR (thetaHol chi m) m A hlaw hmeas hli hdec (s + (m : ℂ) / 2)
  have hmell := levelMellinForm (chi := chi) (m := m) hb (s + (m : ℂ) / 2) ht
  rw [thetaLam, hXi, hmell]
  rw [show s + (m : ℂ) / 2 - (m : ℂ) / 2 = s by ring]
  rw [show ((Real.sqrt R : ℝ) : ℂ) ^ s * (Real.pi : ℂ) ^ ((m : ℂ) / 2) *
        (Complex.Gamma (s + (m : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) *
          heckeLSeries chi (m : ℤ) s) =
      ((((Real.sqrt R : ℝ)) : ℂ) ^ s * (Real.pi : ℂ) ^ ((m : ℂ) / 2) *
        (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2))) *
        (Complex.Gamma (s + (m : ℂ) / 2) * heckeLSeries chi (m : ℤ) s) by ring]
  rw [levelPiBoot R m s]
  ring

/-- The functional equation of `thetaLam`. -/
lemma levelLam_fe (R : ℝ) (hR : 0 < R) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hconst : A * star A * ((R : ℂ) ^ ((m : ℂ) + 1)) = 1) :
    ∀ s : ℂ, thetaLam R f m A s =
      (A * (((Real.sqrt R : ℝ)) : ℂ) ^ (m + 1)) * star (thetaLam R f m A (star (1 - s))) := by
  intro s
  have hpiStar : star ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) = (Real.pi : ℂ) ^ ((m : ℂ) / 2) := by
    have hcast : (((m : ℝ) / 2 : ℝ) : ℂ) = (m : ℂ) / 2 := by push_cast; ring
    have h := Complex.ofReal_cpow (x := Real.pi) (le_of_lt Real.pi_pos) ((m : ℝ) / 2)
    rw [hcast] at h
    rw [Complex.star_def, ← h, Complex.conj_ofReal]
  have hsqrtStar : star ((((Real.sqrt R : ℝ)) : ℂ) ^ (star (1 - s)))
      = (((Real.sqrt R : ℝ)) : ℂ) ^ (1 - s) := by
    rw [star_thetaB_cpow (Real.sqrt_nonneg R) (star (1 - s))]
    congr 1
    simp
  have hrefl := levXiReflect R hR f m A hconst (s + (m : ℂ) / 2)
  have harg : (m : ℂ) + 1 - star (s + (m : ℂ) / 2) = star (1 - s) + (m : ℂ) / 2 := by
    have h1 : star (s + (m : ℂ) / 2) = star s + (m : ℂ) / 2 := by
      rw [star_add]
      congr 1
      rw [show (m : ℂ) / 2 = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring]
      simp
    have h2 : star (1 - s) = 1 - star s := by simp
    rw [h1, h2]; ring
  rw [harg] at hrefl
  have hstarval : star (thetaLam R f m A (star (1 - s)))
      = (((Real.sqrt R : ℝ)) : ℂ) ^ (1 - s) * ((Real.pi : ℂ) ^ ((m : ℂ) / 2) *
          star (thetaXi R f m A (star (1 - s) + (m : ℂ) / 2))) := by
    rw [thetaLam, star_mul, star_mul, hpiStar, hsqrtStar]
    ring
  calc thetaLam R f m A s
      = ((((Real.sqrt R : ℝ)) : ℂ) ^ s * (Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
          (A * (R : ℂ) ^ ((m : ℂ) + 1 - (s + (m : ℂ) / 2)) *
            star (thetaXi R f m A (star (1 - s) + (m : ℂ) / 2))) := by
        rw [thetaLam, hrefl]
    _ = (A * (((Real.sqrt R : ℝ)) : ℂ) ^ (m + 1)) *
          ((((Real.sqrt R : ℝ)) : ℂ) ^ (1 - s) * ((Real.pi : ℂ) ^ ((m : ℂ) / 2) *
            star (thetaXi R f m A (star (1 - s) + (m : ℂ) / 2)))) := by
        rw [show ((((Real.sqrt R : ℝ)) : ℂ) ^ s * (Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
              (A * (R : ℂ) ^ ((m : ℂ) + 1 - (s + (m : ℂ) / 2)) *
                star (thetaXi R f m A (star (1 - s) + (m : ℂ) / 2)))
            = ((((Real.sqrt R : ℝ)) : ℂ) ^ s * (R : ℂ) ^ ((m : ℂ) + 1 - (s + (m : ℂ) / 2))) *
              (A * (Real.pi : ℂ) ^ ((m : ℂ) / 2) *
                star (thetaXi R f m A (star (1 - s) + (m : ℂ) / 2))) by ring]
        rw [levelSqrtRCpowMul R hR m s]
        ring
    _ = (A * (((Real.sqrt R : ℝ)) : ℂ) ^ (m + 1)) * star (thetaLam R f m A (star (1 - s))) := by
        rw [hstarval]

/-! ## The theorem -/

theorem levelThetaFE (R : ℝ) (hR : 0 < R) (chi : GaussianInt → ℂ) (m : ℕ) (A : ℂ) (hA : A ≠ 0)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hlaw : ∀ u : ℝ, 0 < u → Work.FIArea5.S16Hecke.thetaHol chi m u =
        A * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (Work.FIArea5.S16Hecke.thetaHol chi m (1 / (R * u)))) :
    ∃ (Lam : ℂ → ℂ) (W : ℂ), W ≠ 0 ∧ AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
        Lam s = ((Real.sqrt R / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma (s + (m : ℂ) / 2) *
          Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s) ∧
      (∀ s : ℂ, Lam s = W * star (Lam (star (1 - s)))) := by
  by_cases hzero : ∀ u : ℝ, 0 < u → thetaHol chi m u = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, analyticOn_const, ?_, ?_⟩
    · intro s hs
      have hL : heckeLSeries chi (m : ℤ) s = 0 :=
        L_eq_zero_of_theta_eq_zero (levelMellinForm (chi := chi) (m := m) hb) hzero s hs
      rw [hL, mul_zero]
    · intro s; simp
  · push_neg at hzero
    obtain ⟨u₀, hu₀, hu₀ne⟩ := hzero
    obtain ⟨hmeas, hli⟩ := thetaHol_meas_li hb
    have hsum : Summable (fun z : GaussianInt => thetaSummand chi m u₀ z) := by
      by_contra h
      exact hu₀ne (by rw [thetaHol_eq_tsum, tsum_eq_zero_of_not_summable h])
    obtain ⟨C, _hC0, hC⟩ := thetaHol_bound_of_summable chi m hu₀ hsum
    have hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖thetaHol chi m u‖ ≤ C * Real.exp (-Real.pi * u) :=
      ⟨C * Real.exp (Real.pi * u₀), u₀, hu₀, fun u hu => by
        refine le_trans (hC u hu) (le_of_eq ?_)
        rw [mul_assoc, ← Real.exp_add]; congr 1; ring⟩
    have hne : ∃ u : ℝ, 0 < u ∧ thetaHol chi m u ≠ 0 := ⟨u₀, hu₀, hu₀ne⟩
    have hconst := levelConstOfLaw R hR (thetaHol chi m) m A hlaw hne
    refine ⟨thetaLam R (thetaHol chi m) m A,
      A * (((Real.sqrt R : ℝ)) : ℂ) ^ (m + 1), ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero hA
        (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hR).ne'))
    · obtain ⟨_, _, hAan, hEan⟩ := levCutFacts R hR (thetaHol chi m) m hmeas hli hdec
      refine analyticOn_thetaLam R hR _ m A ?_
      refine hAan.add ?_
      exact ((analyticOn_const (v := A)).mul
        (analyticOn_const_cpow_affine (R : ℂ) (Complex.ofReal_ne_zero.mpr hR.ne') m)).mul hEan
    · exact levelLam_eq R hR chi m A hb hlaw hmeas hli hdec
    · exact levelLam_fe R hR (thetaHol chi m) m A hconst

end

end Work.FIArea6Hecke.R
