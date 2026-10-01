import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue_pair
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

open Complex Metric MeromorphicOn Filter Topology
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

theorem pfPole_pointwise {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T x : ℝ) (R : ℝ)
    (hR : 0 < R) (hgood : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → u.im ≠ T)
    (hx1 : 0 ≤ x) (hx2 : x ≤ 2) (hsR : ‖(x : ℂ) + Complex.I * (T : ℂ)‖ < R)
    (h2R : ‖(2 : ℂ) + Complex.I * (T : ℂ)‖ < R)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + Complex.I * (T : ℂ)) -
        logDeriv (DirichletCharacter.completedLFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
          ((2 - x) / (‖((x : ℂ) + Complex.I * (T : ℂ)) - u‖ * ‖((2 : ℂ) + Complex.I * (T : ℂ)) - u‖))) +
      ‖(((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ =>
          (deriv (DirichletCharacter.completedLFunction χ) w /
            DirichletCharacter.completedLFunction χ w) *
            (1 / (((x : ℂ) + Complex.I * (T : ℂ)) - w) -
             1 / (((2 : ℂ) + Complex.I * (T : ℂ)) - w))) 0 R)‖ := by
  let f : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let s : ℂ := (x : ℂ) + Complex.I * (T : ℂ)
  let c : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R) u
  let J : ℂ := ((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ => (deriv f w / f w) * (1 / (s - w) - 1 / (c - w))) (0 : ℂ) R
  let A : ℝ := ∑ᶠ u : ℂ, (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖)))
  let S : ℂ := ∑ᶠ u : ℂ, (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))
  change ‖logDeriv f s - logDeriv f c‖ ≤ A + ‖J‖
  have hfdiff : Differentiable ℂ f := by
    dsimp [f]
    exact DirichletCharacter.differentiable_completedLFunction hχ
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    exact Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hfdiff (Metric.closedBall (0 : ℂ) R)
  have hdfin : (Function.support d).Finite := by
    dsimp [d]
    exact Commons.Analysis.Complex.divisor_support_finite_closedBall (f := f) (a := (0 : ℂ)) (ρ := R) hfB
  have d_nonneg : ∀ u : ℂ, 0 ≤ (((d u : ℤ) : ℝ)) := by
    intro u
    dsimp [d]
    exact Commons.Analysis.Complex.divisor_nonneg_on_closedBall hfB u
  have hsIm : s.im = T := by dsimp [s]; simp
  have hcIm : c.im = T := by dsimp [c]; simp
  have hfs : f s ≠ 0 := by
    intro hz
    exact (hgood s (by simpa [f] using hz)) hsIm
  have hfc : f c ≠ 0 := by
    intro hz
    exact (hgood c (by simpa [f] using hz)) hcIm
  have hsR' : ‖s‖ < R := by simpa [s] using hsR
  have hcR' : ‖c‖ < R := by simpa [c] using h2R
  have hcirc' : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0 := by
    intro w hw
    simpa [f] using hcirc w hw
  have hmain : deriv f s / f s - deriv f c / f c = S - J := by
    simpa [f, s, c, d, J, S] using
      (Commons.NumberTheory.Linnik.logDeriv_circle_residue_pair (χ := χ) (hχ := hχ)
        (hχprim := hχprim) (s := s) (c := c) (R := R) (hRpos := hR) (hsR := hsR') (hcR := hcR')
        (hΛs := hfs) (hΛc := hfc) (hcirc := hcirc'))
  have hlog : logDeriv f s - logDeriv f c = deriv f s / f s - deriv f c / f c := by
    rw [logDeriv_apply, logDeriv_apply]
  have heq : logDeriv f s - logDeriv f c = S - J := by
    rw [hlog, hmain]
  have htri : ‖logDeriv f s - logDeriv f c‖ ≤ ‖S‖ + ‖J‖ := by
    rw [heq]
    exact norm_sub_le S J
  -- ‖S‖ ≤ A
  have hSnorm : ‖S‖ ≤ A := by
    let Sd : Finset ℂ := hdfin.toFinset
    have hS_supp : Function.support (fun u : ℂ => (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))) ⊆ (Sd : Set ℂ) := by
      intro u hu
      have hdne : d u ≠ 0 := by
        intro hd0
        have : (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) = 0 := by simp [hd0]
        exact hu this
      exact (hdfin.mem_toFinset).2 hdne
    have hA_supp : Function.support (fun u : ℂ => (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖)))) ⊆ (Sd : Set ℂ) := by
      intro u hu
      have hdne : d u ≠ 0 := by
        intro hd0
        have : (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖))) = 0 := by simp [hd0]
        exact hu this
      exact (hdfin.mem_toFinset).2 hdne
    have hS_fin : S = ∑ u ∈ Sd, (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) := by
      dsimp [S]
      rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))) hS_supp]
    have hA_fin : A = ∑ u ∈ Sd, (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖))) := by
      dsimp [A]
      rw [finsum_eq_sum_of_support_subset (fun u : ℂ => (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖)))) hA_supp]
    have hpoint : ∀ u : ℂ, ‖(((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))‖ ≤
        (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖))) := by
      intro u
      by_cases hdu : d u = 0
      · have hz : ((d u : ℤ) : ℂ) = 0 := by simp [hdu]
        have hzr : ((d u : ℤ) : ℝ) = 0 := by simp [hdu]
        rw [hz, hzr]
        simp
      · have hu_s : u ≠ s := by
          intro hus
          have hfu : f u = 0 := Commons.NumberTheory.Linnik.f_zero_of_divisor_ne_zero hfB (by simpa [d] using hdu)
          exact hfs (by simpa [hus] using hfu)
        have hu_c : u ≠ c := by
          intro huc
          have hfu : f u = 0 := Commons.NumberTheory.Linnik.f_zero_of_divisor_ne_zero hfB (by simpa [d] using hdu)
          exact hfc (by simpa [huc] using hfu)
        have hsu : s - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu_s)
        have hcu : c - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu_c)
        have hcs : c - s = ((2 - x : ℝ) : ℂ) := by
          dsimp [c, s]
          rw [Complex.ext_iff]
          constructor <;> simp
        have hk : ‖(1 / (s - u) - 1 / (c - u))‖ = (2 - x) / (‖s - u‖ * ‖c - u‖) := by
          calc
            ‖(1 / (s - u) - 1 / (c - u))‖
                = ‖((c - s) / ((s - u) * (c - u)))‖ := by
                    congr 1
                    field_simp [hsu, hcu]
                    ring
            _ = ‖c - s‖ / ‖(s - u) * (c - u)‖ := by rw [norm_div]
            _ = ‖c - s‖ / (‖s - u‖ * ‖c - u‖) := by rw [norm_mul]
            _ = (2 - x) / (‖s - u‖ * ‖c - u‖) := by
                  rw [hcs]
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
                  exact sub_nonneg.mpr hx2
        have hd0 : 0 ≤ d u := by exact_mod_cast d_nonneg u
        have hn_int : ‖((d u : ℤ) : ℂ)‖ = ((d u : ℤ) : ℝ) := by
          rw [Complex.norm_intCast]
          rw [abs_of_nonneg]
          exact_mod_cast hd0
        have heqnorm : ‖(((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))‖ =
            ((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖)) := by
          calc
            ‖(((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))‖
                = ‖((d u : ℤ) : ℂ)‖ * ‖(1 / (s - u) - 1 / (c - u))‖ := norm_mul _ _
            _ = ((d u : ℤ) : ℝ) * ‖(1 / (s - u) - 1 / (c - u))‖ := by rw [hn_int]
            _ = ((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖)) := by rw [hk]
        exact le_of_eq heqnorm
    calc
      ‖S‖ = ‖∑ u ∈ Sd, (((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))‖ := by rw [hS_fin]
      _ ≤ ∑ u ∈ Sd, ‖(((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u)))‖ := norm_sum_le Sd _
      _ ≤ ∑ u ∈ Sd, (((d u : ℤ) : ℝ) * ((2 - x) / (‖s - u‖ * ‖c - u‖))) := Finset.sum_le_sum (fun u hu => hpoint u)
      _ = A := by rw [hA_fin]
  calc
    ‖logDeriv f s - logDeriv f c‖ ≤ ‖S‖ + ‖J‖ := htri
    _ ≤ A + ‖J‖ := add_le_add_left hSnorm ‖J‖

end Commons.NumberTheory.DirichletCharacter
