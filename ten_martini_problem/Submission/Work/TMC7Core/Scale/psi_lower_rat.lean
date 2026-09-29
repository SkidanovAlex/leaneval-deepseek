import Mathlib
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.iterC_qpow
import Submission.Work.TMComp.LocCantor.defect_upper
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMC7Core.Scale.rat_excess_decay_of_hyperbolic

/-!
# The lower bound on the doubling defect at a rational frequency

For `α = p/q` and `N = m q`,

`-(log 2)/N ≤ lyap α lam E + L_N - 2 L_{2N}`.

The point is the classical doubling estimate for a real unimodular `2×2` matrix `A`
(`LocCantor.defect_upper`):

`log ‖A^{2m}‖_F ≤ log 2 + log ‖A^m‖_F + m log (rhoSL (tr A))`.

Applied to the real `q`-block `A(x) = iterR (p/q) lam E q x` and integrated over `[0,1]`
this gives exactly the claim, using `‖A(x)^k‖_F = ‖A_{kq}(x)‖_F` and
`lyap = (1/q) ∫ log (rhoSL (tr A(x)))`.
-/

namespace Work.TMC7Core.Scale

open MeasureTheory

theorem psi_lower_rat (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    -(Real.log 2) / ((m * q : ℕ) : ℝ) ≤
      lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
        + lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
        - 2 * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hmqR : (0 : ℝ) < ((m * q : ℕ) : ℝ) := by
    have : 0 < m * q := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hmqne : ((m * q : ℕ) : ℝ) ≠ 0 := ne_of_gt hmqR
  have h2mqR : (0 : ℝ) < ((2 * (m * q) : ℕ) : ℝ) := by
    have : 0 < 2 * (m * q) := by positivity
    exact_mod_cast this
  have h2mqne : ((2 * (m * q) : ℕ) : ℝ) ≠ 0 := ne_of_gt h2mqR
  -- the three integrands
  set g1 : ℝ → ℝ := fun x => Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)) with hg1
  set g2 : ℝ → ℝ := fun x => Real.log (frob (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q)) x)) with hg2
  set g3 : ℝ → ℝ := fun x => Real.log (rhoSL ((iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace).re) with hg3
  -- pointwise doubling inequality
  have hpt : ∀ x : ℝ, -(Real.log 2) ≤ (m : ℝ) * g3 x + g1 x - g2 x := by
    intro x
    set Ar : Matrix (Fin 2) (Fin 2) ℝ := Solutions.iterR ((p : ℝ) / (q : ℝ)) lam E q x with hAr
    have hmap : Ar.map Complex.ofRealHom = iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x := by
      rw [hAr]; exact (Solutions.iterC_eq_map _ _ _ q x).symm
    have hdet : Ar.det = 1 := by
      have h := RingHom.map_det Complex.ofRealHom Ar
      rw [RingHom.mapMatrix_apply] at h
      rw [hmap, det_iterC] at h
      exact Complex.ofReal_inj.mp h
    have htr : Ar.trace = (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace.re := by
      have h := Solutions.trace_map_ofReal Ar
      rw [hmap] at h
      have h2 : (iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace.re = Ar.trace := by
        rw [h, Complex.ofReal_re]
      exact h2.symm
    have hpow_m : (Ar.map Complex.ofRealHom) ^ m
        = iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x := by
      rw [hmap, show m * q = q * m from Nat.mul_comm m q]
      exact (Solutions.iterC_qpow p q hq lam E m x).symm
    have hpow_2m : (Ar.map Complex.ofRealHom) ^ (2 * m)
        = iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q)) x := by
      rw [hmap, show 2 * (m * q) = q * (2 * m) from by ring]
      exact (Solutions.iterC_qpow p q hq lam E (2 * m) x).symm
    have hdu := Work.TMComp.LocCantor.defect_upper Ar hdet m hm
    rw [hpow_2m, hpow_m, htr] at hdu
    simp only [hg1, hg2, hg3]
    linarith
  -- continuity of the integrands
  have hc1 : Continuous g1 := by
    rw [hg1]; exact Work.TMC7Core.Lyap.continuous_log_frob_iterC _ _ _ _
  have hc2 : Continuous g2 := by
    rw [hg2]; exact Work.TMC7Core.Lyap.continuous_log_frob_iterC _ _ _ _
  have hc3 : Continuous g3 := by
    rw [hg3]; exact continuous_log_rhoSL_iterC' _ _ _ _
  -- integrate the pointwise bound
  have hmono : (∫ x in (0 : ℝ)..1, (-(Real.log 2) : ℝ))
      ≤ ∫ x in (0 : ℝ)..1, ((m : ℝ) * g3 x + g1 x - g2 x) := by
    refine intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (continuous_const.intervalIntegrable 0 1) ?_ (fun x _ => hpt x)
    exact (((hc3.const_mul (m : ℝ)).add hc1).sub hc2).intervalIntegrable 0 1
  have hconst : (∫ x in (0 : ℝ)..1, (-(Real.log 2) : ℝ)) = -(Real.log 2) := by
    rw [intervalIntegral.integral_const]; simp
  have hInt_rhs : (∫ x in (0 : ℝ)..1, ((m : ℝ) * g3 x + g1 x - g2 x))
      = (m : ℝ) * (∫ x in (0 : ℝ)..1, g3 x) + (∫ x in (0 : ℝ)..1, g1 x)
        - (∫ x in (0 : ℝ)..1, g2 x) := by
    have hi1 : IntervalIntegrable g1 volume (0 : ℝ) 1 := hc1.intervalIntegrable 0 1
    have hi2 : IntervalIntegrable g2 volume (0 : ℝ) 1 := hc2.intervalIntegrable 0 1
    have hi3 : IntervalIntegrable (fun x : ℝ => (m : ℝ) * g3 x) volume (0 : ℝ) 1 :=
      (hc3.const_mul (m : ℝ)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub (hi3.add hi1) hi2,
      intervalIntegral.integral_add hi3 hi1, intervalIntegral.integral_const_mul (m : ℝ) g3]
  rw [hconst, hInt_rhs] at hmono
  -- identify the integrals
  have hlyap : lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      = (1 / (q : ℝ)) * (∫ x in (0 : ℝ)..1, g3 x) := by
    rw [Solutions.lyap_periodic p q hq lam E]
  have hI3 : (∫ x in (0 : ℝ)..1, g3 x) = (q : ℝ) * lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ) := by
    rw [hlyap, ← mul_assoc, mul_one_div, div_self hqne, one_mul]
  have hL1 : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
      = (∫ x in (0 : ℝ)..1, g1 x) / ((m * q : ℕ) : ℝ) := by
    simp only [lyapAvg, hg1]
  have hL2 : lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q))
      = (∫ x in (0 : ℝ)..1, g2 x) / ((2 * (m * q) : ℕ) : ℝ) := by
    simp only [lyapAvg, hg2]
  have hI1 : (∫ x in (0 : ℝ)..1, g1 x)
      = ((m * q : ℕ) : ℝ) * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) := by
    rw [hL1]; exact (mul_div_cancel₀ _ hmqne).symm
  have hI2 : (∫ x in (0 : ℝ)..1, g2 x)
      = ((2 * (m * q) : ℕ) : ℝ) * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q)) := by
    rw [hL2]; exact (mul_div_cancel₀ _ h2mqne).symm
  -- combine
  have hcomb : (m : ℝ) * (∫ x in (0 : ℝ)..1, g3 x) + (∫ x in (0 : ℝ)..1, g1 x)
        - (∫ x in (0 : ℝ)..1, g2 x)
      = ((m * q : ℕ) : ℝ) * (lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
          + lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
          - 2 * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q))) := by
    rw [hI3, hI1, hI2]
    have hcast : ((m * q : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by push_cast; ring
    have hcast2 : ((2 * (m * q) : ℕ) : ℝ) = 2 * ((m * q : ℕ) : ℝ) := by push_cast; ring
    rw [hcast2, hcast]
    ring
  have hfin : -(Real.log 2) ≤ ((m * q : ℕ) : ℝ) * (lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
          + lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
          - 2 * lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * (m * q))) := hcomb ▸ hmono
  rw [div_le_iff₀ hmqR, mul_comm]
  exact hfin

end Work.TMC7Core.Scale
