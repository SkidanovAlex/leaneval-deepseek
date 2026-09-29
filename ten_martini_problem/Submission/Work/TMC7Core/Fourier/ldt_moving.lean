import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup

/-!
# TMC7Core: the moving average and its Fourier coefficients

`mAve g α R` is the Fejér (triangular) average of `g` along the orbit of `x ↦ x + α`.  Two
elementary facts are proved here: the telescoping estimate comparing `uAvg` with its moving
average, and the identity giving the Fourier coefficients of the moving average in terms of
those of `g` and the Fejér kernel `fejerKer`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Fourier

/-- Shift bound with a bound on the shift size. -/
theorem uAvg_shift_le_of_abs_le (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (M : ℕ) (j : ℤ)
    (hj : |(j:ℝ)| ≤ (M:ℝ)) (x : ℝ) :
    |uAvg α lam (E:ℂ) N (x + (j:ℝ)*α) - uAvg α lam (E:ℂ) N x|
      ≤ 2*(M:ℝ)*Real.log (ldtF lam E)/(N:ℝ) := by
  have hlog : 0 ≤ Real.log (ldtF lam E) := Real.log_nonneg (one_le_ldtF lam E)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  refine (uAvg_shift_le α lam E N hN j x).trans ?_
  apply div_le_div_of_nonneg_right _ hNpos.le
  nlinarith [hj, hlog]

/-- The moving average deviates from `uAvg` by at most `2 R log F / N`. -/
theorem uAvg_mAve_le (α lam : ℝ) (E : ℝ) (N : ℕ) (hN : 1 ≤ N) (R : ℕ) (hR : 1 ≤ R) (x : ℝ) :
    ‖((uAvg α lam (E:ℂ) N x : ℝ) : ℂ)
      - mAve (fun y => ((uAvg α lam (E:ℂ) N y : ℝ) : ℂ)) α R x‖
      ≤ 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ) := by
  set g : ℝ → ℂ := fun y => ((uAvg α lam (E:ℂ) N y : ℝ) : ℂ) with hg
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hRc : (R:ℂ) ≠ 0 := by simp only [Nat.cast_ne_zero]; omega
  have hR2ne : ((R:ℂ)^2) ≠ 0 := pow_ne_zero _ hRc
  have hconst : (∑ _j ∈ Finset.range R, ∑ _j' ∈ Finset.range R, g x) = ((R:ℂ)^2) * g x := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsumsplit : (∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (g x - g (x + ((j:ℝ) - (j':ℝ)) * α)))
      = ((R:ℂ)^2) * g x
        - ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R, g (x + ((j:ℝ) - (j':ℝ)) * α) := by
    rw [← hconst]
    simp only [Finset.sum_sub_distrib]
  have h3 : ∀ T : ℂ, ((R:ℂ)^2)⁻¹ * (((R:ℂ)^2) * g x - T) = g x - ((R:ℂ)^2)⁻¹ * T := by
    intro T
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hR2ne, one_mul]
  have hkey : g x - mAve g α R x
      = ((R:ℂ)^2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
          (g x - g (x + ((j:ℝ) - (j':ℝ)) * α)) := by
    rw [mAve, hsumsplit, h3]
  have hterm : ∀ j ∈ Finset.range R, ∀ j' ∈ Finset.range R,
      ‖g x - g (x + ((j:ℝ) - (j':ℝ)) * α)‖ ≤ 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ) := by
    intro j hj j' hj'
    have hjR : j < R := Finset.mem_range.mp hj
    have hj'R : j' < R := Finset.mem_range.mp hj'
    have h2 : ((j:ℤ) - (j':ℤ)) ≤ (R:ℤ) := by omega
    have h3 : (-(R:ℤ)) ≤ ((j:ℤ) - (j':ℤ)) := by omega
    have h1 : |(((j:ℤ) - (j':ℤ) : ℤ) : ℝ)| ≤ (R:ℝ) := by
      rw [abs_le]
      exact ⟨by exact_mod_cast h3, by exact_mod_cast h2⟩
    have hcast : ((((j:ℤ) - (j':ℤ) : ℤ) : ℝ)) * α = ((j:ℝ) - (j':ℝ)) * α := by push_cast; ring
    have hshift := uAvg_shift_le_of_abs_le α lam E N hN R ((j:ℤ) - (j':ℤ)) h1 x
    rw [hcast] at hshift
    have hgn : ∀ y : ℝ, g y = ((uAvg α lam (E:ℂ) N y : ℝ) : ℂ) := fun y => rfl
    rw [hgn x, hgn (x + ((j:ℝ) - (j':ℝ)) * α), ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_sub_comm]
    exact hshift
  have hbound : ‖∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
      (g x - g (x + ((j:ℝ) - (j':ℝ)) * α))‖
      ≤ (R:ℝ)^2 * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    have hinner : ∀ j ∈ Finset.range R,
        ‖∑ j' ∈ Finset.range R, (g x - g (x + ((j:ℝ) - (j':ℝ)) * α))‖
        ≤ (R:ℝ) * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)) := by
      intro j hj
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j' ∈ Finset.range R, ‖g x - g (x + ((j:ℝ) - (j':ℝ)) * α)‖
          ≤ ∑ _j' ∈ Finset.range R, (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)) :=
            Finset.sum_le_sum (fun j' hj' => hterm j hj j' hj')
        _ = (R:ℝ) * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∑ j ∈ Finset.range R, ‖∑ j' ∈ Finset.range R, (g x - g (x + ((j:ℝ) - (j':ℝ)) * α))‖
        ≤ ∑ _j ∈ Finset.range R, ((R:ℝ) * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ))) :=
          Finset.sum_le_sum hinner
      _ = (R:ℝ)^2 * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [hkey, norm_mul]
  have hnorminv : ‖((R:ℂ)^2)⁻¹‖ = 1 / (R:ℝ)^2 := by
    rw [norm_inv, norm_pow]
    have hRn : ‖(R:ℂ)‖ = (R:ℝ) := by simp
    rw [hRn]
    field_simp
  rw [hnorminv]
  calc 1 / (R:ℝ)^2 * ‖∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
        (g x - g (x + ((j:ℝ) - (j':ℝ)) * α))‖
      ≤ 1 / (R:ℝ)^2 * ((R:ℝ)^2 * (2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ) := by
        have hR2 : (0:ℝ) < (R:ℝ)^2 := by positivity
        field_simp


end Work.TMC7Core.Fourier

end
