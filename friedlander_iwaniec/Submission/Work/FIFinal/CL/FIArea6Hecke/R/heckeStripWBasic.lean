
/-
# Submission.Work.FIArea6Hecke.R.heckeStripWBasic

Non-vanishing and analyticity of the Phragmén–Lindelöf weight heckeStripW on the strip
1/2 <= re s <= 1.  These are the structural hypotheses of the Phragmén–Lindelöf principle applied
to Lval / heckeStripW.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.lvalLineOneBound
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The base (4d)^20 is positive. -/
lemma fourDpow20_pos (d : ℕ) (hd : 1 ≤ d) : (0 : ℝ) < (4 * (d : ℝ)) ^ (20 : ℕ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  positivity

/-- 4d(z+2) stays at distance at least 10 from the origin on the closed strip
1/2 <= re z <= 1. -/
lemma norm_fourD_mul_add_two_ge (d : ℕ) (hd : 1 ≤ d) {z : ℂ} (h1 : 1 / 2 ≤ z.re) :
    (10 : ℝ) ≤ ‖((4 * (d : ℝ)) : ℂ) * (z + 2)‖ := by
  have h := Complex.abs_re_le_norm (((4 * (d : ℝ)) : ℂ) * (z + 2))
  have hre : (((4 * (d : ℝ)) : ℂ) * (z + 2)).re = 4 * (d : ℝ) * (z.re + 2) := by
    simp [Complex.mul_re]
  rw [hre] at h
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) ≤ 4 * (d : ℝ) * (z.re + 2) := by nlinarith [hd1, h1]
  rw [abs_of_nonneg hpos] at h
  have h10 : (10 : ℝ) ≤ 4 * (d : ℝ) * (z.re + 2) := by nlinarith [hd1, h1]
  linarith

/-- The weight does not vanish on the closed strip 1/2 <= re z <= 1. -/
lemma heckeStripW_ne_zero {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (h0 : 1 / 2 ≤ z.re) (h1 : z.re ≤ 1) :
    heckeStripW d z ≠ 0 := by
  have hbase : ((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fourDpow20_pos d hd)
  have hA : ((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ^ (1 - z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hB : Complex.Gamma (2 - z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have hre : (2 - z / 2).re = 2 - z.re / 2 := by simp
    rw [hre]; linarith
  have hC : Complex.Gamma (1 + z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have hre : (1 + z / 2).re = 1 + z.re / 2 := by simp
    rw [hre]; linarith
  have hD : Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2)) ≠ 0 := by
    intro hlog
    have hre : Real.log ‖((4 * (d : ℝ)) : ℂ) * (z + 2)‖ = 0 := by
      have := congrArg Complex.re hlog
      rwa [Complex.log_re, Complex.zero_re] at this
    have hnorm := norm_fourD_mul_add_two_ge d hd h0
    have h1' : Real.log 10 ≤ Real.log ‖((4 * (d : ℝ)) : ℂ) * (z + 2)‖ :=
      Real.log_le_log (by norm_num) hnorm
    rw [hre] at h1'
    have h2' : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
    linarith
  unfold heckeStripW
  exact mul_ne_zero (mul_ne_zero hA (pow_ne_zero 20 (div_ne_zero hB hC))) (pow_ne_zero 8 hD)

/-- The weight is differentiable on the strip 1/4 <= re z <= 5/4 (in particular on the closed
strip 1/2 <= re z <= 1). -/
lemma heckeStripW_differentiableAt {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (h0 : 1 / 4 ≤ z.re)
    (h1 : z.re ≤ 5 / 4) : DifferentiableAt ℂ (heckeStripW d) z := by
  have hbase : ((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fourDpow20_pos d hd)
  have hA : DifferentiableAt ℂ
      (fun z : ℂ => ((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ^ (1 - z)) z := by
    refine DifferentiableAt.const_cpow (f := fun z : ℂ => 1 - z) ?_ (Or.inl hbase)
    fun_prop
  have hB : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (2 - z / 2)) z := by
    have harg : ∀ k : ℕ, (2 - z / 2) ≠ -(k : ℂ) := by
      intro k hk
      have h1' : (2 - z / 2).re = 2 - z.re / 2 := by simp
      have h2' : (-(k : ℂ)).re = -(k : ℝ) := by simp
      have hk' := congrArg Complex.re hk
      rw [h1', h2'] at hk'
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact (Complex.differentiableAt_Gamma _ harg).comp z (by fun_prop)
  have hC : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (1 + z / 2)) z := by
    have harg : ∀ k : ℕ, (1 + z / 2) ≠ -(k : ℂ) := by
      intro k hk
      have h1' : (1 + z / 2).re = 1 + z.re / 2 := by simp
      have h2' : (-(k : ℂ)).re = -(k : ℝ) := by simp
      have hk' := congrArg Complex.re hk
      rw [h1', h2'] at hk'
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact (Complex.differentiableAt_Gamma _ harg).comp z (by fun_prop)
  have hCnz : Complex.Gamma (1 + z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have h1' : (1 + z / 2).re = 1 + z.re / 2 := by simp
    rw [h1']; linarith
  have hD : DifferentiableAt ℂ
      (fun z : ℂ => Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))) z := by
    refine DifferentiableAt.comp (g := Complex.log)
      (f := fun z : ℂ => (((4 * (d : ℝ)) : ℂ) * (z + 2))) (x := z) ?_ ?_
    · have hz : (((4 * (d : ℝ)) : ℂ) * (z + 2)) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        have hre : (((4 * (d : ℝ)) : ℂ) * (z + 2)).re = 4 * (d : ℝ) * (z.re + 2) := by
          simp [Complex.mul_re]
        rw [hre]
        have hd0 : (0 : ℝ) < (d : ℝ) := by
          have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        nlinarith
      exact Complex.differentiableAt_log hz
    · exact DifferentiableAt.mul (differentiableAt_const _) (by fun_prop)
  unfold heckeStripW
  exact (hA.mul ((hB.div hC hCnz).pow 20)).mul (hD.pow 8)

end

end Work.FIArea6Hecke.R
