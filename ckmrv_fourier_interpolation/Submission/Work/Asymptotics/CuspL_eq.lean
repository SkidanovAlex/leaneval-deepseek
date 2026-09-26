import Mathlib
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Asymptotics.cusp_L_second
import Submission.Work.Asymptotics.GcuspDefs

noncomputable section

open UpperHalfPlane Filter
open scoped Topology

namespace Work.Asymptotics

/-!
# The constant `cuspL ℓ` of the cusp expansion of `𝓛`

`cusp_L_second` provides, for every CKMRV logarithm data `ℓ`, a constant `c` with

  `ℓ.L z = πiz + c - 8E + 12E² + O(‖E‖³)`,   `E = e^{πiz}`,

and `cuspL ℓ` is defined to be that constant.  Since `ℓ.L` is the canonical branch `Lfun`
(`LogLambdaData_L_eq_Lfun`) and `Lfun` has the explicit expansion with `c = 4 log 2`
(`Lfun_second_order`), the constant is forced: two expansions of order `O(‖E‖³)` can
differ only by `O(‖E‖³)`, and `E → 0` along `Im z → ∞`.
-/

/-- The point `(1 + N) i` of the upper half plane. -/
private def zPt (N : ℕ) : ℍ :=
  ⟨((1 + (N : ℝ) : ℝ) : ℂ) * Complex.I, by
    rw [Complex.mul_I_im, Complex.ofReal_re]; positivity⟩

private lemma zPt_coe (N : ℕ) :
    ((zPt N : ℍ) : ℂ) = ((1 + (N : ℝ) : ℝ) : ℂ) * Complex.I := by
  simp [zPt]

private lemma zPt_im (N : ℕ) : (zPt N).im = 1 + (N : ℝ) := by
  show (((zPt N : ℍ) : ℂ)).im = 1 + (N : ℝ)
  rw [zPt_coe, Complex.mul_I_im, Complex.ofReal_re]

private lemma one_le_zPt_im (N : ℕ) : 1 ≤ (zPt N).im := by
  rw [zPt_im]
  have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

private lemma norm_Ept_zPt (N : ℕ) :
    ‖Work.Residues.Ept (zPt N)‖ = Real.exp (-(Real.pi * (1 + (N : ℝ)))) := by
  rw [Work.Residues.Ept_apply, norm_exp_pi_I_mul]
  congr 1
  rw [zPt_coe, Complex.mul_I_im, Complex.ofReal_re]

private lemma exp_neg_pi_succ (N : ℕ) :
    Real.exp (-(Real.pi * (1 + (N : ℝ)))) = Real.exp (-Real.pi) ^ (N + 1) := by
  rw [← Real.exp_nat_mul (-Real.pi) (N + 1)]
  congr 1
  push_cast
  ring

private lemma tendsto_exp_neg_pi :
    Tendsto (fun N : ℕ => Real.exp (-(Real.pi * (1 + (N : ℝ))))) atTop (𝓝 0) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-Real.pi) := Real.exp_nonneg _
  have hr1 : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hpow : Tendsto (fun N : ℕ => Real.exp (-Real.pi) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h1 : Tendsto (fun N : ℕ => Real.exp (-Real.pi) ^ (N + 1)) atTop (𝓝 0) := by
    have h := hpow.mul_const (Real.exp (-Real.pi))
    simp only [zero_mul] at h
    exact h.congr (fun N => by rw [pow_succ])
  exact h1.congr (fun N => (exp_neg_pi_succ N).symm)

/-- The constant of a cusp expansion of order `O(‖E‖³)` is unique: if two constants
satisfy the bound for all `z` with `Im z ≥ 1` then they are equal. -/
private lemma const_eq_of_cusp_bound (c c' : ℂ) (C : ℝ) (_hC : 0 ≤ C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖c - c'‖ ≤ C * ‖Work.Residues.Ept z‖ ^ 3) : c = c' := by
  have hbound : ∀ N : ℕ,
      ‖c - c'‖ ≤ C * Real.exp (-(Real.pi * (1 + (N : ℝ)))) ^ 3 := by
    intro N
    have := h (zPt N) (one_le_zPt_im N)
    rwa [norm_Ept_zPt N] at this
  have hg : Tendsto (fun N : ℕ => C * Real.exp (-(Real.pi * (1 + (N : ℝ)))) ^ 3)
      atTop (𝓝 0) := by
    have h := (tendsto_exp_neg_pi.pow 3).const_mul C
    simpa using h
  have hle : ‖c - c'‖ ≤ 0 := ge_of_tendsto hg (Filter.Eventually.of_forall hbound)
  have hzero : c - c' = 0 := norm_le_zero_iff.mp hle
  exact sub_eq_zero.mp hzero

theorem CuspL_eq (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.cuspL ℓ = 4 * (Real.log 2 : ℂ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Classical.choose_spec (cusp_L_second ℓ)
  obtain ⟨C2, hC2pos, hC2⟩ := Lfun_second_order
  have hbd : ∀ z : ℍ, 1 ≤ z.im →
      ‖4 * (Real.log 2 : ℂ) - Classical.choose (cusp_L_second ℓ)‖
        ≤ (C1 + C2) * ‖Work.Residues.Ept z‖ ^ 3 := by
    intro z hz
    have hA : ‖ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ)
          + Classical.choose (cusp_L_second ℓ) - 8 * Work.Residues.Ept z
          + 12 * (Work.Residues.Ept z) ^ 2)‖ ≤ C1 * ‖Work.Residues.Ept z‖ ^ 3 := hC1 z hz
    have hB : ‖ℓ.L z - (Real.pi : ℂ) * Complex.I * (z : ℂ) - 4 * (Real.log 2 : ℂ)
          + 8 * Work.Residues.Ept z - 12 * (Work.Residues.Ept z) ^ 2‖
        ≤ C2 * ‖Work.Residues.Ept z‖ ^ 3 := by
      have h2 := hC2 (z : ℂ) hz
      rwa [← LogLambdaData_L_eq_Lfun ℓ z, ← Work.Residues.Ept_apply z] at h2
    have hkey : 4 * (Real.log 2 : ℂ) - Classical.choose (cusp_L_second ℓ)
        = (ℓ.L z - ((Real.pi : ℂ) * Complex.I * (z : ℂ)
              + Classical.choose (cusp_L_second ℓ) - 8 * Work.Residues.Ept z
              + 12 * (Work.Residues.Ept z) ^ 2))
          - (ℓ.L z - (Real.pi : ℂ) * Complex.I * (z : ℂ) - 4 * (Real.log 2 : ℂ)
              + 8 * Work.Residues.Ept z - 12 * (Work.Residues.Ept z) ^ 2) := by ring
    rw [hkey]
    refine le_trans (norm_sub_le _ _) ?_
    linarith [hA, hB]
  have hres := const_eq_of_cusp_bound (4 * (Real.log 2 : ℂ))
      (Classical.choose (cusp_L_second ℓ)) (C1 + C2)
      (add_nonneg (le_of_lt hC1pos) (le_of_lt hC2pos)) hbd
  exact (show cuspL ℓ = Classical.choose (cusp_L_second ℓ) from rfl).trans hres.symm

end Work.Asymptotics
