/-
# The quotient of the real parts of two Dedekind zeta functions near `s = 1`

The Dirichlet class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) identifies the residue of `ζ_M` at `s = 1`:

  `(s - 1) * ζ_M(s) → Res_{s=1} ζ_M` as `s → 1⁺` in `ℂ`.

On the real axis `s > 1` the values `ζ_M(s)` are real, so taking real parts we get

  `(s - 1) * Re ζ_M(s) → Res_{s=1} ζ_M` as `s → 1⁺` in `ℝ`.

Since `Res_{s=1} ζ_K > 0` (`NumberField.dedekindZeta_residue_pos`) is non-zero, dividing the
two limits and cancelling the common factor `s - 1` (which is non-zero on `s > 1`) gives the
limit of the quotient
`Re ζ_L(s) / Re ζ_K(s) → Res_{s=1} ζ_L / Res_{s=1} ζ_K`.

This is the analytic input which makes the ratio of the two Dedekind zeta functions converge,
used in the Euler-product comparison of the Čebotarev density chapter.
-/
import Mathlib

open Filter Topology

namespace NK.HeckeL.Nonvanishing

/-- The real parts of a Dedekind zeta function, multiplied by `s - 1`, tend to the residue at
`s = 1` as `s → 1⁺`.  This is the Dirichlet class number formula after taking real parts. -/
theorem tendsto_sub_one_mul_dedekindZeta_re (M : Type*) [Field M] [NumberField M] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta M (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (NumberField.dedekindZeta_residue M)) := by
  have h := (Complex.continuous_re.tendsto
    ((NumberField.dedekindZeta_residue M : ℝ) : ℂ)).comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT M)
  simp only [Complex.ofReal_re] at h
  refine h.congr fun s => ?_
  simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero]

/-- **The quotient of the real parts of the Dedekind zeta functions of `L` and `K` tends to the
quotient of their residues at `s = 1`.** -/
theorem tendsto_dedekindZeta_re_div (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] :
    Filter.Tendsto
      (fun s : ℝ =>
        (NumberField.dedekindZeta L (s : ℂ)).re / (NumberField.dedekindZeta K (s : ℂ)).re)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta_residue L / NumberField.dedekindZeta_residue K)) := by
  have hKpos : NumberField.dedekindZeta_residue K ≠ 0 :=
    ne_of_gt (NumberField.dedekindZeta_residue_pos K)
  refine ((tendsto_sub_one_mul_dedekindZeta_re L).div
    (tendsto_sub_one_mul_dedekindZeta_re K) hKpos).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_Ioi] at hs
  exact mul_div_mul_left _ _ (by linarith : s - 1 ≠ 0)

end NK.HeckeL.Nonvanishing
