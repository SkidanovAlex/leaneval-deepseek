import Mathlib.NumberTheory.NumberField.DedekindZeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.DedekindZeta

open Filter Topology

/-- **The Dedekind zeta function has a simple pole at `s = 1`**, in logarithmic form: for a number
field `K`,
$\log \zeta_K(s) + \log(s-1) \longrightarrow \log\bigl(\mathrm{Res}_{s=1}\zeta_K\bigr)$
as `s → 1⁺`.  Equivalently `log ζ_K(s) = log(1/(s-1)) + O(1)`: this is the input that makes all
Dirichlet density computations work, since it says the total prime-ideal zeta sum
`∑_𝔭 N𝔭^{-s}` grows like `log(1/(s-1))`. -/
theorem tendsto_log_add_log_sub_one (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto
      (fun s : ℝ => Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1))
      (𝓝[>] 1) (𝓝 (Real.log (NumberField.dedekindZeta_residue K))) := by
  have hρ : 0 < NumberField.dedekindZeta_residue K := NumberField.dedekindZeta_residue_pos K
  -- Dirichlet class number formula: `(s - 1) * ζ_K(s) → Res` in `ℂ`.
  have h1 := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  -- Taking real parts.
  have h2 : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re)
      (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    have hcomp :=
      (Complex.continuous_re.tendsto ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)).comp h1
    refine Tendsto.congr (fun s => ?_) hcomp
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re]
  -- Eventually the product is positive, whence the zeta values have positive real part.
  have hg_pos : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      0 < (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re :=
    h2.eventually (Ioi_mem_nhds hρ)
  have hre_pos : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 0 < (NumberField.dedekindZeta K (s : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin, hg_pos] with s hs hg
    have hs1 : 0 < s - 1 := by
      rw [Set.mem_Ioi] at hs; linarith
    exact pos_of_mul_pos_right hg (le_of_lt hs1)
  -- The log identity holds eventually.
  have heq : (fun s : ℝ =>
        Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1))
      =ᶠ[𝓝[>] 1]
      (fun s : ℝ => Real.log ((s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re)) := by
    filter_upwards [self_mem_nhdsWithin, hre_pos] with s hs hre
    have hs1 : 0 < s - 1 := by
      rw [Set.mem_Ioi] at hs; linarith
    rw [mul_comm (s - 1) ((NumberField.dedekindZeta K (s : ℂ)).re),
      Real.log_mul hre.ne' hs1.ne']
  -- Continuity of `log` at the positive residue.
  have hlog : Tendsto (fun s : ℝ => Real.log ((s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re))
      (𝓝[>] 1) (𝓝 (Real.log (NumberField.dedekindZeta_residue K))) :=
    (Real.continuousAt_log hρ.ne').tendsto.comp h2
  exact hlog.congr' heq.symm

end Commons.NumberTheory.NumberField.DedekindZeta