import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal

namespace Work.FIArea6Hecke.R

/-- **Self-duality forces the weight `m` to vanish.**

`Work.FIArea6Hecke.R.SelfDual d chi m` says that `psi chi m z = chi z * (z/|z|)^m` satisfies
`(psi chi m z)^2 = 1` for every `z` which is *primary* and a *unit modulo `4d`*.

The test point is `z = 1 + 4d·i`.  It is primary (`re = 1` odd, `im = 4d` even and `≡ re - 1`
mod `4`), it is a unit modulo `4d` (as `4d | z - 1`, witnessed by `w = 1`), and by periodicity of
the strict character `chi z = chi 1 = 1`.  Hence `SelfDual` at `z` reads
`((z/|z|)^m)^2 = 1`, i.e. `((z/|z|)^2)^m = 1`; and `(z/|z|)^2 = z / z̄` for `z ≠ 0`.  So
`w := z/z̄ = (1+4d·i)/(1-4d·i) ∈ ℚ(i)` satisfies `w^m = 1`, hence `w^(m.natAbs) = 1`, hence (since
`w` has rational coordinates) `w ∈ {1,-1,i,-i}` (`Work.FIArea6Hecke.R.rootOfUnityRatIsFourth`).
But `w = ((1-16d²) + 8d·i)/(1+16d²)` has *both* real and imaginary parts nonzero for `d ≥ 1`
(`Work.FIArea6Hecke.R.div_conj_one_add_4di_rat`), a contradiction.

The proof is the one of `Work.FIArea6Hecke.R.m_eq_zero_of_psiReal` (same file name, module
`Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal`), which does exactly this under the stronger
hypothesis `PsiReal chi m` (`∀ z, star (psi chi m z) = psi chi m z`); here the realness hypothesis
is only available at the single point `z = 1 + 4d·i`, in the self-dual form `(psi)^2 = 1`.  The
helper lemmas `zpow_eq_one_natAbs_of_zpow_eq_one`, `rootOfUnityRatIsFourth` and
`div_conj_one_add_4di_rat` of that module are proven and should be reused. -/
theorem m_eq_zero_of_selfDual {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {m : ℤ}
    (hsd : Work.FIArea6Hecke.R.SelfDual d chi m) : m = 0 := by
  by_contra hm0
  obtain ⟨hchar, _⟩ := hchi
  obtain ⟨h1, _, _, hper, _⟩ := hchar
  -- the test point `z = 1 + 4d·i`
  set z : GaussianInt := ⟨1, ((4*d:ℕ):ℤ)⟩ with hz
  have hdiv : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - 1) := by
    rw [hz, Zsqrtd.intCast_dvd]
    exact ⟨dvd_zero _, by simpa using dvd_refl ((4 * d : ℕ) : ℤ)⟩
  have hchiz : chi z = 1 := (hper z 1 hdiv).trans h1
  have hZval : z.toComplex = (1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I := by
    rw [hz, GaussianInt.toComplex_def']
    push_cast
    ring
  have hpsi : Work.FIArea5.S16Hecke.psi chi m z =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    rw [Work.FIArea5.S16Hecke.psi, hchiz, one_mul]
  -- `z` is primary and a unit modulo `4d`
  have hzp : Work.FIPlan.IsPrimary z := by
    rw [hz]
    refine ⟨⟨0, by norm_num⟩, ⟨2*d, by push_cast; ring⟩, ?_⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨-d, by push_cast; ring⟩
  have hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z := ⟨1, by rw [mul_one]; exact hdiv⟩
  -- `SelfDual` at `z` reads `((Z/c)^m)^2 = 1`
  have hsq : ((z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m) ^ 2 = 1 := by
    have h' := hsd z hzp hzu
    rwa [hpsi] at h'
  -- hence `(Z/c)^m = ±1` is real
  have hreal : star ((z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m) =
      (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ m := by
    rcases sq_eq_one_iff.mp hsq with h' | h' <;> rw [h'] <;> simp
  have hc : star ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) =
      ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) := by simp
  have hZ0 : z.toComplex ≠ 0 := by
    rw [hZval]
    intro hh
    have := congrArg Complex.re hh
    simp at this
  have hc0 : ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro hh
    have h2 : ‖z.toComplex‖ = 0 := by
      rw [Work.FIArea5.S16Hecke.norm_toComplex, hh]
    exact hZ0 (norm_eq_zero.mp h2)
  -- `(z/z̄)^m = 1`
  have hw1 : (z.toComplex / star z.toComplex) ^ m = 1 :=
    zpow_div_conj_eq_one_of_star_eq hc hc0 hZ0 hreal
  have hn : 0 < m.natAbs := Int.natAbs_pos.mpr hm0
  have hwn : (z.toComplex / star z.toComplex) ^ m.natAbs = 1 :=
    zpow_eq_one_natAbs_of_zpow_eq_one hw1
  have hw : z.toComplex / star z.toComplex =
      ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) := by
    rw [hZval]
  rw [hw] at hwn
  -- `z/z̄` is a root of unity with rational coordinates, hence one of `1, -1, i, -i`
  obtain ⟨a, b, hre, him, ha0, hb0⟩ := div_conj_one_add_4di_rat d hd
  rcases rootOfUnityRatIsFourth
      (((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I) /
        star ((1:ℂ) + ((4*d:ℕ):ℂ) * Complex.I))
      a b hre him m.natAbs hn hwn with h' | h' | h' | h'
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact hb0 (by
      have hzero : (b:ℝ) = 0 := by rw [← him, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)
  · exact ha0 (by
      have hzero : (a:ℝ) = 0 := by rw [← hre, h']; simp
      exact_mod_cast hzero)

end Work.FIArea6Hecke.R
