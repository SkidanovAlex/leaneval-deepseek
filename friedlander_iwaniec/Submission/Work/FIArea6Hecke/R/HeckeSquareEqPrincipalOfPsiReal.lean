import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal

namespace Work.FIArea6Hecke.R

open scoped BigOperators

/-! ## `ψ` real forces `χ² = principalStrict d`

The hypothesis `PsiReal χ m` (`ψ_m = χ·(·/|·|)^m` is real-valued) is extremely restrictive:
`m_eq_zero_of_psiReal` shows `m = 0`, and then `psiReal_zero_iff` says that `χ` itself is
real-valued.  A real-valued strict character of the unit group modulo `4d` takes values `±1` on
units (its values are units of `ℂ` that are real and bounded by `1`) and `0` off them; hence its
square is exactly the indicator `principalStrict d` of the units.

Consequently the Hecke eigenvalues of `ψ²` with weight `2m` — which, `m = 0`, are the sums
`Σ_{|z|²=n} χ(z)²` — agree term by term with those of the principal strict character with weight
`0`, so the two Hecke `L`-series coincide.  This is the content of
`HeckeSquareEqPrincipalOfPsiReal` below. -/

/-- **A real-valued strict character `χ` satisfies `χ z · χ z = principalStrict d z` for every
Gaussian integer `z`**.

*Off* the units modulo `4d` both sides vanish: `χ` is strict, and `principalStrict d` is the
indicator of the units.
*On* the units: if `z·w ≡ 1` modulo `4d`, then `χ z · χ w = χ (z·w) = χ 1 = 1` (periodicity and
multiplicativity).  Since `‖χ z‖ ≤ 1` and `‖χ w‖ ≤ 1` while `‖χ z‖·‖χ w‖ = 1`, both norms equal
`1`.  As `χ z` is real, `χ z·χ z = χ z · conj (χ z) = ‖χ z‖² = 1`. -/
lemma chi_mul_self_eq_principalStrict {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hreal : ∀ z : GaussianInt, star (chi z) = chi z) :
    ∀ z : GaussianInt, chi z * chi z = Work.FIArea6Hecke.principalStrict d z := by
  intro z
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [Work.FIArea6Hecke.principalStrict_of_unit hz]
    obtain ⟨hchar, -⟩ := hchi
    obtain ⟨h1, hmul, hnorm, hper, -⟩ := hchar
    obtain ⟨w, hw⟩ := hz
    have hzw : chi z * chi w = 1 := by
      rw [← hmul z w]
      exact (hper (z * w) 1 hw).trans h1
    have hprod : ‖chi z‖ * ‖chi w‖ = 1 := by
      rw [← norm_mul, hzw, norm_one]
    have h1z : ‖chi z‖ = 1 := by
      nlinarith [norm_nonneg (chi z), norm_nonneg (chi w), hnorm z, hnorm w, hprod]
    have hsq : chi z * chi z = ((Complex.normSq (chi z) : ℝ) : ℂ) := by
      have h : chi z * star (chi z) = ((Complex.normSq (chi z) : ℝ) : ℂ) := by
        simpa using Complex.mul_conj (chi z)
      rwa [hreal z] at h
    rw [hsq, Complex.normSq_eq_norm_sq, h1z]
    norm_num
  · rw [Work.FIArea6Hecke.principalStrict_of_not_unit hz]
    obtain ⟨-, hstrict⟩ := hchi
    rw [hstrict z hz, mul_zero]

/-- **The Hecke eigenvalue sequences of `z ↦ χ z · χ z` with weight `2m` (`m = 0`) and of
`principalStrict d` with weight `0` coincide**, because `ψ (χ²) 0 = χ² = principalStrict d`
(`psi chi 0 z = chi z · (z/|z|)^0 = chi z`, and `(·)^0 = 1`). -/
lemma heckeLam_chiSq_zero_eq_principalStrict {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hreal : ∀ z : GaussianInt, star (chi z) = chi z) :
    Work.FIArea5.S16Hecke.heckeLam (fun z : GaussianInt => chi z * chi z) 0
      = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 := by
  funext n
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Work.FIArea5.S16Hecke.psi, Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one, mul_one]
  exact chi_mul_self_eq_principalStrict hchi hreal z

theorem HeckeSquareEqPrincipalOfPsiReal :
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      Work.FIArea6Hecke.R.PsiReal chi m →
      Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) (2 * m)
        = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 := by
  intro d chi m hd hchi hpsi
  have hm : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_psiReal hd hchi hpsi
  subst hm
  have hreal : ∀ z : GaussianInt, star (chi z) = chi z :=
    (Work.FIArea6Hecke.R.psiReal_zero_iff).mp hpsi
  have hlam := heckeLam_chiSq_zero_eq_principalStrict hchi hreal
  have h20 : (2 : ℤ) * 0 = 0 := by norm_num
  funext s
  rw [h20]
  simp only [Work.FIArea5.S16Hecke.heckeLSeries, hlam]

end Work.FIArea6Hecke.R
