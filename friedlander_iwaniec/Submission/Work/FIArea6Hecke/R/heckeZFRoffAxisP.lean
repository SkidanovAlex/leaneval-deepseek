import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.hecke_three_four_one
import Submission.Work.FIArea6Hecke.R.zfrOffAxisSdClean

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **Self-duality implies `PsiRealPrimary`.**

`SelfDual d chi m` says `psi chi m z ^ 2 = 1` on the primary *units* mod `4d`; a primary
non-unit `z` satisfies `chi z = 0` (strictness), hence `psi chi m z = 0`, which is real.  On a
primary unit `psi chi m z ^ 2 = 1` forces `psi chi m z = ±1` (`sq_eq_one_iff`). -/
lemma psiRealPrimary_of_selfDual {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ}
    (hsd : SelfDual d chi m) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    PsiRealPrimary chi m := by
  intro z hzp
  by_cases hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rcases sq_eq_one_iff.mp (hsd z hzp hzu) with h1 | h1 <;> rw [h1] <;> simp
  · have hz0 : chi z = 0 := hchi.2 z hzu
    simp [Work.FIArea5.S16Hecke.psi, hz0]

/-- **The de la Vallée Poussin zero-free region (16.20) with the correct exceptional set** — the
statement `Work.FIArea6Hecke.R.ZFRoffAxis` of `R/ZFRStatementDefs`.

It follows from the corresponding self-dual statement `ZFRoffAxisSd`
(`zfrOffAxisSdClean`, assembled from its two cases: the self-dual case, where only the real axis is
excluded and which reduces to the complex zero-free region for real characters, and the
non-self-dual case, the classical `(3,4,1)` argument, which admits no exception).

The exceptional sets match: `PsiRealPrimary χ m` and `SelfDual d χ m` are equivalent on the values
`ψ` takes on the primary elements — `psiRealPrimary_of_selfDual` gives `SelfDual → PsiRealPrimary`,
and the converse is the trivial restriction to primary units.  Hence `¬(s.im = 0 ∧ SelfDual)`
follows from the target's hypothesis `¬(s.im = 0 ∧ PsiRealPrimary)`. -/
theorem heckeZFRoffAxisP :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ,
          1 - c / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re → s.re ≤ 2 →
            ¬ (s.im = 0 ∧ Work.FIArea6Hecke.R.PsiRealPrimary chi m) →
            Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  have hsd : Work.FIArea6Hecke.R.ZFRoffAxisSd := Work.FIArea6Hecke.R.zfrOffAxisSdClean
  rw [Work.FIArea6Hecke.R.ZFRoffAxisSd] at hsd
  obtain ⟨c, hc, h⟩ := hsd
  refine ⟨c, hc, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hreg hsle2 hexc
  exact h d chi m Lam hd hchi hAn hagr s hreg hsle2
    (fun hcon => hexc ⟨hcon.1, psiRealPrimary_of_selfDual hcon.2 hchi⟩)

end

end Work.FIArea6Hecke.R
