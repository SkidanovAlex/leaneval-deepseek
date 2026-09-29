import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.amoM_strip
import Submission.Work.TMComp.MAnalytic.amoM_section
import Submission.Work.TMComp.MAnalytic.strip_section

/-!
# The section relation for AJ's `m`-function above the strip threshold

`amoM α lam z x` is AJ's `m`-function, defined as the `limUnder` of the backward Möbius
iterates.  `amoM_section` proves the section relation

  `S_z(x) · m(x) = m(x+α)`

*conditionally* on the convergence of those iterates.  Here we discharge the condition for
energies with `4 ≤ Im z` using the fixed-point solution of the strip equation
(`amoM_strip`, `strip_section`): for such `z` there is `σ > 0` and a bounded analytic
section `M` on `{|Im x| < σ}` which is the limit of the backward iterates, so `amoM` agrees
with `M` on the real line and the section relation for `M` transfers to `amoM`.
-/

namespace Work.TMComp.MAnalytic

/-- The `limUnder` defining `amoM` is the actual limit of the backward Möbius iterates. -/
theorem amoM_eq_of_tendsto {α lam : ℝ} {z : ℂ} {M : ℂ → ℂ}
    (hM : ∀ y : ℝ, Filter.Tendsto
      (fun n : ℕ => Work.TMContract.mob (Work.TMContract.backIterC α lam z n y) Complex.I)
      Filter.atTop (nhds (M (y : ℂ)))) :
    ∀ y : ℝ, Work.TMContract.amoM α lam z y = M (y : ℂ) := by
  intro y
  exact (hM y).limUnder_eq

theorem amoM_section_upper {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) (x : ℝ) :
    Work.TMContract.mob (Work.TMContract.tmC lam z x) (Work.TMContract.amoM α lam z x)
      = Work.TMContract.amoM α lam z (x + α) := by
  -- the strip width for this energy, and the analytic section it produces
  obtain ⟨σ, hσpos, hσz⟩ := strip_sigma_exists hlam hz
  obtain ⟨M, -, -, -, hMlim⟩ := amoM_strip hlam hz hσpos hσz
  -- the `limUnder` in the definition of `amoM` is the genuine limit `M (y : ℂ)`
  have hamoM : ∀ y : ℝ, Work.TMContract.amoM α lam z y = M (y : ℂ) :=
    amoM_eq_of_tendsto hMlim
  -- the section relation for `M`, then transfer it to `amoM`
  have hsec := amoM_section (α := α) (lam := lam) (E := z) (by linarith)
    (m := fun y => M (y : ℂ)) hMlim
  rw [hamoM x, hamoM (x + α)]
  exact hsec x

end Work.TMComp.MAnalytic
