import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Series.Deleg.phiAPointwise
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remSource_facts` — the `hInt` hypothesis bundle of the mode-series differentiation

The termwise differentiation of the mode series `psiSeries α (RemSource α ψ)` needs the
bundle `hInt`:

* `t ↦ cmode m (RemSource α ψ) t` continuous on `Ioi 0`;
* `t ↦ cmode m (RemSource α ψ) t · t^((2m+5)/α − 1)` integrable on `Ioo 0 1`;
* `t ↦ cmode m (RemSource α ψ) t · t^(−2m/α − 1)` integrable on `Ioi 1`;

together with the same three statements for the radial profile `𝒜φ = VocabO.phiA α`.

`RemSource α ψ z θ = α²·(𝒜φ)(z)·ψ(θ)` is separable in `z`, and `Series/RemSetup.lean` gives

  `cmode m (RemSource α ψ) t = α²·(𝒜φ)(t)·bmode m ψ`   (`cmode_RemSource`),

so each `cmode`-conjunct is a scalar multiple of the corresponding `phiA`-conjunct and all the
content is in the three analytic facts about `𝒜φ`, proved in
`Series/Deleg/psiSeriesIntegrability.lean` from the explicit form
`𝒜φ(z) = 4αz²(z−2)/(1+z)⁴ + 2(5+α)z(1−z)/(1+z)³` (`z ≠ −1`):

* `𝒜φ` is rational with its only pole at `z = −1`, hence continuous on `Ioi 0`;
* `|𝒜φ(t)| ≤ (10α+10)·t` on `(0,1)` and `|𝒜φ(t)| ≤ (14α+10)/t` on `(1,∞)`, so the integrands
  are dominated by `(10α+10)·t^{(2m+5)/α}` and `(14α+10)·t^{−2m/α−2}`, integrable because
  `(2m+5)/α > −1` and `−2m/α − 2 < −1` (here `α > 0`, `m ≥ 0`).
-/

namespace Work.FTS.PhiStar.Series.SmoothAux

/-- The hypothesis bundle `hInt` of `deriv_series`: continuity of the `cmode`-slices of the
remainder source and the two weighted integrability statements for them, together with the
same three facts for the radial profile `𝒜φ = VocabO.phiA α`. -/
theorem remSource_facts (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) :
    (∀ m : ℕ, ContinuousOn (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t) (Set.Ioi 0)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) ∧
    ContinuousOn (Work.FTS.VocabO.phiA α) (Set.Ioi 0) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) := by
  refine ⟨?_, ?_, ?_, Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α,
    fun m => Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiAIntSmall α hα m,
    fun m => Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiAIntLarge α hα m⟩
  · -- continuity: `cmode m (RemSource α ψ) = α²·bmode m ψ · 𝒜φ`
    intro m
    refine ContinuousOn.congr (f := fun t : ℝ =>
      (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ) * Work.FTS.VocabO.phiA α t) ?_ ?_
    · exact (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiACont α).const_mul _
    · intro t _
      simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
      ring
  · -- integrability near `0`
    intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul
        (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiAIntSmall α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro t _
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring
  · -- integrability at `∞`
    intro m
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * (Work.FTS.VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul
        (Work.FTS.PhiStar.Series.Deleg.psiSeriesIntegrability_phiAIntLarge α hα m) _
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [Work.FTS.PhiStar.Series.cmode_RemSource]
    ring

end Work.FTS.PhiStar.Series.SmoothAux
