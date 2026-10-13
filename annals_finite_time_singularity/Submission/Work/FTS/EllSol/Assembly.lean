/-
# `Work.FTS.EllSol.Assembly` — the assembly of `exists_ellSol` (items (a), (c), (e))

This module assembles the design's `exists_ellSol` from

* the abstract Hamel-basis selector `exists_linear_selector` (`Hamel.lean`, item (e), proved),
* the closure of the Galerkin class under linear combinations (item (a); taken here as the
  hypothesis `hGlin`, proved in `galClass_lin.lean`),
* the closure of the solution class `EllClassO` under linear combinations (item (c); taken here
  as the hypothesis `hClin`, proved in `ellClassO_lin.lean`),
* the zero elements `GalClass α 0` (`galClass_zero`, proved below) and `EllClassO α 0 0`
  (`Defs.ellClassO_zero`, proved),
* item (b) `EllClassOExists` (the single hypothesis of the area) and
* item (d) `EllPkgGoOfClass`.

The output is `ExistsEllSol`, i.e. the design's

  `∃ Ce > 0, ∃ α₀ > 0, ∀ α ∈ (0, α₀], ∃ EllSol : Fn →ₗ[ℝ] Fn,
      ∀ g, GalClass α g → EllPkgGo α Ce g (EllSol g)`.

The selector is applied to the *paired* class
`P α g Ψ := EllClassO α g Ψ ∧ EllPkgGo α Ce g Ψ`, which is closed under the same linear
combinations as `EllClassO` (the `EllPkgGo` part being derived from `EllClassO` by item (d)).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllSol.Hamel
import Submission.Work.FTS.EllipticEst.RegQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- `GalClass α 0`: the zero profile is in the Galerkin class. -/
theorem galClass_zero (α : ℝ) : Work.FTS.Nonlin.GalClass α (0 : Fn) := by
  refine ⟨Work.FTS.EllipticEst.RegQ_zero α 6, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro z; rfl
    · intro z; rfl
  · intro θ hθ
    refine ⟨by simp, ?_⟩
    rw [Work.FTS.EllipticEst.pz_zero_fun]; simp
  · refine ⟨?_, ?_⟩
    · intro j i hji θ hθ
      simp only [Work.FTS.EllipticEst.pthIter_zero_fun,
        Work.FTS.EllipticEst.pzIter_zero_fun]
      exact tendsto_const_nhds
    · intro a b hab θ hθ
      simp only [Work.Spaces.mixed, Work.FTS.EllipticEst.DthIter_zero_fun,
        Work.FTS.EllipticEst.DzIter_zero_fun]
      exact tendsto_const_nhds
  · simp [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]

/-- **The assembly of `exists_ellSol`.**  Given the linearity of the Galerkin class (item (a)),
the linearity of the solution class (item (c)), the existence of a solution in the class
(item (b), the single hypothesis) and the estimates for every solution of the class (item (d)),
there is a *linear* solution operator `EllSol` on the whole space whose values on `GalClass α`
are elliptic solutions carrying the package `EllPkgGo`. -/
theorem exists_ellSol_of_lin
    (hGlin : ∀ {α : ℝ}, 0 < α → ∀ (g g' : Fn) (c : ℝ), Work.FTS.Nonlin.GalClass α g →
      Work.FTS.Nonlin.GalClass α g' → Work.FTS.Nonlin.GalClass α (g + c • g'))
    (hClin : ∀ {α : ℝ} (hα : 0 < α) (g g' Ψ Ψ' : Fn) (c : ℝ),
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      EllClassO α g Ψ → EllClassO α g' Ψ' → EllClassO α (g + c • g') (Ψ + c • Ψ'))
    (hb : EllClassOExists) (hd : EllPkgGoOfClass) : ExistsEllSol := by
  obtain ⟨αb, hαb, hb⟩ := hb
  obtain ⟨Ce, αd, hCe, hαd, hd⟩ := hd
  refine ⟨Ce, hCe, min αb αd, lt_min hαb hαd, ?_⟩
  intro α hα hαm
  have hbα : ∀ g, Work.FTS.Nonlin.GalClass α g → ∃ Ψ, EllClassO α g Ψ :=
    fun g hg => hb α hα (le_trans hαm (min_le_left αb αd)) g hg
  have hdα : ∀ g Ψ, Work.FTS.Nonlin.GalClass α g → EllClassO α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ :=
    fun g Ψ hg h => hd α hα (le_trans hαm (min_le_right αb αd)) g Ψ hg h
  obtain ⟨EllSol, hEll⟩ :=
    exists_linear_selector (α := α)
      (P := fun g Ψ => EllClassO α g Ψ ∧ Work.FTS.VocabO.EllPkgGo α Ce g Ψ)
      (galClass_zero α)
      (fun g g' c hg hg' => hGlin hα g g' c hg hg')
      ⟨ellClassO_zero hα, hdα 0 0 (galClass_zero α) (ellClassO_zero hα)⟩
      (fun g g' Ψ Ψ' c hg hg' hP hP' =>
        ⟨hClin hα g g' Ψ Ψ' c hg hg' hP.1 hP'.1,
          hdα (g + c • g') (Ψ + c • Ψ') (hGlin hα g g' c hg hg')
            (hClin hα g g' Ψ Ψ' c hg hg' hP.1 hP'.1)⟩)
      (fun g hg => by
        obtain ⟨Ψ, hΨ⟩ := hbα g hg
        exact ⟨Ψ, hΨ, hdα g Ψ hg hΨ⟩)
  exact ⟨EllSol, fun g hg => (hEll g hg).2⟩

end Work.FTS.EllSol
