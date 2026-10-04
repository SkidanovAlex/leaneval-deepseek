import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.B3.ENormSq_le_succ
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The level-monotonicity of the B3 energy `ENormB`

For `1 ≤ m ≤ k` the level-`m` energy of a section with smooth chart data is controlled by its
level-`k` energy: the periodised components are periodisations of functions supported in the open
half-cube, so `B3/ENormSq_le_succ` gives the Poincaré step
`ENormSq m (D.Rper i h a b) ≤ C * ENormSq (m+1) (D.Rper i h a b)`, and the chain is iterated.
-/

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The energy is nonnegative. -/
lemma ENormSq_nonneg_gal {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => by positivity

/-- **One step of the Poincaré chain for the periodised components.** -/
theorem ENormSq_Rper_le_succ (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq m (D.Rper i h a b)
          ≤ C * Work.Diff.STE.ENormSq (m + 1) (D.Rper i h a b) := by
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hh i a b
    exact absurd a.isLt (by simp [hn])
  · have : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.ENormSq_le_succ
      (ι := Fin (Module.finrank ℝ E)) m
    refine ⟨C, hC, ?_⟩
    intro h hh i a b
    refine hCb (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ))
      (D.Rper i h a b) ?_ ?_ ?_ ?_ ?_
    · exact Complex.ofRealCLM.contDiff.comp
        (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) D h hh i a b)
    · intro z hz
      simp only [Function.mem_support, Complex.ofReal_ne_zero] at hz
      have hsupp : z ∈ Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
        D.R_support i h a b hz
      simpa [Set.mem_pi] using hsupp
    · exact (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData (I := I) D h hh i a b).1
    · exact (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData (I := I) D h hh i a b).2
    · intro z
      rfl

end

end Work.Diff.STE.Lead.GalTame
