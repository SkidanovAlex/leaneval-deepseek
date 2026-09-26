import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Sweep
import Submission.Work.Smooth.Morse.Span.carrier_eq_top
import Submission.Work.Smooth.Morse.Surface.isCompact_torus

/-!
# The *global* crossing hypothesis is unsatisfiable

The sweep theorems of this chapter are stated twice: with the local models imposed on the whole
line `ℝ` (`Submission/Work/Smooth/Morse/Sweep.lean`), and with the local models imposed only on the
band `Set.Icc a b` of levels actually swept (`Submission/Work/Smooth/Morse/Banded.lean`).  This
file proves that the *global* form is vacuous when combined with Pardon's box sandwich: there is
no `C^∞` function on the torus — with locally finitely many critical values — whose winding span
changes preserve the span at *every* critical value.

The reason is elementary: `g|_F` is bounded on the compact surface `F`, so for `a` below its range
the region `F ∩ {g < a}` is empty (winding span `⊥`) and for `b` above its range the region is all
of `F` (winding span `⊤`, `Work.Smooth.Morse.WindingSpan_carrier_eq_top`); but the crossing data at
every critical value forces the span to be independent of the level
(`Work.Smooth.Morse.windingSpan_eq_of_levelSweep_of_crossing`), i.e. `⊥ = ⊤`.

Consequently a statement of Pardon's sweeping step with the sandwich and the crossing data
quantified over *all* `t : ℝ` is true but proves nothing; the local models of Pardon's family of
spheres are only available where the box is actually swept, which is why the box-sweep statements
of this chapter are banded (`Work.Smooth.Morse.boxSweep_containsEssentialLoop_of_crossing_on`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Application

noncomputable section

/-- **There is no function whose regions' winding spans are locally constant in the crossing sense
at every level.**  A `C^∞` function on the embedded torus with locally finitely many critical
values cannot satisfy: at every critical value `t₀`, the winding spans of `region (t₀ - ε)` and
`region (t₀ + ε)` agree. -/
theorem not_global_crossing (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcrit : LocallyFiniteCriticalValues ψ g)
    (hcross : ∀ t₀ ∈ criticalValues ψ g, ∃ ε : ℝ, 0 < ε ∧
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ - ε)) =
        Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (t₀ + ε))) : False := by
  classical
  -- the span is independent of the level
  have hconst : ∀ a b : ℝ, Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g a) =
      Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g b) :=
    fun a b => windingSpan_eq_of_levelSweep_of_crossing ψ hg hcrit hcross a b
  -- `g|_F` is bounded on the compact surface
  have hcomp := Work.Smooth.Morse.Surface.isCompact_torus ψ
  obtain ⟨M, hM⟩ := hcomp.bddAbove_image hg.continuous.continuousOn
  obtain ⟨m, hm⟩ := hcomp.bddBelow_image hg.continuous.continuousOn
  -- below the range the region is empty, above it the region is everything
  have hregionA : region ψ g (m - 1) = ∅ := by
    ext x
    constructor
    · rintro ⟨hxc, hxg⟩
      simp only [Set.mem_ofPred_eq] at hxg
      have := hm ⟨x, hxc, rfl⟩
      linarith
    · simp
  have hregionB : region ψ g (M + 1) = (torus ψ).carrier := by
    ext x
    constructor
    · rintro ⟨hxc, -⟩
      exact hxc
    · intro hxc
      refine ⟨hxc, ?_⟩
      simp only [Set.mem_ofPred_eq]
      have := hM ⟨x, hxc, rfl⟩
      linarith
  have hempty : Work.SurgeryInvariance.WindingSpan (torus ψ) (∅ : Set R3) = ⊥ := by
    rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_eq_bot]
    rintro v ⟨γ, hγ, -⟩
    exact absurd (hγ 0) (Set.notMem_empty _)
  have hbot : Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (m - 1)) = ⊥ := by
    rw [hregionA, hempty]
  have htop : Work.SurgeryInvariance.WindingSpan (torus ψ) (region ψ g (M + 1)) = ⊤ := by
    rw [hregionB, WindingSpan_carrier_eq_top]
  have heq : (⊥ : Submodule ℚ (ℚ × ℚ)) = ⊤ := by
    rw [← hbot, hconst (m - 1) (M + 1), htop]
  have hmem : (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
    rw [heq]
    exact Submodule.mem_top
  have hzero : (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) = 0 := (Submodule.mem_bot (R := ℚ)).mp hmem
  have hfirst : (1 : ℚ) = 0 := by simpa using congrArg Prod.fst hzero
  exact one_ne_zero hfirst

end

end Work.Smooth.Morse.Application
