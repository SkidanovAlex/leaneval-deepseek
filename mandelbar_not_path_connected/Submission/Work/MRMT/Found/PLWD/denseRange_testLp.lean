/-
`Work.MRMT.Found.PLWD.denseRange_testLp`

Density of the `C¹` compactly supported test functions (with support in the open ball `B(0,R)`)
in `L²(B(0,R))`, i.e. `DenseRange (Work.MRMT.Found.testLp R)`.

The proof has three layers, and the two analytic ones are proved in separate files of this
directory:

* `exists_continuous_approx_indicator` — an indicator function of a measurable subset of the ball
  is approximated in `L²(ℂ)` by a *continuous* function whose support lies in a strictly smaller
  closed ball (Urysohn + inner regularity);
* `exists_testSpace_approx_of_continuous` — such a continuous function is approximated in `L²(ℂ)`
  by a mollification, which is `C¹` and whose support stays in the open ball (mollification with
  a bump of small enough outer radius);
* `exists_testSpace_approx_indicator` below combines the two, and
  `denseRange_testLp_of_approx` runs `MeasureTheory.MemLp.induction_dense` to conclude.
-/
import Mathlib
import Submission.Work.MRMT.Found.PLWD.Defs
import Submission.Work.MRMT.Found.PLWD.exists_continuous_approx_indicator
import Submission.Work.MRMT.Found.PLWD.exists_testSpace_approx_of_continuous
import Submission.Work.MRMT.Found.PLWD.denseRange_testLp_of_approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Indicator functions of finite-measure subsets of the ball are approximated in `L²(ℂ)` by
elements of `testSpace R`.  The continuous approximant lives in a strictly smaller closed ball,
so that its mollification (with a bump of sufficiently small outer radius) has support in
`B(0,R)` and hence belongs to `testSpace R`. -/
theorem exists_testSpace_approx_indicator {R : ℝ} (hR : 0 < R) {s : Set ℂ}
    (hsm : MeasurableSet s) (hsR : s ⊆ Metric.ball 0 R)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) s < ⊤) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Work.MRMT.Found.testSpace R,
      MeasureTheory.eLpNorm (fun z => (ψ : ℂ → ℂ) z - s.indicator (fun _ => c) z) 2
        (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨f, r, hfc, hrR, hsupp, hf⟩ :=
    exists_continuous_approx_indicator hR hsm hsR hfin c hε2
  obtain ⟨ψ, hψ⟩ := exists_testSpace_approx_of_continuous hrR hfc hsupp hε2
  refine ⟨ψ, ?_⟩
  have hsplit : (fun z => (ψ : ℂ → ℂ) z - s.indicator (fun _ => c) z)
      = fun z => ((ψ : ℂ → ℂ) z - f z) + (f z - s.indicator (fun _ => c) z) := by
    ext z
    ring
  rw [hsplit]
  calc MeasureTheory.eLpNorm
          (fun z => ((ψ : ℂ → ℂ) z - f z) + (f z - s.indicator (fun _ => c) z)) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      ≤ MeasureTheory.eLpNorm (fun z => (ψ : ℂ → ℂ) z - f z) 2
            (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        + MeasureTheory.eLpNorm (fun z => f z - s.indicator (fun _ => c) z) 2
            (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hψ hf
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

/-- The main theorem: the classes of the `C¹` compactly supported test functions with support in
`B(0,R)` are dense in `L²(B(0,R))`. -/
theorem denseRange_testLp (R : ℝ) : DenseRange (Work.MRMT.Found.testLp R) := by
  rcases lt_or_ge 0 R with hR | hR
  · refine denseRange_testLp_of_approx hR fun {s : Set ℂ} hsm hsR hfin c ε hε => ?_
    exact exists_testSpace_approx_indicator hR hsm hsR hfin c hε
  · -- the ball is empty, so the measure is zero and `L²` is a subsingleton
    haveI : Subsingleton
        (Lp ℂ 2 ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict (Metric.ball 0 R))) := by
      rw [Metric.ball_eq_empty.2 hR, Measure.restrict_empty]
      exact ⟨fun x y => Lp.ext_iff.2 rfl⟩
    refine Metric.denseRange_iff.2 fun F δ hδ => ⟨0, ?_⟩
    rw [Subsingleton.elim F (Work.MRMT.Found.testLp R 0)]
    simpa using hδ

end Work.MRMT.Found.PLWD
