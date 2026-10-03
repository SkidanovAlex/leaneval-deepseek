import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.criticalSet_isDiscreteIn

/-!
# The critical set of a harmonic function is locally finite

If `u : X → ℝ` is harmonic on an open set `U` and nowhere locally constant there, then the set of
points of `U` at which the gradient of `u` vanishes is *locally finite* in `U`; in fact it is
discrete in `U` (`Work.CriticalSet.criticalSet_isDiscreteIn`), and every point of `U` has a
neighbourhood meeting the critical set at most in that point.

Consequently the critical set meets every compact subset of `U` in a finite set.  This is the
"regular values are plentiful" input for the exhaustion and period-integrality arguments of the
uniformization theorem, replacing Sard's lemma.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The critical set of a nowhere-locally-constant harmonic function is locally finite.**

For `u` harmonic on the open set `U` and not eventually constant near any point of `U`, every point
of `U` has a neighbourhood meeting `criticalSet u U` in a finite set. -/
theorem criticalSet_isLocallyFinite {u : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hu : Submission.HarmonicOnX u U) (hnlc : NotLocallyConstantOn u U) :
    IsLocallyFiniteIn (criticalSet u U) U :=
  (criticalSet_isDiscreteIn hU hu hnlc).isLocallyFiniteIn

/-- **Finiteness of the critical set on compact subsets.**

A compact subset of the domain of a nowhere-locally-constant harmonic function contains only
finitely many critical points. -/
theorem finite_criticalSet_inter_isCompact {u : X → ℝ} {U K : Set X} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hu : Submission.HarmonicOnX u U)
    (hnlc : NotLocallyConstantOn u U) : (criticalSet u U ∩ K).Finite := by
  classical
  have hdisc := criticalSet_isDiscreteIn hU hu hnlc
  choose V hV using fun x (hx : x ∈ K) => hdisc x (hKU hx)
  obtain ⟨t, hcover⟩ := hK.elim_nhds_subcover' V fun x hx => (hV x hx).1
  have hfin : (⋃ x ∈ (t : Set ↥K), criticalSet u U ∩ V (x : X) x.2).Finite := by
    refine Set.Finite.biUnion t.finite_toSet ?_
    intro x _
    exact (Set.finite_singleton (x : X)).subset (hV (x : X) x.2).2
  refine hfin.subset ?_
  rintro y ⟨hyS, hyK⟩
  obtain ⟨x, hxt, hyV⟩ := mem_iUnion₂.mp (hcover hyK)
  refine mem_iUnion₂.mpr ⟨x, ?_, hyS, hyV⟩
  simpa using hxt

end Work.CriticalSet
