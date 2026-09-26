import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.WindingSpanLink
import Submission.Work.SurgeryInvariance.WindingSpan.meridianCurve

/-!
# The winding span as Pardon's homological invariant

`Work.CoreTopology.HomPieceData P A` records Pardon's invariant `U ↦ im(H₁(F ∩ U; ℚ) → H₁(F; ℚ))`
as an abstract assignment of a `ℚ`-subspace of `A = H₁(F; ℚ)` to every region `U ⊆ ℝ³`, together
with the predicates `HomPieceData.HasEssentialLoop` and `HomPieceData.Dichotomy`.  The sibling
module `Work.CoreTopology.WindingSpanLink` (which imports this subproject) records that the
*concrete* invariant `Work.SurgeryInvariance.WindingSpan P U ≤ ℚ² = H₁(T²; ℚ)` is an instance of
this piece data, `Work.CoreTopology.HomPieceData.ofWindingSpan P`, so that Pardon's abstract
`spherefamily` / `doublebubble` lemmas apply to it verbatim.  Two of their hypotheses are thereby
*proved* rather than assumed:

* `HasEssentialLoop U ↔ ContainsEssentialLoop U` for this piece data is
  `Work.CoreTopology.HomPieceData.ofWindingSpan_hasEssentialLoop` (from
  `WindingSpan_eq_bot_iff`);
* the local `1`-Lipschitz dimension bound along a `2`-surgery family is
  `Work.SurgeryInvariance.Sweep.hstep` (in the sharp form of *equality* of the winding spans).

The present file records the numerical facts about the ground field `ℚ` and the non-degeneracy of
`A = ℚ × ℚ` that the abstract lemmas require, and (below) the *failure* of the remaining
hypothesis, the dichotomy, for the concrete invariant: it is the statement that *every* region of
`ℝ³` has winding span `⊥` or `⊤`, and the meridian circle
`{φ ↦ P.psi θ φ}` of the torus has winding span exactly `ℚ·(0,1)`
(`Work.SurgeryInvariance.WindingSpan.meridianCurve`).  This is why the invariance of the
essential-piece invariant is proved in `Work.SurgeryInvariance.Core` *directly*, without passing
through the dichotomy.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

/-- The `ℚ`-dimension of `ℚ × ℚ` is `2`. -/
theorem finrank_pair : Module.finrank ℚ (ℚ × ℚ) = 2 := by
  simp [Module.finrank_prod, Module.finrank_self]

/-- `ℚ × ℚ` is non-degenerate as a `ℚ`-vector space: it has dimension `2 > 1`.  This is Pardon's
`g ≥ 1` as it appears in the hypotheses of `Work.CoreTopology.sphere_family`. -/
theorem one_lt_finrank_pair : 1 < Module.finrank ℚ (ℚ × ℚ) := by
  rw [finrank_pair]; norm_num

/-- The dichotomy for the concrete invariant is the statement that *every* region of `ℝ³` has
winding span `⊥` or `⊤`. -/
theorem dichotomy_ofWindingSpan_iff (P : Work.CoreTopology.ParamTorus) :
    (Work.CoreTopology.HomPieceData.ofWindingSpan P).Dichotomy ↔
      ∀ U : Set R3, WindingSpan P U = ⊥ ∨ WindingSpan P U = ⊤ :=
  Iff.rfl

/-- **The dichotomy fails for the concrete invariant.**  `HomPieceData.Dichotomy` asks that
*every* region `U ⊆ ℝ³` has winding span `⊥` or `⊤`.  The meridian circle of the torus is a region
whose winding span is exactly the line `ℚ·(0,1)`: it contains the meridian curve (winding `(0,1)`)
and no loop of nonzero longitude winding.  Hence the dichotomy hypothesis of
`Work.CoreTopology.double_bubble` / `Work.CoreTopology.sphere_family` cannot be discharged for the
concrete invariant `WindingSpan`, and the invariance of the essential-piece invariant must be
proved directly — which is what `Work.SurgeryInvariance.Core` does. -/
theorem not_dichotomy_ofWindingSpan (P : Work.CoreTopology.ParamTorus) :
    ¬ (Work.CoreTopology.HomPieceData.ofWindingSpan P).Dichotomy := by
  intro h
  have hU := (dichotomy_ofWindingSpan_iff P).mp h (Set.range fun φ : ℝ => P.psi 0 φ)
  rw [Work.SurgeryInvariance.WindingSpan.meridianCurve P 0] at hU
  rcases hU with hbot | htop
  · have hmem : ((0 : ℚ), (1 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← hbot]
      exact Submodule.subset_span (Set.mem_singleton _)
    simp at hmem
  · have hmem : ((1 : ℚ), (0 : ℚ)) ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have h0 : a = 0 := by
      have := congrArg Prod.snd ha
      simpa using this
    have h1 := congrArg Prod.fst ha
    rw [h0] at h1
    simp at h1

/-- There is a region of `ℝ³` whose winding span is neither `⊥` nor `⊤`: the meridian circle. -/
theorem exists_windingSpan_not_bot_not_top (P : Work.CoreTopology.ParamTorus) :
    ∃ U : Set R3, WindingSpan P U ≠ ⊥ ∧ WindingSpan P U ≠ ⊤ := by
  refine ⟨Set.range fun φ : ℝ => P.psi 0 φ, ?_, ?_⟩
  · rw [Work.SurgeryInvariance.WindingSpan.meridianCurve P 0]
    intro h
    have hmem : ((0 : ℚ), (1 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← h]
      exact Submodule.subset_span (Set.mem_singleton _)
    simp at hmem
  · rw [Work.SurgeryInvariance.WindingSpan.meridianCurve P 0]
    intro h
    have hmem : ((1 : ℚ), (0 : ℚ)) ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      rw [h]
      exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have h0 : a = 0 := by
      have := congrArg Prod.snd ha
      simpa using this
    have h1 := congrArg Prod.fst ha
    rw [h0] at h1
    simp at h1

end

end Work.SurgeryInvariance
