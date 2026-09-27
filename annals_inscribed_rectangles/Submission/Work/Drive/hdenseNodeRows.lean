import Mathlib
import Submission.Work.Drive.hdenseNodeE5
import Submission.Work.Drive.exists_designTripleAtN_blockT6AtN_of_rows

/-!
# The node `Work.Drive.hdense_sideGerm` from the class-row family: **the last input**

The `hdense` node is now the *composition* of three proved pieces:

* `Work.Drive.hdense_sideGerm_of_E4` (`hdenseNodeE5.lean`) — the (E5) wiring: from the one-parameter
  design data `DesignTripleAtN ∧ BlockT6AtN` at every quadruple `(a, c')`, the node's conclusion for
  the *given* chart perturbation `Ξ`;
* `Work.Drive.exists_designTripleAtN_blockT6AtN_of_rows` (`exists_designTripleAtN_blockT6AtN_of_rows.lean`)
  — the (E4) producer: one localized Sard call in the design's parameter `t : ℝ¹²`, from the *class-row
  family* `R` of the triple;
* this module: `Work.Drive.ClassRowFamily` (the row family as a predicate) and
  `Work.Drive.hdense_sideGerm_of_classRowFamily` — the node from a *producer of the row families*.

So the node reduces to the single statement

> for every collision-free triple `(a, c')` of angles there is an open set `R ⊆ ℝ¹²`, dense at every
> point of the closed unit ball, at which the perturbed class triple of the design is **odd**

— the `R`-producer, `Work.Drive.exists_classRowFamily`, i.e. the lead's §3 class rows plus §2.1
(`encodedGeneric.exists_homotopy_meet3Hyp_encoded`) and §2.5
(`hasClassLinearization_of_endData`), fed to `odd_ncard_classTripleSet_of_hasClassLinearization`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The class-row family of the design's triple `(0, a, a + c')`**: an open set of design parameters,
dense at every point of the closed unit ball, at which the perturbed class triple of the design is odd.
This is exactly the `R`-input of `Work.Drive.exists_designTripleAtN_blockT6AtN_of_rows`, and hence the
last input of the node `Work.Drive.hdense_sideGerm`. -/
def ClassRowFamily (Q : ℂ → CappingSpace) (c : ℝ) (a c' : UnitAddCircle)
    (R : Set (EuclideanSpace ℝ (Fin 12))) : Prop :=
  IsOpen R ∧
    (∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ R ∧ ‖y - x‖ < δ) ∧
    (∀ t ∈ R, Odd (classTripleSet
      (fun k z => chartPert ((blk k) t)
        (rotPresentation Q ((![0, a, a + c'] : Fin 3 → UnitAddCircle) k) z))).ncard)

/-- **The node from a producer of the class-row families.**  Given, for every collision-free triple
`(a, c')`, an open set `R` dense at every point of the closed unit ball with the oddness property
(`Work.Drive.ClassRowFamily`), the node's conclusion follows for the given chart perturbation `Ξ`. -/
theorem hdense_sideGerm_of_classRowFamily {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (hR : ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      ∃ R : Set (EuclideanSpace ℝ (Fin 12)), ClassRowFamily Q c a c' R) :
    ∀ a c' : UnitAddCircle, a ∈ Work.Drive.Zc γ → c' ∈ Work.Drive.Zc γ →
      a + c' ∈ Work.Drive.Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Work.Drive.Zc γ ∧ q.2 ∈ Work.Drive.Zc γ ∧ q.1 + q.2 ∈ Work.Drive.Zc γ ∧
          Work.Drive.sideGerm Ξ Q c q.1 * Work.Drive.sideGerm Ξ Q c (q.1 + q.2)
            + Work.Drive.sideGerm Ξ Q c (-q.1) * Work.Drive.sideGerm Ξ Q c q.2
            + Work.Drive.sideGerm Ξ Q c (-(q.1 + q.2)) * Work.Drive.sideGerm Ξ Q c (-q.2) = 1} := by
  refine hdense_sideGerm_of_E4 hγinj hQ Ξ c hΞ hc hcbot ?_
  intro a c' ha hc' hac ε' hε'
  obtain ⟨R, hRopen, hRdense, hRodd⟩ := hR a c' ha hc' hac
  exact exists_designTripleAtN_blockT6AtN_of_rows hQ hc hcbot hdisjZc a c' ha hc' hac
    R hRopen hRdense hRodd ε' hε'

end

end Work.Drive
