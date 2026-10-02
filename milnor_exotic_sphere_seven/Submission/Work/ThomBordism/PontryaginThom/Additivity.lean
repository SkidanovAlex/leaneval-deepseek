import Submission.Work.ThomBordism.PontryaginThom.HurewiczAdditive
import Submission.Work.ThomBordism.PontryaginThom.Assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity over families, as a theorem

Item 3 of the chapter: the Pontryagin–Thom class of a disjoint union of a family is the *product* of
the classes of the pieces (in the group `π_{k+8}(T)`), so the Hurewicz pairings — and hence the
normal Pontryagin numbers — add.  `Additivity.ptAdditivity` proves this, i.e. discharges the input
`Work.ThomBordism.PontryaginThom.PTAdditivity` of `Defs.lean`:

* `ptAdditivity : PTAdditivity k D` — given a rep for each piece of a finite family, there is one for
  the family, with the classes multiplied and the pairings summed (`hurewiczClassOf_prod` of
  `HurewiczAdditive.lean`, i.e. the pinch computation).

Consequently the *only* geometric inputs left are the existence of the construction per manifold
(`PTExists`) and transversality (`Transversality`, `TransversalityFamily`):

* `PTInputs'` — the input bundle without additivity, with `PTInputs'.toPTInputs`;
* `transversalityCore_of_inputs'`, `transversalityCoreFamily_of_inputs'` — the assembly at
  `PTInputs'`, i.e. with one hypothesis fewer than `Assembly.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- **Item 3: additivity over families, proved.**  For a finite family `F` of closed oriented smooth
`8`-manifolds, if each piece carries Pontryagin–Thom data, so does the disjoint union: take the
*product* of the classes of the pieces as its class, and the collapse map any cube representative.
The two pairings add because the Hurewicz class is additive under the product
(`hurewiczClassOf_prod`) and the Kronecker pairing is linear. -/
theorem ptAdditivity {k : ℕ} {D : ThomTarget k} : PTAdditivity k D := by
  intro ι _ F h
  classical
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  -- the canonical commutative-monoid structure, registered under the unfolded head as well, so
  -- that no type-class search has to unfold `HomotopyGroup` on the goal's side
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  let r : ∀ i, PTRep (F i) k D := fun i => (h i).some
  let α : HomotopyGroup (Fin (k + 8)) D.T D.t₀ := ∏ i, (r i).α
  refine ⟨{ collapse := Quotient.out α, hurewicz_p1sq := ?_, hurewicz_p2 := ?_ }⟩
  · rw [show (Quotient.mk _ (Quotient.out α) : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = α from
        Quotient.out_eq α,
      hurewiczClassOf_prod (T := D.T) (t₀ := D.t₀) (n := k + 8) (one_le_add_eight k)
        (fun i => (r i).α),
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (r i).α)
        = (r i).normal.normalP1Sq from (r i).hurewicz_p1sq]
    exact (r i).normal.normalP1Sq_eq
  · rw [show (Quotient.mk _ (Quotient.out α) : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = α from
        Quotient.out_eq α,
      hurewiczClassOf_prod (T := D.T) (t₀ := D.t₀) (n := k + 8) (one_le_add_eight k)
        (fun i => (r i).α),
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (r i).α)
        = (r i).normal.normalP2 from (r i).hurewicz_p2]
    exact (r i).normal.normalP2_eq

/-- **The geometric inputs of the chapter, without additivity** (which is now a theorem,
`ptAdditivity`): the Pontryagin–Thom construction per manifold, and transversality in the single
and family forms. -/
structure PTInputs' (k : ℕ) (D : ThomTarget k) where
  /-- item 1: the construction exists for every closed oriented smooth `8`-manifold -/
  exists_rep : PTExists k D
  /-- transversality, single manifold -/
  transversality : Transversality k D
  /-- transversality, families -/
  transversalityFamily : TransversalityFamily k D

/-- The inputs without additivity give the inputs of `Defs.lean` (additivity is not assumed but
proved, `ptAdditivity`). -/
theorem PTInputs'.toPTInputs {k : ℕ} {D : ThomTarget k} (hin : PTInputs' k D) : PTInputs k D :=
  { exists_rep := hin.exists_rep
    additivity := ptAdditivity
    transversality := hin.transversality
    transversalityFamily := hin.transversalityFamily }

/-- **`TransversalityCore` from the construction and transversality** (additivity not needed). -/
theorem transversalityCore_of_inputs' {k : ℕ} (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hin : PTInputs' k D) : TransversalityCore :=
  transversalityCore_of_inputs D hk hrat hin.toPTInputs

/-- **`TransversalityCoreFamily` from the construction and transversality** (additivity not
needed: it is proved in `ptAdditivity`). -/
theorem transversalityCoreFamily_of_inputs' {k : ℕ} (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hin : PTInputs' k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs D hk hrat hin.toPTInputs

/-- **`TransversalityCore` from `PTInputs'` and `RationalHurewiczStable3`** (`k ≥ 11`). -/
theorem transversalityCore_of_inputs'_three {k : ℕ} (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hin : PTInputs' k D) : TransversalityCore :=
  transversalityCore_of_inputs_three D hk hrat hin.toPTInputs

/-- **`TransversalityCoreFamily` from `PTInputs'` and `RationalHurewiczStable3`** (`k ≥ 11`). -/
theorem transversalityCoreFamily_of_inputs'_three {k : ℕ} (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hin : PTInputs' k D) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs_three D hk hrat hin.toPTInputs

end

end Work.ThomBordism.PontryaginThom
