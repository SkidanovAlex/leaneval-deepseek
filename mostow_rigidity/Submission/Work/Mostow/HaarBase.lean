import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.VolDefs

/-!
# Shared base for the Haar bridge (area B, `haarBridge`)

Definitions and elementary instances used by the delegated chapters of area B:

* `Work.Mostow.bmat v` — the matrix of the hyperbolic boost sending `e₀` to `hlift v`
  (definition only; its `O(n,1)`- and action-properties are proved in `HaarBoost`);
* `Work.Mostow.Ksub n hA` — the stabiliser of the origin in `PO n 1`, the compact subgroup
  whose orbits are the fibres of the orbit map `g ↦ g • 0`;
* missing instances making `PO n 1` a second countable Hausdorff topological group.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {n : ℕ}

/-! ## Instances for matrix spaces, subtypes and `PO n 1` -/

instance instSecondCountableTopologyMatrix (m k : Type*) [Countable m] [Countable k]
    (α : Type*) [TopologicalSpace α] [SecondCountableTopology α] :
    SecondCountableTopology (Matrix m k α) :=
  inferInstanceAs (SecondCountableTopology (m → k → α))

instance instSecondCountableTopologySubtype (α : Type*) [TopologicalSpace α]
    [SecondCountableTopology α] (p : α → Prop) : SecondCountableTopology (Subtype p) := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis α
  exact (hb.induced Subtype.val).secondCountableTopology (hbc.image _)

instance instSecondCountableTopologyMatrixSum (p q : ℕ) :
    SecondCountableTopology (MatrixSum (Fin p) (Fin q) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ))

instance instSecondCountableTopologyUnitary (α : Type*) [Monoid α] [StarMul α]
    [TopologicalSpace α] [SecondCountableTopology α] :
    SecondCountableTopology (unitary α) := inferInstance

instance instSecondCountableTopologyPO (p q : ℕ) : SecondCountableTopology (PO p q) :=
  inferInstance

/-- The centre of a unitary group is closed. -/
theorem isClosed_center_unitary (p q : ℕ) :
    IsClosed (Subgroup.center (unitary (MatrixSum (Fin p) (Fin q) ℝ)) :
      Set (unitary (MatrixSum (Fin p) (Fin q) ℝ))) := by
  have hset : (Subgroup.center (unitary (MatrixSum (Fin p) (Fin q) ℝ)) :
        Set (unitary (MatrixSum (Fin p) (Fin q) ℝ))) =
      ⋂ y : unitary (MatrixSum (Fin p) (Fin q) ℝ), {x | y * x = x * y} := by
    ext x
    show x ∈ Subgroup.center (unitary (MatrixSum (Fin p) (Fin q) ℝ)) ↔ _
    rw [Subgroup.mem_center_iff]
    simp only [Set.mem_iInter, Set.mem_setOf_eq, mul_comm]
  rw [hset]
  exact isClosed_iInter fun y =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

instance instT2SpacePO (p q : ℕ) : T2Space (PO p q) := by
  haveI : IsClosed (Subgroup.center (unitary (MatrixSum (Fin p) (Fin q) ℝ)) :
      Set (unitary (MatrixSum (Fin p) (Fin q) ℝ))) := isClosed_center_unitary p q
  exact inferInstance

/-! ## The boost matrix -/

open Matrix in
/-- The matrix of the hyperbolic boost sending `e₀ = hlift 0` to `hlift v`.
It should satisfy `(bmat v)ᵀ J (bmat v) = J` and `(bmat v) *ᵥ e₀ = hlift v`
(proved in `Submission.Work.Mostow.HaarBoost`). -/
def bmat (v : E n) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  fromBlocks
    (1 + (1 / (1 + tpart v)) •
      (replicateCol (Fin 1) (fun i => v i) * replicateRow (Fin 1) (fun i => v i)))
    (replicateCol (Fin 1) (fun i => v i))
    (replicateRow (Fin 1) (fun i => v i))
    (tpart v • (1 : Matrix (Fin 1) (Fin 1) ℝ))

/-! ## The stabiliser of the origin -/

/-- The stabiliser of the origin in `PO n 1`, as a subgroup (`POActionProp` supplies the
action axioms). -/
def Ksub (n : ℕ) (hA : POActionProp n) : Subgroup (PO n 1) where
  carrier := {g | g • (0 : E n) = 0}
  one_mem' := by
    obtain ⟨-, -, -, hone, -, -, -⟩ := hA
    show (1 : PO n 1) • (0 : E n) = 0
    rw [hone]
  mul_mem' := by
    obtain ⟨-, -, -, -, hmul, -, -⟩ := hA
    intro a b ha hb
    show (a * b) • (0 : E n) = 0
    rw [hmul a b (0 : E n), hb, ha]
  inv_mem' := by
    obtain ⟨-, -, -, hone, hmul, -, -⟩ := hA
    intro a ha
    show a⁻¹ • (0 : E n) = 0
    have h := hmul a⁻¹ a (0 : E n)
    rw [inv_mul_cancel, hone] at h
    rw [ha] at h
    exact h.symm

@[simp] theorem mem_Ksub {hA : POActionProp n} {g : PO n 1} :
    g ∈ Ksub n hA ↔ g • (0 : E n) = 0 := Iff.rfl

/-! ## Elementary topological facts -/

/-- A discrete subset of a second countable space is countable. -/
theorem countable_of_isDiscrete (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    {s : Set α} (hs : IsDiscrete s) : s.Countable := by
  classical
  have hdisc : DiscreteTopology s := (isDiscrete_iff_discreteTopology (s := s)).1 hs
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis α
  have key : ∀ x : s, ∃ c ∈ b, c ∩ (s : Set α) = {(x : α)} := by
    intro x
    have hopen : IsOpen ({(x : s)} : Set s) := isOpen_discrete _
    rw [isOpen_induced_iff] at hopen
    obtain ⟨u, hu, hux⟩ := hopen
    have hxmem : (x : α) ∈ u := by
      have hx : x ∈ Subtype.val ⁻¹' u := by rw [hux]; exact rfl
      exact hx
    obtain ⟨c, hcb, hxc, hcu⟩ := hb.exists_subset_of_mem_open hxmem hu
    refine ⟨c, hcb, ?_⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨hyu, hys⟩
      have hy : (⟨y, hys⟩ : s) ∈ Subtype.val ⁻¹' u := hcu hyu
      rw [hux] at hy
      simpa using congrArg Subtype.val hy
    · intro y hy
      rw [hy]
      exact ⟨hxc, x.2⟩
  choose c hcb hc using key
  let F : s → ↥b := fun x => ⟨c x, hcb x⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have hxy' : c x = c y := congrArg Subtype.val hxy
    have h1 : (x : α) ∈ c x ∩ (s : Set α) := by
      have h2 : (↑x : α) ∈ ({(↑x : α)} : Set α) := rfl
      rwa [← hc x] at h2
    rw [hxy', hc y] at h1
    exact Subtype.ext h1
  haveI : Countable ↥b := hbc.to_subtype
  haveI : Countable s := hinj.countable
  exact Set.countable_coe_iff.1 inferInstance

end

end Work.Mostow
