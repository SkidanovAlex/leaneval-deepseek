import Mathlib
import Submission.Work.Whitney.TCMProdDefs
import Submission.Work.Whitney.TCMAssocUp
import Submission.Work.Whitney.tcmRelCup_assoc_general
import Submission.Work.Whitney.tcmRelCup_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# The three block projections of the two coordinate worlds, at `r = 1`

`tcmX B p (q+1) = B × (ℝ^p × ℝ^{q+1})` and `tcmX B (p+q) 1 = B × (ℝ^{p+q} × ℝ^1)` are the two
coordinate worlds of the associativity of `Work.Whitney.tcmProd` at `r = 1`; the transport between
them is `psiA`.  The five maps below read off, in either world, the first `p` coordinates, the middle
`q` coordinates and the last coordinate; the three identities `q1A_eq`, `q2A_eq`, `q3A_eq` say that
the two readings agree.

These are the `r = 1` instances of the block identities of `Submission/Work/Whitney/TCMAssocUp.lean`
(there the transport `castMap B (Nat.add_assoc m n r).symm` appears explicitly; at `r = 1` it is the
identity, `castMap_add_assoc_one`).
-/

namespace Work.Whitney.TCMAssocUp

open Work.Thom

noncomputable section

/-- The transport from the `(p, q+1)`-world to the `(p+q, 1)`-world. -/
def psiA (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p (q + 1), tcmX B (p + q) 1) :=
  (Fib.tcmF_inv B (p + q) 1).comp (tcmF B p (q + 1))

def q1A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p (q + 1), B × EuclideanSpace ℝ (Fin p)) :=
  tcmPr1 B p (q + 1)

def q2A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p (q + 1), B × EuclideanSpace ℝ (Fin q)) :=
  (tcmPr1 B q 1).comp ((Fib.tcmF_inv B q 1).comp (tcmPr2 B p (q + 1)))

def q3A (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B p (q + 1), B × EuclideanSpace ℝ (Fin 1)) :=
  (tcmPr2 B q 1).comp ((Fib.tcmF_inv B q 1).comp (tcmPr2 B p (q + 1)))

def q1B (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B (p + q) 1, B × EuclideanSpace ℝ (Fin p)) :=
  (tcmPr1 B p q).comp ((Fib.tcmF_inv B p q).comp (tcmPr1 B (p + q) 1))

def q2B (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B (p + q) 1, B × EuclideanSpace ℝ (Fin q)) :=
  (tcmPr2 B p q).comp ((Fib.tcmF_inv B p q).comp (tcmPr1 B (p + q) 1))

def q3B (B : Type) [TopologicalSpace B] (p q : ℕ) :
    C(tcmX B (p + q) 1, B × EuclideanSpace ℝ (Fin 1)) :=
  tcmPr2 B (p + q) 1

/-- At `r = 1` the transport `castMap B (Nat.add_assoc p q 1).symm` is the identity. -/
theorem castMap_add_assoc_one (B : Type) [TopologicalSpace B] (p q : ℕ)
    (y : B × EuclideanSpace ℝ (Fin (p + (q + 1)))) :
    TCMAssocUp.castMap B (Nat.add_assoc p q 1).symm y = y := by
  rw [TCMAssocUp.castMap_apply]

/-- **First block.** -/
theorem q1A_eq (B : Type) [TopologicalSpace B] (p q : ℕ) :
    q1A B p q = (q1B B p q).comp (psiA B p q) := by
  apply ContinuousMap.ext
  intro x
  have h := congrArg (fun (f : C(B × EuclideanSpace ℝ (Fin (p + (q + 1))),
      B × EuclideanSpace ℝ (Fin p))) => f (tcmF B p (q + 1) x))
    (TCMAssocUp.tcmPr1_comp_castMap_symm B p q 1)
  simp only [ContinuousMap.comp_apply] at h
  simp only [castMap_add_assoc_one, Fib.tcmF_inv_tcmF] at h
  show tcmPr1 B p (q + 1) x
    = tcmPr1 B p q (Fib.tcmF_inv B p q (tcmPr1 B (p + q) 1
        (Fib.tcmF_inv B (p + q) 1 (tcmF B p (q + 1) x))))
  exact h.symm

/-- **Middle block.** -/
theorem q2A_eq (B : Type) [TopologicalSpace B] (p q : ℕ) :
    q2A B p q = (q2B B p q).comp (psiA B p q) := by
  apply ContinuousMap.ext
  intro x
  have h := (TCMAssocUp.tcmPr23_comp_castMap_symm B p q 1).1
    (TCMAssocUp.castMap B (Nat.add_assoc p q 1).symm (tcmF B p (q + 1) x))
  simp only [castMap_add_assoc_one, Fib.tcmF_inv_tcmF] at h
  show tcmPr1 B q 1 (Fib.tcmF_inv B q 1 (tcmPr2 B p (q + 1) x))
    = tcmPr2 B p q (Fib.tcmF_inv B p q (tcmPr1 B (p + q) 1
        (Fib.tcmF_inv B (p + q) 1 (tcmF B p (q + 1) x))))
  exact h.symm

/-- **Last block.** -/
theorem q3A_eq (B : Type) [TopologicalSpace B] (p q : ℕ) :
    q3A B p q = (q3B B p q).comp (psiA B p q) := by
  apply ContinuousMap.ext
  intro x
  have h := (TCMAssocUp.tcmPr23_comp_castMap_symm B p q 1).2
    (TCMAssocUp.castMap B (Nat.add_assoc p q 1).symm (tcmF B p (q + 1) x))
  simp only [castMap_add_assoc_one, Fib.tcmF_inv_tcmF] at h
  show tcmPr2 B q 1 (Fib.tcmF_inv B q 1 (tcmPr2 B p (q + 1) x))
    = tcmPr2 B (p + q) 1 (Fib.tcmF_inv B (p + q) 1 (tcmF B p (q + 1) x))
  exact h.symm

/-! ## Transport along an equality of the source (or input) sets

Copied from `Submission/Work/Whitney/tcmProd_assoc.lean` (which is import-cycle-blocked); the
associativity endgame needs these to move `relCohMap`-pullbacks across set equalities. -/

/-- The preimage of `A ∪ C` under the inverse coordinate identification is the punctured set. -/
theorem tcmF_inv_preimage_union (B : Type) [TopologicalSpace B] (m n : ℕ) :
    (Fib.tcmF_inv B m n) ⁻¹' (tcmA B m n) ∪ (Fib.tcmF_inv B m n) ⁻¹' (tcmC B m n)
      = Punct B (m + n) := by
  rw [← Set.preimage_union, tcmA_union_tcmC]
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Punct, Fib.tcmF_inv_apply]
  constructor
  · intro h h0
    exact h (by rw [h0]; simp)
  · intro h h0
    exact h (by
      have h2 := congrArg (tcmSumLin m n) h0
      simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2)

/-- Transport of a `relCohMap` along a (variable) equality of the source sets. -/
theorem relCohMap_set_cast {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {S T : Set X} (h : S = T) (f : C(X, Y)) (B : Set Y) (hB : ∀ x ∈ T, f x ∈ B)
    (hB' : ∀ x ∈ S, f x ∈ B) (n : ℕ) (x : RelCoh ℤ n Y B) :
    h.symm ▸ ((relCohMap f S B hB' ℤ n).hom x) = (relCohMap f T B hB ℤ n).hom x := by
  cases h
  rw [Subsingleton.elim hB' hB]

/-- Transport of a `relCohMap` along a (variable) equality of the source sets. -/
theorem relCohMap_set_cast' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {S T : Set X} (h : S = T) (f : C(X, Y)) (B : Set Y) (hB : ∀ x ∈ T, f x ∈ B)
    (hB' : ∀ x ∈ S, f x ∈ B) (n : ℕ) (x : RelCoh ℤ n Y B) :
    h.symm ▸ ((relCohMap f T B hB ℤ n).hom x) = (relCohMap f S B hB' ℤ n).hom x := by
  cases h
  rw [Subsingleton.elim hB' hB]

/-- A `relCohMap`-pullback of a class cast along an equality of the *input* sets: the cast can be
moved across the pullback. -/
theorem relCohMap_cast_set {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {S T : Set Y} (h : S = T) (f : C(X, Y)) (A : Set X) (hA : ∀ x ∈ A, f x ∈ S)
    (hA' : ∀ x ∈ A, f x ∈ T) (n : ℕ) (x : RelCoh ℤ n Y S) :
    (relCohMap f A T hA' ℤ n).hom (h ▸ x) = (relCohMap f A S hA ℤ n).hom x := by
  cases h
  rw [Subsingleton.elim hA hA']

/-- The same, with the cast on the other side. -/
theorem relCohMap_cast_set' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {S T : Set Y} (h : S = T) (f : C(X, Y)) (A : Set X) (hA : ∀ x ∈ A, f x ∈ S)
    (hA' : ∀ x ∈ A, f x ∈ T) (n : ℕ) (x : RelCoh ℤ n Y T) :
    (relCohMap f A S hA ℤ n).hom (h.symm ▸ x) = (relCohMap f A T hA' ℤ n).hom x := by
  cases h
  rw [Subsingleton.elim hA hA']

end

end Work.Whitney.TCMAssocUp
