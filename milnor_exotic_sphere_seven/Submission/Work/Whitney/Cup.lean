import Mathlib
import Submission.Work.Thom.ThomAPI
import Submission.Work.Cohomology.cupNaturalH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The cup product in the degrees of the Chern classes

The Chern classes of a complex bundle of rank `m` live in `Coh ℤ (2*j) B`
(`Work.Thom.chernClass m j`), so the right-hand side of the Whitney formula
`c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)` involves a cup product in the degrees `2*i` and `2*j`,
whose value lives in `Coh ℤ (2*i + 2*j)`; the surrounding equation lives in `Coh ℤ (2*k)` with
`k = i + j`.  The identification `2*i + 2*j = 2*(i+j)` is `Nat.mul_add 2 i j`, and the transport is
`Work.Thom.cohTransport` (the degree cast of ADDENDUM 20).  This module packages the resulting
*graded* product once and for all:

* `Work.Whitney.cupChern a b x y ∈ Coh ℤ (2*(a+b)) B` — the product of `x ∈ H^{2a}` and
  `y ∈ H^{2b}`, with the degree bookkeeping built in (no side conditions);
* `Work.Whitney.cohTransport_CohMap` — the degree cast commutes with pullback (the transport is an
  isomorphism of `ModuleCat ℤ`, so it is natural);
* `Work.Whitney.cupChern_CohMap` — **naturality of the graded cup product**;
* `Work.Whitney.cupChern_one_right`, `cupChern_one_left` — the unit laws of the graded product.

With these, the two sides of the Whitney formula are honest elements of the same module
`Coh ℤ (2*k) B`, and the formula can be stated and used without any visible cast.
-/

namespace Work.Whitney

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- The singular simplicial set of `B` — the ambient object of the cohomology `Coh ℤ n B`. -/
abbrev ssB (B : Type) [TopologicalSpace B] : SSet := TopCat.toSSet.obj (TopCat.of B)

/-- **The degree cast commutes with pullback.**  `Work.Thom.cohTransport h` is (the underlying
linear map of) an isomorphism of `ModuleCat ℤ`, so it commutes with every morphism of that category,
in particular with `CohMap f ℤ n`. -/
theorem cohTransport_CohMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    {n n' : ℕ} (h : n = n') (f : C(B₁, B₂)) (x : Work.Thom.Coh ℤ n B₂) :
    (Work.Thom.CohMap f ℤ n').hom (Work.Thom.cohTransport h x)
      = Work.Thom.cohTransport h ((Work.Thom.CohMap f ℤ n).hom x) := by
  subst h
  rw [Work.Thom.cohTransport_rfl]
  rfl

/-- Two successive degree casts compose. -/
theorem cohTransport_trans {n n' n'' : ℕ} (h : n = n') (h' : n' = n'')
    (x : Work.Thom.Coh ℤ n B) :
    Work.Thom.cohTransport h' (Work.Thom.cohTransport h x)
      = Work.Thom.cohTransport (h.trans h') x := by
  subst h
  subst h'
  rw [Work.Thom.cohTransport_rfl]

/-- **The graded cup product of two Chern-type classes**: `x ∈ H^{2a}(B;ℤ)`,
`y ∈ H^{2b}(B;ℤ)`, product in `H^{2(a+b)}(B;ℤ)`.  The degree bookkeeping
(`2*a + 2*b = 2*(a+b)`) is done by `Work.Thom.cohTransport`. -/
noncomputable def cupChern (a b : ℕ) (x : Work.Thom.Coh ℤ (2 * a) B)
    (y : Work.Thom.Coh ℤ (2 * b) B) : Work.Thom.Coh ℤ (2 * (a + b)) B :=
  Work.Thom.cohTransport (Nat.mul_add 2 a b).symm
    (Work.Cohomology.cupH' ℤ (ssB B) (2 * a) (2 * b) x y)

/-- The defining equation of `Work.Whitney.cupChern`. -/
theorem cupChern_def (a b : ℕ) (x : Work.Thom.Coh ℤ (2 * a) B)
    (y : Work.Thom.Coh ℤ (2 * b) B) :
    cupChern a b x y = Work.Thom.cohTransport (Nat.mul_add 2 a b).symm
      (Work.Cohomology.cupH' ℤ (ssB B) (2 * a) (2 * b) x y) := rfl

/-- **Naturality of the graded cup product.** -/
theorem cupChern_CohMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    (f : C(B₁, B₂)) (a b : ℕ) (x : Work.Thom.Coh ℤ (2 * a) B₂)
    (y : Work.Thom.Coh ℤ (2 * b) B₂) :
    (Work.Thom.CohMap f ℤ (2 * (a + b))).hom (cupChern a b x y)
      = cupChern a b ((Work.Thom.CohMap f ℤ (2 * a)).hom x)
          ((Work.Thom.CohMap f ℤ (2 * b)).hom y) := by
  rw [cupChern_def, cupChern_def, Work.Thom.cohTransport_CohMap,
    Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom f) (2 * a) (2 * b) x y]

end

end Work.Whitney
