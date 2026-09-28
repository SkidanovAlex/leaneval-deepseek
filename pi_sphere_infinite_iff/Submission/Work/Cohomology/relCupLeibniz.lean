import Mathlib
import Submission.Work.Cohomology.RelCup

/-!
# The Leibniz rule for the relative cup product

For a topological space `X` and a subset `A ⊆ X`, the relative cup product
`relCup R X A : C^n(X,A) → C^m(X,A) → C^{n+m}(X,A)` (`Submission.Work.Cohomology.RelCup`) is,
by construction, the restriction of the absolute Alexander–Whitney cup product of the singular
cochains to the submodule `relKern R X A` of cochains vanishing on `A`.  Consequently the Leibniz
(product) rule for the relative differential `relDiffLM`

  `δ(a ⌣ b) = (δa) ⌣ b + (-1)^n · a ⌣ (δb)`

is an immediate consequence of the absolute Leibniz rule `Work.Cohomology.cupLeibniz` for
`cochainDiff` on the singular cochain complex of `TopCat.toSSet.obj X`: it suffices to compare the
underlying cochains (`Subtype.ext`), where the transport along `(n+1)+m = n+m+1` behaves as
expected (`eqRec_relKern_coe`).

The transport is needed in the first summand because the two degrees `(n + 1) + m` and `n + m + 1`
are only equal after `Nat.add_right_comm`, whereas `n + (m + 1)` and `n + m + 1` are
definitionally equal, so the second summand needs no cast.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- Transporting a relative cochain along an equality of degrees commutes with the underlying
element: the `Subtype.val` of the transported element is the transported `Subtype.val`. -/
lemma eqRec_relKern_coe (R : Type) [CommRing R] (X : TopCat) (A : Set X) {p q : ℕ}
    (h : p = q) (x : relKern R X A p) :
    (h ▸ x).1 = h ▸ x.1 := by
  cases h
  rfl

/-- **The Leibniz rule for the relative cup product.**  For relative cochains `a ∈ C^n(X,A)` and
`b ∈ C^m(X,A)`,

  `δ(a ⌣ b) = (δa) ⌣ b + (-1)^n · a ⌣ (δb)`,

with the first summand transported along `Nat.add_right_comm n 1 m : (n+1)+m = n+m+1`. -/
theorem relCupLeibniz (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern R X A n) (b : relKern R X A m) :
    relDiffLM R X A (n + m) (relCup R X A n m a b) =
      (Nat.add_right_comm n 1 m ▸ relCup R X A (n + 1) m (relDiffLM R X A n a) b) +
      ((-1 : R) ^ n) • relCup R X A n (m + 1) a (relDiffLM R X A m b) := by
  apply Subtype.ext
  simp only [eqRec_relKern_coe R X A, relDiffLM_coe, relCup_coe, Submodule.coe_add,
    Submodule.coe_smul]
  rw [singularCochain_d_apply R X (cup R (TopCat.toSSet.obj X) a.1 b.1),
    singularCochain_d_apply R X a.1, singularCochain_d_apply R X b.1]
  exact cupLeibniz R (TopCat.toSSet.obj X) a.1 b.1

end

end Work.Cohomology
