/-
  CoreStep: the degree of the intersection of two restricted semi-Pfaffian sets.

  `Work.WilE7.interSet X Y` is the DNF-over-the-concatenated-chain presentation of `X.set ∩ Y.set`
  (`Work.WilE7.interSet_set`): the chain is `EAChain.cat X.c Y.c` and the DNF list is
  `(X.basics.product Y.basics).map (fun b => interBasic b.1 b.2)`, where `interBasic B B'`
  conjoins the two branches after reindexing the atoms along `EAPoly.inl` (left factor) and
  `EAPoly.inr` (right factor).

  The degree estimate is the exact analogue of `Work.WilE7.Basic.prod_deg_le` for the product:

  * `interBasic B B'` only *renames* the variables of the two atoms and concatenates the two atom
    lists, and `MvPolynomial.rename` never raises the total degree, so
    `(interBasic B B').deg ≤ B.deg + B'.deg` (`deg_interBasic_le`);
  * summing over the product list, `Work.WilE7.sumProduct` turns
    `∑_{(B,B')} (B.deg + B'.deg)` into `Y.basics.length * X.deg + X.basics.length * Y.deg`.

  The bound is in fact an equality: `interBasic_holds` shows that the conjunction loses no atom,
  so a list of `m` *trivial* branches of `X` (degree `0`) contributes exactly `m * Y.deg`, which
  is precisely the term `X.basics.length * Y.deg` on the right.
-/
import Mathlib
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.sumProduct
import Submission.Work.WilE7.ProdDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## The degree of a conjunction of two branches -/

/-- `atomDeg` does not increase under the variable renaming `Work.WilE7.EAPoly.inl`, which views
an `EA`-polynomial on the left factor of a concatenated chain: it is a `MvPolynomial.rename`, and
`rename` never raises the total degree. -/
theorem atomDeg_inl_le {k r₁ r₂ : ℕ} (Q : EAPoly k r₁) :
    atomDeg (Work.WilE7.EAPoly.inl (r₂ := r₂) Q) ≤ atomDeg Q :=
  Nat.add_le_add_right
    (MvPolynomial.totalDegree_rename_le (Sum.map id (Fin.castAdd r₂)) Q) 1

/-- `atomDeg` does not increase under the variable renaming `Work.WilE7.EAPoly.inr`, which views
an `EA`-polynomial on the right factor of a concatenated chain. -/
theorem atomDeg_inr_le {k r₁ r₂ : ℕ} (Q : EAPoly k r₂) :
    atomDeg (Work.WilE7.EAPoly.inr (r₁ := r₁) Q) ≤ atomDeg Q :=
  Nat.add_le_add_right
    (MvPolynomial.totalDegree_rename_le (Sum.map id (Fin.natAdd r₁)) Q) 1

/-- Conjoining two branches over the concatenated chain does not raise the degree:
`Work.WilE7.interBasic` renames the variables of the two sides and concatenates the two lists of
atoms, so the degree (the sum of the `atomDeg`s) is at most the sum of the two degrees. -/
theorem deg_interBasic_le {k r r' : ℕ} (B : Basic k r) (B' : Basic k r') :
    (Work.WilE7.interBasic B B').deg ≤ B.deg + B'.deg := by
  have h1 : ((B.eqs.map (Work.WilE7.EAPoly.inl (r₂ := r'))).map atomDeg).sum
      ≤ (B.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B.eqs _ _
      (fun Q _ => atomDeg_inl_le (r₂ := r') Q)
  have h2 : ((B.pos.map (Work.WilE7.EAPoly.inl (r₂ := r'))).map atomDeg).sum
      ≤ (B.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B.pos _ _
      (fun Q _ => atomDeg_inl_le (r₂ := r') Q)
  have h3 : ((B'.eqs.map (Work.WilE7.EAPoly.inr (r₁ := r))).map atomDeg).sum
      ≤ (B'.eqs.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B'.eqs _ _
      (fun Q _ => atomDeg_inr_le (r₁ := r) Q)
  have h4 : ((B'.pos.map (Work.WilE7.EAPoly.inr (r₁ := r))).map atomDeg).sum
      ≤ (B'.pos.map atomDeg).sum := by
    rw [List.map_map]
    exact Work.WilE7.sum_map_le_of_pointwise B'.pos _ _
      (fun Q _ => atomDeg_inr_le (r₁ := r) Q)
  simp only [Basic.deg, Work.WilE7.interBasic, List.map_append, List.sum_append]
  linarith

/-! ## The degree of the intersection -/

/-- **Degree of the intersection.** The degree of `Work.WilE7.interSet X Y` is at most
`Y.basics.length * X.deg + X.basics.length * Y.deg` (in fact it is equal). -/
theorem interSet_deg_le {k : ℕ} (X Y : WilkiesDesign.E.SemiPf k) :
    (Work.WilE7.interSet X Y).deg ≤ Y.basics.length * X.deg + X.basics.length * Y.deg := by
  have hsum : (Work.WilE7.interSet X Y).deg
      ≤ ((X.basics.product Y.basics).map
          (fun p : Basic k X.r × Basic k Y.r => p.1.deg + p.2.deg)).sum := by
    show (List.map (fun b : Basic k (X.r + Y.r) => b.deg)
        (List.map (fun b => Work.WilE7.interBasic b.1 b.2)
          (X.basics.product Y.basics))).sum
      ≤ (List.map (fun p : Basic k X.r × Basic k Y.r => p.1.deg + p.2.deg)
          (X.basics.product Y.basics)).sum
    rw [List.map_map]
    refine Work.WilE7.sum_map_le_of_pointwise _ _ _ ?_
    rintro ⟨B, B'⟩ -
    exact deg_interBasic_le B B'
  rw [Work.WilE7.sumProduct] at hsum
  exact hsum

end Work.CoreStep
