import Mathlib
import Submission.Work.Mostow.margulisCuspDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! The sheet-preserving lift `ToO` represents the same element of `PO n 1`.

`ToO g = O1.ofMatrix (LambdaMat g) _`, `LambdaMat g = tsign (Quotient.out g) • mat (Quotient.out g)`
(`Submission.Work.Mostow.StabLift`), and `PO n 1 = O1 n ⧸ Subgroup.center (O1 n)`. As an element of
`O1 n`, `ToO g` has matrix `tsign (Quotient.out g) • mat (Quotient.out g)`, i.e. it is
`tsign (Quotient.out g) • Quotient.out g`, which differs from `Quotient.out g` by the central
element `tsign (Quotient.out g) • 1 = ±1` (`hA.1`: the centre is `{1, -1}`), hence has the same image
in `PO n 1`; and `(Quotient.out g : PO n 1) = g` (`Quotient.out_eq`).

Useful: `mat_ToO`, `QuotientGroup.eq`, `QuotientGroup.eq_one_iff`, `O1.ofMatrix`, `mat_O1_ofMatrix`,
`O1_form_col`, `O1_form_row`, `O1.mat_injective`, `Work.Mostow.tsign_eq_one_or`, `Work.Mostow.tsign_sq`. -/
theorem coeToO (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) :
    (Work.Mostow.ToO g : LeanEval.Geometry.MostowRigidity.PO n 1) = g := by
  -- the underlying matrix of the lift is `tsign · mat`
  have hmat : Submission.Mostow.mat (ToO g)
      = Submission.Mostow.tsign (Quotient.out g)
        • Submission.Mostow.mat (Quotient.out g) := by
    rw [mat_ToO, LambdaMat]
  -- `-1` is central, by `hA.1`
  have hneg1 : (-1 : O1 n) ∈ Subgroup.center (O1 n) := (hA.1 _).mpr (Or.inr rfl)
  rcases Submission.Mostow.Hyper.tsign_eq_one_or (Quotient.out g) with hts | hts
  · -- the lift is the representative itself
    have hEq : ToO g = Quotient.out g := by
      apply O1.mat_injective
      rw [hmat, hts, one_smul]
    exact hEq ▸ QuotientGroup.out_eq' g
  · -- the lift is the negative of the representative, hence the same class in `PO n 1`
    have hEq : ToO g = -(Quotient.out g) := by
      apply O1.mat_injective
      rw [hmat, hts, neg_one_smul, mat_neg]
    have hmem : (-(Quotient.out g) : O1 n)⁻¹ * Quotient.out g ∈ Subgroup.center (O1 n) := by
      rw [inv_neg, neg_mul, inv_mul_cancel]
      exact hneg1
    have hq : ((-(Quotient.out g) : O1 n) : PO n 1) = ((Quotient.out g : O1 n) : PO n 1) :=
      (QuotientGroup.eq (s := Subgroup.center (O1 n))).mpr hmem
    exact hEq ▸ hq.trans (QuotientGroup.out_eq' g)

end Work.Mostow
