import Mathlib
import Submission.Work.Kunneth.EzawAux
import Submission.Work.Kunneth.EzawBoundary

/-!
# The defect of the recursion in `phiSum`/`psiSum` form

`dfc W p q` (`EZAWHomotopy.lean`) is the defect that the model chain `W p q` has to fill.  Its
φ- and ψ-parts are alternating sums of the individual coface terms `phiT`/`psiT`; this file
rewrites them as a single application of the alternating coface maps `phiSum`/`psiSum`
(`phiTsum`, `psiTsum`, `dfc2`, `dfc_eq_dfc2`), which is the form in which the cancellation of the
second-order terms in the cycle condition becomes a direct application of `phiSum_comp`,
`psiSum_comp` and `psiSum_phiSum`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The `φ`-part of the defect, as a single application of `phiSum`. -/
noncomputable def phiTsum (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    ↥((tMod (p + 1) q).X ((p + 1) + q)) :=
  dcast (p + 1) q (Nat.add_right_comm p 1 q).symm ((phiSum p q).f (p + q + 1) (W p q))

/-- The `ψ`-part of the defect, as a single application of `psiSum`. -/
noncomputable def psiTsum (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    ↥((tMod p (q + 1)).X (p + (q + 1))) :=
  (psiSum p q).f (p + q + 1) (W p q)

/-- `phiTsum` is the alternating sum of the individual `φ`-terms. -/
lemma phiTsum_eq (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    phiTsum W p q = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • phiT W p q i := by
  have h1 : phiTsum W p q = dcast (p + 1) q (Nat.add_right_comm p 1 q).symm
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((phiMod p q i).f (p + q + 1)).hom (W p q)) := by
    rw [phiTsum, phiSum_f_apply]
  rw [h1, dcast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dcast_smul]
  rfl

/-- `psiTsum` is the alternating sum of the individual `ψ`-terms. -/
lemma psiTsum_eq (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    psiTsum W p q = ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • psiT W p q j := by
  rw [psiTsum, psiSum_f_apply]
  refine Finset.sum_congr rfl (fun j _ => rfl)

/-- The defect of the recursion, in `phiSum`/`psiSum` form. -/
noncomputable def dfc2 (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    ↥((tMod p q).X (p + q)) :=
  match p, q with
  | 0, 0 => Em 0 0
  | 0, q + 1 => Em 0 (q + 1) - psiTsum W 0 q
  | p + 1, 0 => Em (p + 1) 0 - phiTsum W p 0
  | p + 1, q + 1 =>
      Em (p + 1) (q + 1) - phiTsum W p (q + 1) - (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q

lemma dfc_eq_dfc2 (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    dfc W p q = dfc2 W p q := by
  match p, q with
  | 0, 0 => rfl
  | 0, q + 1 => rw [dfc, dfc2, psiTsum_eq]
  | p + 1, 0 => rw [dfc, dfc2, phiTsum_eq]
  | p + 1, q + 1 => rw [dfc, dfc2, phiTsum_eq, psiTsum_eq]

end

end Work.Kunneth
