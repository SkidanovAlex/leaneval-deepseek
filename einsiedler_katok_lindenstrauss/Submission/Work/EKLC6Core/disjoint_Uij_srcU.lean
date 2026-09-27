import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_source
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Interfaces

/-!
# Trivial intersection of `U_qr` with the join of the two `p`-source root groups

For three distinct indices `p, q, r` of `Fin 3`, the "source `p`" join
`U_pq ⊔ U_pr` — the group of unipotents `1 + s E_pq + t E_pr` (`srcU_sub`, see
`EKLContract/Lemmas/isHoro_sup_same_source.lean`) — meets the root group `U_qr` trivially.

The proof is entrywise.  An element of `U_pq ⊔ U_pr` agrees with the identity off the slots
`(p,q)` and `(p,r)` (`srcU_sub_eq_set`), so in particular its `(q,r)`-entry vanishes because
`(q,r) ∉ {(p,q),(p,r)}` (both alternatives would force `q = p`).  But an element of `U_qr` is a
transvection `u_qr(s) = 1 + s E_qr`, whose `(q,r)`-entry is exactly `s`; hence `s = 0` and the
element is `1`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

theorem disjoint_Uij_srcU {p q r : Fin 3} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    ∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.Uij hqr →
      g ∈ Work.EKLContract.Uij hpq ⊔ Work.EKLContract.Uij hpr → g = 1 := by
  intro g hg hgsup
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hqr g).mp hg
  -- membership of `u_qr(s)` in the join, transported to the entrywise description
  have hmem' : Work.EKLContract.uij hqr s ∈
      (Work.EKLContract.Lemmas.srcU_sub hpq hpr : Set Work.EKLContract.SL3) := by
    rw [← Work.EKLContract.Lemmas.srcU_sup_eq_sub hpq hpr]
    exact hgsup
  have hmem : Work.EKLContract.uij hqr s ∈ Work.EKLContract.Lemmas.srcU_set p q r := by
    rwa [Work.EKLContract.Lemmas.srcU_sub_eq_set hpq hpr hqr] at hmem'
  -- the slot `(q,r)` is not one of the slots `(p,q)`, `(p,r)`
  have hcond : ¬((q = p ∧ r = q) ∨ (q = p ∧ r = r)) := by
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hpq h1.symm
    · exact hpq h1.symm
  -- the `(q,r)`-entry of `u_qr(s)` is `s`
  have h0 : Work.EKLContract.toMat (Work.EKLContract.uij hqr s) q r = s := by
    rw [Work.EKLContract.Lemmas.horoUij_toMat hqr, Matrix.add_apply, Matrix.single_apply,
      if_pos ⟨rfl, rfl⟩, Matrix.one_apply_ne hqr, zero_add]
  have hs0 : s = 0 := by
    have h := hmem q r hcond
    rw [h0, Matrix.one_apply_ne hqr] at h
    exact h
  rw [hs0, Work.EKLContract.Lemmas.horoUij_zero hqr]

end Work.EKLC6Core
