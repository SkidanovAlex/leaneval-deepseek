import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLC8Core.aPrime_conj_u
import Submission.Work.EKLProd.map_conj_eq_of_carried

/-!
# Conjugation by `a'_{01}(s) = diag(e^s, e^s, e^{-2s})` fixes measures carried by `U_01`

`a'_{01}(s)` has equal exponents on the slots `0` and `1`, so conjugating the transvection
`u_01(r) = 1 + r E_01` by it rescales the parameter by `e^{s-s} = 1`: it *commutes* with every
element of the root group `U_01` (`Work.EKLC8Core.aPrime_conj_u`, transported here to
`Work.EKLCContract.Uij h01`).  Consequently a measure carried by `U_01` (i.e. giving `U_01`
full mass) is invariant under conjugation by `a'_{01}(s)`; this is the centraliser instance of
`Work.EKLProd.map_conj_eq_of_carried`.

This is the `A'_{01}`-part of the `A`-covariance `U7` used in the leafwise argument.
-/

namespace Work.EKLCompLeaf

open MeasureTheory Work.EKLContract

/-- `a'_{01}(s) = aPrime 2 s` commutes with every element of the root group `U_01`. -/
theorem aPrime_comm_uij_h01 (s r : ℝ) :
    aPrime 2 s * uij Work.EKLComp.h01 r = uij Work.EKLComp.h01 r * aPrime 2 s := by
  have h := Work.EKLC8Core.aPrime_conj_u s r
  have h' : aPrime 2 s * uij Work.EKLComp.h01 r * (aPrime 2 s)⁻¹ = uij Work.EKLComp.h01 r := h
  calc aPrime 2 s * uij Work.EKLComp.h01 r
      = (aPrime 2 s * uij Work.EKLComp.h01 r * (aPrime 2 s)⁻¹) * aPrime 2 s := by group
    _ = uij Work.EKLComp.h01 r * aPrime 2 s := by rw [h']

/-- A measure carried by `U_01` is invariant under conjugation by `a'_{01}(s)`. -/
theorem map_conj_aPrime_eq_self (m : MeasureTheory.Measure Work.EKLContract.SL3)
    (hm : m (Work.EKLContract.Uij Work.EKLComp.h01 : Set Work.EKLContract.SL3)ᶜ = 0) (s : ℝ) :
    m.map (fun g => Work.EKLContract.aPrime 2 s * g * (Work.EKLContract.aPrime 2 s)⁻¹) = m := by
  refine Work.EKLProd.map_conj_eq_of_carried (T := Uij Work.EKLComp.h01)
    (g₀ := aPrime 2 s) ?_ hm
  intro g hg
  obtain ⟨r, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 g).mp hg
  exact aPrime_comm_uij_h01 s r

end Work.EKLCompLeaf
