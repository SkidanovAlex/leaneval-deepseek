import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/KT/DESIGN.md 'Addendum: psi'. SHARED helper needed by psi_exists (H8) and psi_comm (H6). CONVENTION: [Ring A] + explicit commutativity, never [CommRing A].
-/

namespace Work.KT.Psi

open Matrix

/-- Conjugation invariance. -/
theorem cls_conj (A : Type) [Ring A] (N : ℕ) (P u v : Matrix (Fin N) (Fin N) A)
    (huv : u * v = 1) (hvu : v * u = 1) :
    cls (⟨N, u * P * v⟩ : Mat A) = cls ⟨N, P⟩ := by
  by_cases hP : Mat.IsIdem (⟨N, P⟩ : Mat A)
  · have hPP : P * P = P := hP
    have hQ : Mat.IsIdem (⟨N, u * P * v⟩ : Mat A) := by
      show (u * P * v) * (u * P * v) = u * P * v
      calc (u * P * v) * (u * P * v) = u * P * (v * u) * P * v := by noncomm_ring
        _ = u * (P * P) * v := by rw [hvu]; noncomm_ring
        _ = u * P * v := by rw [hPP]
    have hMvN : Mat.MvN (⟨N, P⟩ : Mat A) ⟨N, u * P * v⟩ := by
      refine ⟨u * P, P * v, ?_, ?_⟩
      · calc (P * v) * (u * P) = P * (v * u) * P := by noncomm_ring
          _ = P := by rw [hvu]; simp [hPP]
      · calc (u * P) * (P * v) = u * (P * P) * v := by noncomm_ring
          _ = u * P * v := by rw [hPP]
    exact (cls_eq_of_MvN hP hQ hMvN).symm
  · have hQ : ¬ Mat.IsIdem (⟨N, u * P * v⟩ : Mat A) := by
      intro hc
      refine hP ?_
      have key : v * ((u * P * v) * (u * P * v)) * u = v * (u * P * v) * u :=
        congrArg (fun M => v * M * u) hc
      have e1 : v * ((u * P * v) * (u * P * v)) * u
          = (v * u) * P * (v * u) * P * (v * u) := by noncomm_ring
      have e2 : v * (u * P * v) * u = (v * u) * P * (v * u) := by noncomm_ring
      rw [e1, e2, hvu] at key
      show P * P = P
      simpa using key
    rw [cls_zero_of_not_idem hQ, cls_zero_of_not_idem hP]

end Work.KT.Psi
