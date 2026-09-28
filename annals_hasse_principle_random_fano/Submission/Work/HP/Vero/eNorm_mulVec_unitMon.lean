import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulAux

/-! Multiplying a coefficient vector by a single monomial `X^P` preserves the Euclidean norm. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

theorem eNorm_mulVec_unitMon {e f n : ℕ} (P : Mon e n) (c : Mon f n → ℤ) :
    eNorm (mulVec e f (e + f) (unitMon (R := ℤ) P) c) = eNorm c := by
  set G : Mon (e + f) n → ℤ := mulVec e f (e + f) (unitMon (R := ℤ) P) c with hG
  have hGval : ∀ M, G M = ∑ q : Mon f n, if addMon P q = M then c q else 0 := by
    intro M
    rw [hG, mulVec_apply_addMon]
    have step1 : ∀ p : Mon e n,
        (∑ q : Mon f n, if addMon p q = M then (unitMon (R := ℤ) P p) * c q else 0)
          = (if p = P then (∑ q : Mon f n, if addMon P q = M then c q else 0) else 0) := by
      intro p
      by_cases hp : p = P
      · subst hp
        simp [unitMon_same]
      · have h0 : unitMon (R := ℤ) P p = 0 := by simp [unitMon, hp]
        rw [if_neg hp]
        apply Finset.sum_eq_zero
        intro q _
        rw [h0, zero_mul]
        split <;> rfl
    rw [Finset.sum_congr rfl (fun p _ => step1 p)]
    rw [Finset.sum_ite_eq']
    simp
  have hval : ∀ q : Mon f n, G (addMon P q) = c q := by
    intro q
    rw [hGval (addMon P q)]
    have h1 : (∑ q' : Mon f n, if addMon P q' = addMon P q then c q' else 0)
        = (if addMon P q = addMon P q then c q else 0) :=
      Finset.sum_eq_single (a := q)
        (fun b _ hb => by rw [if_neg]; intro h; exact hb (addMon_injective_right P h))
        (fun hq => absurd (Finset.mem_univ q) hq)
    rw [h1, if_pos rfl]
  have himg : ∀ M : Mon (e + f) n,
      M ∉ (Finset.univ : Finset (Mon f n)).image (fun q => addMon P q) → G M = 0 := by
    intro M hM
    rw [hGval M]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro h
    exact hM (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, h⟩)
  simp only [eNorm]
  congr 1
  have hpart : (∑ M : Mon (e + f) n, (((G M : ℤ) : ℝ)) ^ 2)
      = ∑ M ∈ (Finset.univ : Finset (Mon f n)).image (fun q => addMon P q),
          (((G M : ℤ) : ℝ)) ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun M _ hM => by rw [himg M hM]; simp)).symm
  rw [hpart]
  have hreindex : (∑ M ∈ (Finset.univ : Finset (Mon f n)).image (fun q => addMon P q),
          (((G M : ℤ) : ℝ)) ^ 2)
      = ∑ q : Mon f n, (((G (addMon P q) : ℤ) : ℝ)) ^ 2 :=
    Finset.sum_image (fun q _ q' _ hq => addMon_injective_right P hq)
  rw [hreindex]
  exact Finset.sum_congr rfl fun q _ => by rw [hval q]

end Work.HP.Vero
