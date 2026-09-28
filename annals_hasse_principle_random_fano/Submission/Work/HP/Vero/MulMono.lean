import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulAux
import Submission.Work.HP.Vero.mulVec_symm
import Submission.Work.HP.Vero.mulVec_add_left
import Submission.Work.HP.Vero.mulVec_smul_left

/-! Right-linearity of `mulVec`, and the product of two monomial indicators. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

theorem mulVec_add_right {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B B' : Mon b n → R) :
    mulVec a b d A (B + B') = mulVec a b d A B + mulVec a b d A B' := by
  rw [mulVec_symm (A := A) (B := B + B'), mulVec_add_left,
    mulVec_symm (A := A) (B := B), mulVec_symm (A := A) (B := B')]

theorem mulVec_smul_right {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (c : R) (A : Mon a n → R) (B : Mon b n → R) :
    mulVec a b d A (c • B) = c • mulVec a b d A B := by
  rw [mulVec_symm, mulVec_smul_left, mulVec_symm]

theorem mulVec_unitMon_unitMon {a b n : ℕ} {R : Type*} [CommSemiring R]
    (p : Mon a n) (q : Mon b n) :
    mulVec a b (a + b) (unitMon (R := R) p) (unitMon (R := R) q)
      = unitMon (R := R) (addMon p q) := by
  funext M
  rw [mulVec_apply_addMon]
  have h1 : ∀ p' : Mon a n, p' ≠ p →
      (∑ q' : Mon b n,
        (if addMon p' q' = M then (unitMon (R := R) p p') * (unitMon (R := R) q q') else 0)) = 0 := by
    intro p' hp'
    apply Finset.sum_eq_zero
    intro q' _
    have h0 : unitMon (R := R) p p' = 0 := by simp [unitMon, hp']
    rw [h0, zero_mul]
    split <;> rfl
  have step1 : (∑ p' : Mon a n, ∑ q' : Mon b n,
        (if addMon p' q' = M then (unitMon (R := R) p p') * (unitMon (R := R) q q') else 0))
      = (∑ q' : Mon b n,
        (if addMon p q' = M then (unitMon (R := R) p p) * (unitMon (R := R) q q') else 0)) :=
    Finset.sum_eq_single (a := p) (fun p' _ hp' => h1 p' hp')
      (fun hp => absurd (Finset.mem_univ p) hp)
  rw [step1]
  have h2 : ∀ q' : Mon b n, q' ≠ q →
      (if addMon p q' = M then (unitMon (R := R) p p) * (unitMon (R := R) q q') else 0) = 0 := by
    intro q' hq'
    have h0 : unitMon (R := R) q q' = 0 := by simp [unitMon, hq']
    rw [h0, mul_zero]
    split <;> rfl
  have step2 : (∑ q' : Mon b n,
        (if addMon p q' = M then (unitMon (R := R) p p) * (unitMon (R := R) q q') else 0))
      = (if addMon p q = M then (unitMon (R := R) p p) * (unitMon (R := R) q q) else 0) :=
    Finset.sum_eq_single (a := q) (fun q' _ hq' => h2 q' hq')
      (fun hq => absurd (Finset.mem_univ q) hq)
  rw [step2, unitMon_same, unitMon_same, mul_one, unitMon]
  by_cases h : addMon p q = M
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem sum_smul_unitMon {d n : ℕ} {R : Type*} [CommSemiring R] (F : Mon d n → R) :
    (∑ M : Mon d n, F M • unitMon (R := R) M) = F := by
  funext M'
  rw [Finset.sum_apply]
  have h1 : ∀ b : Mon d n, b ≠ M' → F b * (if M' = b then (1 : R) else 0) = 0 := by
    intro b hb; rw [if_neg (fun h => hb h.symm), mul_zero]
  have hs : (∑ M : Mon d n, F M * (if M' = M then (1 : R) else 0))
      = (F M' * (if M' = M' then (1 : R) else 0)) :=
    Finset.sum_eq_single (a := M') (fun b _ hb => h1 b hb)
      (fun h => absurd (Finset.mem_univ M') h)
  simpa [Pi.smul_apply, smul_eq_mul, unitMon] using hs

end Work.HP.Vero
