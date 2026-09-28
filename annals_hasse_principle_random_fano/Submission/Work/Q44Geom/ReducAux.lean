import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.PairsAux
import Submission.Work.Q44Geom.ReducDefs

/-!
# Elementary auxiliary facts for `Work.Q44Geom.reducible_count`

Cast compatibility between the integral multiplication `Work.HP.Vero.mulVec` and its real
counterpart, injectivity of `formOf`, and finiteness of Euclidean balls of integer vectors.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom

open Work.HP
open Work.HP.Vero

/-- `eNorm` is the Euclidean norm of the realification. -/
lemma eNorm_eq_rNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    eNorm v = rNorm (fun i => (v i : ℝ)) := rfl

lemma eNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

/-- `mulVec` commutes with the cast `ℤ → ℝ`. -/
lemma mulVec_intCast {a b : ℕ} (A : Mon a 4 → ℤ) (B : Mon b 4 → ℤ) :
    (fun M : Mon (a + b) 4 => ((mulVec a b (a + b) A B M : ℤ) : ℝ))
      = mulVec a b (a + b) (fun m => (A m : ℝ)) (fun m => (B m : ℝ)) := by
  funext M
  simp only [mulVec]
  push_cast
  simp

lemma eNorm_mulVec_intCast {a b : ℕ} (A : Mon a 4 → ℤ) (B : Mon b 4 → ℤ) :
    eNorm (mulVec a b (a + b) A B)
      = rNorm (mulVec a b (a + b) (fun m => (A m : ℝ)) (fun m => (B m : ℝ))) := by
  rw [eNorm_eq_rNorm, mulVec_intCast]

/-- `formOf` is injective. -/
lemma formOf_injective {d : ℕ} {a b : Mon d 4 → ℤ}
    (h : formOf d 4 a = formOf d 4 b) : a = b := by
  funext m
  have h1 := congrArg (fun p : MvPolynomial (Fin 5) ℚ => p.coeff m.toFinsupp) h
  rw [formOf_coeff, formOf_coeff] at h1
  exact_mod_cast h1

/-- A primitive integral vector is nonzero. -/
lemma isPrim_ne_zero' {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h
  have h0 : Finset.univ.gcd v = 0 := by
    rw [h]
    rw [Finset.gcd_eq_zero_iff]
    intro i _
    rfl
  rw [IsPrim] at hv
  rw [h0] at hv
  exact one_ne_zero hv.symm

lemma finite_ball {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) :
    (({A : ι → ℤ | eNorm A ≤ R} : Set (ι → ℤ))).Finite := by
  refine (Finset.finite_toSet (Fintype.piFinset
    (fun _ : ι => Finset.Icc (-(⌈R⌉₊ : ℤ)) (⌈R⌉₊ : ℤ)))).subset ?_
  intro A hA
  simp only [Finset.mem_coe] at hA ⊢
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : |(A i : ℝ)| ≤ eNorm A := abs_apply_le_eNorm A i
  have h2 : |(A i : ℝ)| ≤ (⌈R⌉₊ : ℝ) := le_trans (le_trans h1 hA) (Nat.le_ceil R)
  obtain ⟨h3, h4⟩ := abs_le.mp h2
  exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩

lemma finite_pair_ball {d d' : ℕ} (R S : ℝ) :
    (({p : (Mon d 4 → ℤ) × (Mon d' 4 → ℤ) |
        eNorm p.1 ≤ R ∧ eNorm p.2 ≤ S} : Set _)).Finite :=
  (finite_ball (ι := Mon d 4) R).prod (finite_ball (ι := Mon d' 4) S)

end Work.Q44Geom
