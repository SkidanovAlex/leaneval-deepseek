import Mathlib
import Submission.Work.HP.Defs

/-!
# Real-analogue definitions for the Veronese wedge estimate

This file (owned by the author of `Work.HP.veronese_wedge`) introduces the real-valued
companions of the definitions from `Submission/Work/HP/Defs.lean` that are needed for the
analytic estimate

`c * ‖x ∧ y‖ * ‖x‖^{d-1} ‖y‖^{d-1} ≤ ‖ν(x) ∧ ν(y)‖`,

together with the elementary bridges between the integral and the real formulations.

* `veroneseR d n x` is the Veronese map of a *real* vector;
* `wedgeR v w` is the covolume `√(‖v‖²‖w‖² - ⟨v,w⟩²)` of a pair of *real* vectors;
* `monWeight d n m` is the multinomial coefficient of the exponent vector `m`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-! ## The real Veronese map -/

/-- The Veronese map `ν_{d,n}` of a real vector. -/
def veroneseR (d n : ℕ) (x : Fin (n + 1) → ℝ) : Mon d n → ℝ :=
  fun m => ∏ i, x i ^ (m.1 i : ℕ)

/-! ## The real covolume -/

section vectors
variable {ι : Type*} [Fintype ι]

/-- The covolume `√(‖v‖²‖w‖² - ⟨v,w⟩²)` of a pair of real vectors. -/
def wedgeR (v w : ι → ℝ) : ℝ :=
  Real.sqrt (rNorm v ^ 2 * rNorm w ^ 2 - (dotR v w) ^ 2)

end vectors

/-! ## The multinomial weight of an exponent vector -/

/-- The multinomial coefficient `d! / ∏ m_i!` attached to an exponent vector `m`. -/
def monWeight (d n : ℕ) (m : Mon d n) : ℕ :=
  Nat.multinomial Finset.univ (fun i => (m.1 i : ℕ))

/-! ## Elementary bridges -/

section bridges
variable {ι : Type*} [Fintype ι]

@[simp] lemma toR_apply {ι : Type*} (v : ι → ℤ) (i : ι) : toR v i = (v i : ℝ) := rfl

lemma eNorm_eq_rNorm_toR_W (v : ι → ℤ) : eNorm v = rNorm (toR v) := rfl

lemma wedgeNorm_eq_wedgeR (v w : ι → ℤ) : wedgeNorm v w = wedgeR (toR v) (toR w) := by
  simp only [wedgeNorm, wedgeR, eNorm_eq_rNorm_toR_W]

@[simp] lemma toR_veronese_R (d n : ℕ) (x : Fin (n + 1) → ℤ) :
    toR (veronese d n x) = veroneseR d n (toR x) := by
  funext m
  simp only [toR_apply, veronese, veroneseR]
  push_cast
  rfl

lemma rNorm_veronese_toR (d n : ℕ) (x : Fin (n + 1) → ℤ) :
    rNorm (veroneseR d n (toR x)) = eNorm (veronese d n x) := by
  rw [← toR_veronese_R, eNorm_eq_rNorm_toR_W]

lemma dotR_veronese_toR (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    dotR (toR (veronese d n x)) (toR (veronese d n y))
      = dotR (veroneseR d n (toR x)) (veroneseR d n (toR y)) := by
  simp only [toR_veronese_R]

lemma wedgeNorm_veronese_eq (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    wedgeNorm (veronese d n x) (veronese d n y)
      = wedgeR (veroneseR d n (toR x)) (veroneseR d n (toR y)) := by
  simp only [wedgeNorm_eq_wedgeR, toR_veronese_R]

end bridges

end Work.HP
