import Mathlib
import Submission.Work.HP.Sig2.Poisson1D

/-!
# Shared definitions for the 0-phase Gaussian Poisson summation

This file sets up the vocabulary used by `Work.HP.Sig2.gaussian_poisson_zero`:

* `qForm G x = xᵀ G x`, the quadratic form of a real matrix, on an arbitrary finite index type;
* the "peeled data" of a matrix indexed by `Fin (R+1)`: its top-left entry `pHead`, its first row
  tail `pVec`, its bottom-right block `pTail`, the vector `pWind = (pTail G)⁻¹ *ᵥ pVec G` and the
  Schur complement `pSchur G = pHead G - ∑ i, pVec G i * pWind G i`;
* `finStatement n`, the statement of the Poisson identity for matrices indexed by `Fin n`.
-/

noncomputable section

open Matrix

namespace Work.HP.Sig2

/-- The quadratic form `x ᵀ G x` of a real matrix `G`, on a general finite index type. -/
def qForm {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * G i j * x j

lemma qForm_eq_dotProduct {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) :
    qForm G x = x ⬝ᵥ (G *ᵥ x) := by
  simp only [qForm, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma qForm_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {G : Matrix ι ι ℝ}
    (hG : G.PosSemidef) (x : ι → ℝ) : 0 ≤ qForm G x := by
  rw [qForm_eq_dotProduct]
  have := hG.re_dotProduct_nonneg x
  simpa using this

/-- Top-left entry of a matrix indexed by `Fin (R+1)`. -/
def pHead {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) : ℝ := G 0 0

/-- First row tail of a matrix indexed by `Fin (R+1)`. -/
def pVec {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) : Fin R → ℝ := fun i => G 0 i.succ

/-- Bottom-right block of a matrix indexed by `Fin (R+1)`. -/
def pTail {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) : Matrix (Fin R) (Fin R) ℝ :=
  fun i j => G i.succ j.succ

/-- `(pTail G)⁻¹ *ᵥ pVec G`, the vector completing the square for the bottom-right block. -/
def pWind {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) : Fin R → ℝ :=
  (pTail G)⁻¹ *ᵥ pVec G

/-- The Schur complement of the bottom-right block: `pHead G - bᵀ (pTail G)⁻¹ b`. -/
def pSchur {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) : ℝ :=
  pHead G - ∑ i, pVec G i * pWind G i

/-- The 0-phase Gaussian Poisson summation for matrices indexed by `Fin n`. -/
def finStatement (n : ℕ) : Prop :=
  ∀ (G : Matrix (Fin n) (Fin n) ℝ), G.PosDef → ∀ (s : ℝ), 0 < s → ∀ (u : Fin n → ℝ),
    (∑' m : Fin n → ℤ,
      Complex.exp (((-(Real.pi / s ^ 2) * qForm G (fun i => (m i : ℝ) + u i)) : ℝ)))
      = ((s : ℂ) ^ n / ((Real.sqrt G.det : ℝ) : ℂ)) *
        ∑' m : Fin n → ℤ,
          Complex.exp (((-(Real.pi * s ^ 2) * qForm G⁻¹ (fun i => (m i : ℝ))) : ℝ)
            + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * u j : ℝ) : ℂ))

end Work.HP.Sig2
