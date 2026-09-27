import Mathlib

/-!
# `Work.KT.Bott.LauDefs` — matrix-norm and straight-line-homotopy scaffolding

Self-contained tools for `Work.KT.Bott.laurent_approx` (the Laurent approximation of invertible
matrices over `C(X × S¹, ℂ)`): the `ℓ∞` operator norm `mNorm` of a square matrix (the norm in
which the Neumann-series invertibility criterion `Work.KT.isUnit_one_sub_of_matNorm_lt_one` is
phrased), the parameter function `tC` and the entrywise linear segment `seg`.
-/

set_option linter.style.haveILetI false

namespace Work.KT.Bott.LauDefs

open Matrix

noncomputable section

/-- The `ℓ∞` operator norm of a square matrix, as an `NNReal`: `sup_i ∑_j ‖A i j‖`. -/
def mNorm {R : Type*} [NormedRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) : NNReal :=
  Finset.univ.sup fun i => ∑ j, ‖A i j‖₊

/-- Submultiplicativity of the `ℓ∞` operator norm. -/
lemma mNorm_mul_le {R : Type*} [NormedRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R) :
    mNorm n (A * B) ≤ mNorm n A * mNorm n B := by
  letI : NormedRing (Matrix (Fin n) (Fin n) R) := Matrix.linftyOpNormedRing
  have hA : ‖A‖₊ = mNorm n A := Matrix.linfty_opNNNorm_def A
  have hB : ‖B‖₊ = mNorm n B := Matrix.linfty_opNNNorm_def B
  have hAB : ‖A * B‖₊ = mNorm n (A * B) := Matrix.linfty_opNNNorm_def (A * B)
  rw [← hAB, ← hA, ← hB]
  exact nnnorm_mul_le A B

/-- Scalar multiplication does not increase the `ℓ∞` operator norm by more than the norm of the
scalar. -/
lemma mNorm_smul_le {R : Type*} [NormedRing R] (n : ℕ) (c : R)
    (A : Matrix (Fin n) (Fin n) R) : mNorm n (c • A) ≤ ‖c‖₊ * mNorm n A := by
  unfold mNorm
  refine Finset.sup_le fun i _ => ?_
  have h1 : ∀ j : Fin n, ‖(c • A) i j‖₊ ≤ ‖c‖₊ * ‖A i j‖₊ := by
    intro j
    simpa [Matrix.smul_apply] using nnnorm_mul_le c (A i j)
  calc ∑ j, ‖(c • A) i j‖₊ ≤ ∑ j, ‖c‖₊ * ‖A i j‖₊ := Finset.sum_le_sum fun j _ => h1 j
    _ = ‖c‖₊ * ∑ j, ‖A i j‖₊ := by rw [Finset.mul_sum]
    _ ≤ ‖c‖₊ * Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) :=
        mul_le_mul_of_nonneg_left
          (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)) (by positivity)

/-- Mapping a matrix through a ring homomorphism whose values do not increase the norm does not
increase the `ℓ∞` operator norm. -/
lemma mNorm_map_le {R S : Type*} [NormedRing R] [NormedRing S] (n : ℕ) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (A : Matrix (Fin n) (Fin n) R) :
    mNorm n (A.map φ) ≤ mNorm n A := by
  unfold mNorm
  refine Finset.sup_le fun i _ => ?_
  calc ∑ j, ‖(A.map φ) i j‖₊ = ∑ j, ‖φ (A i j)‖₊ := by simp [Matrix.map_apply]
    _ ≤ ∑ j, ‖A i j‖₊ := Finset.sum_le_sum fun j _ => by
        rw [← NNReal.coe_le_coe]
        simpa using hφ (A i j)
    _ ≤ Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) :=
        Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)

/-- `mNorm` is insensitive to the order of the difference. -/
lemma mNorm_sub_comm {R : Type*} [NormedRing R] (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) R) : mNorm n (A - B) = mNorm n (B - A) := by
  unfold mNorm
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply]
  rw [show A i j - B i j = -(B i j - A i j) by abel, nnnorm_neg]

/-- The parameter `t ∈ [0,1]`, as a continuous `ℂ`-valued function on `Y × [0,1]`. -/
def tC (Y : Type) [TopologicalSpace Y] : C(Y × unitInterval, ℂ) :=
  ⟨fun p => ((p.2 : ℝ) : ℂ), by fun_prop⟩

@[simp] lemma tC_apply (Y : Type) [TopologicalSpace Y] (p : Y × unitInterval) :
    tC Y p = ((p.2 : ℝ) : ℂ) := rfl

@[simp] lemma tC_zero (Y : Type) [TopologicalSpace Y] (y : Y) :
    tC Y (y, 0) = 0 := rfl

@[simp] lemma tC_one (Y : Type) [TopologicalSpace Y] (y : Y) :
    tC Y (y, 1) = 1 := rfl

/-- The linear segment joining two matrices over `C(Y, ℂ)`, as a matrix over `C(Y × [0,1], ℂ)`:
entry `(i,j)` is the function `(y,t) ↦ (1-t) * u i j y + t * V i j y`. -/
def seg {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    Matrix (Fin n) (Fin n) C(Y × unitInterval, ℂ) :=
  fun i j => ⟨fun p => (1 - tC Y p) * u i j p.1 + tC Y p * V i j p.1, by
    have h1 : Continuous fun p : Y × unitInterval => u i j p.1 :=
      (u i j).continuous.comp continuous_fst
    have h2 : Continuous fun p : Y × unitInterval => V i j p.1 :=
      (V i j).continuous.comp continuous_fst
    have h3 : Continuous fun p : Y × unitInterval => tC Y p := (tC Y).continuous
    exact ((continuous_const.sub h3).mul h1).add (h3.mul h2)⟩

@[simp] lemma seg_apply_zero {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) (i j : Fin n) (y : Y) :
    seg u V i j (y, 0) = u i j y := by simp [seg]

@[simp] lemma seg_apply_one {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (u V : Matrix (Fin n) (Fin n) C(Y, ℂ)) (i j : Fin n) (y : Y) :
    seg u V i j (y, 1) = V i j y := by simp [seg]

end

end Work.KT.Bott.LauDefs
