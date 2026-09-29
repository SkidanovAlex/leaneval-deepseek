import Mathlib
import Submission.HvdH.Interfaces

/-!
# Tensor infrastructure for the Gaussian resampling maps (paper Thm 4.1)

The resampling maps `A = ⊗ᵢ resA sᵢ tᵢ α` and `B = ⊗ᵢ resB sᵢ tᵢ α` of Theorem 4.1 are tensors
(Kronecker products) of the one-dimensional matrices from `Submission.HvdH.Interfaces`.

We define the tensor of a family of matrices given as a scalar entry function
`f : ℕ → ℕ → ℕ → ℂ` (`f i j k` = `(i`-th matrix)₍ⱼₖ₎`) acting on flat lexicographic arrays
`Fin (List.prod ss) → ℂ`, exactly in the digits layout of `HvdH.digits`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Unbundled matrix entry: `M j k` when `j < n`, `k < m`, else `0`. -/
noncomputable def unb (n m : ℕ) (M : Matrix (Fin n) (Fin m) ℂ) (j k : ℕ) : ℂ :=
  if h : j < n ∧ k < m then M ⟨j, h.1⟩ ⟨k, h.2⟩ else 0

@[simp] theorem unb_apply {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℂ) {j k : ℕ}
    (hj : j < n) (hk : k < m) : unb n m M j k = M ⟨j, hj⟩ ⟨k, hk⟩ := by
  simp [unb, hj, hk]

/-- Unbundled entry of the normalised 1-D DFT matrix. -/
noncomputable def dE (n : ℕ) : ℕ → ℕ → ℂ := unb n n (dftMat n)

/-- Unbundled entry of `resA s t α : Matrix (Fin t) (Fin s)`. -/
noncomputable def rA (s t α : ℕ) : ℕ → ℕ → ℂ := unb t s (resA s t α)

/-- Unbundled entry of `resB s t α : Matrix (Fin s) (Fin t)`. -/
noncomputable def rB (s t α : ℕ) : ℕ → ℕ → ℂ := unb s t (resB s t α)

/-- `∏ᵢ f i (digits ts J)ᵢ (digits ss K)ᵢ`. -/
noncomputable def digitProd (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) (J K : ℕ) : ℂ :=
  ((List.range ss.length).map
    (fun i => f i ((digits ts J).getD i 0) ((digits ss K).getD i 0))).prod

/-- Tensor (Kronecker product) of a family of matrices, acting on flat lexicographic arrays. -/
noncomputable def tensorFun (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ)
    (u : Fin ss.prod → ℂ) : Fin ts.prod → ℂ :=
  fun J => ∑ K : Fin ss.prod, digitProd ss ts f (J : ℕ) (K : ℕ) * u K

/-- The tensor as a linear map. -/
noncomputable def tensorLin (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (Fin ss.prod → ℂ) →ₗ[ℂ] (Fin ts.prod → ℂ) where
  toFun := tensorFun ss ts f
  map_add' u v := by
    funext J
    simp only [tensorFun, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext J
    simp only [tensorFun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun K _ => ?_
    ring

@[simp] theorem tensorLin_apply (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) (u : Fin ss.prod → ℂ) :
    tensorLin ss ts f u = tensorFun ss ts f u := rfl

/-- `A := ⊗ᵢ resA sᵢ tᵢ α : (Fin ss.prod → ℂ) → (Fin ts.prod → ℂ)`. -/
noncomputable def resAop (ss ts : List ℕ) (α : ℕ) :
    (Fin ss.prod → ℂ) →ₗ[ℂ] (Fin ts.prod → ℂ) :=
  tensorLin ss ts (fun i => rA (ss.getD i 0) (ts.getD i 0) α)

/-- `B := ⊗ᵢ resB sᵢ tᵢ α : (Fin ts.prod → ℂ) → (Fin ss.prod → ℂ)`. -/
noncomputable def resBop (ss ts : List ℕ) (α : ℕ) :
    (Fin ts.prod → ℂ) →ₗ[ℂ] (Fin ss.prod → ℂ) :=
  tensorLin ts ss (fun i => rB (ss.getD i 0) (ts.getD i 0) α)

/-- `⊗ᵢ dftMat tᵢ`, the tensor factorisation of the multidimensional DFT. -/
noncomputable def dftOp (ts : List ℕ) : (Fin ts.prod → ℂ) →ₗ[ℂ] (Fin ts.prod → ℂ) :=
  tensorLin ts ts (fun i => dE (ts.getD i 0))

end Work.Resample
