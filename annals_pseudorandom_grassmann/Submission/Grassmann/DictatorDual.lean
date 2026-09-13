import Submission.Grassmann.Dictator

/-!
# The dual dictators of `L(V,W)`

Besides the `1_{A·v = w}` family, the other family of dictators of the shortcode space
`L(V,W)` is `1_{A*φ = ψ}` (`φ ∈ W*`, `ψ ∈ V*`).  These are the *transposes* of the first
family, so their degree-`1` property follows from `degLe_indicator_mulVec_eq` together with
the fact that transposition preserves the Fourier degree.

Concretely, for `A : Matrix (Fin m) (Fin n) 𝔽₂` (a map `𝔽₂ⁿ → 𝔽₂ᵐ`) and `φ : Fin m → 𝔽₂`,
`A*φ` is the functional `i ↦ ∑_j φ j * A j i` on `𝔽₂ⁿ`, i.e. `(Aᵀ).mulVec φ`.
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-- Transposition of a function on matrices. -/
def transposeFun {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    Matrix (Fin n) (Fin m) (ZMod 2) → ℂ :=
  fun B => f Bᵀ

/-- The character of the transpose is the transpose character. -/
lemma mchar_transpose {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : mchar Y Aᵀ = mchar Yᵀ A := by
  rw [mchar, mchar, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.transpose_apply, Matrix.transpose_apply]

/-- Transposition intertwines the Fourier transform (up to transposing the index). -/
lemma fhat_transposeFun {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ)
    (Y : Matrix (Fin m) (Fin n) (ZMod 2)) :
    fhat (transposeFun f) Y = fhat f Yᵀ := by
  rw [fhat, fhat]
  refine (Fintype.sum_equiv (Matrix.transposeAddEquiv (Fin n) (Fin m) (ZMod 2)).toEquiv
    (fun B : Matrix (Fin n) (Fin m) (ZMod 2) => f Bᵀ * mchar Y B)
    (fun A : Matrix (Fin m) (Fin n) (ZMod 2) => f A * mchar Y Aᵀ) ?_).trans ?_
  · intro B
    simp [Matrix.transposeAddEquiv, Matrix.transpose_transpose]
  · refine Finset.sum_congr rfl fun A _ => ?_
    rw [mchar_transpose]

/-- Transposition preserves the degree. -/
lemma degLe_transposeFun_iff {m n d : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    DegLe d (transposeFun f) ↔ DegLe (m := m) (n := n) d f := by
  constructor
  · intro h A hA
    have hY : d < (Aᵀ).rank := by rwa [Matrix.rank_transpose]
    have hthis := h Aᵀ hY
    rwa [fhat_transposeFun, Matrix.transpose_transpose] at hthis
  · intro h Y hY
    rw [fhat_transposeFun]
    exact h Yᵀ (by rwa [Matrix.rank_transpose])

/-- **The dual dictators have degree `1`**: `A ↦ 1_{A*φ = 0}` has degree at most `1`. -/
theorem degLe_indicator_dual {m n : ℕ} (φ : Fin m → ZMod 2) :
    DegLe 1 (transposeFun (m := n) (n := m)
      (fun B : Matrix (Fin n) (Fin m) (ZMod 2) =>
        if B.mulVec φ = 0 then (1 : ℂ) else 0)) :=
  (degLe_transposeFun_iff (m := n) (n := m) _).mpr
    (degLe_indicator_mulVec_zero (m := n) (n := m) φ)

/-- The same, written in terms of `(Aᵀ)·φ` (i.e. `A*φ`). -/
theorem degLe_indicator_dual' {m n : ℕ} (φ : Fin m → ZMod 2) :
    DegLe 1 (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
      if (Aᵀ).mulVec φ = 0 then (1 : ℂ) else 0) :=
  degLe_indicator_dual (m := m) (n := n) φ

end

end Submission.Grassmann
