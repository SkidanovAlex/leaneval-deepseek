import Mathlib
import Submission.Work.KT.Defs

/-!
# `1` is Murray–von Neumann equivalent to `h ⊗ (1 - h)` for a `2 × 2` matrix with
trace one and vanishing determinant

Let `R` be a commutative ring and `h ∈ M₂(R)` with `tr h = 1` and `det h = 0`.
By Cayley–Hamilton `h` is then an idempotent of rank one: all its `2 × 2` minors vanish,
i.e. `h i k * h l j = h i j * h l k` for all indices (lemma `key_minor` below).  The
complementary idempotent `1 - h` has entries `(1 - h)₀₀ = h₁₁`, `(1 - h)₀₁ = -h₀₁`,
`(1 - h)₁₀ = -h₁₀`, `(1 - h)₁₁ = h₀₀`.

The Kronecker product `h ⊗ (1 - h)` is then a rank-one idempotent in `M₄(R)`, and it is
Murray–von Neumann equivalent to the `1 × 1` identity: the explicit factorisation
`h ⊗ (1 - h) = v · uᵀ` with `uᵀ · v = 1` is

  `v = (h₀₁, -h₀₀, h₁₁, -h₁₀)ᵀ`,   `u = (h₁₀, -h₀₀, h₁₁, -h₀₁)ᵀ`,

the normalisation `uᵀ v = a² + d² + 2 b c = (a + d)² = 1` being exactly `tr h = 1`.

This is the algebraic input identifying the rank-one projective module `h R² ⊗ (1-h) R²`
with `R`, used in the `K`-theoretic computation of the Hopf invariant.
-/

namespace Work.KT.Fund

open Matrix

/-- The column-vector entries `v_{i,k} = (-1)^k h_{i,1-k}` of the first factor:
`v_{i,0} = h_{i,1}`, `v_{i,1} = -h_{i,0}`. -/
private def mvV {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R) (i k : Fin 2) : R :=
  if k = 0 then h i 1 else -h i 0

/-- The row-vector entries `u_{j,l} = (-1)^l h_{1-l,j}` of the second factor:
`u_{j,0} = h_{1,j}`, `u_{j,1} = -h_{0,j}`. -/
private def mvU {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R) (j l : Fin 2) : R :=
  if l = 0 then h 1 j else -h 0 j

/-- **Rank-one relations.**  `tr h = 1` and `det h = 0` force all `2 × 2` minors of `h` to
vanish: `h_{ik} h_{lj} = h_{ij} h_{lk}`.  (Together with Cayley–Hamilton this says that `h`
is a rank-one idempotent; only the vanishing of the minors is needed below.) -/
private lemma key_minor {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (hdet : h 0 0 * h 1 1 = h 0 1 * h 1 0) :
    ∀ i j k l : Fin 2, h i k * h l j = h i j * h l k := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one] <;>
    first
      | rfl
      | (linear_combination (1 : R) * hdet)
      | (linear_combination (-1 : R) * hdet)
      | ring

/-- **The outer-product identity.**  With `v` and `u` as above, `v_{ik} u_{jl}` is the
`((i,k),(j,l))` entry of `h ⊗ (1 - h)`. -/
private lemma mvV_mul_mvU {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (htr : h 0 0 + h 1 1 = 1) (hdet : h 0 0 * h 1 1 = h 0 1 * h 1 0) :
    ∀ i j k l : Fin 2, mvV h i k * mvU h j l = h i j * (1 - h) k l := by
  have h1 : (1 : R) - h 0 0 = h 1 1 := by rw [sub_eq_iff_eq_add, add_comm]; exact htr.symm
  have h2 : (1 : R) - h 1 1 = h 0 0 := by rw [sub_eq_iff_eq_add]; exact htr.symm
  have f00 : (1 - h) 0 0 = h 1 1 := by simp [Matrix.sub_apply, h1]
  have f01 : (1 - h) 0 1 = -h 0 1 := by simp [Matrix.sub_apply]
  have f10 : (1 - h) 1 0 = -h 1 0 := by simp [Matrix.sub_apply]
  have f11 : (1 - h) 1 1 = h 0 0 := by simp [Matrix.sub_apply, h2]
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [Fin.zero_eta, Fin.mk_one, mvV, mvU, f00, f01, f10, f11] <;>
    norm_num <;>
    first
      | rfl
      | (linear_combination (1 : R) * hdet)
      | (linear_combination (-1 : R) * hdet)
      | ring

/-- **`1` and `h ⊗ (1 - h)` are Murray–von Neumann equivalent.**  The witnesses are the
explicit column `v` and row `uᵀ`; `uᵀ v = (h₀₀ + h₁₁)² = 1` uses `tr h = 1`, and
`v uᵀ = h ⊗ (1 - h)` is `mvV_mul_mvU`. -/
theorem mvN_one_kron_of_trace_det {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (htr : h 0 0 + h 1 1 = 1) (hdet : h 0 0 * h 1 1 = h 0 1 * h 1 0) :
    Mat.MvN (Mat.one R 1) (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩) := by
  let a : Matrix (Fin (2 * 2)) (Fin 1) R :=
    fun p _ => mvV h ((finProdFinEquiv (m := 2) (n := 2)).symm p).1
      ((finProdFinEquiv (m := 2) (n := 2)).symm p).2
  let b : Matrix (Fin 1) (Fin (2 * 2)) R :=
    fun _ q => mvU h ((finProdFinEquiv (m := 2) (n := 2)).symm q).1
      ((finProdFinEquiv (m := 2) (n := 2)).symm q).2
  refine ⟨a, b, ?_, ?_⟩
  · -- `b * a = 1`, i.e. `∑ₓ uₓ vₓ = 1`
    change b * a = (1 : Matrix (Fin 1) (Fin 1) R)
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.mul_apply]
    rw [Matrix.one_apply, if_pos rfl]
    rw [← Equiv.sum_comp (finProdFinEquiv (m := 2) (n := 2)) (fun r => b 0 r * a r 0)]
    rw [Fintype.sum_prod_type]
    simp only [a, b, Equiv.symm_apply_apply]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [mvV, mvU]
    norm_num
    linear_combination (h 0 0 + h 1 1 + 1) * htr - 2 * hdet
  · -- `a * b = h ⊗ (1 - h)`
    change a * b = kronMat h (1 - h)
    ext p q
    obtain ⟨⟨i, k⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective p
    obtain ⟨⟨j, l⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective q
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_one]
    simp only [a, b, Equiv.symm_apply_apply]
    rw [kronMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
    simp only [Equiv.symm_apply_apply]
    exact mvV_mul_mvU h htr hdet i j k l

end Work.KT.Fund
