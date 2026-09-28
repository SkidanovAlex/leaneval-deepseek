import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# The squared determinant of the lattice spanned by two integer vectors

For two `ℤ`-linearly independent vectors `x y : ι → ℤ`, the rank-`2` lattice
`L = span ℤ {x, y}` has determinant (= Euclidean covolume) equal to
`√(‖x‖²‖y‖² - ⟨x,y⟩²)`, the covolume of the parallelogram spanned by `x` and `y`.
Squaring, the classical formula

`detL (span ℤ {x, y})² = ‖x‖² ‖y‖² - ⟨x,y⟩²`

follows: the right hand side is non-negative by Cauchy–Schwarz, so the square root
in the definition of the determinant can be unwound with `Real.sq_sqrt`.

The determinant is computed from the Gram matrix of the `ℤ`-basis of `L` given by
`Module.Basis.span hxy` (indexed by `Fin 2`), using basis-independence of `detL`
(`Work.HP.Lat.detL_basis_gram`).  Concretely the Gram matrix is
`!![‖x‖², ⟨x,y⟩; ⟨x,y⟩, ‖y‖²]` and its determinant is `‖x‖²‖y‖² - ⟨x,y⟩²`.

Note `dotZ x y` is the integer pairing `∑ i, x i * y i` of `Work.HP.Defs`, whose real
cast is the Euclidean inner product `∑ i, (x i : ℝ) * (y i : ℝ)`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.ESL

open Work.HP

theorem detL_span_pair_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) :
    detL (Submodule.span ℤ ({x, y} : Set (ι → ℤ))) ^ 2
      = eNorm x ^ 2 * eNorm y ^ 2 - ((dotZ x y : ℤ) : ℝ) ^ 2 := by
  -- Rewrite the two-element spanning set as the range of the pair `![x, y]`.
  have hspan : Submodule.span ℤ ({x, y} : Set (ι → ℤ))
      = Submodule.span ℤ (Set.range ![x, y]) := by
    congr 1
    ext z
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
  -- Identify `detL` with the square root of the determinant of the Gram matrix of the
  -- canonical basis of the span.
  have hgram : detL (Submodule.span ℤ ({x, y} : Set (ι → ℤ)))
      = √((∑ k, (x k : ℝ) * (x k : ℝ)) * (∑ k, (y k : ℝ) * (y k : ℝ))
        - (∑ k, (x k : ℝ) * (y k : ℝ)) * (∑ k, (y k : ℝ) * (x k : ℝ))) := by
    rw [hspan, Work.HP.Lat.detL_basis_gram _ (Module.Basis.span hxy), Matrix.det_fin_two]
    simp only [Matrix.of_apply, Module.Basis.coe_span_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  -- The three entries of the Gram matrix, in terms of `eNorm` and `dotZ`.
  have hSx : (∑ k, (x k : ℝ) * (x k : ℝ)) = eNorm x ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ((x i : ℝ)))]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_two]
  have hSy : (∑ k, (y k : ℝ) * (y k : ℝ)) = eNorm y ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ((y i : ℝ)))]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_two]
  have hTyx : (∑ k, (y k : ℝ) * (x k : ℝ)) = ∑ k, (x k : ℝ) * (y k : ℝ) :=
    Finset.sum_congr rfl fun k _ => by ring
  have hdot : ((dotZ x y : ℤ) : ℝ) = ∑ k, (x k : ℝ) * (y k : ℝ) := by
    simp only [dotZ, Int.cast_sum, Int.cast_mul]
  -- Cauchy–Schwarz: the radicand is non-negative.
  have hCS : (∑ k, (x k : ℝ) * (y k : ℝ)) ^ 2
      ≤ (∑ k, (x k : ℝ) * (x k : ℝ)) * (∑ k, (y k : ℝ) * (y k : ℝ)) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun k => (x k : ℝ)) (fun k => (y k : ℝ))
    simpa [pow_two] using h
  have hnonneg : 0 ≤ eNorm x ^ 2 * eNorm y ^ 2 - (∑ k, (x k : ℝ) * (y k : ℝ)) ^ 2 := by
    rw [← hSx, ← hSy]
    nlinarith [hCS]
  rw [hgram, hSx, hSy, hTyx, hdot]
  conv_lhs => rw [← pow_two]
  rw [Real.sq_sqrt hnonneg]

end Work.HP.ESL
