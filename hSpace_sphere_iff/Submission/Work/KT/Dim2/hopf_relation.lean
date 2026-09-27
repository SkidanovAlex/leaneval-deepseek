import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.sum_mvN_assoc
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.mvN_additive
import Submission.Work.KT.mvN_comm
import Submission.Work.KT.mvN_assoc
import Submission.Work.KT.Fund.hopf_trace_det
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det
import Submission.Work.KT.Fund.mvN_one_kron_of_trace_det

/-!
# The Bott relation `H² + 1 = 2H` for the Hopf bundle over `S²`

This file proves the Murray–von Neumann relation
`(hopfIdem ⊗ hopfIdem) ⊕ 1₁ ~ hopfIdem ⊕ hopfIdem` over `C(S², ℂ)`, i.e. `[H⊗H] + 1 = 2[H]`
in `K⁰(S²)`, equivalently `(H-1)² = 0`.

The argument runs through the splitting of the rank-two bundle `ℂ² ⊗ H` (the Euler sequence):
`H ⊗ H ⊕ 1  ~  (H ⊗ H) ⊕ (H ⊗ (1 - H))  ~  H ⊗ (H ⊕ (1 - H))  ~  H ⊗ 1₂  ~  H ⊕ H`.

* first equivalence: `1 ~ H ⊗ H^⊥` (`Fund.mvN_one_kron_of_trace_det`), the trivialisation
  `H ⊗ (1 - H) ≅ 1` coming from the standard Hermitian structure on `ℂ²`;
* `⊕` is a congruence for `Mat.MvN` (`sum_mvN_congr`);
* the middle two: `Mat.kron` distributes over `Mat.sum` (`mvN_additive`) and the complementary
  projection `H ⊕ (1 - H)` is the trivial rank-two bundle (`mvN_sum_compl`);
* the last: `H ⊗ 1₂` and `H ⊕ H` are the two reindexings of the single Kronecker matrix
  `h ⊗ 1` along `Fin 2 × Fin 2 ≃ Fin 4`.

Everything is proved first for an abstract `2 × 2` matrix `h` with trace `1` and vanishing
determinant over a commutative ring (`hopf_relation_general`), and then specialised to
`hopfIdem`, whose trace and determinant are supplied by `Fund.hopf_trace_det`.  `K`-theory here
lives in the matrix model of `Submission.Work.KT.Defs`.
-/

namespace Work.KT.Dim2

open Matrix

noncomputable section

/-! ## The index identification `Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2` -/

/-- `Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2`: the first summand is sent to the second tensor leg `0`, the
second summand to the second tensor leg `1`. -/
def sumProdFinTwo : Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2 where
  toFun
    | Sum.inl i => (i, 0)
    | Sum.inr j => (j, 1)
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv := by rintro (i | j) <;> simp
  right_inv := by rintro ⟨i, j⟩; fin_cases j <;> simp

@[simp] lemma sumProdFinTwo_inl (i : Fin 2) : sumProdFinTwo (Sum.inl i) = (i, 0) := rfl
@[simp] lemma sumProdFinTwo_inr (j : Fin 2) : sumProdFinTwo (Sum.inr j) = (j, 1) := rfl

/-- Reading `h ⊗ 1₂` along `Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2` gives the block diagonal matrix
`[[h, 0], [0, h]]`; both are the same Kronecker matrix in different coordinates. -/
lemma fromBlocks_eq_reindex_kron_h {R : Type} [Ring R] (h : Matrix (Fin 2) (Fin 2) R) :
    Matrix.fromBlocks h 0 0 h
      = Matrix.reindex sumProdFinTwo.symm sumProdFinTwo.symm
          (Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R)) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-! ## Reindexing invariance of `Mat.MvN` for an abstract index type -/

/-- Two reindexings of the same idempotent matrix are Murray–von Neumann equivalent; the common
witnesses are `K` itself read through the two bijections. -/
theorem mvN_reindex_reindex_fin {A : Type} [Ring A] {ι : Type} [Fintype ι]
    (K : Matrix ι ι A) (hK : K * K = K) {m k : ℕ} (e : ι ≃ Fin m) (f : ι ≃ Fin k) :
    Mat.MvN (⟨m, Matrix.reindex e e K⟩ : Mat A) ⟨k, Matrix.reindex f f K⟩ := by
  refine ⟨Matrix.reindex f e K, Matrix.reindex e f K, ?_, ?_⟩
  · show Matrix.reindex e f K * Matrix.reindex f e K = Matrix.reindex e e K
    rw [reindexMul, hK]
  · show Matrix.reindex f e K * Matrix.reindex e f K = Matrix.reindex f f K
    rw [reindexMul, hK]

/-! ## `H ⊗ 1₂ ~ H ⊕ H` -/

/-- For a `2 × 2` idempotent `h`, the bundle `h ⊗ 1₂` (the Kronecker matrix `h ⊗ 1`, reindexed to
`Fin (2 * 2)`) is Murray–von Neumann equivalent to `h ⊕ h`: both are reindexings of the single
Kronecker matrix `h ⊗ 1` along the two identifications `Fin 2 × Fin 2 ≃ Fin 4`. -/
lemma mvN_kron_one_two {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (hh : h * h = h) :
    Mat.MvN (Mat.kron (⟨2, h⟩ : Mat R) (Mat.one R 2)) (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, h⟩) := by
  have hK : Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R) *
      Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R)
      = Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [← Matrix.mul_kronecker_mul h h (1 : Matrix (Fin 2) (Fin 2) R) 1, hh, mul_one]
  have hgen := mvN_reindex_reindex_fin
    (K := Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R)) hK
    finProdFinEquiv (sumProdFinTwo.symm.trans finSumFinEquiv)
  have hR : Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks h 0 0 h)
      = Matrix.reindex (sumProdFinTwo.symm.trans finSumFinEquiv)
          (sumProdFinTwo.symm.trans finSumFinEquiv)
          (Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R)) := by
    rw [fromBlocks_eq_reindex_kron_h h, mvNassoc_reindex_reindex]
  change Mat.MvN
    (⟨2 * 2, Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) h (1 : Matrix (Fin 2) (Fin 2) R))⟩ : Mat R)
    (⟨2 + 2, Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks h 0 0 h)⟩ : Mat R)
  rw [hR]
  exact hgen

/-! ## The Bott relation for an abstract rank-one projection -/

/-- **The Bott relation for a rank-one `2 × 2` projection.**  If `h` is a `2 × 2` matrix over a
commutative ring with trace `1` and vanishing determinant, then
`(h ⊗ h) ⊕ 1 ~ h ⊕ h`.  Only the trace and determinant of `h` are used: they make `h` (and its
complement `1 - h`) idempotent, and trivialise `h ⊗ (1 - h)` (`Fund.mvN_one_kron_of_trace_det`). -/
theorem hopf_relation_general {R : Type} [CommRing R] (h : Matrix (Fin 2) (Fin 2) R)
    (htr : h 0 0 + h 1 1 = 1) (hdet : h 0 0 * h 1 1 = h 0 1 * h 1 0) :
    Mat.MvN ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum (Mat.one R 1))
      (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, h⟩) := by
  have hcomm : ∀ x y : R, x * y = y * x := fun x y => mul_comm x y
  -- idempotency
  have hhidem : Mat.IsIdem (⟨2, h⟩ : Mat R) := Fund.twoByTwo_idem_of_trace_det h htr hdet
  have heidem : Mat.IsIdem (⟨2, 1 - h⟩ : Mat R) := Mat.isIdem_one_sub hhidem
  have hKK : Mat.IsIdem (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩) :=
    Mat.kron_idem hcomm hhidem hhidem
  -- (A) `1 ~ H ⊗ (1 - H)`
  have hA : Mat.MvN (Mat.one R 1) (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩) :=
    Fund.mvN_one_kron_of_trace_det h htr hdet
  -- (B) add `H ⊗ H` on both sides
  have hB : Mat.MvN ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum (Mat.one R 1))
      ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum
        (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩)) :=
    sum_mvN_congr R (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩) (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩)
      (Mat.one R 1) (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩) (Mat.mvN_refl hKK) hA
  -- (C1) tensor distributes over the block sum
  have hC1 : Mat.MvN (Mat.kron (⟨2, h⟩ : Mat R) (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩))
      ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum
        (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩)) :=
    mvN_additive.1 R (⟨2, h⟩ : Mat R) (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩
  -- (C2) `H ⊕ (1 - H) ~ 1₂`, hence `H ⊗ (H ⊕ (1 - H)) ~ H ⊗ 1₂`
  have hC2a : Mat.MvN (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩) (Mat.one R 2) :=
    mvN_sum_compl R (⟨2, h⟩ : Mat R) hhidem
  have hC2 : Mat.MvN (Mat.kron (⟨2, h⟩ : Mat R) (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩))
      (Mat.kron (⟨2, h⟩ : Mat R) (Mat.one R 2)) :=
    mvN_kron_right hcomm hC2a hhidem
  -- (D) `H ⊗ 1₂ ~ H ⊕ H`
  have hC3 : Mat.MvN (Mat.kron (⟨2, h⟩ : Mat R) (Mat.one R 2))
      (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, h⟩) := mvN_kron_one_two h hhidem
  -- idempotency of each matrix in the chain
  have i1 : ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum (Mat.one R 1)).IsIdem :=
    Mat.sum_idem hKK (Mat.one_isIdem R 1)
  have i2 : ((Mat.kron (⟨2, h⟩ : Mat R) ⟨2, h⟩).sum
      (Mat.kron (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩)).IsIdem :=
    Mat.sum_idem hKK (Mat.kron_idem hcomm hhidem heidem)
  have i3 : (Mat.kron (⟨2, h⟩ : Mat R) (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, 1 - h⟩)).IsIdem :=
    Mat.kron_idem hcomm hhidem (Mat.sum_idem hhidem heidem)
  have i4 : (Mat.kron (⟨2, h⟩ : Mat R) (Mat.one R 2)).IsIdem :=
    Mat.kron_idem hcomm hhidem (Mat.one_isIdem R 2)
  have i5 : (Mat.sum (⟨2, h⟩ : Mat R) ⟨2, h⟩).IsIdem := Mat.sum_idem hhidem hhidem
  exact Mat.mvN_trans i1 i2 i5 hB
    (Mat.mvN_trans i2 i3 i5 (Mat.mvN_symm hC1)
      (Mat.mvN_trans i3 i4 i5 hC2 hC3))

/-! ## The Bott relation for the Hopf bundle -/

/-- The Bott relation `H ⊗ H ⊕ 1 ≅ H ⊕ H` for the Hopf bundle, in its sharpest form: the
rank-two bundle `H ⊗ H ⊕ 1` (the block sum `(hopfIdem ⊗ hopfIdem) ⊕ 1₁`, a `5 × 5` idempotent
over `C(S², ℂ)`) is Murray–von Neumann equivalent to `H ⊕ H`, a `4 × 4` idempotent.  This is
`[H⊗H] + 1 = 2[H]` in `K⁰(S²)`, i.e. `(H-1)² = 0`.  Geometrically it is the split Euler sequence
`0 → 1 → ℂ² ⊗ H → H ⊗ H → 0`, using the Hermitian structure on `ℂ²` (the tautological line
`L ⊂ ℂ²` and its orthogonal complement `L^⊥ ≅ L^{-1}`, with `L^{-1} ⊗ L ≅ 1`). -/
theorem hopf_relation :
    Work.KT.Mat.MvN
      (Work.KT.Mat.sum
        (Work.KT.Mat.kron Work.KT.hopfIdem Work.KT.hopfIdem)
        (Work.KT.Mat.one C(Work.KT.S2, ℂ) 1))
      (Work.KT.Mat.sum Work.KT.hopfIdem Work.KT.hopfIdem) := by
  exact hopf_relation_general hopfIdem.2 Fund.hopf_trace_det.1 Fund.hopf_trace_det.2

end

end Work.KT.Dim2
