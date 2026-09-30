import Mathlib
import Submission.Work.BW.vaaler_minkowski_int
import Submission.Work.BW.logHeight_le_of_mixed_coord_le
import Submission.Work.BW.normAtPlace_le_of_repr_le
import Submission.Work.BW.prod_place_pow_le
import Submission.Work.BW.finprod_finitePlace_iSup_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Coordinates for the Siegel step over a number field

This file sets up the vocabulary used by `Submission/Work/BW/siegel_numberField.lean`:

* the orthonormal coordinates of `E^N` (`E` the Euclidean mixed space of `F`), reindexed from
  `Fin N × index F` into a single `Fin (N * d)` — so that matrices, `Matrix.mulVec` and
  `Work.BW.vaaler_minkowski_int` can be applied directly;
* `siegelNormCoord N x`, the coordinate vector of the mixed embedding of `x : Fin N → 𝓞 F`;
* `siegelGramDet v`, the Gram determinant `√det (AᵀA)` of the matrix whose columns are the `v i`;
* `siegelVaalerMinkowskiFin`, the Vaaler + Minkowski theorem in this coordinate form;
* `siegelLogHeightLeOfNormCoord`, bounding the height by a coordinate bound.
-/

open scoped Classical

namespace Work.BW

open NumberField Matrix

noncomputable section

/-- `Fintype.card (index F) = [F : ℚ]` for a number field `F`. -/
lemma siegelCardIndex (F : Type*) [Field F] [NumberField F] :
    Fintype.card (NumberField.mixedEmbedding.index F) = Module.finrank ℚ F := by
  rw [← Module.finrank_eq_card_basis (NumberField.mixedEmbedding.stdBasis F),
    NumberField.mixedEmbedding.finrank]

variable {F : Type*} [Field F] [NumberField F]

/-- The reindexing `Fin N × index F ≃ Fin (N * d)` of the orthonormal coordinates of `E^N`. -/
def siegelCoordIdxEquiv (N : ℕ) :
    (Fin N × NumberField.mixedEmbedding.index F) ≃ Fin (N * Module.finrank ℚ F) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) (Fintype.equivFinOfCardEq (siegelCardIndex F))).trans
    finProdFinEquiv

/-- The `l`-th orthonormal coordinate of the mixed embedding of a tuple of algebraic integers. -/
def siegelNormCoord (N : ℕ) (x : Fin N → NumberField.RingOfIntegers F)
    (l : Fin (N * Module.finrank ℚ F)) : ℝ :=
  (NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F
        (((x ((siegelCoordIdxEquiv (F := F) N).symm l).1 : NumberField.RingOfIntegers F)) : F))
      ((siegelCoordIdxEquiv (F := F) N).symm l).2

/-- `siegelNormCoord` in the original `(j, w)` indexing. -/
lemma siegelNormCoord_apply (N : ℕ) (x : Fin N → NumberField.RingOfIntegers F) (j : Fin N)
    (w : NumberField.mixedEmbedding.index F) :
    siegelNormCoord (F := F) N x (siegelCoordIdxEquiv (F := F) N (j, w)) =
      (NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F ((x j : NumberField.RingOfIntegers F) : F)) w := by
  simp [siegelNormCoord]

/-- The Gram determinant `√det (AᵀA)` of the matrix whose columns are the `v i`. -/
def siegelGramDet {N k : ℕ} (v : Fin k → (Fin (N * Module.finrank ℚ F) → ℝ)) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of (fun i i' => ∑ l, v i l * v i' l)))

/-- The Gram matrix `Mᵀ * M` of a matrix, as an explicit matrix of inner products of columns. -/
lemma siegelGram_eq {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ) :
    Mᵀ * M = Matrix.of (fun i i' => ∑ l, M l i * M l i') := by
  ext i i'
  simp [Matrix.mul_apply, Matrix.transpose_apply]

/-- The Gram matrix of a family with `ℝ`-independent columns is nonsingular. -/
lemma siegelDetGramNeZero {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (h : LinearIndependent ℝ (fun j => M.col j)) : (Mᵀ * M).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hxne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : x ⬝ᵥ ((Mᵀ * M) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  have h2 : x ⬝ᵥ ((Mᵀ * M) *ᵥ x) = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose (A := Mᵀ) (x := x), Matrix.transpose_transpose]
  have hMx : M *ᵥ x = 0 := dotProduct_self_eq_zero.mp (by rw [← h2]; exact h1)
  have hsum : ∑ j, x j • M.col j = 0 := by
    rw [show (∑ j, x j • M.col j) = M *ᵥ x from by
      ext l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.col_apply, mul_comm]]
    exact hMx
  exact hxne (funext fun i => Fintype.linearIndependent_iff.mp h x hsum i)

/-- **Vaaler + Minkowski in orthonormal coordinates.**  If the coordinate vectors
`v i : Fin (N*d) → ℝ` are `ℝ`-linearly independent and `siegelGramDet v ≤ r ^ k`, then there is a
nonzero integer combination whose coordinates are all bounded by `r` in absolute value. -/
theorem siegelVaalerMinkowskiFin {N k : ℕ} (hk : 1 ≤ k)
    (v : Fin k → (Fin (N * Module.finrank ℚ F) → ℝ)) (hli : LinearIndependent ℝ v) {r : ℝ}
    (hr : 0 < r) (h : siegelGramDet v ≤ r ^ k) :
    ∃ t : Fin k → ℤ, t ≠ 0 ∧ ∀ l, |∑ i, (t i : ℝ) * v i l| ≤ r := by
  set M : Matrix (Fin (N * Module.finrank ℚ F)) (Fin k) ℝ := Matrix.of (fun l i => v i l)
  have hcol : (fun j => M.col j) = v := by
    funext j l
    rw [Matrix.col_apply]
    rfl
  have hdet : (Mᵀ * M).det ≠ 0 := siegelDetGramNeZero M (by rw [hcol]; exact hli)
  have hgram : Real.sqrt (Mᵀ * M).det ≤ r ^ k := by
    have h2 : Mᵀ * M = Matrix.of (fun i i' => ∑ l, v i l * v i' l) := by
      rw [siegelGram_eq]
      ext i i'
      simp [M]
    rw [h2]
    exact h
  obtain ⟨t, htne, ht⟩ := vaaler_minkowski_int hk M hdet hr hgram
  refine ⟨t, htne, fun l => ?_⟩
  have hsum : (∑ i, (t i : ℝ) * v i l) = ∑ i, M l i * (t i : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [M, mul_comm]
  rw [hsum]
  exact ht l

/-- **Height bound from an orthonormal coordinate bound.**  If all orthonormal coordinates of the
mixed embedding of `x : Fin N → 𝓞 F` are bounded by `ρ ≥ 1`, then
`logHeight x ≤ d · log ρ + r₂ · log 2`. -/
theorem siegelLogHeightLeOfNormCoord (N : ℕ) (x : Fin N → NumberField.RingOfIntegers F) {ρ : ℝ}
    (hρ : 1 ≤ ρ) (h : ∀ l, |siegelNormCoord (F := F) N x l| ≤ ρ) :
    Height.logHeight (fun j => (x j : F)) ≤ (Module.finrank ℚ F : ℝ) * Real.log ρ +
      (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * Real.log 2 := by
  refine logHeight_le_of_mixed_coord_le (F := F) x hρ fun j w => ?_
  have h' := h (siegelCoordIdxEquiv (F := F) N (j, w))
  rwa [siegelNormCoord_apply] at h'

end

end Work.BW

namespace Work.BW

open NumberField Matrix

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- **Height bound from an orthonormal coordinate bound**, with no lower bound on `ρ`.  If a
nonzero tuple `x : Fin N → 𝓞 F` has all orthonormal coordinates of its mixed embedding bounded by
`ρ > 0` in absolute value, then `logHeight x ≤ d · log ρ + r₂ · log 2`.

Compared with `siegelLogHeightLeOfNormCoord` (which assumes `1 ≤ ρ`), this uses the product formula
rather than `log⁺`: the finite places contribute at most `0` (integrality) and the archimedean
places contribute `log ρ` (real) resp. `log (√2 ρ)` (complex). -/
theorem siegelLogHeightLeOfNormCoordOfPos {N : ℕ} (x : Fin N → NumberField.RingOfIntegers F)
    (hx : x ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ l, |siegelNormCoord (F := F) N x l| ≤ ρ) :
    Height.logHeight (fun j => (x j : F)) ≤ (Module.finrank ℚ F : ℝ) * Real.log ρ +
      (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * Real.log 2 := by
  classical
  have hx' : (fun j => (x j : F)) ≠ 0 := by
    intro h0
    exact hx (funext fun j => by
      have h1 := congrFun h0 j
      simp only [Pi.zero_apply] at h1
      exact Subtype.coe_injective h1)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (funext fun j => absurd j.2 (by omega)) hx
    · exact h
  haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hbound : ∀ v : NumberField.InfinitePlace F,
      (⨆ j, v ((x j : F))) ≤ Work.BW.placeBound (F := F) ρ v := by
    intro v
    refine ciSup_le fun j => ?_
    rw [← NumberField.mixedEmbedding.normAtPlace_apply]
    refine Work.BW.normAtPlace_le_of_repr_le (NumberField.mixedEmbedding F ((x j : F)))
      hρ.le ?_ v
    intro k
    have h1 := h (siegelCoordIdxEquiv (F := F) N (j, k))
    rwa [siegelNormCoord_apply] at h1
  have harch : (∏ v : NumberField.InfinitePlace F, (⨆ j, v ((x j : F))) ^ v.mult) ≤
      ρ ^ (Module.finrank ℚ F) * 2 ^ (NumberField.InfinitePlace.nrComplexPlaces F) := by
    refine (Finset.prod_le_prod₀ ?_ ?_).trans (Work.BW.prod_place_pow_le ρ)
    · intro v _
      exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v fun j => (x j : F)) _
    · intro v _
      exact pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass v fun j => (x j : F))
        (hbound v) _
  have hfin : (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F))) ≤ 1 :=
    Work.BW.finprod_finitePlace_iSup_le_one x hx
  have hprod : Height.mulHeight (fun j => (x j : F)) ≤
      ρ ^ (Module.finrank ℚ F) * 2 ^ (NumberField.InfinitePlace.nrComplexPlaces F) := by
    rw [NumberField.mulHeight_eq hx']
    calc (∏ v : NumberField.InfinitePlace F, (⨆ j, v ((x j : F))) ^ v.mult) *
          (∏ᶠ v : NumberField.FinitePlace F, ⨆ j, v ((x j : F)))
        ≤ (∏ v : NumberField.InfinitePlace F, (⨆ j, v ((x j : F))) ^ v.mult) * 1 :=
          mul_le_mul_of_nonneg_left hfin
            (Finset.prod_nonneg fun v _ =>
              pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v fun j => (x j : F)) _)
      _ = (∏ v : NumberField.InfinitePlace F, (⨆ j, v ((x j : F))) ^ v.mult) := mul_one _
      _ ≤ ρ ^ (Module.finrank ℚ F) * 2 ^ (NumberField.InfinitePlace.nrComplexPlaces F) := harch
  have hlog := Real.log_le_log (Height.mulHeight_pos _) hprod
  have heq : Real.log (ρ ^ (Module.finrank ℚ F) *
        2 ^ (NumberField.InfinitePlace.nrComplexPlaces F))
      = (Module.finrank ℚ F : ℝ) * Real.log ρ +
        (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [Height.logHeight_eq_log_mulHeight]
  exact hlog.trans heq.le

end

end Work.BW
