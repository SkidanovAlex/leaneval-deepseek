import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HPgram
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.detgam_span_coords_detL

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix

namespace Work.HP

/-- Expansion of a basis of a sublattice `M ≤ L` in a basis of `L`: the coordinates are read off
from the transition matrix `LinearMap.toMatrix bM bL (Submodule.inclusion h)`. -/
lemma sub_basis_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M L : Submodule ℤ (ι → ℤ)} (hML : M ≤ L) {r : ℕ}
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M) (j : Fin r) :
    (bM j : ι → ℤ)
      = ∑ i, (LinearMap.toMatrix bM bL (Submodule.inclusion hML)) i j • (bL i : ι → ℤ) := by
  have hsum : Submodule.inclusion hML (bM j)
      = ∑ i, (LinearMap.toMatrix bM bL (Submodule.inclusion hML)) i j • bL i := by
    rw [← bL.sum_repr (Submodule.inclusion hML (bM j))]
    exact Finset.sum_congr rfl (fun i _ => by rw [LinearMap.toMatrix_apply])
  have hcoe := congrArg (fun y : L => Submodule.subtype L y) hsum
  simp only [map_sum, map_smul] at hcoe
  simpa using hcoe

/-- For `M ≤ L` of equal rank, the Gram determinant of a basis of `M` dominates that of a basis of
`L`.  If `T` is the integral transition matrix (columns = coordinates of the `bM i` in `bL`), then
`Gram(bM) = Tᵀ Gram(bL) T` over `ℝ`, so `det Gram(bM) = (det T)² det Gram(bL)`; both determinants
are positive (`Lat.gramMat_det_pos`), whence `det T ≠ 0`. -/
theorem gramMat_det_le_of_inclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M L : Submodule ℤ (ι → ℤ)} (hML : M ≤ L) {r : ℕ}
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M) :
    (gramMat r L bL).det ≤ (gramMat r M bM).det := by
  classical
  set T : Matrix (Fin r) (Fin r) ℤ := LinearMap.toMatrix bM bL (Submodule.inclusion hML)
    with hTdef
  set A : Matrix (Fin r) (Fin r) ℝ := T.map (fun z : ℤ => (z : ℝ)) with hAdef
  -- Expansion of each `bM i` in the basis `bL`, with coefficients `T`.
  have hexp : ∀ j, (bM j : ι → ℤ) = ∑ i, T i j • (bL i : ι → ℤ) := by
    intro j
    rw [hTdef]
    exact sub_basis_expand hML bL bM j
  -- Coordinate-wise expansion with the transposed matrix: `bM i = ∑ j, Tᵀ i j • bL j`.
  have hu : ∀ i x, ((bM i : ι → ℤ) x : ℝ) = ∑ j, Aᵀ i j * ((bL j : ι → ℤ) x : ℝ) := by
    intro i x
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (congrFun (hexp i).symm x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul] at h2
    rw [← h2]
    simp only [hAdef, Matrix.transpose_apply, Matrix.map_apply]
  -- Change of coordinates for real Gram matrices.
  have hgram := gram_of_coord_expansion
    (w := fun j (_ : ι) => ((bL j : ι → ℤ) _ : ℝ))
    (A := Aᵀ) (u := fun i (_ : ι) => ((bM i : ι → ℤ) _ : ℝ)) hu
  have hidM : (Matrix.of fun i j : Fin r =>
        ∑ x, (((bM i : ι → ℤ)) x : ℝ) * (((bM j : ι → ℤ)) x : ℝ)) = gramMat r M bM := by
    ext i j; simp [gramMat]
  have hidL : (Matrix.of fun i j : Fin r =>
        ∑ x, (((bL i : ι → ℤ)) x : ℝ) * (((bL j : ι → ℤ)) x : ℝ)) = gramMat r L bL := by
    ext i j; simp [gramMat]
  have hgram2 : gramMat r M bM = Aᵀ * gramMat r L bL * A := by
    rw [← hidM, ← hidL, hgram, Matrix.transpose_transpose]
  -- Determinant relation `det Gram(bM) = (det A)² det Gram(bL)`.
  have hdet : (gramMat r M bM).det = (A.det) ^ 2 * (gramMat r L bL).det := by
    rw [hgram2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hposL : 0 < (gramMat r L bL).det := Lat.gramMat_det_pos r L bL
  have hposM : 0 < (gramMat r M bM).det := Lat.gramMat_det_pos r M bM
  -- `det A ≠ 0`, hence `(det A)² ≥ 1`.
  have hA_ne : A.det ≠ 0 := by
    intro h0
    refine absurd hposM ?_
    rw [hdet, h0]
    simp
  have hT_ne : T.det ≠ 0 := by
    intro h0
    apply hA_ne
    rw [hAdef, ← Int.cast_det, h0]
    simp
  have hA_sq_ge : (1 : ℝ) ≤ (A.det) ^ 2 := by
    have hcast : A.det = ((T.det : ℤ) : ℝ) := by rw [hAdef, ← Int.cast_det]
    have h1 : (1 : ℤ) ≤ T.det ^ 2 := by
      have hp : 0 < T.det ^ 2 := sq_pos_of_ne_zero hT_ne
      omega
    calc (1 : ℝ) ≤ ((T.det ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
      _ = ((T.det : ℤ) : ℝ) ^ 2 := by push_cast; ring
      _ = (A.det) ^ 2 := by rw [hcast]
  rw [hdet]
  nlinarith [hposL, hA_sq_ge]

/-- `detL` is antitone for inclusions of equal rank: a larger lattice of the same rank has no
larger covolume.  (`detL` is the square root of the Gram determinant of any `ℤ`-basis, see
`Work.HP.Lat.detL_basis_gram`.)

HINT (note the orientation!).  Take `ℤ`-bases `bL` of `L` and `bP` of `P` with a common index type
`Fin r`, `r = rk L = rk P` (`Submodule.basisOfPid` + `Module.finrank_eq_card_basis` + reindexing), and
let `A : Matrix (Fin r) (Fin r) ℤ` be the coordinate matrix of the `bP j` in the basis `bL`:
`(bP j : ι → ℤ) = ∑ i, A i j • (bL i : ι → ℤ)` (from `Module.Basis.sum_repr`).  Then
`Gram(bP) = A_ℝ * Gram(bL) * A_ℝᵀ` entrywise (`Work.HP.gram_of_coord_expansion` in
`Submission/Work/HP/detgam_span_coords_detL.lean` does exactly this transformation), so
`det Gram(bP) = (det A)^2 * det Gram(bL)`; taking square roots (`Lat.detL_basis_gram` for both
bases, `Real.sqrt_mul`, `Real.sqrt_sq`) gives `detL P = |det A| · detL L`, and it remains to see
`A.det ≠ 0`.  For that: if `A.det = 0` there is a nonzero row vector `t : Fin r → ℤ` with
`∑ i, t i * A i j = 0` for all `j` (use the rational left kernel of `A` and clear denominators, or
for `r = 2` the explicit witnesses `(A 1 0, -A 0 0)` and `(A 1 1, -A 0 1)`), and then
`∑ j, t j • (bP j : ι → ℤ) = ∑ i, (∑ j, t j * A i j) • (bL i) = 0`, contradicting the
`ℤ`-independence of the `bP j`.  Finally `|A.det| ≥ 1` because `A.det ≠ 0`, so
`detL L = detL P / |det A| ≤ detL P`. -/
theorem detgam_detL_le_of_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {P L : Submodule ℤ (ι → ℤ)} (h : P ≤ L) (hrk : rk P = rk L) :
    detL L ≤ detL P := by
  classical
  obtain ⟨nL, bL⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  obtain ⟨nP, bP0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) P
  have hnL : rk L = nL := by
    have := Module.finrank_eq_card_basis bL
    simpa [rk] using this
  have hnP : rk P = nP := by
    have := Module.finrank_eq_card_basis bP0
    simpa [rk] using this
  have hn : nL = nP := by rw [← hnL, ← hrk, hnP]
  let bP : Module.Basis (Fin nL) ℤ P := bP0.reindex (finCongr hn).symm
  have hle : (gramMat nL L bL).det ≤ (gramMat nL P bP).det :=
    gramMat_det_le_of_inclusion h bL bP
  have hL : detL L = Real.sqrt (gramMat nL L bL).det :=
    Lat.detL_basis_gram L bL
  have hP : detL P = Real.sqrt (gramMat nL P bP).det :=
    Lat.detL_basis_gram P bP
  rw [hL, hP]
  exact Real.sqrt_le_sqrt hle

end Work.HP
