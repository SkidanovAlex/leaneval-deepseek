/-
  WilE7 / DimAPI — surjectivity of the differential of a `Good` absolute stratum's equation map.

  `S : Stratum 0 q` is an absolute stratum, i.e. a semi-Pfaffian set `S.X` in `ℝ^(0+q)` together
  with `S.j` defining equations `S.h a`.  `S.Good` says that at every point `z ∈ S.X.set`

  * the equations vanish,
  * the *fibrewise* Jacobian `(eaEval S.X.c (eaD S.X.c (yDir 0 l) (S.h a)) z)_{a,l}` — the
    `S.j × q` matrix of the derivatives along the last `q` coordinates, which for `p = 0` are
    *all* the coordinates — has rank `S.j`,
  * the level set of the equations coincides with `S.X` locally.

  The rank statement is exactly what is needed: the full Jacobian
  `(eaEval S.X.c (eaD S.X.c i (S.h a)) z)_{a : Fin S.j, i : Fin (0+q)}` is the same matrix up to
  the reindexing of its columns by the bijection `Fin.natAdd 0 : Fin q → Fin (0+q)`
  (`Fin.natAdd_zero`), so it also has rank `S.j`; a matrix whose rank equals its number of rows
  defines a surjective linear map, whence the range of the differential is `⊤`.

  The reindexing step is `rank_submatrix_of_inv` below (rank invariance under a bijective
  reindexing of the columns, proved from `Matrix.rank_submatrix_le` in both directions).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE7.Auxiliary.rangePiEqTopOfRank

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

/-- The rank of a matrix does not change when its columns are reindexed by a function `f` which
has a left inverse `g` (in particular by a bijection).  Both inequalities come from
`Matrix.rank_submatrix_le`: one for `f`, one for `g`, using `f (g i) = i`. -/
lemma rank_submatrix_of_inv {m n n' : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (f : Fin n' → Fin n)
    (g : Fin n → Fin n') (hg : ∀ i, f (g i) = i) :
    (M.submatrix id f).rank = M.rank := by
  refine le_antisymm (Matrix.rank_submatrix_le M id f) ?_
  have h1 : M = (M.submatrix id f).submatrix id g := by
    ext a i; simp [Matrix.submatrix, hg i]
  calc M.rank = ((M.submatrix id f).submatrix id g).rank := congrArg Matrix.rank h1
    _ ≤ (M.submatrix id f).rank := Matrix.rank_submatrix_le _ id g

/-- **The differential of the equation map of a `Good` absolute stratum is surjective.**

The equation map is `w ↦ (a ↦ eaEval S.X.c (S.h a) w) : ℝ^(0+q) → ℝ^(S.j)`, and its differential
at a point `z` of the stratum is the full Jacobian `(eaEval S.X.c (eaD S.X.c i (S.h a)) z)`.
`S.Good` gives the full row rank `S.j` of this Jacobian (its columns are the `q` fibre directions,
which for `p = 0` exhaust all coordinates), so the differential maps onto `ℝ^(S.j)`. -/
theorem range_fderiv_good_eq_top {q : ℕ} (S : WilkiesDesign.E.Stratum 0 q)
    (hS : S.Good) {z : Fin (0 + q) → ℝ} (hz : z ∈ S.X.set) :
    (fderiv ℝ (fun w : Fin (0 + q) → ℝ => fun a : Fin S.j =>
        WilkiesDesign.E.eaEval S.X.c (S.h a) w) z).range = ⊤ := by
  set M : Matrix (Fin S.j) (Fin (0 + q)) ℝ :=
    Matrix.of (fun (a : Fin S.j) (i : Fin (0 + q)) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c i (S.h a)) z) with hM
  -- The differential of the equation map is the matrix-vector map of the full Jacobian.
  have hG : HasFDerivAt (fun w : Fin (0 + q) → ℝ => fun a : Fin S.j =>
        WilkiesDesign.E.eaEval S.X.c (S.h a) w)
      (ContinuousLinearMap.pi (fun a : Fin S.j => ∑ i : Fin (0 + q),
        WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c i (S.h a)) z •
          (ContinuousLinearMap.proj i : (Fin (0 + q) → ℝ) →L[ℝ] ℝ))) z :=
    hasFDerivAt_pi.mpr fun a =>
      Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z
  rw [hG.fderiv]
  -- A matrix with rank equal to its number of rows gives a surjective map.
  refine Work.WilE7.Aux.rangePiEqTopOfRank
    (fun (a : Fin S.j) (i : Fin (0 + q)) =>
      WilkiesDesign.E.eaEval S.X.c (WilkiesDesign.E.eaD S.X.c i (S.h a)) z) ?_
  -- The `Good` matrix is the full Jacobian with its columns reindexed by `Fin.natAdd 0`.
  have hN : (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      WilkiesDesign.E.eaEval S.X.c
        (WilkiesDesign.E.eaD S.X.c (Work.WilE5.yDir 0 l) (S.h a)) z)
      = M.submatrix id (Fin.natAdd 0) := by
    rw [hM]
    ext a l
    simp [Matrix.submatrix, Work.WilE5.yDir]
  have hrank : M.rank = S.j := by
    have h1 := rank_submatrix_of_inv M (Fin.natAdd 0) (Fin.cast (Nat.zero_add q))
      (fun i => by ext; simp)
    rw [← h1, ← hN]
    exact Work.WilE5.Stratum.good_rank hS hz
  exact hrank

end Work.WilE7.DimAPI
