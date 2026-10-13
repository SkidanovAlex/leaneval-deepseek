/-
  WilG4c : vocabulary for the affine-interpolation graph lemma `Work.WilG4c.AffineInterpGraph`.

  Given `Ω`-definable graphs of `lo, hi : ℝ^m → ℝ`, we want the graph of the interpolation
  `(x, t) ↦ lo x + (hi x - lo x) * t` to be `Ω`-definable, with a format and a degree that
  depend on the input only through `F` and `D`.

  As in `Work.WilG4a.affine_chart_graph_mem` we work in `ℝ^{m+4}`, with coordinates
  `(params, t, y, u, v)` (`u` records `lo` of the parameters, `v` records `hi`), but the
  relation set is now

    `ipRelSet m = {z | z (acgY m) = z (acgU m) + (z (acgV m) - z (acgU m)) * z (acgT m)}`

  i.e. `y = u + (v - u) * t`.  The relation is *expanded* to `y - u - v * t + u * t` in the
  polynomial `ipRelPoly m`, in which form the crude `MvPolynomial.totalDegree` calculus gives
  the honest bound `2` (the unexpanded form `(v - u) * t` would only give `3`).
-/
import Mathlib
import Submission.Work.WilG4a.affine_chart_graph_mem
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open WilkiesDesign

namespace Work.WilG4c

/-! ## The relation set `y = u + (v - u) * t` -/

/-- The polynomial `y - u - v * t + u * t` of `ℝ^{m+4}`: the expanded form of the relation
`y = u + (v - u) * t`. -/
def ipRelPoly (m : ℕ) : MvPolynomial (Fin (m+4)) ℝ :=
  MvPolynomial.X (Work.WilG4a.acgY m) - MvPolynomial.X (Work.WilG4a.acgU m) -
    MvPolynomial.X (Work.WilG4a.acgV m) * MvPolynomial.X (Work.WilG4a.acgT m) +
      MvPolynomial.X (Work.WilG4a.acgU m) * MvPolynomial.X (Work.WilG4a.acgT m)

/-- The relation `y = u + (v - u) * t` in `ℝ^{m+4}`. -/
def ipRelSet (m : ℕ) : Set (Fin (m+4) → ℝ) :=
  {z | z (Work.WilG4a.acgY m) =
    z (Work.WilG4a.acgU m) +
      (z (Work.WilG4a.acgV m) - z (Work.WilG4a.acgU m)) * z (Work.WilG4a.acgT m)}

theorem mem_ipRelSet (m : ℕ) (z : Fin (m+4) → ℝ) :
    z ∈ ipRelSet m ↔ z (Work.WilG4a.acgY m) =
      z (Work.WilG4a.acgU m) +
        (z (Work.WilG4a.acgV m) - z (Work.WilG4a.acgU m)) * z (Work.WilG4a.acgT m) :=
  Iff.rfl

theorem ipRelPoly_eval (m : ℕ) (z : Fin (m+4) → ℝ) :
    MvPolynomial.eval z (ipRelPoly m) =
      z (Work.WilG4a.acgY m) - z (Work.WilG4a.acgU m) -
        z (Work.WilG4a.acgV m) * z (Work.WilG4a.acgT m) +
          z (Work.WilG4a.acgU m) * z (Work.WilG4a.acgT m) := by
  simp [ipRelPoly]

theorem ipRelPoly_set (m : ℕ) :
    {z : Fin (m+4) → ℝ | MvPolynomial.eval z (ipRelPoly m) = 0} = ipRelSet m := by
  ext z
  rw [Set.mem_ofPred_eq, ipRelPoly_eval, mem_ipRelSet]
  constructor <;> intro h <;> linarith

/-! ## The degree bound and the `Ω`-membership -/

theorem ipRelPoly_totalDegree_le (m : ℕ) : (ipRelPoly m).totalDegree ≤ 2 := by
  have hX : ∀ s : Fin (m+4), (MvPolynomial.X s : MvPolynomial (Fin (m+4)) ℝ).totalDegree ≤ 2 := by
    intro s
    rw [MvPolynomial.totalDegree_X]
    decide
  have hmul : ∀ s t : Fin (m+4),
      (MvPolynomial.X s * MvPolynomial.X t : MvPolynomial (Fin (m+4)) ℝ).totalDegree ≤ 2 := by
    intro s t
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  have hVT := hmul (Work.WilG4a.acgV m) (Work.WilG4a.acgT m)
  have hUT := hmul (Work.WilG4a.acgU m) (Work.WilG4a.acgT m)
  have hYU : ((MvPolynomial.X (Work.WilG4a.acgY m) - MvPolynomial.X (Work.WilG4a.acgU m) :
      MvPolynomial (Fin (m+4)) ℝ)).totalDegree ≤ 2 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (hX _) (by decide)
    · exact le_trans (hX _) (by decide)
  have h1 : ((MvPolynomial.X (Work.WilG4a.acgY m) - MvPolynomial.X (Work.WilG4a.acgU m)) -
      MvPolynomial.X (Work.WilG4a.acgV m) * MvPolynomial.X (Work.WilG4a.acgT m) :
      MvPolynomial (Fin (m+4)) ℝ).totalDegree ≤ 2 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le hYU hVT)
  rw [ipRelPoly]
  exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le h1 hUT)

/-- `ipRelSet m` is `Ω`-definable with format the ambient dimension `m+4` and degree `2`. -/
theorem ipRelSet_mem (S : WilkiesDesign.SOMin) (m : ℕ) :
    ipRelSet m ∈ S.Ω (m+4) 2 (m+4) := by
  have h := S.hyp (m+4) (ipRelPoly m)
  rw [ipRelPoly_set] at h
  exact Work.WilG5.mem_mono h (m+4) 2 le_rfl (ipRelPoly_totalDegree_le m)

end Work.WilG4c
