import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_split
import Submission.Work.Smooth.JordanSeparation.lwalk_transport

/-!
# The loop of the deleted walk

The `hαβ` half of the loop-level cut identity: the loop of `W.del i j` (deleting the piece from the
`i`-th to the `j`-th vertex) is null-homotopic as soon as the loop

`(joinNat W.edge i).trans (Path.cast (joinNat (fun l => W.edge (i + ((j-i) + l))) (W.n - j)) … …)`

(dropping the closed piece `W.sub i j` and then joining) is.  See `PLAN_GRID_CRUX.md`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable (W : LWalk)

theorem pt_at_cut (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    W.pt i = W.pt j := by
  show W.c * gpt (W.v i) = W.c * gpt (W.v j)
  rw [hcl]

theorem del_pt_le_self (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).pt i = W.pt i :=
  del_pt_of_le W i j hij hj hcl le_rfl

/-- The first `i` edges of the deleted walk, against the first `i` edges of `W`. -/
theorem del_head_eq (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    joinNat (p := fun k => (W.del i j hij hj hcl).pt k)
        (fun k => (W.del i j hij hj hcl).edge k) i
      = Path.cast (joinNat W.edge i) (del_pt_zero W i j hij hj hcl)
          (del_pt_le_self W i j hij hj hcl) :=
  joinNat_cast_bound (h := fun k hk => del_pt_of_le W i j hij hj hcl hk)
    (F := fun k => (W.del i j hij hj hcl).edge k) (G := fun k => W.edge k)
    (hFG := fun k hk => del_edge_cast W i j hij hj hcl hk) i le_rfl

/-- The edges of the deleted walk past the cut, against the tail of `W`. -/
theorem del_tail_eq (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    joinNat (p := fun k => (W.del i j hij hj hcl).pt (i + k))
        (fun k => (W.del i j hij hj hcl).edge (i + k)) (W.n - j)
      = Path.cast (joinNat (p := fun l => W.pt (j + l)) (fun l => W.edge (j + l)) (W.n - j))
          (del_pt_tail W i j hij hj hcl 0) (del_pt_tail W i j hij hj hcl (W.n - j)) :=
  joinNat_cast (h := fun k => del_pt_tail W i j hij hj hcl k)
    (F := fun k => (W.del i j hij hj hcl).edge (i + k)) (G := fun l => W.edge (j + l))
    (hFG := fun k => del_edge_tail W i j hij hj hcl k) (W.n - j)

theorem pt_reindex (i j l : ℕ) (hij : i < j) :
    W.pt (j + l) = W.pt (i + ((j - i) + l)) := by
  congr 1
  omega

/-- Reindexing the tail of `W`: from the `j + l` form to the `i + ((j-i) + l)` form. -/
theorem tail_reindex (i j K : ℕ) (hij : i < j) :
    joinNat (p := fun l => W.pt (j + l)) (fun l => W.edge (j + l)) K
      = Path.cast (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
            (fun l => W.edge (i + ((j - i) + l))) K)
          (pt_reindex W i j 0 hij) (pt_reindex W i j K hij) := by
  refine joinNat_cast (p := fun l => W.pt (j + l)) (q := fun l => W.pt (i + ((j - i) + l)))
    (h := fun l => pt_reindex W i j l hij) (F := fun l => W.edge (j + l))
    (G := fun l => W.edge (i + ((j - i) + l))) (hFG := fun l => ?_) K
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  simp only [LWalk.edge, segPath, Path.segment_apply]
  rw [pt_reindex W i j l hij]
  rw [show W.pt (j + l + 1) = W.pt (i + ((j - i) + l) + 1) from by congr 1; omega]


/-- **The `hαβ` half of the loop-level cut identity.**  If the loop of the deleted walk
`W.del i j` is null-homotopic, then so is the "cut" loop

`(joinNat W.edge i).trans (Path.cast (joinNat (fun l => W.edge (i + ((j-i) + l))) (W.n - j)) … …)`,

the complement of the closed piece `W.sub i j` inside `W`. -/
theorem del_loop_homotopic (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (h : Path.Homotopic (W.del i j hij hj hcl).loop (Path.refl ((W.del i j hij hj hcl).pt 0))) :
    Path.Homotopic ((joinNat W.edge i).trans (Path.cast
      (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
        (fun l => W.edge (i + ((j - i) + l))) (W.n - j))
      (pt_sub_self W i j hij hj hcl) (pt_closed_cut W i j hij hj).symm)) (Path.refl (W.pt 0)) := by
  have hJ : Path.Homotopic
      (Path.cast (joinNat (p := fun k => (W.del i j hij hj hcl).pt k)
        (fun k => (W.del i j hij hj hcl).edge k) (i + (W.n - j))) rfl
        ((W.del i j hij hj hcl).pt_last).symm)
      (Path.refl ((W.del i j hij hj hcl).pt 0)) := h
  have h2 : Path.Homotopic (joinNat (p := fun k => (W.del i j hij hj hcl).pt k)
      (fun k => (W.del i j hij hj hcl).edge k) (i + (W.n - j)))
      ((Path.cast (joinNat W.edge i) (del_pt_zero W i j hij hj hcl)
          (del_pt_le_self W i j hij hj hcl)).trans
        (Path.cast (joinNat (p := fun l => W.pt (j + l)) (fun l => W.edge (j + l)) (W.n - j))
          (del_pt_tail W i j hij hj hcl 0) (del_pt_tail W i j hij hj hcl (W.n - j)))) := by
    refine (joinNat_add (fun k => (W.del i j hij hj hcl).edge k) i (W.n - j)).trans ?_
    rw [del_head_eq W i j hij hj hcl, del_tail_eq W i j hij hj hcl]
  have hg : Path.Homotopic
      (((Path.cast (joinNat W.edge i) (del_pt_zero W i j hij hj hcl)
          (del_pt_le_self W i j hij hj hcl)).trans
        (Path.cast (joinNat (p := fun l => W.pt (j + l)) (fun l => W.edge (j + l)) (W.n - j))
          (del_pt_tail W i j hij hj hcl 0) (del_pt_tail W i j hij hj hcl (W.n - j)))).cast rfl
        ((W.del i j hij hj hcl).pt_last).symm)
      (Path.refl ((W.del i j hij hj hcl).pt 0)) :=
    ((Path.Homotopic.pathCast h2 rfl ((W.del i j hij hj hcl).pt_last).symm)).symm.trans hJ
  have heq : ((Path.cast (joinNat W.edge i) (del_pt_zero W i j hij hj hcl)
          (del_pt_le_self W i j hij hj hcl)).trans
        (Path.cast (joinNat (p := fun l => W.pt (j + l)) (fun l => W.edge (j + l)) (W.n - j))
          (del_pt_tail W i j hij hj hcl 0) (del_pt_tail W i j hij hj hcl (W.n - j)))).cast rfl
        ((W.del i j hij hj hcl).pt_last).symm
      = Path.cast ((joinNat W.edge i).trans (Path.cast
          (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
            (fun l => W.edge (i + ((j - i) + l))) (W.n - j))
          (pt_sub_self W i j hij hj hcl) (pt_closed_cut W i j hij hj).symm))
        (del_pt_zero W i j hij hj hcl) (del_pt_zero W i j hij hj hcl) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe, Path.cast_coe, Path.trans_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos ht, dif_pos ht, Path.cast_coe]
    · rw [dif_neg ht, dif_neg ht, Path.cast_coe, Path.cast_coe]
      rw [tail_reindex W i j (W.n - j) hij, Path.cast_coe]
  rw [heq] at hg
  have hZ : (Path.cast ((joinNat W.edge i).trans (Path.cast
          (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
            (fun l => W.edge (i + ((j - i) + l))) (W.n - j))
          (pt_sub_self W i j hij hj hcl) (pt_closed_cut W i j hij hj).symm))
        (del_pt_zero W i j hij hj hcl) (del_pt_zero W i j hij hj hcl)).cast
        (del_pt_zero W i j hij hj hcl).symm (del_pt_zero W i j hij hj hcl).symm
      = (joinNat W.edge i).trans (Path.cast
          (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
            (fun l => W.edge (i + ((j - i) + l))) (W.n - j))
          (pt_sub_self W i j hij hj hcl) (pt_closed_cut W i j hij hj).symm) := by
    rw [Path.cast_cast, Path.cast_self]
  have hR : (Path.refl ((W.del i j hij hj hcl).pt 0)).cast
        (del_pt_zero W i j hij hj hcl).symm (del_pt_zero W i j hij hj hcl).symm
      = Path.refl (W.pt 0) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    exact congrArg (fun z => Path.refl z t) (del_pt_zero W i j hij hj hcl)
  have hcast := Path.Homotopic.pathCast hg (del_pt_zero W i j hij hj hcl).symm
    (del_pt_zero W i j hij hj hcl).symm
  rw [hZ, hR] at hcast
  exact hcast


/-- **The loop-level cut identity.**  If the closed piece `W.sub i j` and the deleted walk
`W.del i j` are both null-homotopic then so is `W`. -/
theorem nullhomotopic_of_sub_del (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (hδ : Path.Homotopic (W.sub i j hij hj hcl).loop (Path.refl ((W.sub i j hij hj hcl).pt 0)))
    (hdel : Path.Homotopic (W.del i j hij hj hcl).loop
      (Path.refl ((W.del i j hij hj hcl).pt 0))) :
    Path.Homotopic W.loop (Path.refl (W.pt 0)) :=
  nullhomotopic_of_cut W hij hj (pt_sub_self W i j hij hj hcl) (pt_closed_cut W i j hij hj)
    (sub_loop_homotopic W i j hij hj hcl hδ) (del_loop_homotopic W i j hij hj hcl hdel)

end LWalk

end

end Work.Smooth.JordanSeparation
