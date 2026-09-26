import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic
import Submission.Work.Smooth.JordanSeparation.plCutAssemble

/-!
# Splitting a closed lattice walk at a repeated vertex

For a closed lattice walk `W` and a *non-trivial* double point, i.e. `i < j ≤ W.n` with
`W.v i = W.v j` and `(i,j) ≠ (0, W.n)`, the walk splits as `α · δ · β` where
* `δ = W.sub i j` is the closed sub-walk from the `i`-th to the `j`-th vertex,
* `α · β` is realized by `W.del i j`,

both strictly shorter than `W`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable (W : LWalk)

/-- The closed sub-walk from the `i`-th to the `j`-th vertex (`W.v i = W.v j`). -/
abbrev sub (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) : LWalk where
  n := j - i
  c := W.c
  cpos := W.cpos
  v := fun k => W.v (i + k)
  step := by
    intro k hk
    have h1 : i + k < W.n := by omega
    exact W.step (i + k) h1
  closed := by
    show W.v (i + (j - i)) = W.v (i + 0)
    rw [Nat.add_zero, Nat.add_sub_cancel' (le_of_lt hij)]
    exact hcl.symm

/-- The walk obtained by deleting the piece between the `i`-th and the `j`-th vertex. -/
abbrev del (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) : LWalk where
  n := i + (W.n - j)
  c := W.c
  cpos := W.cpos
  v := fun k => if k ≤ i then W.v k else W.v (j + (k - i))
  step := by
    intro k hk
    by_cases h2 : k + 1 ≤ i
    · have h1 : k ≤ i := by omega
      show GridStep (if k ≤ i then W.v k else W.v (j + (k - i)))
        (if k + 1 ≤ i then W.v (k + 1) else W.v (j + (k + 1 - i)))
      rw [if_pos h1, if_pos h2]
      exact W.step k (by omega)
    · by_cases h1 : k ≤ i
      · have hki : k = i := by omega
        show GridStep (if k ≤ i then W.v k else W.v (j + (k - i)))
          (if k + 1 ≤ i then W.v (k + 1) else W.v (j + (k + 1 - i)))
        rw [if_pos h1, if_neg h2, hki]
        have hval : W.v (j + (i + 1 - i)) = W.v (j + 1) := by
          congr 1; omega
        rw [hval, hcl]
        exact W.step j (by omega)
      · have h1' : i < k := by omega
        show GridStep (if k ≤ i then W.v k else W.v (j + (k - i)))
          (if k + 1 ≤ i then W.v (k + 1) else W.v (j + (k + 1 - i)))
        rw [if_neg h1, if_neg h2]
        have hval : W.v (j + (k + 1 - i)) = W.v (j + (k - i) + 1) := by
          congr 1; omega
        rw [hval]
        exact W.step (j + (k - i)) (by omega)
  closed := by
    by_cases hle : i + (W.n - j) ≤ i
    · have hjn : j = W.n := by omega
      show (if i + (W.n - j) ≤ i then W.v (i + (W.n - j))
        else W.v (j + (i + (W.n - j) - i))) = (if 0 ≤ i then W.v 0 else W.v (j + (0 - i)))
      rw [if_pos hle, if_pos (Nat.zero_le i)]
      have hii : i + (W.n - j) = i := by omega
      rw [hjn] at hcl
      rw [hii]
      exact hcl.trans W.closed
    · show (if i + (W.n - j) ≤ i then W.v (i + (W.n - j))
        else W.v (j + (i + (W.n - j) - i))) = (if 0 ≤ i then W.v 0 else W.v (j + (0 - i)))
      rw [if_neg hle, if_pos (Nat.zero_le i), Nat.add_sub_cancel_left, Nat.add_sub_cancel' hj]
      exact W.closed

@[simp] theorem sub_pt (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) (k : ℕ) :
    (W.sub i j hij hj hcl).pt k = W.pt (i + k) := rfl

@[simp] theorem sub_edge (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) (k : ℕ) :
    (W.sub i j hij hj hcl).edge k = W.edge (i + k) := rfl

@[simp] theorem sub_path (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.sub i j hij hj hcl).path
      = joinNat (p := fun l => W.pt (i + l)) (fun l => W.edge (i + l)) (j - i) := rfl

theorem del_pt_of_le (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    {k : ℕ} (hk : k ≤ i) : (W.del i j hij hj hcl).pt k = W.pt k := by
  show W.c * gpt (if k ≤ i then W.v k else W.v (j + (k - i))) = W.pt k
  rw [if_pos hk]

theorem del_pt_zero (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).pt 0 = W.pt 0 :=
  del_pt_of_le W i j hij hj hcl (Nat.zero_le i)

theorem del_pt_last (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).pt (i + (W.n - j)) = W.pt 0 := by
  by_cases hle : i + (W.n - j) ≤ i
  · have hjn : j = W.n := by omega
    show W.c * gpt (if i + (W.n - j) ≤ i then W.v (i + (W.n - j))
      else W.v (j + (i + (W.n - j) - i))) = W.pt 0
    rw [if_pos hle]
    have hii : i + (W.n - j) = i := by omega
    rw [hii]
    rw [hjn] at hcl
    rw [hcl, W.closed]
  · show W.c * gpt (if i + (W.n - j) ≤ i then W.v (i + (W.n - j))
      else W.v (j + (i + (W.n - j) - i))) = W.pt 0
    rw [if_neg hle, Nat.add_sub_cancel_left, Nat.add_sub_cancel' hj]
    exact W.pt_last


theorem pt_sub_self (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    W.pt (i + 0) = W.pt (i + (j - i)) := by
  have h0 : i + 0 = i := Nat.add_zero i
  rw [h0]
  rw [Nat.add_sub_cancel' (le_of_lt hij)]
  show W.c * gpt (W.v i) = W.c * gpt (W.v j)
  rw [hcl]

theorem pt_closed_cut (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) :
    W.pt (i + ((j - i) + (W.n - j))) = W.pt 0 := by
  have h : i + ((j - i) + (W.n - j)) = W.n := by omega
  rw [h]
  exact W.pt_last


theorem sub_pt_zero (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.sub i j hij hj hcl).pt 0 = W.pt (i + 0) := rfl

theorem sub_pt_last' (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.sub i j hij hj hcl).pt 0 = W.pt (i + (j - i)) :=
  (sub_pt_zero W i j hij hj hcl).trans (pt_sub_self W i j hij hj hcl)



/-- Transport of a null-homotopy of the sub-walk's loop into the `hδ` hypothesis of
`nullhomotopic_of_cut`. -/
theorem sub_loop_homotopic (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (h : Path.Homotopic (W.sub i j hij hj hcl).loop
      (Path.refl ((W.sub i j hij hj hcl).pt 0))) :
    Path.Homotopic
      (Path.cast (joinNat (p := fun l => W.pt (i + l)) (fun l => W.edge (i + l)) (j - i)) rfl
        (pt_sub_self W i j hij hj hcl))
      (Path.refl (W.pt i)) := by
  have h1 : (W.sub i j hij hj hcl).loop
      = Path.cast (joinNat (p := fun l => W.pt (i + l)) (fun l => W.edge (i + l)) (j - i)) rfl
          (pt_sub_self W i j hij hj hcl) := rfl
  rw [h1] at h
  exact h



/-- For `k < i`, the `k`-th edge of the deleted walk is the `k`-th edge of `W`, as a `Path.cast`. -/
theorem del_edge_cast (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    {k : ℕ} (hk : k < i) :
    (W.del i j hij hj hcl).edge k
      = Path.cast (W.edge k) (del_pt_of_le W i j hij hj hcl (by omega : k ≤ i))
          (del_pt_of_le W i j hij hj hcl (by omega : k + 1 ≤ i)) := by
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  simp only [LWalk.edge, segPath, Path.segment_apply]
  rw [del_pt_of_le W i j hij hj hcl (show k ≤ i by omega),
    del_pt_of_le W i j hij hj hcl (show k + 1 ≤ i by omega)]


/-- The vertices of the deleted walk past the cut. -/
theorem del_pt_of_ge (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    {l : ℕ} (hl : 0 < l) :
    (W.del i j hij hj hcl).pt (i + l) = W.pt (j + l) := by
  have hnot : ¬ (i + l ≤ i) := by omega
  show W.c * gpt (if i + l ≤ i then W.v (i + l) else W.v (j + (i + l - i)))
      = W.c * gpt (W.v (j + l))
  rw [if_neg hnot, show j + (i + l - i) = j + l from by omega]

theorem del_pt_at_cut (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).pt i = W.pt j := by
  rw [del_pt_of_le W i j hij hj hcl le_rfl]
  show W.c * gpt (W.v i) = W.c * gpt (W.v j)
  rw [hcl]

/-- The vertices of the deleted walk just past the cut (one step beyond the cut). -/
theorem del_pt_of_ge_succ (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (l : ℕ) : (W.del i j hij hj hcl).pt (i + l + 1) = W.pt (j + l + 1) := by
  have hnot : ¬ (i + l + 1 ≤ i) := by omega
  show W.c * gpt (if i + l + 1 ≤ i then W.v (i + l + 1) else W.v (j + (i + l + 1 - i)))
      = W.c * gpt (W.v (j + l + 1))
  rw [if_neg hnot, show j + (i + l + 1 - i) = j + l + 1 from by omega]

/-- The vertex of the deleted walk one step past the cut. -/
theorem del_pt_of_ge_one (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) :
    (W.del i j hij hj hcl).pt (i + 1) = W.pt (j + 1) := by
  have hnot : ¬ (i + 1 ≤ i) := by omega
  show W.c * gpt (if i + 1 ≤ i then W.v (i + 1) else W.v (j + (i + 1 - i)))
      = W.c * gpt (W.v (j + 1))
  rw [if_neg hnot, show j + (i + 1 - i) = j + 1 from by omega]

/-- The edges of the deleted walk past the cut, as `Path.cast`s of the corresponding edges of `W`
(the tail of `W` starting at the `j`-th vertex). -/
theorem del_edge_ge_cast (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j)
    (l : ℕ) :
    (W.del i j hij hj hcl).edge (i + l) = Path.cast (W.edge (j + l))
        (by rcases Nat.eq_zero_or_pos l with h | h
            · subst h; rw [Nat.add_zero, Nat.add_zero]; exact del_pt_at_cut W i j hij hj hcl
            · exact del_pt_of_ge W i j hij hj hcl h)
        (by rcases Nat.eq_zero_or_pos l with h | h
            · subst h; rw [Nat.add_zero, Nat.add_zero]; exact del_pt_of_ge_one W i j hij hj hcl
            · exact del_pt_of_ge_succ W i j hij hj hcl l) := by
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  simp only [LWalk.edge, segPath, Path.segment_apply]
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h
    rw [Nat.add_zero, Nat.add_zero, del_pt_at_cut W i j hij hj hcl]
    rw [show (W.del i j hij hj hcl).pt (i + 1) = W.pt (j + 1) from
      del_pt_of_ge_one W i j hij hj hcl]
    simp only [Nat.add_zero]
  · rw [del_pt_of_ge W i j hij hj hcl h, del_pt_of_ge_succ W i j hij hj hcl l]

end LWalk

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable (W : LWalk)

/-- The vertices of the deleted walk past the cut, in one total formula in the number of steps. -/
theorem del_pt_tail (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) (l : ℕ) :
    (W.del i j hij hj hcl).pt (i + l) = W.pt (j + l) := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h
    rw [Nat.add_zero, Nat.add_zero]
    exact del_pt_at_cut W i j hij hj hcl
  · exact del_pt_of_ge W i j hij hj hcl h

/-- The edges of the deleted walk past the cut, as `Path.cast`s of the edges of the tail of `W`. -/
theorem del_edge_tail (i j : ℕ) (hij : i < j) (hj : j ≤ W.n) (hcl : W.v i = W.v j) (l : ℕ) :
    (W.del i j hij hj hcl).edge (i + l)
      = Path.cast (W.edge (j + l)) (del_pt_tail W i j hij hj hcl l)
          (del_pt_tail W i j hij hj hcl (l + 1)) := by
  rw [del_edge_ge_cast W i j hij hj hcl l]

/-- **The cut identity.**  If a closed lattice walk splits at the repeated vertex `W.v i = W.v j`
into `α · δ · β` (with `δ` the piece from `i` to `j`), and both `δ` and `α · β` are null-homotopic
in `U`, then so is `W`.  `hval` is only used to know that the relevant paths live in `U`. -/

theorem nullhomotopic_of_cut (W : LWalk) {i j : ℕ} (hij : i < j) (hj : j ≤ W.n)
    (hpt : W.pt i = W.pt (i + (j - i)))
    (hclosed : W.pt (i + ((j - i) + (W.n - j))) = W.pt 0)
    (hδ : Path.Homotopic
      (Path.cast (joinNat (p := fun l => W.pt (i + l)) (fun l => W.edge (i + l)) (j - i)) rfl hpt)
      (Path.refl (W.pt i)))
    (hαβ : Path.Homotopic
      ((joinNat W.edge i).trans (Path.cast
        (joinNat (p := fun l => W.pt (i + ((j - i) + l)))
          (fun l => W.edge (i + ((j - i) + l))) (W.n - j)) hpt hclosed.symm))
      (Path.refl (W.pt 0))) :
    Path.Homotopic W.loop (Path.refl (W.pt 0)) := by
  have hidx : i + ((j - i) + (W.n - j)) = W.n := by omega
  have hcut := nullhomotopic_of_joinNat_cut (p := W.pt) (F := W.edge) hpt hclosed hδ hαβ
  have hcut' : Path.Homotopic (Path.cast (joinNat W.edge W.n) rfl W.pt_last.symm)
      (Path.refl (W.pt 0)) := by
    convert hcut using 2 <;> rw [hidx]
  have hloop : W.loop = Path.cast (joinNat W.edge W.n) rfl W.pt_last.symm := rfl
  rw [hloop]
  exact hcut'

end LWalk

end

end Work.Smooth.JordanSeparation
