import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_side
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_base
import Submission.Work.Smooth.JordanSeparation.plCutCast

/-!
# The peel: the clamped lifted-edge family, and the flipped walk

`LWalk.ptMin`/`LWalk.edgeUNat` give the ℕ-indexed family of lifted edges of a walk (clamped at
`W.n`), so that the lifted loop is a `joinNat` and the surgery lemma `joinNat_pair_congr` applies.
`LWalk.flip` is the walk obtained by moving the vertex at index `k` from `p` to `p - (1,1)` (the
corner cut of the peel).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable {W : LWalk} {U : Set ℂ}

/-- The `k`-th vertex of the walk clamped at `W.n`, as a point of `↥U`. -/
def ptMin (W : LWalk) (hval : ∀ t, W.path t ∈ U) (k : ℕ) : ↥U :=
  ⟨W.pt (min k W.n), W.pt_mem hval (min_le_right _ _)⟩

@[simp] theorem ptMin_apply (hval : ∀ t, W.path t ∈ U) (k : ℕ) :
    ((W.ptMin hval k : ↥U) : ℂ) = W.pt (min k W.n) := rfl

theorem ptMin_eq_ptU (hval : ∀ t, W.path t ∈ U) (k : ℕ) (hk : k ≤ W.n) :
    W.ptMin hval k = W.ptU hval k hk :=
  Subtype.ext (by rw [ptMin_apply, ptU_apply, Nat.min_eq_left hk])

/-- The `k`-th lifted edge of the walk, for all `k` (clamped: constant past the end). -/
def edgeUNat (W : LWalk) (hval : ∀ t, W.path t ∈ U) (k : ℕ) :
    Path (W.ptMin hval k) (W.ptMin hval (k + 1)) :=
  if h : k < W.n then
    Path.cast (W.edgeU hval k h) (W.ptMin_eq_ptU hval k (le_of_lt h))
      (W.ptMin_eq_ptU hval (k + 1) (Nat.succ_le_of_lt h))
  else
    (Path.refl (W.ptMin hval k)).cast rfl (Subtype.ext (by
      rw [ptMin_apply, ptMin_apply, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]))

theorem edgeUNat_apply (hval : ∀ t, W.path t ∈ U) (k : ℕ) (t : unitInterval) :
    ((W.edgeUNat hval k t : ↥U) : ℂ) = if h : k < W.n then W.edge k t else W.pt W.n := by
  by_cases h : k < W.n
  · simp only [edgeUNat, dif_pos h]
    rw [path_cast_apply]
    rfl
  · simp only [edgeUNat, dif_neg h]
    rw [path_cast_apply]
    simp only [Path.refl_apply]
    rw [ptMin_apply, Nat.min_eq_right (by omega)]

/-- The lifted loop of the walk, as the `joinNat` of the clamped lifted edges. -/
def loopNat (W : LWalk) (hval : ∀ t, W.path t ∈ U) :
    Path (W.ptMin hval 0) (W.ptMin hval 0) :=
  (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).cast
    ((W.ptMin_eq_ptU hval 0 (Nat.zero_le _)).symm)
    (Subtype.ext (by
      show W.pt (min 0 W.n) = W.pt (min W.n W.n)
      rw [Nat.min_eq_left (Nat.zero_le _), Nat.min_self, W.pt_last]))

/-- The endpoint equality used to close `loopNat` up. -/
theorem ptMin_zero_eq_last (hval : ∀ t, W.path t ∈ U) :
    W.ptMin hval 0 = W.ptMin hval W.n := by
  rw [W.ptMin_eq_ptU hval 0 (Nat.zero_le _), W.ptMin_eq_ptU hval W.n (le_refl _)]
  exact Subtype.ext W.pt_last.symm

/-- **The interface lemma.**  `loopNat` is the endpoint cast of the `joinNat` of the clamped
lifted edges; this is the form in which the `joinNat` surgery lemmas
(`joinNat_pair_congr`, `nullhomotopic_of_joinNat_cut`) are applied to `loopNat`. -/
theorem loopNat_eq_joinNat (hval : ∀ t, W.path t ∈ U) :
    W.loopNat hval = (joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).cast
      ((W.ptMin_eq_ptU hval 0 (Nat.zero_le _)).symm)
      (W.ptMin_zero_eq_last hval) := rfl

@[simp] theorem loopNat_apply (hval : ∀ t, W.path t ∈ U) (t : unitInterval) :
    W.loopNat hval t
      = ((joinNat (p := W.ptMin hval) (W.edgeUNat hval) W.n).cast
          ((W.ptMin_eq_ptU hval 0 (Nat.zero_le _)).symm)
          (W.ptMin_zero_eq_last hval)) t := rfl

theorem ptMin_zero_eq (hval : ∀ t, W.path t ∈ U) :
    W.ptMin hval 0 = W.ptU hval 0 (Nat.zero_le _) :=
  W.ptMin_eq_ptU hval 0 (Nat.zero_le _)

/-! The four lattice steps around the corner. -/

theorem gridStep_11_10 (p : ℤ × ℤ) : GridStep (p - (1, 1)) (p - (1, 0)) := by
  refine Or.inl ⟨?_, Or.inl ?_⟩
  · show (p - (1, 1)).1 = (p - (1, 0)).1
    simp
  · show (p - (1, 0)).2 = (p - (1, 1)).2 + 1
    simp

theorem gridStep_11_01 (p : ℤ × ℤ) : GridStep (p - (1, 1)) (p - (0, 1)) := by
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show (p - (1, 1)).2 = (p - (0, 1)).2
    simp
  · show (p - (0, 1)).1 = (p - (1, 1)).1 + 1
    simp

theorem gridStep_10_11 (p : ℤ × ℤ) : GridStep (p - (1, 0)) (p - (1, 1)) := by
  refine Or.inl ⟨?_, Or.inr ?_⟩
  · show (p - (1, 0)).1 = (p - (1, 1)).1
    simp
  · show (p - (1, 0)).2 = (p - (1, 1)).2 + 1
    simp

theorem gridStep_01_11 (p : ℤ × ℤ) : GridStep (p - (0, 1)) (p - (1, 1)) := by
  refine Or.inr ⟨?_, Or.inr ?_⟩
  · show (p - (0, 1)).2 = (p - (1, 1)).2
    simp
  · show (p - (0, 1)).1 = (p - (1, 1)).1 + 1
    simp

/-- **The flipped walk.**  The walk with the vertex at index `k` moved from `p = W.v k` to
`p - (1,1)`, assuming the corner hypothesis: the two neighbours of `p` are `p - (1,0)` and
`p - (0,1)`. -/
def flip (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) : LWalk where
  n := W.n
  c := W.c
  cpos := W.cpos
  v := fun j => if j = k then W.v k - (1, 1) else W.v j
  step := by
    intro j hj
    by_cases h1 : j = k
    · show GridStep (if j = k then W.v k - (1, 1) else W.v j)
        (if j + 1 = k then W.v k - (1, 1) else W.v (j + 1))
      rw [if_pos h1, if_neg (by omega : ¬ (j + 1 = k)), h1]
      rcases hb with hb | hb
      · rw [hb]; exact gridStep_11_10 (W.v k)
      · rw [hb]; exact gridStep_11_01 (W.v k)
    · by_cases h2 : j + 1 = k
      · have hk1' : j = k - 1 := by omega
        show GridStep (if j = k then W.v k - (1, 1) else W.v j)
          (if j + 1 = k then W.v k - (1, 1) else W.v (j + 1))
        rw [if_neg h1, if_pos h2, hk1']
        rcases ha with ha | ha
        · rw [ha]; exact gridStep_10_11 (W.v k)
        · rw [ha]; exact gridStep_01_11 (W.v k)
      · show GridStep (if j = k then W.v k - (1, 1) else W.v j)
          (if j + 1 = k then W.v k - (1, 1) else W.v (j + 1))
        rw [if_neg h1, if_neg h2]
        exact W.step j hj
  closed := by
    have h0 : (0 : ℕ) ≠ k := by omega
    have hn : W.n ≠ k := by omega
    simp only [if_neg h0, if_neg hn]
    exact W.closed

theorem flip_v (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) (j : ℕ) :
    (W.flip hk1 hk2 ha hb).v j = if j = k then W.v k - (1, 1) else W.v j := rfl

theorem flip_v_self (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) :
    (W.flip hk1 hk2 ha hb).v k = W.v k - (1, 1) := by
  rw [flip_v]; simp

theorem flip_v_of_ne (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) {j : ℕ} (hj : j ≠ k) :
    (W.flip hk1 hk2 ha hb).v j = W.v j := by
  rw [flip_v]; simp [hj]

theorem flip_n (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) :
    (W.flip hk1 hk2 ha hb).n = W.n := rfl

theorem flip_c (W : LWalk) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1)) :
    (W.flip hk1 hk2 ha hb).c = W.c := rfl

end LWalk

end

end Work.Smooth.JordanSeparation
