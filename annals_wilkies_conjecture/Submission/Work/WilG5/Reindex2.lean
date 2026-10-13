/-
  WilG5 — second reindexing module: the "keep the last `k` coordinates" operation `lastN`.

  `lastN k A = {u : Fin k → ℝ | ∃ x : Fin n → ℝ, Fin.append x u ∈ A}` for `A ⊆ ℝ^{n+k}`.
  The naive recursion `lastN (k+1) A = {u | Fin.init u ∈ lastN k (projLast A)}` is FALSE (see
  the header of `Basic` for the counterexample), so `lastN` is built from the *balanced*
  reindexing of `Reindex` instead:

  * `A₁ := liftFirst k A ⊆ ℝ^{(n+k)+k}`  (`A` on the first `n+k` coordinates);
  * transport `A₁` along `(n+k) + k = k + (n+k)` to the type `Fin (k + (n+k))`, so that the
    first `k` coordinates of the ambient are the ones to be kept;
  * reindex along the explicit permutation `shiftPerm n k`, which moves the last `k`
    coordinates of `A` (its `u`-part) to the front (`shiftPerm_uIdx`, `shiftPerm_xIdx`);
  * project the rest away with `projN (n+k)`.

  Main results: `lastN_eq_projN` (the set equality, the mathematical content) and `lastN_mem`
  (its `Ω`-membership corollary).
-/
import Submission.Work.WilG5.Reindex

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 1. The permutation and its evaluations -/

/-- The map of `Fin (k + (n+k))` that sends the block `[n, n+k)` (the `u`-part of a point of
`A ⊆ ℝ^{n+k}`) to the front `[0,k)`, the block `[0,n)` (the `x`-part) to `[k, k+n)`, and
keeps the remaining coordinates. -/
def shiftPerm (n k : ℕ) (i : Fin (k + (n + k))) : Fin (k + (n + k)) :=
  if h : i.val < n then ⟨k + i.val, by omega⟩
  else if h2 : i.val < n + k then ⟨i.val - n, by omega⟩
  else ⟨i.val, by omega⟩

/-- The index `n + j` of `Fin (k + (n+k))`: the position of `A`'s `j`-th `u`-coordinate. -/
def uIdx (n k : ℕ) (j : Fin k) : Fin (k + (n + k)) := ⟨n + j.val, by omega⟩

/-- The index `i` of `Fin (k + (n+k))` for `i : Fin n`: the position of `A`'s `x`-coordinates. -/
def xIdx (n k : ℕ) (i : Fin n) : Fin (k + (n + k)) := ⟨i.val, by omega⟩

/-- The index with the same value, as an index of the ambient `Fin (k + (n+k))`. -/
def midIdx (n k : ℕ) (i : Fin (n + k)) : Fin (k + (n + k)) := ⟨i.val, by omega⟩

theorem shiftPerm_uIdx (n k : ℕ) (j : Fin k) :
    shiftPerm n k (uIdx n k j) = ⟨j.val, by omega⟩ := by
  unfold shiftPerm uIdx
  rw [dite_eq_right (by simp only [Fin.val_mk]; omega), dite_eq_left (by simp only [Fin.val_mk]; omega)]
  exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem shiftPerm_xIdx (n k : ℕ) (i : Fin n) :
    shiftPerm n k (xIdx n k i) = ⟨k + i.val, by omega⟩ := by
  unfold shiftPerm xIdx
  rw [dite_eq_left (by simp only [Fin.val_mk]; omega)]

theorem shiftPerm_high (n k : ℕ) (i : Fin (k + (n + k))) (h : n + k ≤ i.val) :
    shiftPerm n k i = i := by
  unfold shiftPerm
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

/-- `Fin.cast` of `Fin.castAdd` is the index with the same value. -/
theorem cast_castAdd (n k : ℕ) (i : Fin (n + k)) :
    (Fin.cast (Nat.add_comm (n + k) k) (Fin.castAdd k i) : Fin (k + (n + k))) = midIdx n k i :=
  Fin.ext rfl

@[simp] theorem midIdx_val {n k : ℕ} (i : Fin (n + k)) : (midIdx n k i).val = i.val := rfl
@[simp] theorem uIdx_val {n k : ℕ} (j : Fin k) : (uIdx n k j).val = n + j.val := rfl
@[simp] theorem natAdd_val {m : ℕ} (n : ℕ) (i : Fin m) : (Fin.natAdd n i).val = n + i.val := rfl

/-! ## 2. The set equality -/

theorem lastN_eq_projN {n k : ℕ} (A : Set (Fin (n + k) → ℝ)) :
    lastN k A = projN (n + k)
      {z : Fin (k + (n + k)) → ℝ |
        z ∘ shiftPerm n k ∈ (Nat.add_comm (n + k) k) ▸ liftFirst k A} := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Fin.append x (fun _ : Fin k => (0 : ℝ)), ?_⟩
    change (Fin.append u (Fin.append x (fun _ : Fin k => (0 : ℝ)))) ∘ shiftPerm n k ∈
      (Nat.add_comm (n + k) k) ▸ liftFirst k A
    rw [mem_ndrec]
    change (fun i' : Fin (n + k) =>
        ((Fin.append u (Fin.append x (fun _ : Fin k => (0 : ℝ)))) ∘ shiftPerm n k)
          (Fin.cast (Nat.add_comm (n + k) k) (Fin.castAdd k i'))) ∈ A
    convert hx using 1
    funext i'
    by_cases hlt : i'.val < n
    · have hidx : Fin.cast (Nat.add_comm (n + k) k) (Fin.castAdd k i') =
          xIdx n k ⟨i'.val, hlt⟩ := Fin.ext rfl
      have hperm : shiftPerm n k (xIdx n k ⟨i'.val, hlt⟩) =
          Fin.natAdd k (Fin.castAdd k (⟨i'.val, hlt⟩ : Fin n)) := by
        rw [shiftPerm_xIdx]
        exact Fin.ext rfl
      have hA : (Fin.append u (Fin.append x (fun _ : Fin k => (0 : ℝ))))
          (Fin.natAdd k (Fin.castAdd k (⟨i'.val, hlt⟩ : Fin n))) = x ⟨i'.val, hlt⟩ := by
        rw [Fin.append_right, Fin.append_left]
      have hB : (Fin.append x u) i' = x ⟨i'.val, hlt⟩ := by
        conv_lhs => rw [show i' = Fin.castAdd k (⟨i'.val, hlt⟩ : Fin n) from Fin.ext rfl]
        rw [Fin.append_left]
      rw [Function.comp_apply, hidx, hperm, hA, hB]
    · have hle : n ≤ i'.val := by omega
      have hidx : Fin.cast (Nat.add_comm (n + k) k) (Fin.castAdd k i') =
          uIdx n k ⟨i'.val - n, by omega⟩ := by
        rw [cast_castAdd]
        exact Fin.ext (by rw [midIdx_val, uIdx_val]; exact (Nat.add_sub_cancel' hle).symm)
      have hperm : shiftPerm n k (uIdx n k ⟨i'.val - n, by omega⟩) =
          Fin.castAdd (n + k) (⟨i'.val - n, by omega⟩ : Fin k) := by
        rw [shiftPerm_uIdx]
        exact Fin.ext rfl
      have hA : (Fin.append u (Fin.append x (fun _ : Fin k => (0 : ℝ))))
          (Fin.castAdd (n + k) (⟨i'.val - n, by omega⟩ : Fin k)) =
          u ⟨i'.val - n, by omega⟩ := by
        rw [Fin.append_left]
      have hB : (Fin.append x u) i' = u ⟨i'.val - n, by omega⟩ := by
        conv_lhs => rw [show i' = Fin.natAdd n (⟨i'.val - n, by omega⟩ : Fin k) from by
          apply Fin.ext
          rw [natAdd_val]
          exact (Nat.add_sub_cancel' hle).symm]
        rw [Fin.append_right]
      rw [Function.comp_apply, hidx, hperm, hA, hB]
  · rintro ⟨y, hy⟩
    change (Fin.append u y) ∘ shiftPerm n k ∈ (Nat.add_comm (n + k) k) ▸ liftFirst k A at hy
    rw [mem_ndrec] at hy
    set T : Fin (n + k) → ℝ := fun i'' =>
      ((Fin.append u y) ∘ shiftPerm n k) (Fin.cast (Nat.add_comm (n + k) k) (Fin.castAdd k i''))
      with hTdef
    have hT : T ∈ A := hy
    refine ⟨fun i : Fin n => T (Fin.castAdd k i), ?_⟩
    convert hT using 1
    funext i'
    by_cases hlt : i'.val < n
    · have hidx : i' = Fin.castAdd k (⟨i'.val, hlt⟩ : Fin n) := Fin.ext rfl
      rw [hidx, Fin.append_left]
    · have hle : n ≤ i'.val := by omega
      have huj : i' = Fin.natAdd n (⟨i'.val - n, by omega⟩ : Fin k) := by
        apply Fin.ext
        rw [natAdd_val]
        exact (Nat.add_sub_cancel' hle).symm
      have hval : T (Fin.natAdd n (⟨i'.val - n, by omega⟩ : Fin k)) =
          u ⟨i'.val - n, by omega⟩ := by
        change ((Fin.append u y) ∘ shiftPerm n k)
          (Fin.cast (Nat.add_comm (n + k) k)
            (Fin.castAdd k (Fin.natAdd n (⟨i'.val - n, by omega⟩ : Fin k)))) =
          u ⟨i'.val - n, by omega⟩
        have hc : Fin.cast (Nat.add_comm (n + k) k)
            (Fin.castAdd k (Fin.natAdd n (⟨i'.val - n, by omega⟩ : Fin k))) =
            uIdx n k ⟨i'.val - n, by omega⟩ := by
          rw [cast_castAdd]
          exact Fin.ext (by rw [midIdx_val, natAdd_val, uIdx_val])
        rw [Function.comp_apply, hc, shiftPerm_uIdx]
        have hw : (⟨(⟨i'.val - n, by omega⟩ : Fin k).val, by omega⟩ : Fin (k + (n + k))) =
            Fin.castAdd (n + k) (⟨i'.val - n, by omega⟩ : Fin k) := Fin.ext rfl
        rw [hw, Fin.append_left]
      rw [huj, Fin.append_right, hval]
/-! ## 3. The `Ω`-membership -/

theorem lastN_mem {n : ℕ} (k F D : ℕ) {A : Set (Fin (n + k) → ℝ)}
    (h : A ∈ S.Ω F D (n + k)) :
    lastN k A ∈ S.Ω (max ((F + k) + (k + (n + k))) (4 * ((k + (n + k)) + (k + (n + k))) + 8)
        + 1 + (k + (n + k)) + (k + (n + k))) (D + (2 * (k + (n + k)) + 4)) k := by
  have h1 : liftFirst k A ∈ S.Ω (F + k) D ((n + k) + k) := liftFirst_mem (S := S) k F D h
  have h2 : ((Nat.add_comm (n + k) k) ▸ liftFirst k A) ∈ S.Ω (F + k) D (k + (n + k)) :=
    omega_ndrec (S := S) (Nat.add_comm (n + k) k) h1
  have h3 : {z : Fin (k + (n + k)) → ℝ |
      z ∘ shiftPerm n k ∈ (Nat.add_comm (n + k) k) ▸ liftFirst k A} ∈
      S.Ω (max ((F + k) + (k + (n + k))) (4 * ((k + (n + k)) + (k + (n + k))) + 8) + 1
        + (k + (n + k))) (D + (2 * (k + (n + k)) + 4)) (k + (n + k)) :=
    reindex_mem (S := S) (shiftPerm n k) h2
  have h4 := projN_mem (S := S) (n + k) _ _ h3
  rw [lastN_eq_projN A]
  exact mem_mono h4 _ _ (by omega) (by omega)

end Work.WilG5
