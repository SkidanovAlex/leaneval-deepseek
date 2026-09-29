import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paWords
import Submission.Work.Resample.axisBridge
import Submission.Work.Resample.axisIter_disc
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.dropVal_ev
import Submission.Work.MainP.ss_prod_le_ts_prod

/-!
# Proofs for the `Ã` program: list glue, iteration, prologue, epilogue
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## List glue -/

/-- The default element of `ℤ × ℤ` is `(0,0)` (the `getD` default of `HvdH.slices`). -/
theorem paDefault : (default : ℤ × ℤ) = (0, 0) := rfl

/-- `s < (List.map f (List.range (A*B))).length`. -/
theorem paLtMap {A B s : ℕ} {β : Type} (f : ℕ → List β) (hs : s < A * B) :
    s < ((List.range (A * B)).map f).length := by
  simpa using hs

/-- `j < (List.map f (List.range m)).length`. -/
theorem paLtMap2 {m j : ℕ} {β : Type} (f : ℕ → β) (hj : j < m) :
    j < ((List.range m).map f).length := by
  simpa using hj

/-- `i < (List.range n).length`. -/
theorem paLtRange {n i : ℕ} (hs : i < n) : i < (List.range n).length := by
  simpa using hs

/-- The index of the `(s,j)`-entry of a flat `A × m × B` array stays in range. -/
theorem paSliceIdx_lt (A m B s j : ℕ) (hs : s < A * B) (hj : j < m) :
    (s / B * m + j) * B + s % B < A * m * B := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hs
    · exact h
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; simp at hs
    · exact h
  have h1 : s / B < A := (Nat.div_lt_iff_lt_mul hB).mpr hs
  have h2 : s % B < B := Nat.mod_lt _ hB
  have h3 : s / B * m + j + 1 ≤ A * m := by
    have hjm : j + 1 ≤ m := by omega
    calc s / B * m + j + 1 ≤ (A - 1) * m + m := by
          have hle : s / B ≤ A - 1 := by omega
          have hmul : s / B * m ≤ (A - 1) * m := Nat.mul_le_mul_right m hle
          omega
      _ = ((A - 1) + 1) * m := by ring
      _ = A * m := by rw [Nat.sub_add_cancel hA]
  calc (s / B * m + j) * B + s % B
      < (s / B * m + j) * B + B := by omega
    _ = (s / B * m + j + 1) * B := by ring
    _ ≤ A * m * B := Nat.mul_le_mul_right B h3

/-- `slices` commutes with `cfxVal`. -/
theorem paGlueA (A m B : ℕ) (zs : List (ℤ × ℤ)) (hz : zs.length = A * m * B) {s : ℕ}
    (hs : s < A * B) :
    (HvdH.slices A m B (zs.map HvdH.cfxVal)).getD s []
      = ((HvdH.slices A m B zs).getD s []).map HvdH.cfxVal := by
  rw [HvdH.slices, HvdH.slices]
  rw [List.getD_eq_getElem _ _ (paLtMap (β := HvdH.Val)
        (fun s => (List.range m).map (fun j => (zs.map HvdH.cfxVal).getD
          ((s / B * m + j) * B + s % B) (default : HvdH.Val))) hs),
      List.getD_eq_getElem _ _ (paLtMap (β := ℤ × ℤ)
        (fun s => (List.range m).map (fun j => zs.getD
          ((s / B * m + j) * B + s % B) (default : ℤ × ℤ))) hs)]
  rw [List.getElem_map, List.getElem_map, List.getElem_range (paLtRange hs)]
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp_apply]
  have hidx : (s / B * m + j) * B + s % B < zs.length := by
    rw [hz]; exact paSliceIdx_lt A m B s j hs hj
  rw [List.getD_eq_getElem _ _ (by simpa using hidx), List.getD_eq_getElem _ _ hidx,
    List.getElem_map]

/-- The `(s,j)`-entry of the `s`-th slice is `sliceIn`. -/
theorem paGlueB (A m B : ℕ) (zs : List (ℤ × ℤ)) {s j : ℕ} (hs : s < A * B) (hj : j < m) :
    ((HvdH.slices A m B zs).getD s []).getD j (0, 0) = sliceIn m B zs s j := by
  rw [HvdH.slices]
  rw [List.getD_eq_getElem _ _ (paLtMap (β := ℤ × ℤ)
        (fun s => (List.range m).map (fun j => zs.getD
          ((s / B * m + j) * B + s % B) (default : ℤ × ℤ))) hs)]
  rw [List.getElem_map, List.getElem_range (paLtRange hs)]
  rw [List.getD_eq_getElem _ _ (paLtMap2 (β := ℤ × ℤ)
        (fun j => zs.getD ((s / B * m + j) * B + s % B) (default : ℤ × ℤ)) hj)]
  rw [List.getElem_map]
  rw [List.getElem_range (paLtRange hj)]
  simp only [sliceIn]
  rw [paDefault]

/-- A list is the `ofFn` of its `getD` entries. -/
theorem paGlueC (n : ℕ) (w : List (ℤ × ℤ)) (f : Fin n → ℤ × ℤ) (hw : w.length = n)
    (h : ∀ k : Fin n, w.getD (k : ℕ) (0, 0) = f k) : w = List.ofFn f := by
  apply List.ext_getElem
  · rw [hw, List.length_ofFn]
  · intro k h1 h2
    have hk : k < n := by rw [hw] at h1; exact h1
    have hh := h ⟨k, hk⟩
    rw [List.getD_eq_getElem w (0,0) h1] at hh
    rw [hh, List.getElem_ofFn]

/-- `unslices` of per-slice `cfxVal`-images of `Φ` is `axisList` of the flat array. -/
theorem paGlueD (A m n B : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)) (hz : zs.length = A * m * B)
    (os : List (List HvdH.Val)) (hos : os.length = A * B)
    (he : ∀ s < A * B, ∃ w : List (ℤ × ℤ), os.getD s [] = w.map HvdH.cfxVal ∧ w.length = n ∧
      ∀ k : Fin n, w.getD (k : ℕ) (0, 0) = Φ (fun j : Fin m =>
        ((HvdH.slices A m B zs).getD s []).getD (j : ℕ) (0, 0)) k) :
    HvdH.unslices A n B os = (axisList A m n B Φ zs).map HvdH.cfxVal := by
  have he' : ∀ s < A * B, os.getD s []
      = (List.ofFn (Φ (fun j : Fin m => sliceIn m B zs s (j : ℕ)))).map HvdH.cfxVal := by
    intro s hs
    obtain ⟨w, hw, hwl, hwk⟩ := he s hs
    have hw' : w = List.ofFn (fun k : Fin n => Φ (fun j : Fin m =>
        ((HvdH.slices A m B zs).getD s []).getD (j : ℕ) (0, 0)) k) :=
      paGlueC n w _ hwl (fun k => by rw [hwk k])
    have hfe : (fun j : Fin m => ((HvdH.slices A m B zs).getD s []).getD (j : ℕ) (0, 0))
        = (fun j : Fin m => sliceIn m B zs s (j : ℕ)) := by
      funext j
      exact paGlueB A m B zs hs j.isLt
    rw [hw, hw', hfe]
  rw [axisList_eq_axisPairs]
  exact unslices_axisPairs A m n B hm hn hB Φ zs hz os hos he'

/-- One axis application preserves the disc. -/
theorem paGlueE (p A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ))
    (hz : ∀ z ∈ zs, HvdH.inDisc p z)
    (hΦ : ∀ w : Fin m → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin n, HvdH.inDisc p (Φ w k)) :
    ∀ z ∈ axisList A m n B Φ zs, HvdH.inDisc p z :=
  axisList_disc A m n B p Φ hΦ zs hz

/-! ## Iterating a `WordP` program -/

/-- `k` copies of `c` in sequence, without a trailing `skip`. -/
def paIterN (c : HvdH.Cmd) : ℕ → HvdH.Cmd
  | 0 => .skip
  | 1 => c
  | (k + 2) => .seq c (paIterN c (k + 1))

@[simp] theorem paIterN_zero (c : HvdH.Cmd) : paIterN c 0 = .skip := rfl
@[simp] theorem paIterN_one (c : HvdH.Cmd) : paIterN c 1 = c := rfl
theorem paIterN_succ_succ (c : HvdH.Cmd) (k : ℕ) : paIterN c (k + 2) = .seq c (paIterN c (k + 1)) :=
  rfl

/-- Peeling one round off the front of `paIterN c k` for `k ≥ 1`. -/
theorem paIterN_succ (c : HvdH.Cmd) {k : ℕ} (hk : 1 ≤ k) : paIterN c (k + 1) = .seq c (paIterN c k) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  rfl

/-- **`k`-fold iteration of a `WordP` program.** -/
theorem WordP.iterate {main : HvdH.Cmd} (c : HvdH.Cmd)
    (P : ℕ → List HvdH.Val → List HvdH.Val → (HvdH.Stk → List HvdH.Val) → Prop) (C : ℕ → ℕ) :
    ∀ (k i : ℕ), 1 ≤ k →
      (∀ t, i ≤ t → t < i + k → WordP main c (P t)
        (fun vs rest a out b => P (t + 1) out rest b) (fun _ _ _ => C t)) →
      WordP main (paIterN c k) (P i) (fun vs rest a out b => P (i + k) out rest b)
        (fun _ _ _ => ∑ t ∈ Finset.range k, C (i + t)) := by
  have key : ∀ n : ℕ, 1 ≤ n →
      ∀ i, (∀ t, i ≤ t → t < i + n →
        WordP main c (P t) (fun vs rest a out b => P (t + 1) out rest b) (fun _ _ _ => C t)) →
      WordP main (paIterN c n) (P i) (fun vs rest a out b => P (i + n) out rest b)
        (fun _ _ _ => ∑ t ∈ Finset.range n, C (i + t)) := by
    refine Nat.le_induction (m := 1) ?base ?step
    · intro i h
      simpa only [paIterN_one, Finset.sum_range_one, Nat.add_zero] using h i le_rfl (by omega)
    · intro n hn ih i h
      have h1 : WordP main c (P i) (fun vs rest a out b => P (i + 1) out rest b)
          (fun _ _ _ => C i) := h i le_rfl (by omega)
      have h2 : WordP main (paIterN c n) (P (i + 1))
          (fun vs rest a out b => P (i + 1 + n) out rest b)
          (fun _ _ _ => ∑ t ∈ Finset.range n, C (i + 1 + t)) :=
        ih (i + 1) (fun t ht1 ht2 => h t (by omega) (by omega))
      have hseq : WordP main (.seq c (paIterN c n)) (P i)
          (fun vs rest a out b => ∃ mid a', P (i + 1) mid rest a' ∧ P (i + 1 + n) out rest b)
          (fun _ _ _ => C i + ∑ t ∈ Finset.range n, C (i + 1 + t)) := by
        refine WordP.seq (B := fun _ _ _ => ∑ t ∈ Finset.range n, C (i + 1 + t)) h1 h2 ?_ ?_
        · intro vs rest a mid a' hmid
          exact hmid
        · intro vs rest a mid a' _
          exact le_rfl
      rw [paIterN_succ c hn]
      refine WordP.conseq (Pre' := P i) (Post' := fun vs rest a out b => P (i + (n + 1)) out rest b)
        (C' := fun _ _ _ => ∑ t ∈ Finset.range (n + 1), C (i + t)) hseq ?_ ?_ ?_
      · intro vs rest a hh
        exact hh
      · intro vs rest a out b hpre hpost
        obtain ⟨mid, a', _, hpost⟩ := hpost
        have he : i + 1 + n = i + (n + 1) := by omega
        rwa [he] at hpost
      · intro vs rest a _
        rw [Finset.sum_range_succ']
        have hsum : (∑ t ∈ Finset.range n, C (i + 1 + t))
            = (∑ t ∈ Finset.range n, C (i + (t + 1))) :=
          Finset.sum_congr rfl (fun t _ => by congr 1; omega)
        rw [hsum]
        exact le_of_eq (Nat.add_comm _ _)
  intro k i hk h
  exact key k hk i h

/-- The aggregate budget of the `D` axis passes (Finset form of `PAIterBr`). -/
def PAIterBrF (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) : ℕ :=
  (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j) + 1

/-- **The `D`-fold iteration of one axis step.** -/
theorem paIter (Kb Kc0 : ℕ) (round : HvdH.Cmd) :
    ∃ (iter : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ)
        (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)),
      HvdH.ResParams p α ss ts → Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      (∀ j < HvdH.D, WordP main round
        (fun vs rest a => PAInv p α ss ts Φ zs0 j vs rest a)
        (fun vs rest a out b => PAInv p α ss ts Φ zs0 (j + 1) out rest b)
        (fun _ _ _ => Kc0 * PABr Kb Cm p α ss ts j)) →
      WordP main iter
        (fun vs rest a => PAInv p α ss ts Φ zs0 0 vs rest a)
        (fun vs rest a out b => PAInv p α ss ts Φ zs0 HvdH.D out rest b)
        (fun _ _ _ => Kc * PAIterBrF Kb Cm p α ss ts) := by
  refine ⟨paIterN round HvdH.D, Kc0 + 1, ?_⟩
  intro main N Cm p α ss ts Φ zs0 hpar hmon hmb hN hround
  have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
  have hiter := WordP.iterate (main := main) round (fun j => PAInv p α ss ts Φ zs0 j)
    (fun j => Kc0 * PABr Kb Cm p α ss ts j) HvdH.D 0 hD1
    (fun t _ ht2 => hround t (by omega))
  refine WordP.mono hiter (fun vs rest a => ?_)
  have h1 : (∑ t ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts (0 + t))
      ≤ (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j) :=
    Finset.sum_le_sum (fun t _ => le_of_eq (by rw [Nat.zero_add]))
  have h2 : (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j) + 1
      = PAIterBrF Kb Cm p α ss ts := rfl
  rw [← Finset.mul_sum]
  calc Kc0 * (∑ t ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts (0 + t))
      ≤ Kc0 * (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j) := Nat.mul_le_mul_left _ h1
    _ ≤ (Kc0 + 1) * ((∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j) + 1) := by
        nlinarith [Nat.zero_le Kc0, Nat.zero_le (∑ j ∈ Finset.range HvdH.D, PABr Kb Cm p α ss ts j)]
    _ = (Kc0 + 1) * PAIterBrF Kb Cm p α ss ts := by rw [h2]

end Work.Resample
