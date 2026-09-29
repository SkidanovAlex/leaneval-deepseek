import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.fxTensorErr
import Submission.Work.Resample.axisIter_getD_fxTensorRec
import Submission.Work.Resample.axisList_blkAlt
import Submission.Work.Resample.axKit
import Submission.Work.Resample.axisPairsMidAxis
import Submission.Work.Resample.axisIter_length

/-!
# The axis bridge

This file proves `Work.Resample.axisBridge`, the bridge between the three descriptions of the
axis-by-axis application of one-dimensional slice maps used in the resampling program of paper
Theorem 4.1:

* `axisPairs`/`midAxis` (the `List.ofFn`/`Fin`-indexed description),
* `progAxis` versus `fxTensorRec` (the iterated composition, list level versus fixed-point level),
* `HvdH.unslices` (the `LayoutLib.applyAlong` output layout) versus `axisPairs`.

The middle item is proved by comparing `progAxis` with the `slices`/`unslices`-based iteration
`axisIter` (`axisList_eq_axisPairs`, `progAxis_eq_axisIter`) and then invoking
`axisIter_getD_fxTensorRec`, which peels the *first* axis (as `fxTensorRec` does) whereas
`progAxis` peels the last one.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## One axis pass: the `slices`/`unslices` description and `axisPairs`

`axisList A m n B Φ es` is the list-level form of `LayoutLib.applyAlong`: apply `Φ` to every
`m`-slice of the flat `A × m × B` array `es` and reassemble the results into an `A × n × B` array.
It agrees with `axisPairs`, which reads the slices with `sliceIn`. -/
theorem axisList_eq_axisPairs (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (es : List (ℤ × ℤ)) : axisList A m n B Φ es = axisPairs A m n B Φ es := by
  apply List.ext_getElem
  · rw [axisList_length_axisIter_length]; simp [axisPairs]
  · intro idx h1 h2
    have hidx : idx < A * n * B := by rwa [axisList_length_axisIter_length] at h1
    have hidx2 : idx < A * n * B := by simpa [axisPairs] using h2
    rcases Nat.eq_zero_or_pos (n * B) with h | h
    · have h0 : A * n * B = 0 := by rw [Nat.mul_assoc, h, Nat.mul_zero]
      omega
    · have hn : 0 < n := fxTE_pos_left h
      have hB : 0 < B := fxTE_pos_right h
      rw [List.getElem_eq_getD (h := h1) (0,0), List.getElem_eq_getD (h := h2) (0,0)]
      rw [axisList_getD A m n B Φ es hn hB idx hidx]
      unfold axisPairs
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx2,
        Option.map_some, Option.getD_some]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact Nat.mod_lt _ hn),
        List.getElem_ofFn]
      congr 1
      funext j
      simp only [sliceIn]
      have hdiv : (idx / (n * B) * B + idx % B) / B = idx / (n * B) := by
        rw [Nat.mul_comm (idx / (n*B)) B, Nat.mul_add_div hB, Nat.div_eq_of_lt (Nat.mod_lt _ hB),
          Nat.add_zero]
      have hmod : (idx / (n * B) * B + idx % B) % B = idx % B := by
        rw [Nat.mul_comm (idx / (n*B)) B, Nat.mul_add_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hB)]
      rw [hdiv, hmod]

/-! ## The iterated pass: `progAxis` and `axisIter`

Both peel the *last* axis at each step, with the same layout parameters, so the equality is an
immediate induction. -/
theorem progAxis_eq_axisIter (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ)) :
    ∀ (k : ℕ) (zs : List (ℤ × ℤ)), progAxis ss ts Φ k zs = axisIter ts ss Φ k zs := by
  intro k
  induction k with
  | zero => intro zs; rfl
  | succ k ih =>
    intro zs
    rw [progAxis, axisIter, ih]
    exact (axisList_eq_axisPairs _ _ _ _ _ _).symm

/-! ## `progAxis` versus `fxTensorRec` -/
theorem progAxis_ofFn_fxTensorRec (ss ts : List ℕ) (hl : ts.length = ss.length)
    (hpos : ∀ i < ts.length, 0 < ts.getD i 0 ∧ 0 < ss.getD i 0)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (u : Fin ts.prod → ℤ × ℤ) :
    progAxis ss ts Φ ts.length (List.ofFn u) = List.ofFn (fxTensorRec ts ss Φ u) := by
  rw [progAxis_eq_axisIter ss ts Φ ts.length (List.ofFn u)]
  have hlen : (List.ofFn u).length = (ts.take ts.length).prod * (ts.drop ts.length).prod := by
    rw [List.length_ofFn, List.take_length, List.drop_length, List.prod_nil, mul_one]
  have hlen_ax : (axisIter ts ss Φ ts.length (List.ofFn u)).length = ss.prod := by
    rw [axisIter_length ts ss hl.symm ts.length (le_refl _) (fun j hj => (hpos j hj).1) Φ
      (List.ofFn u) hlen]
    have h1 : ss.take ts.length = ss := by rw [hl, List.take_length]
    have h2 : ts.drop ts.length = [] := List.drop_length
    rw [h1, h2, List.prod_nil, mul_one]
  apply List.ext_getElem
  · rw [hlen_ax, List.length_ofFn]
  · intro J h1 h2
    rw [List.getElem_eq_getD (h := h1) (0,0), List.getElem_ofFn]
    rw [axisIter_getD_fxTensorRec ts ss hl.symm (fun j hj => (hpos j hj).1)
      (fun j hj => (hpos j hj).2) Φ (List.ofFn u) List.length_ofFn J (by simpa using h2)]
    congr 1
    funext i
    exact ofFn_getD u i.isLt

/-! ## `unslices` versus `axisPairs` -/
theorem unslices_axisPairs (A m n B : ℕ) (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)) (hzs : zs.length = A * m * B)
    (os : List (List HvdH.Val)) (hos : os.length = A * B)
    (he : ∀ s < A * B, os.getD s []
      = (List.ofFn (Φ (fun j : Fin m => sliceIn m B zs s (j : ℕ)))).map HvdH.cfxVal) :
    HvdH.unslices A n B os = (axisPairs A m n B Φ zs).map HvdH.cfxVal := by
  have hb : ∀ idx < A * n * B, idx / (n * B) * B + idx % B < A * B := by
    intro idx hidx
    have hnB : 0 < n * B := Nat.mul_pos hn hB
    have h1 : idx / (n * B) < A :=
      (Nat.div_lt_iff_lt_mul hnB).mpr (by rwa [Nat.mul_assoc] at hidx)
    have h3 : idx / (n * B) * B + idx % B < (idx / (n * B) + 1) * B := by
      rw [Nat.add_mul]
      have := Nat.mod_lt idx hB
      omega
    have h4 : (idx / (n * B) + 1) * B ≤ A * B :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
    omega
  have hmain : ∀ idx < A * n * B,
      (os.getD (idx / (n * B) * B + idx % B) []).getD (idx / B % n) default
        = HvdH.cfxVal ((List.ofFn (Φ (fun j : Fin m =>
            sliceIn m B zs (idx / (n * B) * B + idx % B) (j : ℕ)))).getD (idx / B % n) (0,0)) := by
    intro idx hidx
    have hk : idx / B % n < n := Nat.mod_lt _ hn
    rw [he _ (hb idx hidx)]
    rw [List.getD_eq_getElem _ _
        (by rw [List.length_map, List.length_ofFn]; exact hk), List.getElem_map,
      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk)]
  simp only [HvdH.unslices, axisPairs, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro idx hidx
  rw [List.mem_range] at hidx
  exact hmain idx hidx

theorem axisBridge :
    (∀ (A m n B : ℕ), 0 < m → 0 < n → 0 < B →
      ∀ (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (u : Fin (A * m * B) → ℤ × ℤ),
      Work.Resample.axisPairs A m n B Φ (List.ofFn u)
        = List.ofFn (Work.Resample.midAxis A m n B Φ u)) ∧
    (∀ (ss ts : List ℕ), ts.length = ss.length →
      (∀ i < ts.length, 0 < ts.getD i 0 ∧ 0 < ss.getD i 0) →
      ∀ (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
        (u : Fin ts.prod → ℤ × ℤ),
        Work.Resample.progAxis ss ts Φ ts.length (List.ofFn u)
          = List.ofFn (Work.Resample.fxTensorRec ts ss Φ u)) ∧
    (∀ (A m n B : ℕ), 0 < m → 0 < n → 0 < B →
      ∀ (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)),
      zs.length = A * m * B →
      ∀ (os : List (List HvdH.Val)), os.length = A * B →
      (∀ s < A * B, os.getD s []
        = (List.ofFn (Φ (fun j : Fin m => Work.Resample.sliceIn m B zs s (j : ℕ)))).map HvdH.cfxVal) →
      HvdH.unslices A n B os = (Work.Resample.axisPairs A m n B Φ zs).map HvdH.cfxVal) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A m n B hm hn hB Φ u
    exact axisPairsMidAxis A m n B hm hn hB Φ u
  · intro ss ts hl hpos Φ u
    exact progAxis_ofFn_fxTensorRec ss ts hl hpos Φ u
  · intro A m n B hm hn hB Φ zs hzs os hos he
    exact unslices_axisPairs A m n B hm hn hB Φ zs hzs os hos he

end Work.Resample
