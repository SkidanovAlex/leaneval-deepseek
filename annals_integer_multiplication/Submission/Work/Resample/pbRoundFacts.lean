import Mathlib
import Submission.Work.Resample.pbRoundDefs
import Submission.Work.Resample.axisBridge
import Submission.Work.Main.word.conjDefs
import Submission.Work.Layout.appendDefs

namespace Work.Resample

open HvdH

/-! ## The eight items, as separate lemmas

Every item of `pbRoundFacts` is independent, so each is proved as its own small lemma first. -/

/-- Item 1: the `s`-th slice of a flat `A × m × B` array of fixed-point pairs, in the `slices`
layout, is the `List.ofFn` of `sliceIn`. -/
theorem pbRF_slices_getD (A m B : ℕ) (zs : List (ℤ × ℤ)) (s : ℕ)
    (hzs : zs.length = A * m * B) (hs : s < A * B) :
    (HvdH.slices A m B (zs.map HvdH.cfxVal)).getD s [] =
      (List.ofFn (fun j : Fin m => Work.Resample.sliceIn m B zs s (j : ℕ))).map HvdH.cfxVal := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · simp [h] at hs
    · exact h
  rw [List.getD_eq_getElem _ _ (by simpa [HvdH.slices] using hs)]
  simp only [HvdH.slices, List.getElem_map, List.getElem_range]
  rw [range_map_eq_ofFn, List.map_ofFn, List.ofFn_inj]
  funext i
  simp only [Function.comp_apply, sliceIn]
  have hidx : (s / B * m + (i : ℕ)) * B + s % B < zs.length := by
    rw [hzs]
    have := idxbound (A := A) (m := m) (n := 1) (B := B) (by norm_num) hB s
      (by simpa using hs) (i : ℕ) i.isLt
    simpa using this
  rw [List.getD_eq_getElem _ _ (by simpa using hidx), List.getElem_map,
    List.getD_eq_getElem _ _ hidx]

/-- Item 2: `cfxVal` is injective. -/
theorem pbRF_cfxVal_injective : Function.Injective HvdH.cfxVal := by
  intro x y h
  simp only [HvdH.cfxVal] at h
  obtain ⟨h1, h2⟩ := Val.cons.inj h
  exact Prod.ext (Val.int.inj h1) (Val.int.inj h2)

/-- Item 4: the length of `axisPairs`. -/
theorem pbRF_axisPairs_length (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) : (axisPairs A m n B Φ zs).length = A * n * B := by
  simp [axisPairs]

/-- Item 5: `axisPairs` preserves the disc condition. -/
theorem pbRF_axisPairs_inDisc (p A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hzs : ∀ z ∈ zs, HvdH.inDisc p z)
    (hΦ : ∀ w : Fin m → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin n, HvdH.inDisc p (Φ w k)) :
    ∀ z ∈ Work.Resample.axisPairs A m n B Φ zs, HvdH.inDisc p z := by
  intro z hz
  simp only [axisPairs, List.mem_map, List.mem_range] at hz
  obtain ⟨idx, hidx, rfl⟩ := hz
  have hk : idx / B % n < n := Nat.mod_lt _ hn
  rw [ofFn_getD _ hk]
  refine hΦ _ ?_ _
  intro j
  simp only [sliceIn]
  by_cases h : ((idx / (n * B) * B + idx % B) / B * m + (j : ℕ)) * B
      + (idx / (n * B) * B + idx % B) % B < zs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hzs _ (List.getElem_mem h)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp only [Option.getD_none, inDisc]
    positivity

/-- Item 6: the four list-product facts at a position inside the list. -/
theorem pbRF_list_prod_facts (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).prod = (l.take j).prod * l.getD j 0 ∧
    (l.drop j).prod = l.getD j 0 * (l.drop (j + 1)).prod ∧
    l.prod = (l.take j).prod * (l.drop j).prod ∧
    l.getD j 0 ≤ l.sum := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← List.take_concat_get' l j hj, List.prod_append, List.getD_eq_getElem l 0 hj]
    simp
  · rw [← List.cons_getElem_drop_succ (l := l) (n := j) (h := hj), List.prod_cons,
      List.getD_eq_getElem l 0 hj]
  · exact (List.prod_take_mul_prod_drop l j).symm
  · rw [List.getD_eq_getElem l 0 hj]
    exact List.le_sum_of_mem (List.getElem_mem hj)

/-- Item 8: the encoded size of `cvecVal zs` for an in-disc array. -/
theorem pbRF_cvecVal_vsz_le (p : ℕ) (zs : List (ℤ × ℤ)) (hzs : ∀ z ∈ zs, HvdH.inDisc p z) :
    HvdH.vsz (HvdH.cvecVal zs) ≤ zs.length * (2 * p + 8) + zs.length + 1 := by
  rw [HvdH.cvecVal, Work.Layout.vsz_ofList]
  have h1 : (List.map HvdH.vsz (List.map HvdH.cfxVal zs)).sum ≤ zs.length * (2 * p + 8) := by
    have h2 := List.sum_le_length_nsmul (List.map HvdH.vsz (List.map HvdH.cfxVal zs)) (2 * p + 8)
      (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [List.mem_map] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        exact Work.Main.word.vsz_cfxVal_le (hzs z' hz'))
    simpa using h2
  have h3 : (List.map HvdH.cfxVal zs).length = zs.length := List.length_map ..
  omega

/-- **List- and array-level facts for the round lemma `Work.Resample.pbRound`.**  Eight independent
elementary facts about `HvdH.slices`/`HvdH.unslices`/`Work.Resample.axisPairs`/`Work.Resample.sliceIn`
(pbDefs), list products and `HvdH.vsz` of a `cvecVal`.  Every item is either a short index chase in
the style of `Submission/Work/Resample/axisBridge.lean` (which proves `unslices_axisPairs` and
`axisList_eq_axisPairs`) or a small list computation; none of them involves any program.  Useful
ingredients already in the workspace: `Work.Layout.range_map_eq_ofFn`, `Work.Resample.axisList_length_axisIter_length`
(`Submission/Work/Resample/axis.lean`), `Work.Main.word.vsz_cfxVal_le`, `Work.Layout.vsz_ofList`
(`Submission/Work/Layout/appendDefs.lean`), `Work.Resample.idxbound`
(`Submission/Work/Resample/axisDefs.lean`). -/
theorem pbRoundFacts :
    (∀ (A m B : ℕ) (zs : List (ℤ × ℤ)) (s : ℕ), zs.length = A * m * B → s < A * B →
      (HvdH.slices A m B (zs.map HvdH.cfxVal)).getD s [] =
        (List.ofFn (fun j : Fin m => Work.Resample.sliceIn m B zs s (j : ℕ))).map HvdH.cfxVal) ∧
    Function.Injective HvdH.cfxVal ∧
    (∀ (n : ℕ) (w : List (ℤ × ℤ)) (f : Fin n → ℤ × ℤ),
      w.length = n → (∀ k : Fin n, w.getD k (0, 0) = f k) → w = List.ofFn f) ∧
    (∀ (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)),
      (Work.Resample.axisPairs A m n B Φ zs).length = A * n * B) ∧
    (∀ (p A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)),
      0 < m → 0 < n → 0 < B → (∀ z ∈ zs, HvdH.inDisc p z) →
      (∀ w : Fin m → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin n, HvdH.inDisc p (Φ w k)) →
      ∀ z ∈ Work.Resample.axisPairs A m n B Φ zs, HvdH.inDisc p z) ∧
    (∀ (l : List ℕ) (j : ℕ), j < l.length →
      (l.take (j + 1)).prod = (l.take j).prod * l.getD j 0 ∧
      (l.drop j).prod = l.getD j 0 * (l.drop (j + 1)).prod ∧
      l.prod = (l.take j).prod * (l.drop j).prod ∧
      l.getD j 0 ≤ l.sum) ∧
    (∀ (l : List ℕ), (∀ x ∈ l, 1 ≤ x) → 1 ≤ l.prod) ∧
    (∀ (p : ℕ) (zs : List (ℤ × ℤ)), (∀ z ∈ zs, HvdH.inDisc p z) →
      HvdH.vsz (HvdH.cvecVal zs) ≤ zs.length * (2 * p + 8) + zs.length + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A m B zs s hzs hs
    exact pbRF_slices_getD A m B zs s hzs hs
  · exact pbRF_cfxVal_injective
  · intro n w f hlen hget
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      have hthis : w.getD i (0, 0) = f ⟨i, by rw [← hlen]; exact h1⟩ :=
        hget ⟨i, by rw [← hlen]; exact h1⟩
      rw [List.getD_eq_getElem w (0, 0) h1] at hthis
      rw [List.getElem_ofFn]
      exact hthis
  · intro A m n B Φ zs
    exact pbRF_axisPairs_length A m n B Φ zs
  · intro p A m n B Φ zs hm hn hB hzs hΦ
    exact pbRF_axisPairs_inDisc p A m n B Φ zs hm hn hB hzs hΦ
  · intro l j hj
    exact pbRF_list_prod_facts l j hj
  · intro l h
    exact List.one_le_prod_of_one_le h
  · intro p zs hzs
    exact pbRF_cvecVal_vsz_le p zs hzs

end Work.Resample
