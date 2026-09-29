import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `zipCvec`: pointwise combination of two coefficient vectors

`zipCvec` is the "zip two lists" word of `KLib` (`KLib.zipWith`), specialised to lists of
coefficient vectors `cvecVal w = ofList (w.map cfxVal)`.  It is the piece the synchronous FFT
uses to combine two vectors of `r` fixed-point complex numbers pointwise: given a word `q`
(`WordR main q`) that combines one pair `cfxVal u :: cfxVal v :: rest` into `cfxVal w :: rest`
at cost `c` and error `Err u v w`, the word `comb q` combines the two whole vectors at cost
`r * (c + K * (2*p+8)) + K`.

The only non-structural input is the size bound `vsz (cfxVal z) ≤ 2*p + 7` for `z ∈ D_p`
(`Work.SynFFT.MrgKit.vsz_cfxVal_le`), which is what makes the `KLib.zipWith` cost
`r * (c + K * (L + 1)) + K` collapse to the target form with `L = 2*p + 7`.
-/

namespace Work.SynFFT

open HvdH

/-- `cfxVal` is injective. -/
lemma zipCvec_cfxVal_inj {u v : ℤ × ℤ} (h : cfxVal u = cfxVal v) : u = v := by
  have h1 : u.1 = v.1 ∧ u.2 = v.2 := by simpa [cfxVal] using h
  exact Prod.ext h1.1 h1.2

/-- Reading the `i`-th entry of a mapped list (`i` in range) : the default of the *source* list is
`(0,0)`, while the default of the mapped list is arbitrary. -/
lemma zipCvec_map_getD (f : ℤ × ℤ → Val) (l : List (ℤ × ℤ)) {i : ℕ} (h : i < l.length) (d : Val) :
    (l.map f).getD i d = f (l.getD i (0,0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  exact congrArg f (by rw [List.getD_eq_getElem l (0,0) h])

/-- Two lists of equal length whose `getD`s agree below the length are equal. -/
lemma zipCvec_list_ext_getD {α : Type} {l₁ l₂ : List α} (d : α) (h : l₁.length = l₂.length)
    (h' : ∀ i < l₁.length, l₁.getD i d = l₂.getD i d) : l₁ = l₂ :=
  List.ext_getElem h (fun i h₁ h₂ => by
    rw [← List.getD_eq_getElem l₁ d h₁, ← List.getD_eq_getElem l₂ d h₂]
    exact h' i h₁)

/-- `getD` at an in-range index of `List.ofFn`. -/
lemma zipCvec_ofFn_getD {n : ℕ} {f : Fin n → ℤ × ℤ} {i : ℕ} (h : i < n) (d : ℤ × ℤ) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem zipCvec (hk : Work.SynFFT.KLib) : ∃ (comb : HvdH.Cmd → HvdH.Cmd) (Kz : ℕ), ∀ (main q : HvdH.Cmd) (rest : List HvdH.Val) (p r : ℕ) (Err : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) → Prop) (c : ℕ) (w₁ w₂ : List (ℤ × ℤ)), w₁.length = r → w₂.length = r → (∀ z ∈ w₁, HvdH.inDisc p z) → (∀ z ∈ w₂, HvdH.inDisc p z) → (∀ u v : ℤ × ℤ, HvdH.inDisc p u → HvdH.inDisc p v → HvdH.WordR main q (fun vs => vs = HvdH.cfxVal u :: HvdH.cfxVal v :: rest) (fun _ out => ∃ w : ℤ × ℤ, out = HvdH.cfxVal w :: rest ∧ HvdH.inDisc p w ∧ Err u v w) (fun _ => c)) → HvdH.WordR main (comb q) (fun vs => vs = HvdH.cvecVal w₁ :: HvdH.cvecVal w₂ :: rest) (fun _ out => ∃ wd : List (ℤ × ℤ), out = HvdH.cvecVal wd :: rest ∧ wd.length = r ∧ (∀ z ∈ wd, HvdH.inDisc p z) ∧ ∀ i : Fin r, Err (w₁.getD (i : ℕ) (0, 0)) (w₂.getD (i : ℕ) (0, 0)) (wd.getD (i : ℕ) (0, 0))) (fun _ => r * (c + Kz * (2 * p + 8)) + Kz) := by
  obtain ⟨comb, K, hK⟩ := hk.zipWith
  refine ⟨comb, K, ?_⟩
  intro main q rest p r Err c w₁ w₂ hw₁ hw₂ hd₁ hd₂ hq
  -- `KLib.zipWith` is applied to the two coefficient vectors `w₁`, `w₂` and to the
  -- pointwise predicate `P`; `q`'s output value is bounded by `2*p+7` by `inDisc`,
  -- so that `L = 2*p+7` and the zip cost is exactly the announced one.
  have hlen : (w₁.map cfxVal).length = (w₂.map cfxVal).length := by simp [hw₁, hw₂]
  have hlen1 : (w₁.map cfxVal).length = r := by simp [hw₁]
  have hlen2 : (w₂.map cfxVal).length = r := by simp [hw₂]
  have hxs : ∀ i < r, (w₁.map cfxVal).getD i .nil = cfxVal (w₁.getD i (0,0)) := fun i hi =>
    zipCvec_map_getD cfxVal w₁ (by simpa [hw₁] using hi) .nil
  have hys : ∀ i < r, (w₂.map cfxVal).getD i .nil = cfxVal (w₂.getD i (0,0)) := fun i hi =>
    zipCvec_map_getD cfxVal w₂ (by simpa [hw₂] using hi) .nil
  have hP : ∀ i < (w₁.map cfxVal).length,
      (∃ u v : ℤ × ℤ, (w₁.map cfxVal).getD i .nil = cfxVal u ∧
        (w₂.map cfxVal).getD i .nil = cfxVal v ∧ inDisc p u ∧ inDisc p v) := by
    intro i hi
    have hi1 : i < r := by simpa [hw₁] using hi
    have hi2 : i < r := by simpa [hw₂, hw₁] using hi
    refine ⟨w₁.getD i (0,0), w₂.getD i (0,0), hxs i hi1, hys i hi2, hd₁ _ ?_, hd₂ _ ?_⟩
    · rw [List.getD_eq_getElem w₁ (0,0) (by simpa [hw₁] using hi)]; exact List.getElem_mem _
    · rw [List.getD_eq_getElem w₂ (0,0) (by simpa [hw₂, hw₁] using hi)]; exact List.getElem_mem _
  have hL : ∀ x ∈ (w₁.map cfxVal) ++ (w₂.map cfxVal), vsz x ≤ 2*p + 7 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact Work.SynFFT.MrgKit.vsz_cfxVal_le p u (hd₁ u hu)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact Work.SynFFT.MrgKit.vsz_cfxVal_le p u (hd₂ u hu)
  have hq' : ∀ x y, (∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧ inDisc p u ∧ inDisc p v) →
      WordR main q (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧
          (∃ u v w : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧ z = cfxVal w ∧ Err u v w ∧ inDisc p w) ∧
          vsz z ≤ 2*p+7) (fun _ => c) := by
    rintro x y ⟨u, v, hx, hy, hu, hv⟩
    refine hk.conseq main q _ _ _ _ _ _ (hq u v hu hv) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hx, hy]
    · intro vs out hvs hpost
      obtain ⟨w, hout, hwd, herr⟩ := hpost
      exact ⟨cfxVal w, hout, ⟨u, v, w, hx, hy, rfl, herr, hwd⟩,
        Work.SynFFT.MrgKit.vsz_cfxVal_le p w hwd⟩
    · intro vs _
      exact le_rfl
  have hmain := hK main q rest _ _ c (2*p+7) hq' (w₁.map cfxVal) (w₂.map cfxVal) hlen hP hL
  refine hk.conseq main (comb q) _ _ _ _ _ _ hmain ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · -- extract the pointwise witnesses `w : ℤ × ℤ` from the zip output `zs : List Val`
    intro vs out hvs hpost
    obtain ⟨zs, hout, hzlen, hQ⟩ := hpost
    have hex : ∀ (i : ℕ) (hi : i < r), ∃ w : ℤ × ℤ,
        zs.getD i .nil = cfxVal w ∧ Err (w₁.getD i (0,0)) (w₂.getD i (0,0)) w ∧ inDisc p w := by
      intro i hi
      have hi1 : i < (w₁.map cfxVal).length := by simpa [hw₁] using hi
      obtain ⟨u, v, w, hx, hy, hz, herr, hwd⟩ := hQ i hi1
      have hx' := hxs i hi
      have hy' := hys i hi
      have hu : u = w₁.getD i (0,0) := zipCvec_cfxVal_inj (hx.symm.trans hx')
      have hv : v = w₂.getD i (0,0) := zipCvec_cfxVal_inj (hy.symm.trans hy')
      refine ⟨w, hz, ?_, hwd⟩
      rw [← hu, ← hv]
      exact herr
    set wd := List.ofFn (fun i : Fin r => Classical.choose (hex i i.isLt)) with hwd_def
    have hwdlen : wd.length = r := by simp [hwd_def]
    have hget : ∀ i (hi : i < r), wd.getD i (0,0) = Classical.choose (hex i hi) := by
      intro i hi
      rw [hwd_def]
      exact zipCvec_ofFn_getD hi (0,0)
    have hzs : zs = wd.map cfxVal := by
      refine zipCvec_list_ext_getD .nil ?_ ?_
      · simp [hzlen, hwdlen, hw₁]
      · intro i hi
        have hir : i < r := by rw [hzlen] at hi; simpa [hw₁] using hi
        have h1 : zs.getD i .nil = cfxVal (Classical.choose (hex i hir)) :=
          (Classical.choose_spec (hex i hir)).1
        have h2 : (wd.map cfxVal).getD i .nil = cfxVal (wd.getD i (0,0)) :=
          zipCvec_map_getD cfxVal wd (by rw [hwdlen]; exact hir) .nil
        rw [h1, h2, hget i hir]
    have hcvec : ofList zs = cvecVal wd := by
      rw [cvecVal, hzs]
    refine ⟨wd, ?_, hwdlen, ?_, ?_⟩
    · rw [hout, hcvec]
    · intro z hz
      rw [hwd_def] at hz
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
      rw [← hi]
      exact (Classical.choose_spec (hex i i.isLt)).2.2
    · intro i
      have h1 := (Classical.choose_spec (hex (i:ℕ) i.isLt)).2.1
      have h2 : wd.getD (i:ℕ) (0,0) = Classical.choose (hex (i:ℕ) i.isLt) := hget (i:ℕ) i.isLt
      rw [h2]
      exact h1
  · intro vs _
    have h2 : (2 * p + 7) + 1 = 2 * p + 8 := by omega
    rw [hlen1, h2]

end Work.SynFFT
