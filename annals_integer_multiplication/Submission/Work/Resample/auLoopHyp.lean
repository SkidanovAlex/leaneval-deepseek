import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auWinRec
import Submission.Work.Resample.auElemsElem
import Submission.Work.Resample.auKSum
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auStreamSz
import Submission.Work.Resample.auWinSlice
import Submission.Work.Resample.auWtSize

/-!
# The hypotheses of the window loop of `Work.Resample.auLoopWord` (paper Lemma 4.9)

`Work.Resample.auLoopWord` runs the window loop over the record table of the resampling: at round
`k` it pops one record `auRecF p α s t k` (whose first entry is the slide
`auK s t (k+1) - auK s t k` of the window centre), advances the input pointer by that slide,
duplicates the window with `Layout.dup`, `drop`s the slide entries from the front of the window,
appends the new entry from the element run, and `take`s the window back to length `auL p α`.

This module collects, in one statement, everything the loop word is told about that data:

* the slides are `0`/`1`-valued (`auK_step_sub`) and telescope to the centre `auK s t k`
  (`auKSum`, `auKArith_mono`, `auK_zero`);
* the windows all have length `auL p α` (`auWinV_length`) and are updated by
  drop/append/take (`auWinRec`);
* the element run `auElems p α s u` is indexed by the centre: when the slide is `1` the entry
  it exposes is exactly `auElem p α s t u k` (`auElemsElem`), which is what the window
  recurrence appends;
* the total number of slides `∑_{k<t} (auK (k+1) - auK k) = auK s t t` does not exceed the
  length of the element run (so the pointer never runs off the array);
* every value that occurs (window entries, weights, the element run, the `nil` marker) has
  encoding size at most `auL p α * (3p+16) + 4 + (2p+8) + 100`: weights are `auWt` values of
  size `≤ auSZ p = 10p+400` (`auWtSize`), entries of the window/element run are `cfxVal z`
  with `z` in the disc (size `≤ 2p+8`, `Work.ConvR.vsz_cfxVal_le`).

The weight table itself is not mentioned: it is delivered by the record table
`auRecsF p α s t`, whose length is `t`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Auxiliary list lemmas -/

/-- `getD` of a `drop`-and-`map`, at an in-range index: the `k`-th entry of `(l.drop n).map f`
is `f` applied to the `(n+k)`-th entry of `l`.  (`getD`-form of `auDropMap_getElem?_getD`.) -/
lemma auDropMap_getD {β γ : Type*} (l : List β) (f : β → γ) (d : β) (d' : γ) (n k : ℕ)
    (h : n + k < l.length) :
    ((l.drop n).map f).getD k d' = f (l.getD (n + k) d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
    List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

/-- The extended array is at least `s + auL p α` long: `auCop p α s * s` covers
`auOff + s + 2·auM + 1 = auOff + s + auL`. -/
lemma auExt_length_ge (p α s : ℕ) (hs : 1 ≤ s) (u : List (ℤ × ℤ)) (hu : u.length = s) :
    s + auL p α ≤ (auExt p α s u).length := by
  have h := auCop_mul_ge p α s hs
  rw [auExt_length p α s u, hu]
  simp only [auL]
  omega

/-- If `auK s t k ≤ s - 1` then the look-up at `auK s t k + auL p α` is a valid index of the
extended array: `auL p α + auK s t k ≤ auL p α + s - 1 < auL p α + s ≤ auExt.length`. -/
lemma auK_add_auL_lt (p α s t k : ℕ) (hs : 2 ≤ s) (hK : auK s t k ≤ s - 1)
    (u : List (ℤ × ℤ)) (hu : u.length = s) :
    auK s t k + auL p α < (auExt p α s u).length := by
  have h := auCop_mul_ge p α s (by omega : 1 ≤ s)
  rw [auExt_length p α s u, hu]
  simp only [auL] at *
  omega

/-- `getD` of the element run, in range: the `(auK s t k)`-th entry of `auElems p α s u` is the
`cfxVal`-image of the `(auK s t k + auL p α)`-th entry of the extended array. -/
lemma auElems_getD_eq (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ)
    (h : auK s t k + auL p α < (auExt p α s u).length) :
    (auElems p α s u).getD (auK s t k) HvdH.Val.nil
      = cfxVal ((auExt p α s u).getD (auK s t k + auL p α) (0, 0)) := by
  rw [auElems, Nat.add_comm (auK s t k) (auL p α)]
  exact auDropMap_getD (auExt p α s u) cfxVal (0, 0) HvdH.Val.nil (auL p α) (auK s t k)
    (by omega)

/-- Every entry of the extended array is an entry of the input array. -/
lemma mem_auExt {p α s : ℕ} {u : List (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ auExt p α s u) :
    z ∈ u := by
  have h1 : z ∈ (List.replicate (auCop p α s) u).flatten := List.mem_of_mem_drop hz
  obtain ⟨t, ht, hzt⟩ := List.mem_flatten.mp h1
  obtain ⟨-, htu⟩ := List.mem_replicate.mp ht
  rwa [htu] at hzt

/-- Every entry of the window of round `k` (`k < t`) is an entry of the input array, hence lies
in the disc. -/
lemma auWin_mem_inDisc (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (u : List (ℤ × ℤ)) (hu : u.length = s) (hd : ∀ z ∈ u, inDisc p z)
    (k : ℕ) (hk : k < t) : ∀ z ∈ auWin p α s t u k, inDisc p z := by
  intro z hz
  obtain ⟨i, hi, hzi⟩ := List.mem_map.mp hz
  rw [List.mem_range] at hi
  rw [← hzi, auIdx p α s t hs hst hα hp hαp u hu k hk i hi]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hu]; exact auJ_lt p α s t k i hs)]
  exact hd _ (List.getElem_mem _)

/-- The uniform size bound of the loop (`auL p α * (3p+16) + 4 + (2p+8) + 100`) dominates the
weight size bound `auSZ p = 10p + 400`, because `p ≥ 100`, `α ≥ 2` give `auL p α ≥ 45`. -/
lemma auSZ_le_winBd (p α : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) :
    auSZ p ≤ auL p α * (3 * p + 16) + 4 + (2 * p + 8) + 100 := by
  have hsqrt : 10 ≤ Nat.sqrt p := by rw [Nat.le_sqrt]; omega
  have hM : 11 * 2 ≤ auM p α := by
    simp only [auM]
    exact Nat.mul_le_mul (by omega) hα
  have hL : 45 ≤ auL p α := by simp only [auL]; omega
  have h4 : 45 * (3 * p + 16) ≤ auL p α * (3 * p + 16) := Nat.mul_le_mul_right _ hL
  simp only [auSZ]
  omega

/-! ## The hypothesis package -/

theorem auLoopHyp (p α s t : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hd : ∀ z ∈ u, HvdH.inDisc p z)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hst : s < t) (hu : u.length = s) :
    (∀ k, Work.Resample.auK s t (k + 1) - Work.Resample.auK s t k ≤ 1) ∧
    (∀ k, ((List.range k).map (fun j => Work.Resample.auK s t (j + 1) - Work.Resample.auK s t j)).sum
      = Work.Resample.auK s t k) ∧
    (∀ k ≤ t, (Work.Resample.auWinV p α s t u k).length = Work.Resample.auL p α) ∧
    (∀ k, k + 1 < t → Work.Resample.auWinV p α s t u (k + 1) =
      ((Work.Resample.auWinV p α s t u k).drop (Work.Resample.auK s t (k + 1) - Work.Resample.auK s t k) ++
        [(Work.Resample.auElems p α s u).getD (Work.Resample.auK s t k) HvdH.Val.nil]).take
          (Work.Resample.auL p α)) ∧
    (∀ k < t, Work.Resample.auK s t (k + 1) - Work.Resample.auK s t k = 1 →
      (Work.Resample.auElems p α s u).getD (Work.Resample.auK s t k) HvdH.Val.nil =
        Work.Resample.auElem p α s t u k) ∧
    (∀ k < t, (Work.Resample.auWts p α s t k).length = Work.Resample.auL p α) ∧
    (Work.Resample.auRecsF p α s t).length = t ∧
    (((List.range t).map (fun j => Work.Resample.auK s t (j + 1) - Work.Resample.auK s t j)).sum
      ≤ (Work.Resample.auElems p α s u).length) ∧
    (∀ v ∈ Work.Resample.auWinV p α s t u 0,
      HvdH.vsz v ≤ Work.Resample.auL p α * (3 * p + 16) + 4 + (2 * p + 8) + 100) ∧
    (∀ k < t, ∀ v ∈ Work.Resample.auWts p α s t k,
      HvdH.vsz v ≤ Work.Resample.auL p α * (3 * p + 16) + 4 + (2 * p + 8) + 100) ∧
    (∀ v ∈ Work.Resample.auElems p α s u,
      HvdH.vsz v ≤ Work.Resample.auL p α * (3 * p + 16) + 4 + (2 * p + 8) + 100) ∧
    HvdH.vsz (HvdH.Val.nil)
      ≤ Work.Resample.auL p α * (3 * p + 16) + 4 + (2 * p + 8) + 100 := by
  have ht : 0 < t := by omega
  have hs1 : 1 ≤ s := by omega
  -- the slide and its monotonicity
  have hslide : ∀ k, auK s t (k + 1) - auK s t k ≤ 1 := fun k => auK_step_sub hst ht
  have hmono : ∀ k, auK s t k ≤ auK s t (k + 1) :=
    fun k => auKArith_mono s t (by omega)
  refine ⟨hslide, fun k => auKSum s t k, fun k _ => auWinV_length p α s t u k, ?_, ?_,
    fun k _ => auWts_length p α s t k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the window recurrence
    intro k hk
    rcases (by have := hslide k; omega :
        auK s t (k + 1) - auK s t k = 0 ∨ auK s t (k + 1) - auK s t k = 1) with h0 | h1
    · -- slide `0`: the window does not move, and the appended entry is truncated away
      have heq : auK s t (k + 1) = auK s t k := by have := hmono k; omega
      have hwin : auWin p α s t u (k + 1) = auWin p α s t u k := by
        simp only [auWin]
        rw [heq]
      rw [h0, List.drop_zero,
        show auWinV p α s t u (k + 1) = auWinV p α s t u k by
          simp only [auWinV]; rw [hwin],
        ← auWinV_length p α s t u k]
      exact List.take_left.symm
    · -- slide `1`: `auWinRec`, with the appended entry identified
      have hKle : auK s t (k + 1) ≤ s := auK_le_s hs1 ht (by omega)
      have hKk : auK s t k ≤ s - 1 := by omega
      have hg : (auElems p α s u).getD (auK s t k) HvdH.Val.nil
          = cfxVal ((auExt p α s u).getD (auK s t k + auL p α) (0, 0)) :=
        auElems_getD_eq p α s t u k (auK_add_auL_lt p α s t k hs hKk u hu)
      rw [h1, hg]
      simpa only [auWinV, h1] using auWinRec p α s t hs hst u hu k hk
  · -- the exposed element when the slide is `1`
    intro k hk hk1
    have hKle : auK s t (k + 1) ≤ s := auK_le_s hs1 ht (by omega)
    have hKk : auK s t k ≤ s - 1 := by omega
    have hrange : auL p α + auK s t k < (auExt p α s u).length := by
      have h := auK_add_auL_lt p α s t k hs hKk u hu
      omega
    rw [List.getD_eq_getElem?_getD, auElemsElem p α s t u k hrange]
    rfl
  · -- length of the record table
    simp [auRecsF]
  · -- the pointer never runs off the element run
    rw [auKSum s t t]
    have h1 : auK s t t ≤ s := auK_le_s hs1 ht le_rfl
    have h2 : s ≤ (auElems p α s u).length := by
      have h := auExt_length_ge p α s hs1 u hu
      rw [auElems, List.length_map, List.length_drop]
      omega
    omega
  · -- size of the initial window
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have h := auWin_mem_inDisc p α s t hs hst hα hp hαp u hu hd 0 ht z hz
    have h2 := Work.ConvR.vsz_cfxVal_le h
    simp only [Work.ConvR.cfxSz] at h2
    have hX : 0 ≤ auL p α * (3 * p + 16) := Nat.zero_le _
    omega
  · -- sizes of the weights
    intro k hk v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    rw [List.mem_range] at hi
    rw [Work.ConvR.vsz_int]
    have h1 := auWtSize p α t (auNsq p α s t k i) (auNsq_nonneg p α s t k i) hα
      (by omega : 1 ≤ t) hp
    have h2 := auSZ_le_winBd p α hp hα
    omega
  · -- sizes of the element run
    intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have hzu : z ∈ u := mem_auExt (List.mem_of_mem_drop hz)
    have h2 := Work.ConvR.vsz_cfxVal_le (hd z hzu)
    simp only [Work.ConvR.cfxSz] at h2
    have hX : 0 ≤ auL p α * (3 * p + 16) := Nat.zero_le _
    omega
  · -- size of the `nil` marker
    have hX : 0 ≤ auL p α * (3 * p + 16) := Nat.zero_le _
    simp only [HvdH.vsz, HvdH.Val.enc, List.length_cons, List.length_nil]
    omega

end Work.Resample
