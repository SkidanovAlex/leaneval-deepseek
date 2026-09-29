import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.lvlAllGetD
import Submission.Work.SynFFT.cvecsInj
import Submission.Work.SynFFT.dftNSubLe
import Submission.Work.SynFFT.chunkSlices
import Submission.Work.SynFFT.arrSize

/-!
# The axis step of the synthetic FFT: shared vocabulary of the `HasAxis` assembly

`Work.SynFFT.HasAxis` (kit2.lean) asks for a word that applies the slice word `HasFFT1` to every
`i`-slice of the `A × t × B` decomposition of a flat array and reassembles the result in the flat
layout.  The assembly (in `Submission/Work/SynFFT/hasAxis.lean`) is

```
T(A,t,B)   -- gather: flat ↦ slice-major (`List.flatten (slices A t B es)`)
axisParamsDown, pick 6, chunksOf t   -- the slices as values
mapList (HasFFT1 word)               -- transform every slice
flatten, axisParamsUp, T(A,B,t), axisSwap23   -- back to the flat layout
```

where `T` is the transpose of `Work.SynFFT.HasAxisTranspose` (axisDefs.lean).  This file holds the
vocabulary shared by the pieces of that assembly: the scattering permutation, the per-slice data,
the per-element predicates of the `mapList` stage, the budget, and the elementary size/read-off
lemmas.

**Import note.** `Submission/Work/SynFFT/axisSliceGetD.lean` and `.../lvlAllGetD.lean` both define
`Work.SynFFT.getD_map_range`, so no module may import both (nor `slicesGetDCvecs`, which pulls in
the first).  Everything this development needs from that file (`getD_map_range`,
`getD_flatten_blocks`) is available in `lvlAllGetD` (`getD_map_range`, `getD_flatten_eq`); the two
lemmas that live only in `slicesGetDCvecs.lean` (`slicesIdx_lt`, the read-off of a slice of a
`cvecs` list) are reproved below under primed names.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## The scattering permutation

`scatterCvecs` says that applying the *transpose* to the slice-major data of shape `A × B × t`
computes exactly the flat array read through the permutation
`i ↦ (i / (t*B)*B + i % B) * t + i / B % t` of `[0, A*t*B)`.  This is the list the axis word must
return. -/

/-- The scattered flat array: `W` read through the permutation that inverts the transpose. -/
def scatList (A t B : ℕ) (W : List (List (ℤ × ℤ))) : List (List (ℤ × ℤ)) :=
  (List.range (A * t * B)).map fun i => W.getD ((i / (t * B) * B + i % B) * t + i / B % t) []

theorem scatList_length (A t B : ℕ) (W : List (List (ℤ × ℤ))) :
    (scatList A t B W).length = A * t * B := by
  simp [scatList]

/-! ## The slices of a flat array -/

/-- The `s`-th slice of the flat `A × t × B` array `ws` (a list of coefficient vectors), as a list
of coefficient vectors of length `t`. -/
def sliceVal (A t B : ℕ) (ws : List (List (ℤ × ℤ))) (s : ℕ) : List (List (ℤ × ℤ)) :=
  (List.range t).map fun j => ws.getD ((s / B * t + j) * B + s % B) []

theorem sliceVal_length (A t B s : ℕ) (ws : List (List (ℤ × ℤ))) :
    (sliceVal A t B ws s).length = t := by
  simp [sliceVal]

theorem getD_sliceVal (A t B s q : ℕ) (ws : List (List (ℤ × ℤ))) (hq : q < t) :
    (sliceVal A t B ws s).getD q [] = ws.getD ((s / B * t + q) * B + s % B) [] :=
  getD_map_range (fun j => ws.getD ((s / B * t + j) * B + s % B) []) [] hq

/-- The flat index of the `(s,j)`-entry of a flat `A × t × B` array is in range. -/
theorem slicesIdxLt' (A t B s j : ℕ) (hs : s < A * B) (hj : j < t) :
    (s / B * t + j) * B + s % B < A * t * B := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hs
    · exact h
  have hdiv : s / B < A := (Nat.div_lt_iff_lt_mul hB).mpr hs
  have hstep : s / B * t + j + 1 ≤ A * t := by
    have h1 : s / B + 1 ≤ A := by omega
    calc s / B * t + j + 1 ≤ s / B * t + t := by omega
      _ = (s / B + 1) * t := by ring
      _ ≤ A * t := Nat.mul_le_mul_right t h1
  calc (s / B * t + j) * B + s % B
      < (s / B * t + j) * B + B := by
        have := Nat.mod_lt s hB; omega
    _ = (s / B * t + j + 1) * B := by ring
    _ ≤ A * t * B := Nat.mul_le_mul_right B hstep

/-- An in-range `getD` of `cvecs` is the `cvecVal` of the corresponding `getD`. -/
theorem cvecsGetD' (ws : List (List (ℤ × ℤ))) (i : ℕ) (h : i < ws.length) :
    (cvecs ws).getD i (default : Val) = cvecVal (ws.getD i []) := by
  rw [cvecs, List.getD_eq_getElem _ (default : Val) (by simpa [List.length_map] using h),
    List.getElem_map, List.getD_eq_getElem _ ([] : List (ℤ × ℤ)) h]

/-- The `s`-th slice of `cvecs ws` is `cvecs` of the `s`-th slice of `ws`. -/
theorem slicesGetD' (A t B : ℕ) (ws : List (List (ℤ × ℤ))) (h : ws.length = A * t * B)
    (s : ℕ) (hs : s < A * B) :
    (HvdH.slices A t B (cvecs ws)).getD s [] = cvecs (sliceVal A t B ws s) := by
  have h1 : (HvdH.slices A t B (cvecs ws)).getD s [] =
      (List.range t).map (fun j => (cvecs ws).getD ((s / B * t + j) * B + s % B)
        (default : Val)) := by
    simp only [HvdH.slices]
    exact getD_map_range _ [] hs
  have h2 : cvecs (sliceVal A t B ws s) =
      (List.range t).map (fun j => cvecVal (ws.getD ((s / B * t + j) * B + s % B) [])) := by
    rw [sliceVal, cvecs, List.map_map]
    rfl
  rw [h1, h2]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact cvecsGetD' ws _ (by rw [h]; exact slicesIdxLt' A t B s j hs hj)

/-- Every entry of a slice of an in-disc array is in-disc. -/
theorem sliceVal_inDisc (p r A t B s : ℕ) (ws : List (List (ℤ × ℤ))) (h : ws.length = A * t * B)
    (hID : ∀ w ∈ ws, InDiscVec p r w) (hs : s < A * B) :
    ∀ w ∈ sliceVal A t B ws s, InDiscVec p r w := by
  intro w hw
  simp only [sliceVal, List.mem_map, List.mem_range] at hw
  obtain ⟨j, hj, rfl⟩ := hw
  rw [List.getD_eq_getElem _ _ (by rw [h]; exact slicesIdxLt' A t B s j hs hj)]
  exact hID _ (List.getElem_mem _)

/-! ## Sizes

`SlOK` bundles the two facts the axis step keeps about every slice; `slL` bounds the encoded size
of such a slice *value*. -/

/-- A slice: `t` coefficient vectors of length `r`, in the disc. -/
def SlOK (p r t : ℕ) (vs : List (List (ℤ × ℤ))) : Prop :=
  vs.length = t ∧ ∀ w ∈ vs, InDiscVec p r w

/-- The encoded-size bound of a slice value. -/
def slL (p r t : ℕ) : ℕ := t * (r * (2 * p + 6) + 2) + 1

theorem vsz_of_SlOK (p r t : ℕ) (hp : 0 < p) (vs : List (List (ℤ × ℤ))) (h : SlOK p r t vs) :
    vsz (ofList (cvecs vs)) ≤ slL p r t := by
  obtain ⟨hlen, hd⟩ := h
  have := vsz_rarrVal_tight p r t hp vs ⟨hlen, hd⟩
  simpa [slL, rarrVal, cvecs] using this

/-! ## The per-element predicates of the slice-map stage -/

/-- The precondition of the slice word: the value is the encoding of a slice. -/
def SlPre (p r t : ℕ) : Val → Prop :=
  fun x => ∃ vs : List (List (ℤ × ℤ)), x = ofList (cvecs vs) ∧ SlOK p r t vs

/-- The postcondition of the slice word: the output is the encoding of a transformed slice, and the
transformed slice approximates the synthetic transform of *any* `e`-approximation of the input
slice with error `≤ e + k`.  (The word is applied with the exact representation of the input slice
as its target, so that the `e` surcharge is only paid once.) -/
def SlPost (p r t k : ℕ) (sgn : ℤ) (e : ℝ) : Val → Val → Prop :=
  fun x y => ∃ vs vs' : List (List (ℤ × ℤ)),
    x = ofList (cvecs vs) ∧ y = ofList (cvecs vs') ∧ SlOK p r t vs ∧ SlOK p r t vs' ∧
    (∀ a : Arr r, ApproxSL p r t vs a e →
      ApproxSL p r t vs' (fun q => dftN r t sgn a q) (e + k))

theorem SlPre_intro (p r t : ℕ) (ws : List (List (ℤ × ℤ))) (h : SlOK p r t ws) :
    SlPre p r t (ofList (cvecs ws)) := ⟨ws, rfl, h⟩

/-! ## Reading off the slices of the flat array

The two facts that turn the chunk list produced by `LayoutLib.chunksOf` into the slices of
`ws`: the `s`-th chunk of the gathered array is `cvecs (sliceVal A t B ws s)`, and that slice
approximates the `s`-th restriction of any `e`-approximation of `ws`. -/

/-- The `s`-th chunk of the gathered array is the encoded `s`-th slice. -/
theorem chunkSliceVal (A t B : ℕ) (ws : List (List (ℤ × ℤ))) (h : ws.length = A * t * B)
    (s : ℕ) (hs : s < A * B) :
    cvecs (sliceVal A t B ws s) =
      ((List.flatten (HvdH.slices A t B (cvecs ws))).drop (s * t)).take t := by
  rw [chunkSlices A t B (cvecs ws) (by simp [cvecs, h]) s hs, slicesGetD' A t B ws h s hs]

/-- A slice of an `e`-approximation of the flat array is an `e`-approximation of the restriction. -/
theorem sliceApprox (p r A t B : ℕ) (u : Arr r) (e : ℝ) (ws : List (List (ℤ × ℤ)))
    (h : ws.length = A * t * B) (hu : ApproxSL p r (A * t * B) ws u e) :
    ∀ s < A * B, ApproxSL p r t (sliceVal A t B ws s)
      (fun j c => u ((s / B * t + j) * B + s % B) c) e := by
  intro s hs
  obtain ⟨-, hu'⟩ := hu
  refine ⟨sliceVal_length A t B s ws, ?_⟩
  intro q hq c
  rw [getD_sliceVal A t B s q ws hq]
  exact hu' _ (slicesIdxLt' A t B s q hs hq) c

/-- If every slice of `Vs` is in-disc, so is every vector of `Vs.flatten`. -/
theorem flatten_InDisc {p r t N : ℕ} (Vs : List (List (List (ℤ × ℤ)))) (hVlen : Vs.length = N)
    (h : ∀ s < N, SlOK p r t (Vs.getD s [])) :
    ∀ w ∈ Vs.flatten, InDiscVec p r w := by
  intro w hw
  rw [List.mem_flatten] at hw
  obtain ⟨l, hl, hwl⟩ := hw
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
  have hsi : (i : ℕ) < N := by rw [← hVlen]; exact i.2
  obtain ⟨-, hd⟩ := h i.1 hsi
  have hVi : Vs.getD (i : ℕ) [] = l := by
    rw [List.getD_eq_getElem _ _ i.2]; exact hi
  rw [hVi] at hd
  exact hd w hwl

/-! ## The budget -/

/-- The cost budget of one axis pass, matching the two summands of `HasAxis`. -/
def axisBd (A t B r p k : ℕ) : ℕ :=
  A * t * B * (r + 1) * (p + 1) * (k + 1) +
    A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2) + 1

theorem bd_ge_main (A t B r p k : ℕ) :
    A * t * B * (r + 1) * (p + 1) * (k + 1) ≤ axisBd A t B r p k := by
  unfold axisBd; omega

theorem bd_ge_log (A t B r p k : ℕ) :
    A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2) ≤ axisBd A t B r p k := by
  unfold axisBd; omega

theorem bd_ge_one (A t B r p k : ℕ) : 1 ≤ axisBd A t B r p k := by
  unfold axisBd; omega

theorem bd_ge_N (A t B r p k : ℕ) : A * t * B ≤ axisBd A t B r p k := by
  have h3 : 0 < (r + 1) * (p + 1) * (k + 1) := by positivity
  calc A * t * B = A * t * B * 1 := (Nat.mul_one _).symm
    _ ≤ A * t * B * ((r + 1) * (p + 1) * (k + 1)) := Nat.mul_le_mul_left _ h3
    _ = A * t * B * (r + 1) * (p + 1) * (k + 1) := by ring
    _ ≤ axisBd A t B r p k := bd_ge_main A t B r p k

theorem bd_ge_Nrp (A t B r p k : ℕ) :
    A * t * B * (r + 1) * (p + 1) ≤ axisBd A t B r p k := by
  have hk : 0 < k + 1 := by positivity
  calc A * t * B * (r + 1) * (p + 1)
      = A * t * B * (r + 1) * (p + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ A * t * B * (r + 1) * (p + 1) * (k + 1) := Nat.mul_le_mul_left _ hk
    _ ≤ axisBd A t B r p k := bd_ge_main A t B r p k

theorem bd_ge_rp (A t B r p k : ℕ) (hN : 0 < A * t * B) :
    (r + 1) * (p + 1) ≤ axisBd A t B r p k := by
  have h1 : 1 ≤ A * t * B := hN
  have h2 : 0 < k + 1 := by positivity
  calc (r + 1) * (p + 1) = 1 * ((r + 1) * (p + 1)) * 1 := by ring
    _ ≤ (A * t * B) * ((r + 1) * (p + 1)) * (k + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) h2
    _ = A * t * B * (r + 1) * (p + 1) * (k + 1) := by ring
    _ ≤ axisBd A t B r p k := bd_ge_main A t B r p k

theorem bd_ge_r (A t B r p k : ℕ) (hN : 0 < A * t * B) : r + 1 ≤ axisBd A t B r p k := by
  have hp : 0 < p + 1 := by positivity
  calc r + 1 = (r + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (r + 1) * (p + 1) := Nat.mul_le_mul_left _ hp
    _ ≤ axisBd A t B r p k := bd_ge_rp A t B r p k hN

theorem bd_ge_p (A t B r p k : ℕ) (hN : 0 < A * t * B) : p + 1 ≤ axisBd A t B r p k := by
  have hr : 0 < r + 1 := by positivity
  calc p + 1 = 1 * (p + 1) := (one_mul _).symm
    _ ≤ (r + 1) * (p + 1) := Nat.mul_le_mul_right _ hr
    _ ≤ axisBd A t B r p k := bd_ge_rp A t B r p k hN

theorem bd_ge_k (A t B r p k : ℕ) (hN : 0 < A * t * B) : k + 1 ≤ axisBd A t B r p k := by
  have hrp : 1 ≤ (r + 1) * (p + 1) := Nat.mul_pos (by omega) (by omega)
  have h1 : 1 ≤ A * t * B := hN
  calc k + 1 = 1 * (k + 1) := (one_mul _).symm
    _ ≤ ((r + 1) * (p + 1)) * (k + 1) := Nat.mul_le_mul_right _ hrp
    _ = (r + 1) * (p + 1) * (k + 1) := by ring
    _ ≤ A * t * B * ((r + 1) * (p + 1) * (k + 1)) := by
        calc (r + 1) * (p + 1) * (k + 1) = 1 * ((r + 1) * (p + 1) * (k + 1)) :=
              (one_mul _).symm
          _ ≤ (A * t * B) * ((r + 1) * (p + 1) * (k + 1)) := Nat.mul_le_mul_right _ h1
    _ = A * t * B * (r + 1) * (p + 1) * (k + 1) := by ring
    _ ≤ axisBd A t B r p k := bd_ge_main A t B r p k

theorem bd_ge_log' (A t B r p k : ℕ) (hN : 0 < A * t * B) :
    (A * t * B).size + 2 ≤ axisBd A t B r p k := by
  have h1 : 1 ≤ A * t * B := hN
  have hrp : 1 ≤ (r + 1) * (p + 1) := Nat.mul_pos (by omega) (by omega)
  calc (A * t * B).size + 2 = 1 * ((A * t * B).size + 2) := (one_mul _).symm
    _ ≤ ((A * t * B) * ((r + 1) * (p + 1))) * ((A * t * B).size + 2) :=
        Nat.mul_le_mul_right _ (by
          calc (1 : ℕ) = 1 * 1 := (Nat.mul_one 1).symm
            _ ≤ (A * t * B) * ((r + 1) * (p + 1)) := Nat.mul_le_mul h1 hrp)
    _ = A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2) := by ring
    _ ≤ axisBd A t B r p k := bd_ge_log A t B r p k

theorem bd_ge_szN (A t B r p k : ℕ) (hN : 0 < A * t * B) :
    A * t * B * ((A * t * B).size + 2) ≤ axisBd A t B r p k := by
  have hrp : 1 ≤ (r + 1) * (p + 1) := Nat.mul_pos (by omega) (by omega)
  calc A * t * B * ((A * t * B).size + 2)
      = A * t * B * 1 * ((A * t * B).size + 2) := by ring
    _ ≤ A * t * B * ((r + 1) * (p + 1)) * ((A * t * B).size + 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrp)
    _ = A * t * B * (r + 1) * (p + 1) * ((A * t * B).size + 2) := by ring
    _ ≤ axisBd A t B r p k := bd_ge_log A t B r p k

/-- `8 (r+1) (p+1)` dominates the encoded size `r (2p+6) + 2` of an in-disc coefficient vector. -/
theorem slL_le_rp (r p : ℕ) : r * (2 * p + 6) + 2 ≤ 8 * (r + 1) * (p + 1) := by
  nlinarith [Nat.zero_le r, Nat.zero_le p]


/-! ## List plumbing for the assembly -/

/-- `ofList` is injective. -/
theorem ofList_inj' : Function.Injective (ofList : List Val → Val) := by
  intro l
  induction l with
  | nil =>
      intro m h
      cases m with
      | nil => rfl
      | cons a t => exact (by have h' : Val.nil = Val.cons a (ofList t) := h; cases h')
  | cons a t ih =>
      intro m h
      cases m with
      | nil => exact (by have h' : Val.cons a (ofList t) = Val.nil := h; cases h')
      | cons b s =>
          have h' : Val.cons a (ofList t) = Val.cons b (ofList s) := h
          simp only [Val.cons.injEq] at h'
          obtain ⟨h1, h2⟩ := h'
          subst h1
          rw [ih h2]

/-- Two lists with the same length and the same `getD` at every index are equal. -/
theorem list_eq_of_getD {α : Type} (l₁ l₂ : List α) (d : α) (h : l₁.length = l₂.length)
    (h' : ∀ i, i < l₁.length → l₁.getD i d = l₂.getD i d) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons b s => simp at h
  | cons a t ih =>
      cases l₂ with
      | nil => simp at h
      | cons b s =>
          have h0 : a = b := by
            have := h' 0 (by simp)
            simpa using this
          subst h0
          have h2 : t.length = s.length := by simpa using h
          have h3 : ∀ i, i < t.length → t.getD i d = s.getD i d := by
            intro i hi
            have := h' (i + 1) (by simpa using hi)
            simpa using this
          rw [ih s h2 h3]

/-- Reading a list of encoded slices. -/
theorem getD_mapCvecs_mapOfList (Vs : List (List (List (ℤ × ℤ)))) (i : ℕ) :
    ((Vs.map cvecs).map ofList).getD i Val.nil = ofList (cvecs (Vs.getD i [])) := by
  have h1 := List.getD_map (f := ofList) (l := Vs.map cvecs) (d := ([] : List Val)) (n := i)
  have h2 := List.getD_map (f := cvecs) (l := Vs) (d := ([] : List (List (ℤ × ℤ)))) (n := i)
  have hnil : Val.nil = ofList ([] : List Val) := rfl
  have hnil2 : cvecs ([] : List (List (ℤ × ℤ))) = ([] : List Val) := rfl
  rw [hnil, h1, ← hnil2, h2]

/-- From a per-index witness of `ys`, build the list of slices `Vs`. -/
theorem exists_sliceList {A B : ℕ} (ys : List Val) (hy : ys.length = A * B)
    (G : ℕ → List (List (ℤ × ℤ)) → Prop)
    (hgood : ∀ s < A * B, ∃ vs' : List (List (ℤ × ℤ)),
      ys.getD s Val.nil = ofList (cvecs vs') ∧ G s vs') :
    ∃ Vs : List (List (List (ℤ × ℤ))), Vs.length = A * B ∧
      ys = (Vs.map cvecs).map ofList ∧ ∀ s < A * B, G s (Vs.getD s []) := by
  classical
  let F : ℕ → List (List (ℤ × ℤ)) :=
    fun s => if hs : s < A * B then Classical.choose (hgood s hs) else []
  have hF : ∀ s (hs : s < A * B), F s = Classical.choose (hgood s hs) := fun s hs => dite_eq_left hs
  have hFspec : ∀ s (hs : s < A * B),
      ys.getD s Val.nil = ofList (cvecs (F s)) ∧ G s (F s) :=
    fun s hs => (hF s hs).symm ▸ Classical.choose_spec (hgood s hs)
  refine ⟨(List.range (A * B)).map F, by simp, ?_, ?_⟩
  · refine list_eq_of_getD ys _ Val.nil (by simp [hy]) (fun i hi => ?_)
    have hiN : i < A * B := by rw [hy] at hi; exact hi
    rw [(hFspec i hiN).1, getD_mapCvecs_mapOfList, getD_map_range F [] hiN, hF i hiN]
  · intro s hs
    rw [getD_map_range F [] hs]
    exact (hFspec s hs).2

end Work.SynFFT
