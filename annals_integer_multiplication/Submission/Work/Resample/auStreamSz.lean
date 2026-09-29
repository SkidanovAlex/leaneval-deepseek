import Mathlib
import Submission.Work.Resample.auConvDefs
import Submission.Work.ConvR.basic

/-!
# Size bounds for the chunks and the stream of the resampling word

Paper Lemma 4.9 (the `q` word of the `Ã₁` slice): the stream `auStream p α s t u` is the
`ofList`-encodings of the `t` chunks `auChunk p α s t u k`, each a `cons` of its weight list
(`auL p α` integer values of size `≤ p + 3`) and of its window (`auL p α` fixed-point complex
values, each of size `≤ 2p + 8` when the window lies in the disc).  This module records the
resulting numerical bounds, which the cost estimate of the map word consumes.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- `vsz` of a `List.map` of values under a uniform pointwise bound. -/
theorem vsz_ofList_map_le {A : Type*} (l : List A) (f : A → Val) (B : ℕ)
    (h : ∀ a ∈ l, vsz (f a) ≤ B) :
    vsz (ofList (l.map f)) ≤ l.length * B + l.length + 1 := by
  rw [Work.ConvR.vsz_ofList, List.length_map]
  have hsum : (List.map vsz (List.map f l)).sum ≤ l.length * B := by
    rw [List.map_map]
    calc (List.map (vsz ∘ f) l).sum ≤ (List.map (fun _ => B) l).sum :=
          List.sum_le_sum (fun a ha => h a ha)
      _ = l.length * B := Work.ConvR.sum_map_const l B
  omega

/-- Size bound on the weight list of one chunk, from the pointwise bound `hw` on the weights. -/
theorem auWts_vsz_le (p α s t k : ℕ)
    (hw : ∀ i, i < auL p α → isz (auWt p α t (auNsq p α s t k i)) ≤ p + 3) :
    vsz (ofList (auWts p α s t k)) ≤ auL p α * (p + 3) + auL p α + 1 := by
  have h := vsz_ofList_map_le (l := List.range (auL p α))
    (f := fun i => Val.int (auWt p α t (auNsq p α s t k i))) (B := p + 3) (by
      intro i hi
      rw [Work.ConvR.vsz_int]
      exact hw i (List.mem_range.mp hi))
  simpa [auWts, List.length_range] using h

/-- Size bound on the window of one chunk, from the disc membership of its entries. -/
theorem auWin_vsz_le (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ)
    (hwin : ∀ z ∈ auWin p α s t u k, inDisc p z) :
    vsz (ofList ((auWin p α s t u k).map cfxVal)) ≤ auL p α * (2 * p + 8) + auL p α + 1 := by
  have hg : auWin p α s t u k =
      List.map (fun i => (auExt p α s u).getD (auK s t k + i) (0, 0)) (List.range (auL p α)) :=
    rfl
  have h := vsz_ofList_map_le (l := List.range (auL p α))
    (f := cfxVal ∘ (fun i => (auExt p α s u).getD (auK s t k + i) (0, 0))) (B := 2 * p + 8) (by
      intro i hi
      have hmem : (fun i => (auExt p α s u).getD (auK s t k + i) (0, 0)) i
          ∈ auWin p α s t u k := by
        rw [hg]
        exact List.mem_map.mpr ⟨i, hi, rfl⟩
      have h1 := Work.ConvR.vsz_cfxVal_le (hwin _ hmem)
      simpa [Work.ConvR.cfxSz, Function.comp_apply] using h1)
  rw [hg, List.map_map]
  simpa [List.length_range, Function.comp_apply] using h

/-- Size bound on one chunk: weights plus window, each of length `auL p α`, plus `cons`/`nil`. -/
theorem auChunk_vsz_le (p α s t : ℕ) (u : List (ℤ × ℤ)) {k : ℕ}
    (hwin : ∀ z ∈ auWin p α s t u k, inDisc p z)
    (hw : ∀ i, i < auL p α → isz (auWt p α t (auNsq p α s t k i)) ≤ p + 3) :
    vsz (auChunk p α s t u k) ≤ auL p α * (3 * p + 16) + 4 := by
  have hwt := auWts_vsz_le p α s t k hw
  have hvec := auWin_vsz_le p α s t u k hwin
  rw [show auChunk p α s t u k
      = Val.cons (ofList (auWts p α s t k)) (ofList ((auWin p α s t u k).map cfxVal)) from rfl,
    Work.ConvR.vsz_cons]
  have hL : 0 ≤ auL p α := Nat.zero_le _
  nlinarith [hwt, hvec, hL]

/-- The encoding size of the stream, expanded. -/
theorem vsz_auStreamV_eq (p α s t : ℕ) (u : List (ℤ × ℤ)) :
    vsz (auStreamV p α s t u)
      = (List.map (fun k => vsz (auChunk p α s t u k)) (List.range t)).sum + t + 1 := by
  rw [show auStreamV p α s t u = ofList (auStream p α s t u) from rfl,
    show auStream p α s t u = List.map (fun k => auChunk p α s t u k) (List.range t) from rfl,
    Work.ConvR.vsz_ofList]
  simp [List.map_map, List.length_range, Function.comp_def]

-- Size bounds for the chunks and the stream of Work.Resample.auConvDefs: a chunk
-- cons (ofList weights) (ofList (window.map cfxVal)) has vsz ≤ auL p α * (p+3) + auL p α * (2p+8) + 3,
-- using isz of each weight ≤ p+3 (hypothesis hw) and vsz (cfxVal z) ≤ 2p+8 for z in the disc
-- (Work.ConvR.vsz_cfxVal_le in Submission/Work/ConvR/basic.lean); the stream of t such chunks has
-- vsz ≤ t * (that bound) + t + 1 (Work.ConvR.vsz_ofList).
theorem auStreamSz (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (u : List (ℤ × ℤ)) (hwin : ∀ k, k < t → ∀ z ∈ Work.Resample.auWin p α s t u k, HvdH.inDisc p z)
    (hw : ∀ k i, k < t → i < Work.Resample.auL p α →
      HvdH.isz (Work.Resample.auWt p α t (Work.Resample.auNsq p α s t k i)) ≤ p + 3) :
    (∀ k, k < t → HvdH.vsz (Work.Resample.auChunk p α s t u k) ≤ Work.Resample.auL p α * (3 * p + 16) + 4) ∧
    HvdH.vsz (Work.Resample.auStreamV p α s t u) ≤ t * (Work.Resample.auL p α * (3 * p + 16) + 4) + t + 1 := by
  have hchunk : ∀ k, k < t → vsz (auChunk p α s t u k) ≤ auL p α * (3 * p + 16) + 4 :=
    fun k hk => auChunk_vsz_le p α s t u (hwin k hk) (fun i hi => hw k i hk hi)
  refine ⟨hchunk, ?_⟩
  have hsum : (List.map (fun k => vsz (auChunk p α s t u k)) (List.range t)).sum
      ≤ t * (auL p α * (3 * p + 16) + 4) := by
    calc (List.map (fun k => vsz (auChunk p α s t u k)) (List.range t)).sum
        ≤ (List.map (fun _ => auL p α * (3 * p + 16) + 4) (List.range t)).sum :=
          List.sum_le_sum (fun k hk => hchunk k (List.mem_range.mp hk))
      _ = (List.range t).length * (auL p α * (3 * p + 16) + 4) :=
          Work.ConvR.sum_map_const (List.range t) _
      _ = t * (auL p α * (3 * p + 16) + 4) := by rw [List.length_range]
  rw [vsz_auStreamV_eq]
  omega

end Work.Resample
