import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.mrgPassDefs
import Submission.Work.ConvR.pwdefs

/-!
# SynFFT: the list/`vsz` kit for the interleave ("merge") pass

`Work.SynFFT.HasMrgPass` (`Submission/Work/SynFFT/hasMrgPass.lean`) is assembled at the
*value-stack* level out of the blocks of `2s` coefficient vectors: it cuts `cvecs ws` into
chunks of `2s` (`LayoutLib.chunksOf`), maps the block word over them (`KLib.mapList`) and
flattens the result.  Its proof reads the list back out of the encoded values, so it needs:

* indexing lemmas for `List.getD` (`drop`/`take` slices, `List.range`-maps, `List.Forall₂`),
* injectivity of `ofList`, `cvecVal` and hence `cvecs`, and the `getD`/`cvecs` interaction,
* the `drop`/`take` description of the `b`-th block `blkVec s ws b`,
* length/membership of `flatten`ed `List.range`-maps,
* the encoding-size bound `vsz (ofList (cvecs ws))` in terms of `p, r` and the length.

Everything is collected in the single lemma `mrgPassListKit` so that the pass assembly can
pick the conjunct it needs.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Generic list indexing -/

/-- Reading a `drop`-then-`take` slice at an index inside the taken length. -/
theorem getD_drop_take' {α : Type} (l : List α) (d : α) (a n q : ℕ) (hq : q < n) :
    ((l.drop a).take n).getD q d = l.getD (a + q) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hq,
    List.getElem?_drop]

/-- The `j`-th entry of `(List.range n).map f`, for `j < n`, is `f j`. -/
theorem getD_map_range' {α : Type} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

/-- `List.Forall₂` is inherited by `getD` when the two lists have the same length. -/
theorem forall₂_getD' {R : HvdH.Val → HvdH.Val → Prop} {l₁ l₂ : List HvdH.Val}
    (hl : l₁.length = l₂.length) (hR : List.Forall₂ R l₁ l₂) (d₁ d₂ : HvdH.Val) (i : ℕ)
    (hi : i < l₁.length) : R (l₁.getD i d₁) (l₂.getD i d₂) := by
  have h2 : i < l₂.length := hl ▸ hi
  rw [List.getD_eq_getElem l₁ d₁ hi, List.getD_eq_getElem l₂ d₂ h2]
  exact hR.get hi h2

/-! ## Flattening blocks -/

/-- An element of the flattening of the `List.range B`-map of `V` lies in some `V b`, `b < B`. -/
theorem mem_flatten_map_range' {B : ℕ} {V : ℕ → List (List (ℤ × ℤ))} {w : List (ℤ × ℤ)}
    (h : w ∈ ((List.range B).map V).flatten) : ∃ b, b < B ∧ w ∈ V b := by
  rw [List.mem_flatten] at h
  obtain ⟨l, hl, hw⟩ := h
  rw [List.mem_map] at hl
  obtain ⟨b, hb, rfl⟩ := hl
  exact ⟨b, List.mem_range.mp hb, hw⟩

/-- The flattening of `B` blocks of `2s` vectors has `B * (2s)` entries. -/
theorem length_flatten_map_range' {B s : ℕ} {V : ℕ → List (List (ℤ × ℤ))}
    (hV : ∀ b, b < B → (V b).length = 2 * s) :
    (((List.range B).map V).flatten).length = B * (2 * s) := by
  rw [List.length_flatten, List.map_map]
  have hmap : (List.range B).map (List.length ∘ V) = (List.range B).map (fun _ => 2 * s) := by
    apply List.map_congr_left
    intro b hb
    exact hV b (List.mem_range.mp hb)
  rw [hmap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-! ## `cvecs` and `blkVec` -/

/-- Reading the `i`-th encoded vector of `cvecs l`, also past the end. -/
theorem cvecs_getD_kit (l : List (List (ℤ × ℤ))) (i : ℕ) :
    (cvecs l).getD i HvdH.Val.nil = HvdH.cvecVal (l.getD i []) := by
  by_cases h : i < l.length
  · exact Work.ConvR.cvecVal_getD h
  · have h' : l.length ≤ i := Nat.le_of_not_lt h
    have h1 : (cvecs l).length ≤ i := by simpa [cvecs] using h'
    rw [List.getD_eq_default (cvecs l) HvdH.Val.nil h1, List.getD_eq_default l [] h']
    rfl

/-- `cvecs` of the `b`-th block of `2s` vectors is the corresponding slice of `cvecs ws`. -/
theorem cvecs_drop_take_kit (s : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ) :
    ((cvecs ws).drop (b * (2 * s))).take (2 * s) = cvecs (blkVec s ws b) := by
  simp only [cvecs, blkVec, List.map_take, List.map_drop]

/-- Reading the `q`-th vector of the `b`-th block. -/
theorem blkVec_getD_kit (s : ℕ) (ws : List (List (ℤ × ℤ))) (b q : ℕ) (hq : q < 2 * s) :
    (blkVec s ws b).getD q [] = ws.getD (b * (2 * s) + q) [] := by
  simp only [blkVec]
  exact getD_drop_take' ws [] (b * (2 * s)) (2 * s) q hq

/-! ## Encoding size of a list of coefficient vectors -/

/-- The encoding size of `ofList (cvecs ws)` is bounded by the number of vectors times the
per-vector bound `13 (r+1) (p+1)`, plus the `cons` overhead. -/
theorem vsz_ofList_cvecs_le_kit (p r t : ℕ) (ws : List (List (ℤ × ℤ)))
    (hlen : ws.length = t) (hIn : ∀ w ∈ ws, InDiscVec p r w) :
    HvdH.vsz (HvdH.ofList (cvecs ws)) ≤ t * (13 * (r + 1) * (p + 1) + 1) + 1 := by
  refine MrgKit.vsz_ofList_le_of_bound (cvecs ws) (13 * (r + 1) * (p + 1)) t ?_ ?_
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact MrgKit.vsz_cvecVal_le p r w (hIn w hw).1 (hIn w hw).2
  · simp only [cvecs, List.length_map, hlen]
    exact le_rfl

/-! ## The kit -/

theorem mrgPassListKit :
    (∀ {α : Type} (l : List α) (d : α) (a n q : ℕ), q < n →
        ((l.drop a).take n).getD q d = l.getD (a + q) d) ∧
    (∀ (f : ℕ → HvdH.Val) (d : HvdH.Val) (n i : ℕ), i < n →
        ((List.range n).map f).getD i d = f i) ∧
    (∀ (l₁ l₂ : List HvdH.Val), HvdH.ofList l₁ = HvdH.ofList l₂ → l₁ = l₂) ∧
    (∀ (l₁ l₂ : List (List (ℤ × ℤ))), Work.SynFFT.cvecs l₁ = Work.SynFFT.cvecs l₂ → l₁ = l₂) ∧
    (∀ (l : List (List (ℤ × ℤ))) (i : ℕ),
        (Work.SynFFT.cvecs l).getD i HvdH.Val.nil = HvdH.cvecVal (l.getD i [])) ∧
    (∀ (R : HvdH.Val → HvdH.Val → Prop) (l₁ l₂ : List HvdH.Val), l₁.length = l₂.length →
        List.Forall₂ R l₁ l₂ → ∀ (d₁ d₂ : HvdH.Val) (i : ℕ), i < l₁.length →
          R (l₁.getD i d₁) (l₂.getD i d₂)) ∧
    (∀ (s : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ),
        ((Work.SynFFT.cvecs ws).drop (b * (2 * s))).take (2 * s)
          = Work.SynFFT.cvecs (Work.SynFFT.blkVec s ws b)) ∧
    (∀ (s : ℕ) (ws : List (List (ℤ × ℤ))) (b q : ℕ), q < 2 * s →
        (Work.SynFFT.blkVec s ws b).getD q [] = ws.getD (b * (2 * s) + q) []) ∧
    (∀ (B : ℕ) (V : ℕ → List (List (ℤ × ℤ))) (w : List (ℤ × ℤ)),
        w ∈ ((List.range B).map V).flatten → ∃ b, b < B ∧ w ∈ V b) ∧
    (∀ (B s : ℕ) (V : ℕ → List (List (ℤ × ℤ))), (∀ b, b < B → (V b).length = 2 * s) →
        (((List.range B).map V).flatten).length = B * (2 * s)) ∧
    (∀ (p r s : ℕ) (v : List (List (ℤ × ℤ))), v.length = 2 * s →
        (∀ w ∈ v, HvdH.InDiscVec p r w) →
        HvdH.vsz (HvdH.ofList (Work.SynFFT.cvecs v)) ≤ 2 * s * (13 * (r + 1) * (p + 1) + 1) + 1) ∧
    (∀ (p r t : ℕ) (ws : List (List (ℤ × ℤ))), ws.length = t →
        (∀ w ∈ ws, HvdH.InDiscVec p r w) →
        HvdH.vsz (HvdH.ofList (Work.SynFFT.cvecs ws)) ≤ t * (13 * (r + 1) * (p + 1) + 1) + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α l d a n q hq
    exact getD_drop_take' l d a n q hq
  · intro f d n i hi
    exact getD_map_range' f d hi
  · intro l₁ l₂ h
    exact Work.ConvR.ofList_injective h
  · intro l₁ l₂ h
    exact List.map_injective_iff.mpr Work.ConvR.cvecVal_injective h
  · intro l i
    exact cvecs_getD_kit l i
  · intro R l₁ l₂ hl hR d₁ d₂ i hi
    exact forall₂_getD' hl hR d₁ d₂ i hi
  · intro s ws b
    exact cvecs_drop_take_kit s ws b
  · intro s ws b q hq
    exact blkVec_getD_kit s ws b q hq
  · intro B V w h
    exact mem_flatten_map_range' h
  · intro B s V hV
    exact length_flatten_map_range' hV
  · intro p r s v hv hIn
    exact vsz_ofList_cvecs_le_kit p r (2 * s) v hv hIn
  · intro p r t ws hlen hIn
    exact vsz_ofList_cvecs_le_kit p r t ws hlen hIn

end Work.SynFFT
