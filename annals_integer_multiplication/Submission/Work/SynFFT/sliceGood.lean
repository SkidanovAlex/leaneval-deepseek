import Mathlib
import Submission.Work.SynFFT.axisStepDefs

namespace Work.SynFFT

open HvdH

/-- `List.Forall₂` read at an index, in `getD` form: the two defaults are irrelevant as long as
the index is in range. -/
theorem forall₂_getD_xsliceGood {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    {d₁ : α} {d₂ : β} (h : List.Forall₂ R l₁ l₂) {i : ℕ} (hi : i < l₁.length) :
    R (l₁.getD i d₁) (l₂.getD i d₂) := by
  induction h generalizing i with
  | nil => simp at hi
  | cons ha _ ih =>
      cases i with
      | zero => simpa using ha
      | succ j => simpa using ih (by simpa using hi)

/-- **The slice word applied to every slice.**  Reading `ys` (the result of `mapList`ing the
slice word over the `A*B` chunks of the gathered array) at an index `s` recovers the slice `s`
after the transform: it is the encoding of a slice `vs'` of `SlOK` shape whose approximation
theorem holds with the error budget raised by `k`.

The mathematical content is the transport of the per-element predicate `SlPost` of `hF` along
the identification `hchunk` of the `s`-th chunk with the `s`-th slice, using injectivity of
`ofList` and of `cvecs` to replace the abstract `vs` of `SlPost` by the concrete slice, so that
the hypothesis `hsl` (the approximation of the slice by the input array `u`) can be fed in. -/
theorem sliceGood {A t B p r k : ℕ} {sgn : ℤ} {e : ℝ} {u : Work.SynFFT.Arr r}
    (ws : List (List (ℤ × ℤ))) (hws : ws.length = A * t * B)
    (hsl : ∀ s < A * B, Work.SynFFT.ApproxSL p r t (Work.SynFFT.sliceVal A t B ws s)
      (fun j c => u ((s / B * t + j) * B + s % B) c) e)
    (hchunk : ∀ s < A * B, Work.SynFFT.cvecs (Work.SynFFT.sliceVal A t B ws s) =
      ((List.flatten (HvdH.slices A t B (Work.SynFFT.cvecs ws))).drop (s * t)).take t)
    (ys : List HvdH.Val)
    (hF : List.Forall₂ (Work.SynFFT.SlPost p r t k sgn e)
      ((List.range (A * B)).map (fun s => HvdH.ofList
        (((List.flatten (HvdH.slices A t B (Work.SynFFT.cvecs ws))).drop (s * t)).take t))) ys) :
    ∀ s < A * B, ∃ vs' : List (List (ℤ × ℤ)),
      ys.getD s HvdH.Val.nil = HvdH.ofList (Work.SynFFT.cvecs vs') ∧
      Work.SynFFT.SlOK p r t vs' ∧
      Work.SynFFT.ApproxSL p r t vs'
        (fun q => Work.SynFFT.dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q)
        (e + k) := by
  have _ : ws.length = A * t * B := hws
  intro s hs
  -- the list of chunks over which the slice word is mapped has length `A * B`
  have hbig : ((List.range (A * B)).map (fun s => HvdH.ofList
      (((List.flatten (HvdH.slices A t B (Work.SynFFT.cvecs ws))).drop (s * t)).take t))).length
      = A * B := by simp
  -- the `s`-th entries of the two lists of `hF` are related
  have hpost := forall₂_getD_xsliceGood (d₁ := HvdH.Val.nil) (d₂ := HvdH.Val.nil) (h := hF) (i := s)
    (hi := by rw [hbig]; exact hs)
  -- ... and the `s`-th chunk of the gathered array is the encoding of the `s`-th slice
  have hgd : ((List.range (A * B)).map (fun s => HvdH.ofList
      (((List.flatten (HvdH.slices A t B (Work.SynFFT.cvecs ws))).drop (s * t)).take t))).getD s
        HvdH.Val.nil
      = HvdH.ofList (Work.SynFFT.cvecs (Work.SynFFT.sliceVal A t B ws s)) := by
    rw [getD_map_range _ _ hs, ← hchunk s hs]
  rw [hgd] at hpost
  unfold SlPost at hpost
  obtain ⟨vs, vs', hx, hy', h1, h2, htr⟩ := hpost
  -- `vs` is the slice itself, so `hsl` applies
  have hvs : vs = sliceVal A t B ws s := (cvecsInj (ofList_inj' hx)).symm
  refine ⟨vs', hy', h2, ?_⟩
  have hA : ApproxSL p r t vs (fun j c => u ((s / B * t + j) * B + s % B) c) e := by
    rw [hvs]; exact hsl s hs
  exact htr _ hA

end Work.SynFFT
