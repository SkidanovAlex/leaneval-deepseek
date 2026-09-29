import Mathlib
import Submission.Work.SynFFT.axisStepDefs
import Submission.Work.SynFFT.axisApproxSLScat
import Submission.Work.SynFFT.axisScatInDisc

/-!
# `axisFinalScat`: assembling the axis step from its two halves

`Work.SynFFT.scatList A t B W` is the flat `A × t × B` array `W` read block by block through the
scattered index map `i ↦ (i / (t*B) * B + i % B) * t + i / B % t` (the inverse of the transpose
applied by the axis word).  Given a list `Vs` of `A*B` slices, each of length `t` and in the disc,
each approximating the synthetic transform of the corresponding restriction of `u`:

* `Vs.flatten` is the flat array of length `A*B*t` that the axis word consumes;
* `axisScatInDisc` gives that the scattered read of `Vs.flatten` stays in the disc;
* `axisApproxSLScat` gives that the scattered read approximates `axisT r t B sgn u`, provided
  every position `s*t + j` of `Vs.flatten` (with `s < A*B`, `j < t`) satisfies the pointwise
  bound.  That pointwise bound is exactly `ApproxSL` of the `s`-th slice, read off through
  `getD_flatten_eq` (the `(s*t+j)`-th entry of `Vs.flatten` is the `j`-th entry of the `s`-th
  slice).

The only new list plumbing needed is that all members of `Vs` have length `t` (they are the
`getD`s at positions `< A*B`, by `hVt`) and consequently `Vs.flatten.length = A*B*t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- If every `getD` of `L` at a position `< N` has length `t`, then every member of `L` has
length `t` (using `L.length = N` to know that every member occurs at such a position). -/
theorem allLen_of_getD {α : Type*} (L : List (List α)) (N t : ℕ) (hN : L.length = N)
    (h : ∀ s, s < N → (L.getD s []).length = t) : ∀ l ∈ L, l.length = t := by
  intro l hl
  obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp hl
  have his : i < N := by rw [← hN]; exact hi
  have hd := h i his
  rw [List.getD_eq_getElem _ [] hi] at hd
  rw [hli] at hd
  exact hd

/-- The flatten of a list of lists of common length `k` has length `L.length * k`. -/
theorem flattenLen_allLen {α : Type*} (L : List (List α)) (k : ℕ)
    (h : ∀ l ∈ L, l.length = k) : L.flatten.length = L.length * k := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [List.flatten_cons, List.length_append,
      ih (fun x hx => h x (List.mem_cons_of_mem l hx)),
      h l (List.mem_cons_self), List.length_cons]
    ring

theorem axisFinalScat (p r A t B : ℕ) (sgn : ℤ) (u : Work.SynFFT.Arr r) (E : ℝ)
    (Vs : List (List (List (ℤ × ℤ)))) (hVlen : Vs.length = A * B)
    (hVt : ∀ s, s < A * B → (Vs.getD s []).length = t)
    (hID : ∀ w ∈ Vs.flatten, HvdH.InDiscVec p r w)
    (hper : ∀ s < A * B, Work.SynFFT.ApproxSL p r t (Vs.getD s [])
        (fun q => Work.SynFFT.dftN r t sgn (fun j c => u ((s / B * t + j) * B + s % B) c) q) E) :
    (Work.SynFFT.scatList A t B Vs.flatten).length = A * t * B ∧
      (∀ w ∈ Work.SynFFT.scatList A t B Vs.flatten, HvdH.InDiscVec p r w) ∧
      Work.SynFFT.ApproxSL p r (A * t * B) (Work.SynFFT.scatList A t B Vs.flatten)
        (Work.SynFFT.axisT r t B sgn u) E := by
  -- every slice of `Vs` has length `t`, hence `Vs.flatten` has length `A*B*t`
  have hmemlen : ∀ l ∈ Vs, l.length = t := allLen_of_getD Vs (A * B) t hVlen hVt
  have hflatlen : Vs.flatten.length = A * B * t := by
    rw [flattenLen_allLen Vs t hmemlen, hVlen]
  refine ⟨scatList_length A t B Vs.flatten, ?_, ?_⟩
  · -- the scattered read stays in the disc
    simpa [scatList] using axisScatInDisc p r A t B Vs.flatten hflatlen hID
  · -- the scattered read approximates the axis transform
    refine axisApproxSLScat p r A t B sgn u E Vs.flatten (scatList A t B Vs.flatten)
      hflatlen rfl ?_
    intro s hs j hj c
    -- the `(s*t+j)`-th entry of `Vs.flatten` is the `j`-th entry of the `s`-th slice
    have hper' := (hper s hs).2 j hj c
    have hg := getD_flatten_eq Vs ([] : List (ℤ × ℤ)) hmemlen s j hj
    rw [hg]
    simpa using hper'

end Work.SynFFT
