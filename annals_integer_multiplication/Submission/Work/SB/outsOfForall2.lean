import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared

namespace Work.SB

open HvdH
open Work.Layout

/-- `ofList` (the `cons`-chain encoding of a list of values) is injective. -/
private lemma ofList_inj {l₁ l₂ : List Val} (h : ofList l₁ = ofList l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs => simp [ofList] at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ofList] at h
    | cons b bs =>
      simp only [ofList, List.foldr_cons] at h
      injection h with hab htl
      subst hab
      rw [ih htl]

/-- The index-free core of `outsOfForall2`: from a `Forall₂` matching the slices `sls` (encoded as
`sls.map ofList`) against an arbitrary list `ys`, extract the list `outs` of decoding lists. -/
private lemma exists_outs_aux {n : ℕ} (Q : List Val → List Val → Prop)
    (sls : List (List Val)) (ys : List Val)
    (hF : List.Forall₂ (fun x y => ∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧
      ol.length = n ∧ Q sl ol) (sls.map ofList) ys) :
    ∃ outs : List (List Val), ys = outs.map ofList ∧ outs.length = sls.length ∧
      (∀ s, s < sls.length → (outs.getD s []).length = n) ∧
      ∀ s, s < sls.length → Q (sls.getD s []) (outs.getD s []) := by
  induction sls generalizing ys with
  | nil =>
    cases hF with
    | nil =>
      exact ⟨[], rfl, rfl, (by intro s hs; simp at hs), (by intro s hs; simp at hs)⟩
  | cons sl sls ih =>
    cases hF with
    | cons hxy hrest =>
      obtain ⟨sl', ol, hsl, hy, hol, hQ⟩ := hxy
      obtain rfl : sl = sl' := ofList_inj hsl
      obtain ⟨outs, hy', hlen, hlen', hQ'⟩ := ih _ hrest
      refine ⟨ol :: outs, ?_, ?_, ?_, ?_⟩
      · rw [hy, hy']; rfl
      · simp [hlen]
      · intro s hs
        cases s with
        | zero => simp only [List.getD_cons_zero]; exact hol
        | succ s =>
          simp only [List.getD_cons_succ]
          exact hlen' s (by simpa using hs)
      · intro s hs
        cases s with
        | zero => simp only [List.getD_cons_zero]; exact hQ
        | succ s =>
          simp only [List.getD_cons_succ]
          exact hQ' s (by simpa using hs)

theorem outsOfForall2 {A B m n : ℕ} (sls : List (List Val))
    (Q : List Val → List Val → Prop) (xs ys : List Val)
    (hlen : sls.length = A * B) (hsl : ∀ s, s < A * B → (sls.getD s []).length = m)
    (hxs : xs = sls.map ofList)
    (hy : ∀ y ∈ ys, ∃ ol : List Val, y = ofList ol)
    (hF : List.Forall₂ (fun x y => ∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧
      ol.length = n ∧ Q sl ol) xs ys) :
    ∃ outs : List (List Val), ys = outs.map ofList ∧ outs.length = A * B ∧
      (∀ s, s < A * B → (outs.getD s []).length = n) ∧
      ∀ s, s < A * B → Q (sls.getD s []) (outs.getD s []) := by
  rw [hxs] at hF
  obtain ⟨outs, h1, h2, h3, h4⟩ := exists_outs_aux Q sls ys hF
  refine ⟨outs, h1, ?_, ?_, ?_⟩
  · rw [h2, hlen]
  · intro s hs
    exact h3 s (by rw [hlen]; exact hs)
  · intro s hs
    exact h4 s (by rw [hlen]; exact hs)

end Work.SB
