import Mathlib
import Submission.Work.Resample.tensorAux

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-!
# Disc preservation for `axisIter`

`axisIter ss ts Φ k es` applies the slice maps `Φ 0, …, Φ (k-1)` along the successive axes of the
flat array `es`.  Each individual axis application `axisList A m n B Φ es` rebuilds its output as
`HvdH.unslices A n B outs`, where every entry of every `outs`-list is either `Φ w j` for a slice
`w` drawn (via `getD`s, hence possibly the default `(0,0)`) from `es`, or a default `(0,0)`.

Consequently, if `Φ` maps vectors of disc elements to vectors of disc elements and every element
of `es` lies in the disc `C̃◦`, then so does every element of the result — the length hypotheses
are not needed, only that `Φ` is disc-preserving and `(0,0)` lies in the disc.
-/

/-- The default fixed-point complex number `(0,0)` lies in the disc. -/
lemma inDisc_default (p : ℕ) : HvdH.inDisc p (default : ℤ × ℤ) := by
  change HvdH.inDisc p ((0,0) : ℤ × ℤ)
  simp [HvdH.inDisc]

/-- `getD` of a list all of whose entries satisfy `P` satisfies `P`, provided the default does. -/
lemma getD_forall {α : Type} {l : List α} {d : α} {P : α → Prop} (hd : P d)
    (hl : ∀ z ∈ l, P z) (i : ℕ) : P (l.getD i d) := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem l d h]
    exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default l d (by omega)]
    exact hd

/-- Every element of a slice of `es` is a `getD` of `es`, hence satisfies `P` if all of `es` does. -/
lemma slices_forall {A m B p : ℕ} {es : List (ℤ × ℤ)} (hes : ∀ z ∈ es, HvdH.inDisc p z) (s : ℕ) :
    ∀ z ∈ (HvdH.slices A m B es).getD s [], HvdH.inDisc p z := by
  refine getD_forall (l := HvdH.slices A m B es) (d := ([] : List (ℤ × ℤ)))
    (P := fun w => ∀ z ∈ w, HvdH.inDisc p z) ?_ ?_ s
  · intro z hz
    simp at hz
  · intro w hw z hz
    simp only [HvdH.slices, List.mem_map] at hw
    obtain ⟨s', -, rfl⟩ := hw
    simp only [List.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact getD_forall (inDisc_default p) hes _

/-- Every element of `HvdH.unslices A n B outs` is a `getD` of some element of `outs`
(hence satisfies `P` if each `outs`-list does), or the default. -/
lemma unslices_forall {A n B : ℕ} (outs : List (List (ℤ × ℤ))) {P : ℤ × ℤ → Prop}
    (h0 : P (default : ℤ × ℤ)) (houts : ∀ w ∈ outs, ∀ z ∈ w, P z) :
    ∀ z ∈ HvdH.unslices A n B outs, P z := by
  intro z hz
  simp only [HvdH.unslices, List.mem_map] at hz
  obtain ⟨idx, -, rfl⟩ := hz
  refine getD_forall h0 ?_ (idx / B % n)
  refine getD_forall (l := outs) (d := ([] : List (ℤ × ℤ))) (P := fun w => ∀ z ∈ w, P z) ?_ houts
    (idx / (n * B) * B + idx % B)
  intro z hz
  simp at hz

/-- One axis application preserves the disc. -/
lemma axisList_disc (A m n B p : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (hΦ : ∀ w : Fin m → ℤ × ℤ, (∀ j, HvdH.inDisc p (w j)) → ∀ j : Fin n, HvdH.inDisc p (Φ w j))
    (es : List (ℤ × ℤ)) (hes : ∀ z ∈ es, HvdH.inDisc p z) :
    ∀ z ∈ axisList A m n B Φ es, HvdH.inDisc p z := by
  show ∀ z ∈ HvdH.unslices A n B ((List.range (A * B)).map fun s =>
    List.ofFn fun j : Fin n => Φ (fun i : Fin m => ((HvdH.slices A m B es).getD s []).getD i (0, 0)) j),
    HvdH.inDisc p z
  refine unslices_forall _ (inDisc_default p) ?_
  intro w hw z hz
  simp only [List.mem_map] at hw
  obtain ⟨s, -, rfl⟩ := hw
  rw [List.mem_ofFn] at hz
  obtain ⟨j, hj⟩ := hz
  rw [← hj]
  exact hΦ _ (fun i => getD_forall (inDisc_default p) (slices_forall (p := p) hes s) i) j

/-- Iterating axis applications preserves the disc (auxiliary form, no `k`-dependent hypotheses
so that the induction on `k` is clean). -/
lemma axisIter_disc_aux (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) (p : ℕ)
    (hΦ : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ j : Fin (ts.getD i 0), HvdH.inDisc p (Φ i w j))
    (es : List (ℤ × ℤ)) (hes : ∀ z ∈ es, HvdH.inDisc p z) :
    ∀ k ≤ ss.length, ∀ z ∈ Work.Resample.axisIter ss ts Φ k es, HvdH.inDisc p z := by
  intro k
  induction k with
  | zero =>
    intro _ z hz
    exact hes z hz
  | succ k ih =>
    intro hk z hz
    have hklt : k < ss.length := by omega
    have hz' : z ∈ axisList ((ts.take k).prod) (ss.getD k 0) (ts.getD k 0) ((ss.drop (k + 1)).prod)
        (Φ k) (axisIter ss ts Φ k es) := hz
    exact axisList_disc ((ts.take k).prod) (ss.getD k 0) (ts.getD k 0) ((ss.drop (k + 1)).prod) p
      (Φ k) (hΦ k hklt) (axisIter ss ts Φ k es) (ih (by omega)) z hz'

theorem axisIter_disc (ss ts : List ℕ) (hl : ts.length = ss.length) (k : ℕ) (hk : k ≤ ss.length) (p : ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (hΦ : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ j : Fin (ts.getD i 0), HvdH.inDisc p (Φ i w j))
    (es : List (ℤ × ℤ)) (hl2 : es.length = (ss.take k).prod * (ss.drop k).prod)
    (hes : ∀ z ∈ es, HvdH.inDisc p z) :
    ∀ z ∈ Work.Resample.axisIter ss ts Φ k es, HvdH.inDisc p z :=
  axisIter_disc_aux ss ts Φ p hΦ es hes k hk

end Work.Resample
