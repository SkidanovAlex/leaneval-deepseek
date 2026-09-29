import Mathlib
import Submission.Work.SB.P3b.Base

namespace Work.SB.P3b

/-- Length of the flattening of a family of blocks which all have length `n`. -/
lemma length_flatten_eq {n : ℕ} {outs : List (List HvdH.Val)}
    (hsl : ∀ s, s < outs.length → (outs.getD s []).length = n) :
    outs.flatten.length = outs.length * n := by
  induction outs with
  | nil => simp
  | cons a t ih =>
    have ha : a.length = n := by
      simpa using hsl 0 (by simp)
    have ht : t.flatten.length = t.length * n := by
      refine ih ?_
      intro s hs
      have := hsl (s + 1) (by simp; omega)
      simpa using this
    rw [List.flatten_cons, List.length_append, ha, ht, List.length_cons]
    ring

/-- Every element of the flattening of a family of equal-length blocks of bounded values is
bounded by `L`. -/
lemma vsz_le_of_mem_flatten {L n : ℕ} {outs : List (List HvdH.Val)}
    (hsl : ∀ s, s < outs.length → (outs.getD s []).length = n)
    (hsz : ∀ s, s < outs.length → ∀ y ∈ outs.getD s [], HvdH.vsz y ≤ L) :
    ∀ y ∈ outs.flatten, HvdH.vsz y ≤ L := by
  induction outs with
  | nil => intro y hy; simp at hy
  | cons a t ih =>
    intro y hy
    rw [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · have ha : ∀ y ∈ a, HvdH.vsz y ≤ L := by
        simpa using hsz 0 (by simp)
      exact ha y hy
    · refine ih ?_ ?_ y hy
      · intro s hs
        have := hsl (s + 1) (by simp; omega)
        simpa using this
      · intro s hs
        have := hsz (s + 1) (by simp; omega)
        simpa using this

theorem flatGetD (A n B L : ℕ) (outs : List (List HvdH.Val)) (hlen : outs.length = A * B)
    (hsl : ∀ s, s < A * B → (outs.getD s []).length = n)
    (hsz : ∀ s, s < A * B → ∀ y ∈ outs.getD s [], HvdH.vsz y ≤ L) :
    ∀ i, i < A * B * n → HvdH.vsz ((outs.flatten).getD i .nil) ≤ L := by
  intro i hi
  have hsl' : ∀ s, s < outs.length → (outs.getD s []).length = n :=
    fun s hs => hsl s (hlen ▸ hs)
  have hsz' : ∀ s, s < outs.length → ∀ y ∈ outs.getD s [], HvdH.vsz y ≤ L :=
    fun s hs => hsz s (hlen ▸ hs)
  have hlen_flat : outs.flatten.length = A * B * n := by
    rw [length_flatten_eq hsl', hlen]
  have hlt : i < outs.flatten.length := by rw [hlen_flat]; exact hi
  rw [List.getD_eq_getElem (outs.flatten) HvdH.Val.nil hlt]
  exact vsz_le_of_mem_flatten hsl' hsz' _ (List.getElem_mem hlt)

end Work.SB.P3b
