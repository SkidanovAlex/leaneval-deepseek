import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs

namespace Work.EQ.FanTri

open Work.EQ

/-- Splitting `asm a σ` at the `i`-th *gap*: the prefix `true^{a₀}σ₀…σ_{i-1}`, the gap
`true^{a_i}`, and the rest.  Stated with `getD` so that the index is not dependent. -/
lemma asm_split_aux (i : ℕ) (a : List ℕ) (σ : List (List Bool))
    (hlen : a.length = σ.length + 1) (hi : i ≤ σ.length) :
    asm a σ = asm (a.take i ++ [0]) (σ.take i)
      ++ List.replicate (a.getD i 0) true
      ++ asm (0 :: a.drop (i + 1)) (σ.drop i) := by
  induction i generalizing a σ with
  | zero =>
    cases a with
    | nil => simp at hlen
    | cons g gs =>
      cases σ with
      | nil => simp [asm]
      | cons t ts => simp [asm, List.append_assoc]
  | succ k ih =>
    cases a with
    | nil => simp at hlen
    | cons g gs =>
      cases σ with
      | nil => simp at hi
      | cons t ts =>
        have hlen' : gs.length = ts.length + 1 := by simp at hlen ⊢; omega
        have hk : k ≤ ts.length := by simp at hi; omega
        simp only [List.take_succ_cons, List.drop_succ_cons, List.getD_cons_succ]
        simp only [asm]
        rw [ih gs ts hlen' hk]
        simp [asm, List.append_assoc]

theorem asm_split (a : List ℕ) (σ : List (List Bool)) (i : ℕ)
    (hlen : a.length = σ.length + 1) (hi : i < a.length) :
    Work.EQ.FanTri.asm a σ = Work.EQ.FanTri.asm (a.take i ++ [0]) (σ.take i)
      ++ List.replicate (a.get ⟨i, hi⟩) true
      ++ Work.EQ.FanTri.asm (0 :: a.drop (i + 1)) (σ.drop i) := by
  have hi' : i ≤ σ.length := by omega
  rw [asm_split_aux i a σ hlen hi']
  have h : List.replicate (a.getD i 0) true = List.replicate (a.get ⟨i, hi⟩) true := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [h]

end Work.EQ.FanTri
