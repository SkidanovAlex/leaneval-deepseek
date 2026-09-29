import Mathlib
import Submission.Work.ConvR.permDefs
import Submission.Work.ConvR.foldRoll_posList
import Submission.Work.ConvR.posList_lt

/-!
# `Work.ConvR.permTop` — reorder a value stack by a permutation

Given `σ.Perm (List.range n)` and a stack `head ++ tail` with `head.length = n`, there is a
straight-line `KernelLib` program (a `roll` at each position of `posList σ.reverse`) which turns
the stack into `σ.map (fun i => head.getD i .nil) ++ tail`, at cost
`K * (n+1) * (n+1) * ((head.map vsz).sum + 1)`.

The program processes the indices of `t := σ.reverse` in order, rolling each to the front; after
step `j` the front holds the moved elements (most recent first) and the untouched remainder of
`head` follows in its original order, so the final front is `σ` and `tail` is unchanged.  The two
purely combinatorial facts are proved in `foldRoll_posList.lean` (`foldRoll_posList`) and
`posList_lt.lean` (`posList_lt`); here we assemble them with the `WordR` calculus of `KernelLib`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Elementary facts about `rollL` -/

theorem getD_append_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).getD k .nil = l.getD k .nil := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, List.cons_append, List.getD_cons_succ]
      exact ih (by simpa using h)

theorem eraseIdx_append_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).eraseIdx k = l.eraseIdx k ++ rest := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      rw [List.cons_append, List.eraseIdx_cons_succ, ih (by simpa using h),
        List.eraseIdx_cons_succ, List.cons_append]

theorem rollL_length {p : ℕ} {W : List Val} (h : p < W.length) :
    (rollL p W).length = W.length := by
  have hp : rollL p W = W[p] :: W.eraseIdx p := by
    rw [rollL, List.getD_eq_getElem W .nil h]
  rw [hp]
  exact (List.getElem_cons_eraseIdx_perm h).length_eq

theorem rollL_append {p : ℕ} {W rest : List Val} (h : p < W.length) :
    rollL p (W ++ rest) = rollL p W ++ rest := by
  rw [rollL, rollL, getD_append_lt h, eraseIdx_append_lt h, List.cons_append]

/-- `rollL` does not change the total encoding size of the window. -/
theorem rollL_szl {p : ℕ} {W : List Val} (h : p < W.length) :
    ((rollL p W).map vsz).sum = (W.map vsz).sum := by
  have hp : rollL p W = W[p] :: W.eraseIdx p := by
    rw [rollL, List.getD_eq_getElem W .nil h]
  rw [hp]
  have hperm : (W[p] :: W.eraseIdx p).Perm W := List.getElem_cons_eraseIdx_perm h
  have hh := List.Perm.sum_eq (hperm.map vsz)
  simpa using hh

theorem szl_take_le (l : List Val) (k : ℕ) :
    ((l.take k).map vsz).sum ≤ (l.map vsz).sum := by
  have h := List.take_append_drop k l
  calc ((l.take k).map vsz).sum
      ≤ ((l.take k).map vsz).sum + ((l.drop k).map vsz).sum := Nat.le_add_right _ _
    _ = ((l.take k ++ l.drop k).map vsz).sum := by rw [List.map_append, List.sum_append]
    _ = (l.map vsz).sum := by rw [h]

/-- `foldRoll` acts on the window `W` and leaves the tail `rest` alone. -/
theorem foldRoll_append {ps : List ℕ} {W rest : List Val} (h : ∀ p ∈ ps, p < W.length) :
    foldRoll ps (W ++ rest) = foldRoll ps W ++ rest := by
  induction ps generalizing W with
  | nil => rfl
  | cons p ps ih =>
    have hp : p < W.length := h p (by simp)
    have e1 : foldRoll (p :: ps) (W ++ rest) = foldRoll ps (rollL p (W ++ rest)) := rfl
    have e2 : foldRoll (p :: ps) W = foldRoll ps (rollL p W) := rfl
    rw [e1, e2, rollL_append hp]
    exact ih (fun q hq => by have hqh := h q (by simp [hq]); rw [rollL_length hp]; exact hqh)

/-! ## The `WordR` calculus for a sequence of rolls -/

/-- Executing `roll` at the positions `ps` on a window `W` (with `rest` untouched) realises
`foldRoll ps W` on the window, at cost `|ps| * Kr * |W| * (Σ W + 1) + 1`. -/
theorem rollList_spec (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
        (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
        (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))) :
    ∀ (ps : List ℕ) (W rest : List Val), (∀ p ∈ ps, p < W.length) →
      WordR main (rollList rollP ps) (fun vs => vs = W ++ rest)
        (fun _ out => out = foldRoll ps W ++ rest)
        (fun _ => ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1) := by
  intro ps
  induction ps with
  | nil =>
    intro W rest _
    refine hK.conseq (main := main) (p := .skip) (P := fun _ => True)
      (Q := fun vs out => out = vs) (C := fun _ => 1)
      (P' := fun vs => vs = W ++ rest) (Q' := fun _ out => out = W ++ rest)
      (C' := fun _ => ([] : List ℕ).length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1)
      (hK.skip main) ?_ ?_ ?_
    · intro vs _; trivial
    · intro vs out hv hQ; rw [hQ, hv]
    · intro vs _; simp
  | cons p ps ih =>
    intro W rest hvalid
    have hp : p < W.length := hvalid p (by simp)
    have hvalid' : ∀ q ∈ ps, q < (rollL p W).length := by
      intro q hq; rw [rollL_length hp]; exact hvalid q (by simp [hq])
    have h1 : WordR main (rollP p) (fun vs => vs = W ++ rest)
        (fun vs out => out = rollL p vs)
        (fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1)) := by
      refine hK.conseq (main := main) (p := rollP p) (P := fun vs => p < vs.length)
        (Q := fun vs out => out = vs.getD p .nil :: vs.eraseIdx p)
        (C := fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1))
        (P' := fun vs => vs = W ++ rest) (Q' := fun vs out => out = rollL p vs)
        (C' := fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1))
        (hroll p) ?_ ?_ ?_
      · intro vs hv
        rw [hv, List.length_append]
        exact lt_of_lt_of_le hp (Nat.le_add_right _ _)
      · intro vs out hv hQ; rw [hQ]; rfl
      · intro vs _; exact le_rfl
    have h2 := ih (rollL p W) rest hvalid'
    have hseq : WordR main (.seq (rollP p) (rollList rollP ps))
        (fun vs => vs = W ++ rest)
        (fun vs out => ∃ mid, mid = rollL p vs ∧ out = foldRoll ps (rollL p W) ++ rest)
        (fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1)
          + (ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1)) :=
      hK.seq (main := main) (p := rollP p) (q := rollList rollP ps)
        (P := fun vs => vs = W ++ rest) (Q := fun vs out => out = rollL p vs)
        (C := fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1))
        (P' := fun mid => mid = rollL p W ++ rest)
        (Q' := fun _ out => out = foldRoll ps (rollL p W) ++ rest)
        (C' := fun _ => ps.length * (Kr * (rollL p W).length * (((rollL p W).map vsz).sum + 1)) + 1)
        (B := fun _ => ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1)
        h1 h2 (by
          intro vs mid hv hmid
          refine ⟨?_, ?_⟩
          · rw [hmid, hv, rollL_append hp]
          · rw [rollL_length hp, rollL_szl hp])
    refine hK.conseq (main := main) (p := .seq (rollP p) (rollList rollP ps))
      (P := fun vs => vs = W ++ rest) (P' := fun vs => vs = W ++ rest)
      (Q := fun vs out => ∃ mid, mid = rollL p vs ∧ out = foldRoll ps (rollL p W) ++ rest)
      (Q' := fun _ out => out = foldRoll (p :: ps) W ++ rest)
      (C := fun vs => Kr * (p + 1) * (((vs.take (p + 1)).map vsz).sum + 1)
          + (ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1))
      (C' := fun _ => (p :: ps).length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1)
      hseq ?_ ?_ ?_
    · intro vs hv; exact hv
    · intro vs out hv hQ
      rcases hQ with ⟨mid, hmid, hout⟩
      rw [hout]; rfl
    · intro vs hv
      rw [hv, List.take_append_of_le_length (Nat.succ_le_of_lt hp)]
      have hA : Kr * (p + 1) * (((W.take (p + 1)).map vsz).sum + 1)
          ≤ Kr * W.length * (((W.map vsz).sum) + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl Kr) (Nat.succ_le_of_lt hp))
          (Nat.add_le_add_right (szl_take_le W (p + 1)) 1)
      calc Kr * (p + 1) * (((W.take (p + 1)).map vsz).sum + 1)
            + (ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1)
          ≤ Kr * W.length * (((W.map vsz).sum) + 1)
            + (ps.length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1) :=
            Nat.add_le_add_right hA _
        _ = (p :: ps).length * (Kr * W.length * (((W.map vsz).sum) + 1)) + 1 := by
            rw [List.length_cons]; ring

/-- Cost arithmetic of `permTop`: only the constant `Kr + 1` is needed. -/
theorem cost_le (Kr n s : ℕ) :
    n * (Kr * n * (s + 1)) + 1 ≤ (Kr + 1) * (n + 1) * (n + 1) * (s + 1) := by
  have hnn : n * n ≤ (n + 1) * (n + 1) := Nat.mul_self_le_mul_self (Nat.le_succ n)
  have h1 : Kr * (n * n) * (s + 1) ≤ Kr * ((n + 1) * (n + 1)) * (s + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left Kr hnn) (le_refl (s + 1))
  have h2 : n * (Kr * n * (s + 1)) = Kr * (n * n) * (s + 1) := by ring
  have h3 : 1 ≤ ((n + 1) * (n + 1)) * (s + 1) := Nat.succ_le_of_lt (by positivity)
  calc n * (Kr * n * (s + 1)) + 1
      = Kr * (n * n) * (s + 1) + 1 := by rw [h2]
    _ ≤ Kr * ((n + 1) * (n + 1)) * (s + 1) + ((n + 1) * (n + 1)) * (s + 1) :=
        Nat.add_le_add h1 h3
    _ = (Kr + 1) * (n + 1) * (n + 1) * (s + 1) := by ring

/-! ## The target -/

theorem permTop (hK : HvdH.KernelLib) :
    ∃ (prog : List ℕ → HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (n : ℕ) (σ : List ℕ)
      (head tail : List HvdH.Val),
      head.length = n → σ.length = n → σ.Perm (List.range n) →
      HvdH.WordR main (prog σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i HvdH.Val.nil) ++ tail)
        (fun _ => K * (n + 1) * (n + 1) * (((head.map HvdH.vsz).sum) + 1)) := by
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  refine ⟨fun σ => rollList rollP (posList σ.reverse), Kr + 1, ?_⟩
  intro main n σ head tail hhead hσlen hperm
  have hvalid : ∀ p ∈ posList σ.reverse, p < head.length := by
    rw [hhead]; exact posList_lt σ n hσlen hperm
  have hspec := rollList_spec hK (hroll main) (posList σ.reverse) head tail hvalid
  have hlen : (posList σ.reverse).length = n := by
    rw [posList]; simp [hσlen]
  refine hK.conseq (main := main) (p := rollList rollP (posList σ.reverse))
    (P := fun vs => vs = head ++ tail) (P' := fun vs => vs = head ++ tail)
    (Q := fun _ out => out = foldRoll (posList σ.reverse) head ++ tail)
    (Q' := fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
    (C := fun _ => (posList σ.reverse).length * (Kr * head.length * (((head.map vsz).sum) + 1)) + 1)
    (C' := fun _ => (Kr + 1) * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1))
    hspec ?_ ?_ ?_
  · intro vs hv; exact hv
  · intro vs out hv hQ
    rw [hQ, ← foldRoll_append hvalid]
    exact foldRoll_posList head tail σ n hhead hσlen hperm
  · intro vs hv
    rw [hlen, hhead]
    exact cost_le Kr n ((head.map vsz).sum)

end Work.ConvR
