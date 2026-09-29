import Mathlib
import Submission.Work.SB.Core.Kw1StageDefs

namespace Work.SB.Core

open HvdH

/-!
# `kw1Forall2`: the per-element relation determines the output list

The per-element word of the first labelling stage sees `cons (int i) v` and returns
`cons (int (keyIdx1 m B i)) v` (`Work.SB.Core.kw1Q`).  `mapList` therefore produces an output
list `ys` related elementwise to the input list `kw1In A m B es`; this file shows that such a
`ys` is *uniquely determined* and equals `kw1Out A m B es`.

The key point is injectivity of `Val.cons` and `Val.int`: the relation `kw1Q x y` supplies a
decomposition `x = cons (int i) v`, but `x` already determines both `i` (its head) and `v` (its
tail), so `y` is forced to be the relabelled `x`.  This is captured by the auxiliary function
`relab`, which rewrites the head label of a `cons` value.
-/

/-- Relabel the head of a `cons` value: `cons (int i) v ↦ cons (int (f i)) v`; other values are
unchanged. -/
def relab (f : ℕ → ℕ) : Val → Val
  | Val.cons (Val.int (Int.ofNat i)) b => Val.cons (Val.int ((f i : ℕ) : ℤ)) b
  | x => x

@[simp] lemma relab_cons (f : ℕ → ℕ) (i : ℕ) (b : Val) :
    relab f (Val.cons (Val.int ((i : ℕ) : ℤ)) b) = Val.cons (Val.int ((f i : ℕ) : ℤ)) b := rfl

/-- A `Forall₂` relation of the form `y = g x` determines `ys` as `xs.map g`. -/
lemma eq_map_of_forall2 {α β : Type*} {g : α → β} {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun x y => y = g x) xs ys) : ys = xs.map g := by
  induction h with
  | nil => rfl
  | cons hy _ ih => simp [hy, ih]

/-- Generic form of `kw1Forall2`: elementwise relation of the `kw1Q`-shape between the
labelled input list and `ys` forces `ys` to be the relabelled list. -/
lemma forall2_kw1Q_relab (n : ℕ) (f : ℕ → ℕ) (v : ℕ → Val) {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ (i : ℕ) (w : Val), i < n ∧
        x = Val.cons (Val.int ((i : ℕ) : ℤ)) w ∧
        y = Val.cons (Val.int (((f i : ℕ) : ℤ))) w)
      ((List.range n).map (fun i => Val.cons (Val.int ((i : ℕ) : ℤ)) (v i))) ys) :
    ys = (List.range n).map (fun i => Val.cons (Val.int (((f i : ℕ) : ℤ))) (v i)) := by
  have h1 : List.Forall₂ (fun x y => y = relab f x)
      ((List.range n).map (fun i => Val.cons (Val.int ((i : ℕ) : ℤ)) (v i))) ys :=
    h.imp (fun x y hxy => by
      obtain ⟨i, w, _hi, hx, hy⟩ := hxy
      rw [hx, relab_cons, hy])
  rw [eq_map_of_forall2 h1, List.map_map]
  simp

theorem kw1Forall2 (A m B : ℕ) (es ys : List HvdH.Val)
    (h : List.Forall₂ (Work.SB.Core.kw1Q A m B) (Work.SB.Core.kw1In A m B es) ys) :
    ys = Work.SB.Core.kw1Out A m B es := by
  rw [kw1In, kw1Out] at *
  unfold kw1Q at h
  exact forall2_kw1Q_relab (A * m * B) (Work.Layout.keyIdx1 m B)
    (fun i => es.getD i Val.nil) h

end Work.SB.Core
