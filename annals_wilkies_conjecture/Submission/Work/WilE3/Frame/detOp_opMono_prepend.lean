import Mathlib
import Submission.Work.WilE3.Frame.Setup

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-! ## The fold combinatorics behind `detOp_opMono_prepend`.

`opMono c h ι m f` is the right fold `(List.finRange k).foldr (fun l g => (detOp c h ι l)^[m l] g) f`
and `Function.update m l (m l + 1)` raises the `l`-th exponent by one.  The whole content of the
lemma is the combinatorics of right folds over `List.finRange k`: since `m` vanishes below `l`, the
groups of the fold with indices `< l` are the identity and the outermost non-trivial group is the
`l`-group, which `detOp c h ι l` may therefore be absorbed into.

We prove this in three steps.
* `foldr_exp_congr`, `foldr_map_exp` — elementary list rewriting lemmas for folds with a family of
  test maps `g i` and exponents `m i`.
* `foldr_prepend` — the abstract statement for an arbitrary list `A ++ l :: B`: the elements of `A`
  carry exponent `0`, so folding them on the outside does nothing, and `g l` composes with the
  `l`-group.
* `Fold_update` — the same statement for `List.finRange n`, by induction on `n` using
  `List.finRange_succ : List.finRange (n+1) = 0 :: (List.finRange n).map Fin.succ`. -/

/-- The ordered word of first-order operators: `(List.finRange n).foldr (fun i g => (g i)^[m i] g)`. -/
private def Fold {α : Type*} {n : ℕ} (g : Fin n → α → α) (m : Fin n → ℕ) (f : α) : α :=
  (List.finRange n).foldr (fun i acc => (g i)^[m i] acc) f

/-- Folds whose exponent functions agree on the list agree. -/
private lemma foldr_exp_congr {α β : Type*} (g : α → β → β) (m m' : α → ℕ) :
    ∀ (L : List α), (∀ a ∈ L, m' a = m a) → ∀ f : β,
      List.foldr (fun i acc => (g i)^[m' i] acc) f L
        = List.foldr (fun i acc => (g i)^[m i] acc) f L := by
  intro L
  induction L with
  | nil => intro _ f; rfl
  | cons a t ih =>
      intro h f
      simp only [List.foldr_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem a hx)) f, h a List.mem_cons_self]

/-- Reindexing a fold along a map of index types. -/
private lemma foldr_map_exp {α β γ : Type*} (g : α → β → β) (m : α → ℕ) (e : γ → α) :
    ∀ (L : List γ) (f : β),
      List.foldr (fun i acc => (g i)^[m i] acc) f (L.map e)
        = List.foldr (fun i acc => (g (e i))^[m (e i)] acc) f L := by
  intro L
  induction L with
  | nil => intro f; rfl
  | cons a t ih =>
      intro f
      simp only [List.map_cons, List.foldr_cons]
      rw [ih f]

/-- The abstract fold statement: if the list of indices is `A ++ l :: B`, if the exponent `m`
vanishes on `A`, and if `m'` agrees with `m` on `A` and `B` but is `m l + 1` at `l`, then the
`l`-th group of the fold is the outermost non-trivial one and absorbs the extra factor `g l`. -/
private lemma foldr_prepend {α β : Type*} (g : α → β → β) (m m' : α → ℕ)
    (A B : List α) (l : α) (f : β)
    (hm : ∀ a ∈ A, m a = 0) (hA : ∀ a ∈ A, m' a = m a) (hB : ∀ a ∈ B, m' a = m a)
    (hl : m' l = m l + 1) :
    g l (List.foldr (fun i acc => (g i)^[m i] acc) f (A ++ l :: B)) =
      List.foldr (fun i acc => (g i)^[m' i] acc) f (A ++ l :: B) := by
  induction A with
  | nil =>
      rw [List.nil_append]
      have h : List.foldr (fun i acc => (g i)^[m' i] acc) f B
          = List.foldr (fun i acc => (g i)^[m i] acc) f B := foldr_exp_congr g m m' B hB f
      simp only [List.foldr_cons]
      rw [hl, ← h, Function.iterate_succ_apply']
  | cons a A' ih =>
      have hma : m a = 0 := hm a List.mem_cons_self
      have hm'a : m' a = m a := hA a List.mem_cons_self
      have ih' := ih (fun x hx => hm x (List.mem_cons_of_mem a hx))
        (fun x hx => hA x (List.mem_cons_of_mem a hx))
      simp only [List.cons_append, List.foldr_cons, hm'a, hma, Function.iterate_zero_apply]
      exact ih'

/-- `Fold_update`: prepending the `l`-th operator to the `List.finRange n`-fold.  Proved by
induction on `n`, peeling off the index `0` using
`List.finRange_succ : List.finRange (n+1) = 0 :: (List.finRange n).map Fin.succ`.  When `l = 0` this
is exactly `foldr_prepend`; when `l = Fin.succ l'` the hypothesis forces `m 0 = 0`, and the fold
over `List.finRange (n+1)` reduces to the fold over `List.finRange n` for the reindexed data
`g ∘ Fin.succ`, `m ∘ Fin.succ`, to which the induction hypothesis applies at `l'`. -/
private lemma Fold_update {α : Type*} : ∀ (n : ℕ) (l : Fin n) (m : Fin n → ℕ)
    (g : Fin n → α → α) (f : α), (∀ i : Fin n, i < l → m i = 0) →
      g l (Fold g m f) = Fold g (Function.update m l (m l + 1)) f := by
  intro n
  induction n with
  | zero => intro l; exact l.elim0
  | succ n ih =>
      intro l m g f hm
      by_cases hl0 : l = 0
      · -- `l = 0`: every other index is above `l`, so `foldr_prepend` applies with `A = []`.
        subst hl0
        simp only [Fold, List.finRange_succ]
        refine foldr_prepend g m (Function.update m 0 (m 0 + 1)) []
          (List.map Fin.succ (List.finRange n)) 0 f ?_ ?_ ?_ ?_
        · intro a ha; exact absurd ha (by simp)
        · intro a ha; exact absurd ha (by simp)
        · intro a ha
          have hne : a ≠ 0 := by
            obtain ⟨i, -, hi⟩ := List.mem_map.mp ha
            exact fun h0 => Fin.succ_ne_zero i (hi.trans h0)
          exact Function.update_of_ne hne (m 0 + 1) m
        · exact Function.update_self 0 (m 0 + 1) m
      · -- `l = Fin.succ l'`: `m 0 = 0` by hypothesis, and the induction hypothesis applies at `l'`.
        obtain ⟨l', rfl⟩ := Fin.eq_succ_of_ne_zero hl0
        have hm0 : m 0 = 0 := hm 0 (Fin.succ_pos l')
        set m' := Function.update m (Fin.succ l') (m (Fin.succ l') + 1) with hm'def
        have hfold : Fold g m f
            = Fold (fun i : Fin n => g (Fin.succ i)) (fun i : Fin n => m (Fin.succ i)) f := by
          simp only [Fold, List.finRange_succ, List.foldr_cons, hm0, Function.iterate_zero_apply]
          exact foldr_map_exp g m Fin.succ (List.finRange n) f
        have hm'0 : m' 0 = 0 := by
          rw [hm'def, Function.update_of_ne (fun h0 : (0 : Fin (n + 1)) = Fin.succ l' =>
            Fin.succ_ne_zero l' h0.symm), hm0]
        have hfold' : Fold g m' f
            = Fold (fun i : Fin n => g (Fin.succ i)) (fun i : Fin n => m' (Fin.succ i)) f := by
          simp only [Fold, List.finRange_succ, List.foldr_cons, hm'0, Function.iterate_zero_apply]
          exact foldr_map_exp g m' Fin.succ (List.finRange n) f
        have hcomp : (fun i : Fin n => m' (Fin.succ i))
            = Function.update (fun i : Fin n => m (Fin.succ i)) l'
                ((fun i : Fin n => m (Fin.succ i)) l' + 1) := by
          rw [hm'def]
          exact Function.update_comp_eq_of_injective m (Fin.succ_injective n) l'
            (m (Fin.succ l') + 1)
        have hms : ∀ i : Fin n, i < l' → (fun i : Fin n => m (Fin.succ i)) i = 0 :=
          fun i hi => hm (Fin.succ i) (Fin.succ_lt_succ_iff.mpr hi)
        rw [hfold, hfold', hcomp]
        exact ih l' (fun i : Fin n => m (Fin.succ i)) (fun i : Fin n => g (Fin.succ i)) f hms

/-- Prepending the (smallest) `detOp` to an `opMono` word.  Both `opMono` and the frame word
`Vword` fold over `List.finRange k`; if every index below `l` is inactive, the outermost group of
the fold is the `l`-group, so `detOp c h ι l` composes with `opMono c h ι m` by increasing the `l`-th
exponent. -/
theorem detOp_opMono_prepend {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (m : Fin k → ℕ) (hm : ∀ i : Fin k, i < l → m i = 0)
    (f : EAPoly k r) :
    detOp c h ι l (opMono c h ι m f) = opMono c h ι (Function.update m l (m l + 1)) f := by
  have key := Fold_update k l m (detOp c h ι) f hm
  simpa only [Fold, opMono] using key

end Work.WilE3.Frame
