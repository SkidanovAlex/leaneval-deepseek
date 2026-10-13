import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.finRange_take_drop_decomp
import Submission.Work.WilE3.Frame.mem_take_finRange_lt

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-! ## The list combinatorics behind the frame word

`Vword` (like `opMono`) is a `List.foldr` over `List.finRange k`, i.e. over the *increasing* list of
indices `0, 1, …, k - 1`: the `foldr` is outermost at the index `0` and innermost at `k - 1`.  The
content of `Vdir_Vword` is therefore purely combinatorial.  For `l : Fin k` the list splits as
`finRange k = (indices < l) ++ l :: (indices > l)`
(`finRange_take_drop_decomp`); all the groups below `l` are inactive (`m i = 0`), so they contribute
the identity, while the groups above `l` carry the same exponents before and after
`Function.update m l (m l + 1)`.  The group at `l` is the *outermost* group of the fold over
`l :: (indices > l)`, so no commutation of the operators is involved.

The result is stated in the general form `foldr_finRange_prepend` (a statement about an arbitrary
family of self-maps `f : Fin k → β → β` and an arbitrary `X : β`), which applies verbatim to any
word folded over `List.finRange k`: `Vword` here and `opMono` in the sibling
`detOp_opMono_prepend`. -/

/-- A `foldr` whose every group is the identity is the identity. -/
private lemma foldr_eq_self_of_forall {α β : Type*} {L : List α} {g : α → β → β}
    (h : ∀ x ∈ L, ∀ Y : β, g x Y = Y) (X : β) : L.foldr g X = X := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.foldr_cons, h a (by simp)]
      exact ih (fun x hx => h x (by simp [hx]))

/-- A `foldr` only sees its groups. -/
private lemma foldr_congr {α β : Type*} {L : List α} {g g' : α → β → β}
    (h : ∀ x ∈ L, g x = g' x) (X : β) : L.foldr g X = L.foldr g' X := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.foldr_cons, List.foldr_cons, h a (by simp)]
      exact congrArg (g' a) (ih fun x hx => h x (by simp [hx]))

/-- The key combinatorial lemma.  If `L = A ++ a :: B`, if the groups on `A` are trivial for both
exponent functions, if `m'` and `m` agree on `B`, and if `m' a = m a + 1`, then the group at `a`
may be pulled out of the `foldr` and its exponent increased. -/
private lemma foldr_append_cons_prepend {α β : Type*} (A B : List α) (a : α) (f : α → β → β)
    (m m' : α → ℕ) (X : β) (ha : m' a = m a + 1)
    (hA : ∀ x ∈ A, m x = 0) (hA' : ∀ x ∈ A, m' x = 0) (hB : ∀ x ∈ B, m' x = m x) :
    f a ((A ++ a :: B).foldr (fun i Y => (f i)^[m i] Y) X) =
      (A ++ a :: B).foldr (fun i Y => (f i)^[m' i] Y) X := by
  have hAid : ∀ Z : β, A.foldr (fun i Y => (f i)^[m i] Y) Z = Z := fun Z =>
    foldr_eq_self_of_forall
      (L := A) (g := fun i Y => (f i)^[m i] Y)
      (fun x hx Y => by simp only [hA x hx, Function.iterate_zero_apply]) Z
  have hAid' : ∀ Z : β, A.foldr (fun i Y => (f i)^[m' i] Y) Z = Z := fun Z =>
    foldr_eq_self_of_forall
      (L := A) (g := fun i Y => (f i)^[m' i] Y)
      (fun x hx Y => by simp only [hA' x hx, Function.iterate_zero_apply]) Z
  have hBid : ∀ Z : β, B.foldr (fun i Y => (f i)^[m i] Y) Z
      = B.foldr (fun i Y => (f i)^[m' i] Y) Z := fun Z =>
    foldr_congr
      (L := B) (g := fun i Y => (f i)^[m i] Y) (g' := fun i Y => (f i)^[m' i] Y)
      (fun x hx => by simp only [hB x hx]) Z
  have ha' : ∀ Z : β, f a ((f a)^[m a] Z) = (f a)^[m' a] Z := by
    intro Z
    rw [ha]
    exact (Function.iterate_succ_apply' (f a) (m a) Z).symm
  calc f a ((A ++ a :: B).foldr (fun i Y => (f i)^[m i] Y) X)
      = f a (A.foldr (fun i Y => (f i)^[m i] Y)
          ((fun i Y => (f i)^[m i] Y) a (B.foldr (fun i Y => (f i)^[m i] Y) X))) := by
        rw [List.foldr_append, List.foldr_cons]
    _ = f a ((fun i Y => (f i)^[m i] Y) a (B.foldr (fun i Y => (f i)^[m i] Y) X)) := by
        rw [hAid]
    _ = f a ((fun i Y => (f i)^[m i] Y) a (B.foldr (fun i Y => (f i)^[m' i] Y) X)) := by
        rw [hBid]
    _ = (fun i Y => (f i)^[m' i] Y) a (B.foldr (fun i Y => (f i)^[m' i] Y) X) :=
        ha' (B.foldr (fun i Y => (f i)^[m' i] Y) X)
    _ = A.foldr (fun i Y => (f i)^[m' i] Y)
          ((fun i Y => (f i)^[m' i] Y) a (B.foldr (fun i Y => (f i)^[m' i] Y) X)) := by
        rw [hAid']
    _ = (A ++ a :: B).foldr (fun i Y => (f i)^[m' i] Y) X := by
        rw [List.foldr_append, List.foldr_cons]

/-- **Pulling the `l`-group out of a word folded over `List.finRange k`.**  If every index below `l`
is inactive (`m i = 0` for `i < l`), then the `l`-group is the outermost group of the fold over the
part of `finRange k` at and above `l`, so that composing one further `f l` with the word increases
the `l`-th exponent by one.  (`Vdir_Vword` is the case `f i = Vdir c h ι i`, `β = (Fin k → ℂ) → ℂ`;
`detOp_opMono_prepend` is the case `f i = detOp c h ι i`, `β = EAPoly k r`.) -/
theorem foldr_finRange_prepend {k : ℕ} {β : Type*} (f : Fin k → β → β) (m : Fin k → ℕ)
    (l : Fin k) (hm : ∀ i : Fin k, i < l → m i = 0) (X : β) :
    f l ((List.finRange k).foldr (fun i Y => (f i)^[m i] Y) X) =
      (List.finRange k).foldr (fun i Y => (f i)^[Function.update m l (m l + 1) i] Y) X := by
  have hd := (finRange_take_drop_decomp l).1
  have hnb := (finRange_take_drop_decomp l).2
  rw [hd]
  refine foldr_append_cons_prepend ((List.finRange k).take l.val)
    ((List.finRange k).drop (l.val + 1)) l f m (Function.update m l (m l + 1)) X ?_ ?_ ?_ ?_
  · exact Function.update_self l (m l + 1) m
  · intro x hx
    exact hm x (by simpa using mem_take_finRange_lt l hx)
  · intro x hx
    have hlt : (x : ℕ) < l.val := mem_take_finRange_lt l hx
    have hne : x ≠ l := by
      intro hxl
      rw [hxl] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [Function.update_of_ne (a := x) (a' := l) hne (m l + 1) m]
    exact hm x (by simpa using hlt)
  · intro x hx
    have hne : x ≠ l := fun hxl => hnb (hxl ▸ hx)
    exact Function.update_of_ne (a := x) (a' := l) hne (m l + 1) m

/-- Prepending a new (smallest) index to an iterated frame derivative.  `Vdir` is differentiation
along the tangential frame vector `VcoefC` (`Vcoef.lean`) and `Vword` its iterated words, both
folded over `List.finRange k` exactly like `opMono`.  If every index below `l` is inactive (`m i = 0`
for `i < l`), then the fold's outermost group is the `l`-group and `V_l` composes with `Vword m` to
give `Vword` of `m` with the `l`-th exponent increased. -/
theorem Vdir_Vword {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (m : Fin k → ℕ) (hm : ∀ i : Fin k, i < l → m i = 0) (F : (Fin k → ℂ) → ℂ) :
    Work.WilE3.Frame.Vdir c h ι l (Work.WilE3.Frame.Vword c h ι m F) =
      Work.WilE3.Frame.Vword c h ι (Function.update m l (m l + 1)) F := by
  unfold Work.WilE3.Frame.Vword
  exact foldr_finRange_prepend (fun i => Work.WilE3.Frame.Vdir c h ι i) m l hm F

end Work.WilE3.Frame
