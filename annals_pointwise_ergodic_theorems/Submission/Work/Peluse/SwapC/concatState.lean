import Mathlib
import Submission.Work.Peluse.SwapC.Basic

/-!
# The concatenation state of `Work.Peluse.SwapC.concatAll`

Auxiliary vocabulary for KKL Proposition 6.2 (`concatAll`).  The proof iterates `concatStep`:
at each step the state is an average over *all* index assignments `ι : (Fin s → Bool) → I` of the
box whose slot list `L` records which raw slot / difference each slot of the box is.  A `CC s` is
such a slot descriptor:

* `CC.raw j a` is the raw slot `q (ι a) j [M]`, i.e. the coefficient pair `(q (ι a) j, 0)`;
* `CC.dff j a b` is the concatenated slot `q (ι a) j [M] − q (ι b) j [M]`, i.e. the pair
  `(q (ι a) j, q (ι b) j)`.

The step lemma then peels the slots not touching the leaf being split, applies `concatStep` to the
inner average over the value of that leaf, and re-averages (Jensen).  The present file only sets up
the vocabulary and the elementary plumbing; the step lemma and the bookkeeping of the iteration live
in `Work.Peluse.SwapC.concatAssembly`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- A slot descriptor of the concatenation state: a raw slot `q (ι a) j` or a concatenated slot
`q (ι a) j − q (ι b) j` (the coefficient pair being `(q (ι a) j, 0)` resp. `(q (ι a) j, q (ι b) j)`). -/
inductive CC (s : ℕ) : Type
  | raw (j : Fin s) (a : Fin s → Bool) : CC s
  | dff (j : Fin s) (a b : Fin s → Bool) : CC s
  deriving DecidableEq

namespace CC

variable {s : ℕ}

/-- The leaf (in the convention of the iteration: the string at which the coefficient is
evaluated) is touched by the slot. -/
def touches (a : Fin s → Bool) : CC s → Prop
  | .raw _ b => b = a
  | .dff _ b c => b = a ∨ c = a

/-- Replace the string `a` by `a'` in a slot (the "doubling" of the step). -/
def subst (a a' : Fin s → Bool) : CC s → CC s
  | .raw j b => .raw j (if b = a then a' else b)
  | .dff j b c => .dff j (if b = a then a' else b) (if c = a then a' else c)

/-- The Bool-valued version of `touches`, for `List.filter`. -/
def touchesb (a : Fin s → Bool) : CC s → Bool
  | .raw _ b => decide (b = a)
  | .dff _ b c => decide (b = a) || decide (c = a)

@[simp] lemma touchesb_eq_true {a : Fin s → Bool} {sl : CC s} :
    touchesb a sl = true ↔ touches a sl := by
  cases sl with
  | raw j b => simp [touchesb, touches]
  | dff j b c => simp [touchesb, touches]

@[simp] lemma touches_raw {a b : Fin s → Bool} {j : Fin s} :
    touches a (.raw j b) = (b = a) := rfl

@[simp] lemma touches_dff {a b c : Fin s → Bool} {j : Fin s} :
    touches a (.dff j b c) = (b = a ∨ c = a) := rfl

@[simp] lemma subst_raw_self {a a' : Fin s → Bool} {j : Fin s} :
    subst a a' (.raw j a) = .raw j a' := by
  rw [subst]; simp

@[simp] lemma subst_raw_of_ne {a a' b : Fin s → Bool} {j : Fin s} (h : b ≠ a) :
    subst a a' (.raw j b) = .raw j b := by
  rw [subst]; simp [h]

@[simp] lemma subst_dff_fst {a a' b c : Fin s → Bool} {j : Fin s} (h : c ≠ a) :
    subst a a' (.dff j a c) = .dff j a' c := by
  rw [subst]; simp [h]

lemma subst_dff_snd {a a' b : Fin s → Bool} {j : Fin s} (h : b ≠ a) :
    subst a a' (.dff j b a) = .dff j b a' := by
  rw [subst]; simp [h]

@[simp] lemma subst_dff_both {a a' : Fin s → Bool} {j : Fin s} :
    subst a a' (.dff j a a) = .dff j a' a' := by
  rw [subst]; simp

@[simp] lemma subst_dff_of_ne {a a' b c : Fin s → Bool} {j : Fin s} (hb : b ≠ a) (hc : c ≠ a) :
    subst a a' (.dff j b c) = .dff j b c := by
  rw [subst]; simp [hb, hc]

/-- A slot is *raw* when its second coefficient is `0`. -/
def IsRaw : CC s → Prop
  | .raw _ _ => True
  | .dff _ _ _ => False

/-- The first coefficient of the slot at the index assignment `ι`. -/
def cA {I : Type} (q : I → Fin s → ℤ) (ι : (Fin s → Bool) → I) : CC s → ℤ
  | .raw j a => q (ι a) j
  | .dff j a _ => q (ι a) j

/-- The second coefficient of the slot at the index assignment `ι` (zero for a raw slot). -/
def cB {I : Type} (q : I → Fin s → ℤ) (ι : (Fin s → Bool) → I) : CC s → ℤ
  | .raw _ _ => 0
  | .dff j _ b => q (ι b) j

end CC

open CC

/-- **The concatenation state.**  The average, over all index assignments
`ι : (Fin s → Bool) → I`, of the box norm of `f` with the slots `L`.  At the start of the iteration
`L` is the list of raw slots at the empty string; at the end it is the list of all the concatenated
slots of `slotSet s`. -/
def cSt (I : Type) [Fintype I] [Nonempty I] {s : ℕ} (q : I → Fin s → ℤ) (M N : ℕ) (f : ℤ → ℂ)
    (L : List (CC s)) : ℝ :=
  avg (fun ι : (Fin s → Bool) → I =>
    pbox L.length (fun k => cA q ι (L.get k)) (fun k => cB q ι (L.get k)) M (symIcc N) f)

/-- `cSt` unfolded, with the list written through its two coefficient functions. -/
lemma cSt_def (I : Type) [Fintype I] [Nonempty I] {s : ℕ} (q : I → Fin s → ℤ) (M N : ℕ)
    (f : ℤ → ℂ) (L : List (CC s)) :
    cSt I q M N f L
      = avg (fun ι : (Fin s → Bool) → I =>
          pbox L.length (fun k => cA q ι (L.get k)) (fun k => cB q ι (L.get k)) M (symIcc N) f) :=
  rfl

lemma cSt_nonneg (I : Type) [Fintype I] [Nonempty I] {s : ℕ} (q : I → Fin s → ℤ) (M N : ℕ)
    (f : ℤ → ℂ) (L : List (CC s)) : 0 ≤ cSt I q M N f L :=
  avg_nonneg fun _ => pbox_nonneg _ _ _ _ _ _

end

end Work.Peluse.SwapC

namespace Work.Peluse.SwapC

open CC

/-! ## The leaf subdivision of the iteration

The `s`-stage iteration of `concatStep` refines the subdivision `{∅}` of `{0,1}^s` step by step:
each step splits one leaf of depth `< s` into its two children.  A leaf is a string together with
its depth; the string has zero coordinates beyond the depth.  The slots of the current state are

* the raw slots `(j, λ)` with `s − 1 − j ≥ depth λ`, and
* the concatenated slots `(j, a, b)` for a pair of distinct leaves `a ≠ b` whose strings first
  differ at coordinate `s − 1 − j` (with `a` carrying `true` and `b` carrying `false`).
-/

/-- The all-`false` string. -/
def czero (s : ℕ) : Fin s → Bool := fun _ => false

/-- A leaf of the subdivision: a string, its depth, and the padding condition. -/
structure CLeaf (s : ℕ) where
  str : Fin s → Bool
  dep : ℕ
  dep_le : dep ≤ s
  pad : ∀ i : Fin s, dep ≤ i.val → str i = false

namespace CLeaf

variable {s : ℕ}

/-- The two children of a splittable leaf: the string itself (its depth-th coordinate is `false`)
and the string with depth-th coordinate `true`. -/
def children (l : CLeaf s) (h : l.dep < s) : List (CLeaf s) :=
  [ { str := l.str, dep := l.dep + 1, dep_le := by omega,
      pad := fun i hi => l.pad i (by omega) },
    { str := Function.update l.str ⟨l.dep, h⟩ true, dep := l.dep + 1, dep_le := by omega,
      pad := by
        intro i hi
        have hne : i ≠ ⟨l.dep, h⟩ := by
          intro he
          have hv : i.val = l.dep := by simpa using congrArg Fin.val he
          omega
        rw [Function.update_apply, if_neg hne]
        exact l.pad i (by omega) } ]

/-- The raw slots at a leaf: all `j : Fin s` with `s - 1 - j ≥ dep`. -/
def raws (l : CLeaf s) : List (CC s) :=
  ((List.finRange s).filter (fun j : Fin s => l.dep ≤ s - 1 - j.val)).map (fun j => CC.raw j l.str)

end CLeaf

variable {s : ℕ}

/-- Split the first leaf of depth `< s`; leave the list unchanged if there is none. -/
def csplitFirst : List (CLeaf s) → List (CLeaf s)
  | [] => []
  | l :: rest => if h : l.dep < s then l.children h ++ rest else l :: csplitFirst rest

/-- The depth-first process: the subdivision after `k` splits. -/
def cproc (s : ℕ) : ℕ → List (CLeaf s)
  | 0 => [{ str := czero s, dep := 0, dep_le := by omega, pad := fun _ _ => rfl }]
  | k + 1 => csplitFirst (cproc s k)

/-- `CLeaf` has decidable equality (the `pad` field is a proof of a proposition). -/
instance (s : ℕ) : DecidableEq (CLeaf s) := fun a b =>
  if h : a.str = b.str ∧ a.dep = b.dep then
    isTrue (by cases a; cases b; simp_all)
  else
    isFalse (by intro hab; exact h ⟨by rw [hab], by rw [hab]⟩)

/-- Refine a leaf list by splitting the leaf `l` into its two children. -/
def refine (Λ : List (CLeaf s)) (l : CLeaf s) : List (CLeaf s) :=
  Λ.flatMap fun l' =>
    if he : l' = l then (if hh : l'.dep < s then l'.children hh else [l']) else [l']

/-- The concatenated slots of a leaf list: for a pair of distinct leaves `a ≠ b` whose strings
first differ at coordinate `s - 1 - j` (`a` carrying `true`, `b` carrying `false`), the slot
`(j, a, b)`.  The condition only involves the strings, not the depths. -/
def genuineDiffs (Λ : List (CLeaf s)) : List (CC s) :=
  (Λ.product Λ).flatMap fun p =>
    ((List.finRange s).filterMap fun j : Fin s =>
      if (∀ i : Fin s, i.val < s - 1 - j.val → p.1.str i = p.2.str i)
          ∧ p.1.str ⟨s - 1 - j.val, by omega⟩ = true
          ∧ p.2.str ⟨s - 1 - j.val, by omega⟩ = false
      then some (CC.dff j p.1.str p.2.str) else none)

/-- The genuine slots of a leaf list: the raw slots at each leaf, followed by the concatenated
slots. -/
def genuineSlots (Λ : List (CLeaf s)) : List (CC s) :=
  (Λ.map CLeaf.raws).flatten ++ genuineDiffs Λ

/-- The leaf that the next split acts on (`none` if the process is finished). -/
def cnextLeaf (Λ : List (CLeaf s)) : Option (CLeaf s) :=
  Λ.find? (fun l => l.dep < s)


/-- A leaf list is a *subdivision* of `{0,1}^s`: every string lies in the cell of exactly one leaf. -/
def IsSubdiv (Λ : List (CLeaf s)) : Prop :=
  ∀ x : Fin s → Bool, ∃! l : CLeaf s, l ∈ Λ ∧ ∀ i : Fin s, i.val < l.dep → l.str i = x i

/-- The statement of KKL Lemma 6.1 (`concatStep`) written out inline, so that the step lemma can
take it as a hypothesis. -/
abbrev CStepHyp : Prop :=
  ∀ (s : ℕ), ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
      (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I => Work.Peluse.LadderP.Swap.pbox (s + 1)
              (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun p : I × I =>
        Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f)


end Work.Peluse.SwapC
