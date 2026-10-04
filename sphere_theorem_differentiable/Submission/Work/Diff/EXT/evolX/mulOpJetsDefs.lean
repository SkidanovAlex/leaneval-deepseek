/-
# The shuffle calculus for the product of two packed operators

This module fixes the combinatorial vocabulary of the Leibniz rule for the *product* of two packed
operators `mulOp A B` of arities `K₁`, `K₂`: the tuple of `K₁ + K₂ + n` fields is split, according to
a binary word `w : Word n` (which of the `n` covariant derivative directions is applied to the first
factor), into the `A`-tuple (of arity `K₁ + #{true}`) and the `B`-tuple (of arity `K₂ + #{false}`).

The words are the inductive type `Word n` (a `cons`-list of `Bool`s of length `n`) so that the
recursion "peel the newest direction" is structural: `Word.cons b w` behaves definitionally.

* `wCntT w`, `wCntF w` — the number of `true` resp. `false` entries of the word;
* `wPosA n w r` — the position, in the level-`(n+1)` tuple, of the `r`-th entry of the `A`-tuple of
  `w : Word (n+1)` (junk outside the range `[0, K₁ + wCntT w)`).  The index is the level minus one,
  which keeps every codomain `Fin (K₁ + K₂ + (n+1))` nonempty;
* `wTupA n w F`, `wTupB n w F` — the two sub-tuples of the level-`n` tuple `F`.
-/
import Mathlib
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.EXT.evolX

open Work.Diff.EXT

/-- **A binary word of length `n`**: which of the `n` covariant derivatives is applied to the first
factor of a product.  `Word.cons b w` means that the newest direction (position `0` of the tuple) is
routed to the first factor (`b = true`) or the second (`b = false`). -/
inductive Word : ℕ → Type
  | nil : Word 0
  | cons : Bool → {n : ℕ} → Word n → Word (n + 1)

namespace Word

/-- The first (newest) entry of a nonempty word. -/
def head : {n : ℕ} → Word (n + 1) → Bool
  | _, cons b _ => b

/-- The word obtained by dropping the first (newest) entry. -/
def tail : {n : ℕ} → Word (n + 1) → Word n
  | _, cons _ w => w

@[simp] theorem head_cons {n : ℕ} (b : Bool) (w : Word n) : head (cons b w) = b := rfl

@[simp] theorem tail_cons {n : ℕ} (b : Bool) (w : Word n) : tail (cons b w) = w := rfl

theorem cons_head_tail {n : ℕ} (w : Word (n + 1)) : cons (head w) (tail w) = w := by
  cases w with
  | cons b w => rfl

instance : Subsingleton (Word 0) := ⟨fun a b => by cases a; cases b; rfl⟩

instance : Inhabited (Word 0) := ⟨nil⟩

/-- `Word (n+1)` is `Bool × Word n`. -/
def consEquiv (n : ℕ) : Bool × Word n ≃ Word (n + 1) where
  toFun p := cons p.1 p.2
  invFun w := (head w, tail w)
  left_inv p := rfl
  right_inv w := by cases w with | cons b w => rfl

instance instFintypeWord : ∀ n, Fintype (Word n)
  | 0 => Fintype.ofSubsingleton (default : Word 0)
  | n + 1 =>
      letI : Fintype (Word n) := instFintypeWord n
      Fintype.ofEquiv (Bool × Word n) (consEquiv n)

end Word

open Word

/-- The number of `true` entries of the word `w`. -/
def wCntT : {n : ℕ} → Word n → ℕ
  | _, Word.nil => 0
  | _, Word.cons b w => wCntT w + b.toNat

/-- The number of `false` entries of the word `w`. -/
def wCntF : {n : ℕ} → Word n → ℕ
  | _, Word.nil => 0
  | _, Word.cons b w => wCntF w + (!b).toNat

@[simp] theorem wCntT_cons_true {n : ℕ} (w : Word n) :
    wCntT (Word.cons true w) = wCntT w + 1 := rfl

@[simp] theorem wCntT_cons_false {n : ℕ} (w : Word n) :
    wCntT (Word.cons false w) = wCntT w := rfl

@[simp] theorem wCntF_cons_true {n : ℕ} (w : Word n) :
    wCntF (Word.cons true w) = wCntF w := rfl

@[simp] theorem wCntF_cons_false {n : ℕ} (w : Word n) :
    wCntF (Word.cons false w) = wCntF w + 1 := rfl

theorem wCntT_add_wCntF : ∀ {n : ℕ} (w : Word n), wCntT w + wCntF w = n
  | _, Word.nil => rfl
  | _, Word.cons b w => by
    have ih := wCntT_add_wCntF w
    cases b <;> simp <;> omega

theorem wCntF_eq {n : ℕ} (w : Word n) : wCntF w = n - wCntT w := by
  have := wCntT_add_wCntF w
  omega

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The position, in the level-`(n+1)` tuple, of the `r`-th entry of the `A`-tuple of the word `w`
(junk outside `[0, K₁ + wCntT w)`).  The first `wCntT w` entries of the `A`-tuple are the
derivative directions routed to `A` (newest first), the remaining `K₁` are its tensor slots. -/
noncomputable def wPosA (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word (n + 1)) →
    ℕ → Fin (K₁ + K₂ + (n + 1))
  | 0, Word.cons true _, r => if r = 0 then ⟨0, by omega⟩ else ⟨min r (K₁ + K₂), by omega⟩
  | 0, Word.cons false _, r => ⟨min (r + 1) (K₁ + K₂), by omega⟩
  | n + 1, Word.cons true w, r =>
      if r = 0 then ⟨0, by omega⟩ else (wPosA K₁ K₂ n w (r - 1)).succ
  | n + 1, Word.cons false w, r => (wPosA K₁ K₂ n w r).succ

/-- The position, in the level-`(n+1)` tuple, of the `r`-th entry of the `B`-tuple of the word `w`
(junk outside `[0, K₂ + wCntF w)`). -/
noncomputable def wPosB (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word (n + 1)) →
    ℕ → Fin (K₁ + K₂ + (n + 1))
  | 0, Word.cons true _, r => ⟨min (K₁ + 1 + r) (K₁ + K₂), by omega⟩
  | 0, Word.cons false _, r =>
      if r = 0 then ⟨0, by omega⟩ else ⟨min (K₁ + r) (K₁ + K₂), by omega⟩
  | n + 1, Word.cons true w, r => (wPosB K₁ K₂ n w r).succ
  | n + 1, Word.cons false w, r =>
      if r = 0 then ⟨0, by omega⟩ else (wPosB K₁ K₂ n w (r - 1)).succ

/-- The `A`-sub-tuple of the level-`n` tuple `F` for the word `w`. -/
noncomputable def wTupA (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word n) →
    (Fin (K₁ + K₂ + n) → TField (I := I) (M := M)) → Fin (K₁ + wCntT w) →
      TField (I := I) (M := M)
  | 0, Word.nil, F => fun i => F ⟨i.val, by
      have hi : (i : ℕ) < K₁ := i.isLt
      omega⟩
  | n + 1, w, F => fun i => F (wPosA K₁ K₂ n w i.val)

/-- The `B`-sub-tuple of the level-`n` tuple `F` for the word `w`. -/
noncomputable def wTupB (K₁ K₂ : ℕ) : (n : ℕ) → (w : Word n) →
    (Fin (K₁ + K₂ + n) → TField (I := I) (M := M)) → Fin (K₂ + wCntF w) →
      TField (I := I) (M := M)
  | 0, Word.nil, F => fun i => F ⟨K₁ + i.val, by
      have hi : (i : ℕ) < K₂ := i.isLt
      omega⟩
  | n + 1, w, F => fun i => F (wPosB K₁ K₂ n w i.val)

/-! ## The recursion equations for the position maps -/

@[simp] theorem wPosA_cons_true_zero (K₁ K₂ n : ℕ) (w : Word n) :
    wPosA K₁ K₂ n (Word.cons true w) 0 =
      (⟨0, by omega⟩ : Fin (K₁ + K₂ + (n + 1))) := by
  cases n with
  | zero => rw [wPosA]; simp
  | succ n => rw [wPosA]; simp

theorem wPosA_cons_true_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    wPosA K₁ K₂ (n + 1) (Word.cons true w) (r + 1) =
      (wPosA K₁ K₂ n w r).succ := by
  rw [wPosA]; simp

theorem wPosA_cons_false (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    wPosA K₁ K₂ (n + 1) (Word.cons false w) r =
      (wPosA K₁ K₂ n w r).succ := by
  rw [wPosA]

theorem wPosA_zero_cons_true (K₁ K₂ : ℕ) (w : Word 0) (r : ℕ) :
    wPosA K₁ K₂ 0 (Word.cons true w) r =
      (if r = 0 then ⟨0, by omega⟩ else ⟨min r (K₁ + K₂), by omega⟩ :
        Fin (K₁ + K₂ + 1)) := by
  rw [wPosA]

theorem wPosA_zero_cons_false (K₁ K₂ : ℕ) (w : Word 0) (r : ℕ) :
    wPosA K₁ K₂ 0 (Word.cons false w) r = ⟨min (r + 1) (K₁ + K₂), by omega⟩ := by
  rw [wPosA]

@[simp] theorem wPosB_cons_false_zero (K₁ K₂ n : ℕ) (w : Word n) :
    wPosB K₁ K₂ n (Word.cons false w) 0 =
      (⟨0, by omega⟩ : Fin (K₁ + K₂ + (n + 1))) := by
  cases n with
  | zero => rw [wPosB]; simp
  | succ n => rw [wPosB]; simp

theorem wPosB_cons_true (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    wPosB K₁ K₂ (n + 1) (Word.cons true w) r =
      (wPosB K₁ K₂ n w r).succ := by
  rw [wPosB]

theorem wPosB_cons_false_succ (K₁ K₂ n : ℕ) (w : Word (n + 1)) (r : ℕ) :
    wPosB K₁ K₂ (n + 1) (Word.cons false w) (r + 1) =
      (wPosB K₁ K₂ n w r).succ := by
  rw [wPosB]; simp

theorem wPosB_zero_cons_true (K₁ K₂ : ℕ) (w : Word 0) (r : ℕ) :
    wPosB K₁ K₂ 0 (Word.cons true w) r = ⟨min (K₁ + 1 + r) (K₁ + K₂), by omega⟩ := by
  rw [wPosB]

theorem wPosB_zero_cons_false (K₁ K₂ : ℕ) (w : Word 0) (r : ℕ) :
    wPosB K₁ K₂ 0 (Word.cons false w) r =
      (if r = 0 then ⟨0, by omega⟩ else ⟨min (K₁ + r) (K₁ + K₂), by omega⟩ :
        Fin (K₁ + K₂ + 1)) := by
  rw [wPosB]

/-! ## The recursion equations for the sub-tuples -/

/-! ## The monomials of the shuffle decomposition

For a word `w : Word n` the `w`-monomial is the product of the `(wCntT w)`-th jet of the first
operator applied to its `A`-sub-tuple with the `(wCntF w)`-th jet of the second operator applied to
its `B`-sub-tuple; `wSum` is the sum of the monomials over all `2^n` words.  The Leibniz rule is the
identity `jetAll g n (K₁+K₂) (mulOp A B) = wSum g K₁ K₂ A B n` at every level. -/

/-- The monomial of the word `w` at level `n`. -/
noncomputable def wMon (g : Submission.Diff.SMet I M) (K₁ K₂ : ℕ)
    (A : (Fin K₁ → TField (I := I) (M := M)) → M → ℝ)
    (B : (Fin K₂ → TField (I := I) (M := M)) → M → ℝ) :
    (n : ℕ) → Word n → (Fin (K₁ + K₂ + n) → TField (I := I) (M := M)) → M → ℝ :=
  fun n w F y =>
    jetAll g (wCntT w) K₁ A (wTupA (I := I) (M := M) K₁ K₂ n w F) y
      * jetAll g (wCntF w) K₂ B (wTupB (I := I) (M := M) K₁ K₂ n w F) y

/-- The sum of the monomials over all words of length `n`. -/
noncomputable def wSum (g : Submission.Diff.SMet I M) (K₁ K₂ : ℕ)
    (A : (Fin K₁ → TField (I := I) (M := M)) → M → ℝ)
    (B : (Fin K₂ → TField (I := I) (M := M)) → M → ℝ) (n : ℕ) :
    (Fin (K₁ + K₂ + n) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y => ∑ w : Word n, wMon (I := I) (M := M) g K₁ K₂ A B n w F y

end Work.Diff.EXT.evolX
