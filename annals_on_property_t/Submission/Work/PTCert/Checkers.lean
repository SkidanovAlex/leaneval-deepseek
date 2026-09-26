import Submission.Work.PTCert.Interfaces

/-!
# PTCert — computable checkers used by the kernel certificate (definitions + soundness Props)

All functions here are designed to be evaluated by `decide +kernel` on `Nat`/`List Nat` data:
no `if` on propositions (only `Bool` via `Nat.beq`/`Nat.ble`/`bif`), recursion by structural
recursion on lists or on a `Nat` fuel.  Measured: table lookups ~20-40 µs, so these checkers are
meant for ≤ ~10^5 calls in total.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-! ## Free-group word model

A free-group letter is a `Nat` `c`: generator `c / 2`, inverted iff `c` is odd.  A word is a
`List Nat`. -/

/-- The free-group element of a word. -/
def evalW {r : ℕ} (w : List ℕ) : FreeGroup (Fin r) :=
  (w.map (fun c => if h : c / 2 < r then
      (if c % 2 = 0 then FreeGroup.of (⟨c / 2, h⟩ : Fin r) else (FreeGroup.of (⟨c / 2, h⟩ : Fin r))⁻¹)
    else 1)).prod

/-- One step of free reduction on a reversed accumulator. -/
def redStep (acc : List ℕ) (c : ℕ) : List ℕ :=
  match acc with
  | [] => [c]
  | d :: t => bif Nat.beq d (c ^^^ 1) then t else c :: d :: t

/-- Free reduction (result is reduced when all letters are `< 2r`). -/
def redW (w : List ℕ) : List ℕ := (w.foldl redStep []).reverse

/-- Inverse word. -/
def invW (w : List ℕ) : List ℕ := (w.map (fun c => c ^^^ 1)).reverse

/-- Image of generator `i` under the letter `k` of rank `r` (see `b1`), as a word. -/
def letterImg (r k i : ℕ) : List ℕ :=
  bif Nat.beq k 0 then [2 * i] else
  let q := (k - 1) / 4
  let kind := (k - 1) % 4
  let i0 := (pairOf r q).1
  let j0 := (pairOf r q).2
  bif Nat.beq i i0 then
    (bif Nat.beq kind 0 then [2 * i0, 2 * j0] else
     bif Nat.beq kind 1 then [2 * i0, 2 * j0 + 1] else
     bif Nat.beq kind 2 then [2 * j0, 2 * i0] else [2 * j0 + 1, 2 * i0])
  else [2 * i]

/-- Apply the letter `k` (as an endomorphism of the free group) to a word, then reduce. -/
def applyLetter (r k : ℕ) (w : List ℕ) : List ℕ :=
  redW (w.flatMap (fun c => bif Nat.beq (c % 2) 0 then letterImg r k (c / 2)
    else invW (letterImg r k (c / 2))))

/-- Image of generator `i` under the product `b1 r k₁ * ⋯ * b1 r kₙ` (rightmost acts first). -/
def prodImg (r : ℕ) (ks : List ℕ) (i : ℕ) : List ℕ := ks.foldr (applyLetter r) [2 * i]

/-- Equality test of two products of letters, on the generators. -/
def modelEq (r : ℕ) (ks ls : List ℕ) : Bool :=
  (List.range r).all (fun i => prodImg r ks i == prodImg r ls i)

/-- The group element of a list of letters. -/
def lprod (r : ℕ) (ks : List ℕ) : MulAut (FreeGroup (Fin r)) := (ks.map (b1 r)).prod

/-- **(M1) Soundness of the word model** (all letters `< NB1 r`). -/
def ModelSound (r : ℕ) : Prop :=
  ∀ ks ls : List ℕ, (∀ k ∈ ks, k < NB1 r) → (∀ k ∈ ls, k < NB1 r) →
    modelEq r ks ls = true → lprod r ks = lprod r ls

/-! ## Permutation check by merge sort with fuel -/

def mergeL : List ℕ → List ℕ → List ℕ
  | [], l => l
  | l, [] => l
  | a :: s, b :: t => bif Nat.ble a b then a :: mergeL s (b :: t) else b :: mergeL (a :: s) t

/-- Split into the elements at even and odd positions. -/
def splitL : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | a :: s => let p := splitL s; (a :: p.2, p.1)

/-- Merge sort with explicit fuel (depth); with fuel `≥ log₂ length + 1` it sorts. -/
def msortF : ℕ → List ℕ → List ℕ
  | 0, l => l
  | f + 1, l => match l with
    | [] => []
    | [a] => [a]
    | l => let p := splitL l; mergeL (msortF f p.1) (msortF f p.2)

/-- `l` is a permutation of `[0, n)`. -/
def isPermRange (l : List ℕ) (n : ℕ) : Bool := msortF 40 l == List.range n

/-- **(M2) Soundness of the permutation check.** -/
def PermCheckSound : Prop := ∀ (l : List ℕ) (n : ℕ), isPermRange l n = true → l.Perm (List.range n)


/-! ## Kernel-evaluable merge sort (fuel-structural)

`mergeL` above is compiled by well-founded recursion and does NOT reduce in the kernel
(`decide +kernel` fails on it; measured 2026-09-26).  The checkers use the fuel versions below. -/

/-- Merge with explicit fuel (structural recursion on the fuel). -/
def mergeF : ℕ → List ℕ → List ℕ → List ℕ
  | 0, s, t => s ++ t
  | f + 1, s, t => match s, t with
    | [], l => l
    | l, [] => l
    | a :: s', b :: t' => bif Nat.ble a b then a :: mergeF f s' (b :: t') else b :: mergeF f (a :: s') t'

/-- Merge sort, kernel-evaluable. -/
def msortK : ℕ → List ℕ → List ℕ
  | 0, l => l
  | f + 1, l => match l with
    | [] => []
    | [a] => [a]
    | l => let p := splitL l; mergeF (p.1.length + p.2.length) (msortK f p.1) (msortK f p.2)

/-- `l` is a permutation of the list `e` (kernel-evaluable): sorted `l` equals `e`. -/
def isPermOf (l e : List ℕ) : Bool := msortK 40 l == e

/-- **(M3) Soundness of the kernel permutation check.** -/
def PermCheckKSound : Prop := ∀ l e : List ℕ, isPermOf l e = true → l.Perm e

end Submission.PTCert
