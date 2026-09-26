import Submission.Work.PTCert.Checkers

/-!
# PTCert — kernel-evaluable primitives for the certificate checks (rank 5)

Conventions (see `NOTES_LEAD_checker.md`):
* letters `0..80` (`b1 5 k`); an element of `B₂` is a *code* `c = 128 * a + b` for the product
  `b1 5 a * b1 5 b`, normalised by `normC` (inverse pairs → `0`, commuting pairs → sorted);
* a signed permutation is given by its *letter table*: a `Nat` packing `81` fields of `7` bits,
  field `k` = `actL 5 pc sc k`; `actC t cm c` is its action on codes;
* random access is by complete binary trees `NT` (index bits read low-first).
All functions are structurally recursive (`Nat.rec`/`List.rec`/`NT.rec`) and use `bif`/`Nat.beq`,
so that `decide +kernel` evaluates them.
-/

set_option autoImplicit false

noncomputable section

namespace Submission.PTCert

/-- Complete binary tree of naturals. -/
inductive NT where
  | leaf (v : ℕ)
  | node (l r : NT)

/-- Lookup (index bits low-first; a leaf answers every remaining index). -/
def NT.get (t : NT) : ℕ → ℕ :=
  NT.rec (motive := fun _ => ℕ → ℕ) (fun v _ => v)
    (fun _ _ gl gr i => bif Nat.beq (i % 2) 0 then gl (i / 2) else gr (i / 2)) t

/-- Field `k` (7 bits) of a letter table. -/
def lk (tab k : ℕ) : ℕ := (tab >>> (7 * k)) % 128

/-- Inverse letter (kernel form). -/
def invLk (k : ℕ) : ℕ := bif Nat.beq k 0 then 0 else ((k - 1) ^^^ 1) + 1

/-- Commutation bit from the commute table (`cm.get a` is an 81-bit mask). -/
def commB (cm : NT) (a b : ℕ) : Bool := Nat.beq ((cm.get a >>> b) % 2) 1

/-- Normal code of the product of letters `a`, `b`. -/
def normC (cm : NT) (a b : ℕ) : ℕ :=
  bif Nat.beq a (invLk b) then 0 else
  bif commB cm a b then (bif Nat.ble a b then 128 * a + b else 128 * b + a) else 128 * a + b

/-- Action of a letter table on a code. -/
def actC (cm : NT) (tab c : ℕ) : ℕ := normC cm (lk tab (c / 128)) (lk tab (c % 128))

/-- The group element of a code. -/
def eltC (c : ℕ) : MulAut (FreeGroup (Fin 5)) := b1 5 (c / 128) * b1 5 (c % 128)

/-- A letter table is correct for the code `(pc, sc)`. -/
def tabOK (pc sc tab : ℕ) : Bool :=
  validPC 5 pc && Nat.blt sc 32 && (List.range 81).all (fun k => Nat.beq (lk tab k) (actL 5 pc sc k))

/-- The commute table is sound (checked by the word model). -/
def cmOK (cm : NT) : Bool :=
  (List.range 81).all (fun a => (List.range 81).all (fun b => !(commB cm a b) || modelEq 5 [a, b] [b, a]))

end Submission.PTCert

end
