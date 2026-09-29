import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.KronP.defs

/-!
# KronP: the specifications of the Kronecker word's pieces

Each `Prop` below is the statement of one delegated lemma about the Kronecker word
(paper Lemma 2.5).  `Submission/Work/KronP/kronecker.lean` assembles them into
`Work.ConvR.KroneckerSpec`.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-- `setup`: push the four constants `3p, 2r, C, D` above `int p, int r`. -/
def SetupSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p r : ℕ) (P Q : Val) (rest : List Val),
      1 ≤ p → 2 ≤ r → IsPow2 r →
      WordR main prog
        (fun vs => vs = .int (p : ℤ) :: .int (r : ℤ) :: P :: Q :: rest)
        (fun _ out => out = .int (3 * p : ℤ) :: .int (2 * r : ℤ) ::
            .int (digitOffset p (2 * r)) :: .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: P :: Q :: rest)
        (fun _ => K * (r + 1) * (p + 1) ^ 2)

/-- `splitPack`: split the two coefficient vectors and pack the four coordinate lists. -/
def SplitPackSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val),
      1 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) → InDiscVec p r u → InDiscVec p r v →
      WordR main prog
        (fun vs => vs = .int (3 * p : ℤ) :: .int (2 * r : ℤ) ::
            .int (digitOffset p (2 * r)) :: .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: cvecVal u :: cvecVal v :: rest)
        (fun _ out => out = zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p] ::
            zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p] ::
            .int (3 * p : ℤ) :: .int (2 * r : ℤ) :: .int (digitOffset p (2 * r)) ::
            .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: rest)
        (fun _ => K * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))

/-- `prodDigits`: one packed product (with `Cmd.self`), offset and base-`2^b` digit extraction. -/
def ProdDigitsSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
    MulBelow main N Cm → ∀ (X Y : ℤ) (b n : ℕ) (C : ℤ) (rest : List Val),
      X.natAbs.size < N → Y.natAbs.size < N → 1 ≤ b → 1 ≤ n → 0 ≤ X * Y + C →
      X * Y + C < 2 ^ (b * n) →
      WordR main prog
        (fun vs => vs = .int X :: .int Y :: .int (b : ℤ) :: .int (n : ℤ) :: .int C :: rest)
        (fun _ out => out = intList (chunks (X * Y + C).toNat b n) ::
            .int (b : ℤ) :: .int (n : ℤ) :: .int C :: rest)
        (fun _ => Cm (max X.natAbs.size Y.natAbs.size) +
          K * (X.natAbs.size + Y.natAbs.size + (n + 1) * (b + 1) + C.natAbs.size + 1))

/-- `combine`: negacyclic fold, coefficientwise subtraction/addition and truncating division. -/
def CombineSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p r : ℕ) (A00 A01 A10 A11 : List ℕ) (rest : List Val),
      A00.length = 2 * r → A01.length = 2 * r → A10.length = 2 * r → A11.length = 2 * r →
      (∀ A ∈ [A00, A01, A10, A11], ∀ m, m < 2 * r → A.getD m 0 < 2 ^ (3 * p)) →
      2 ≤ r → 1 ≤ p →
      WordR main prog
        (fun vs => vs = ofList [intList A00, intList A11, intList A01, intList A10] ::
            .int (3 * p : ℤ) :: .int (2 * r : ℤ) :: .int (digitOffset p (2 * r)) ::
            .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: rest)
        (fun _ out => out = cvecVal (kronW p r A00 A01 A10 A11) :: rest)
        (fun _ => K * (r + 1) * (p + 1) ^ 2)

/-- The arithmetic needed to know that `chunk` applies to the four packed products:
`X·Y + C` is nonnegative and has at most `2r` base-`2^{3p}` digits. -/
def ProdOffsetSpec : Prop :=
  ∀ (p r : ℕ), 1 ≤ p → r < 2 ^ (p - 1) →
    ∀ (l₁ l₂ : List ℤ), l₁.length = r → l₂.length = r →
      (∀ x ∈ l₁, x.natAbs ≤ 2 ^ p) → (∀ x ∈ l₂, x.natAbs ≤ 2 ^ p) →
      0 ≤ pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r) ∧
        pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r) < (2 : ℤ) ^ (3 * p * (2 * r))

/-- The four packed products, via `KernelLib.zipWith`. -/
def ZipFourSpec : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm →
    MulBelow main N Cm → ∀ (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val),
      1 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) → InDiscVec p r u → InDiscVec p r v → 3 * r * p < N →
      WordR main prog
        (fun vs => vs = zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p] ::
            zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p] ::
            .int (3 * p : ℤ) :: .int (2 * r : ℤ) :: .int (digitOffset p (2 * r)) ::
            .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: rest)
        (fun _ out => out = ofList [intList (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p)),
              intList (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)),
              intList (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p)),
              intList (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p))] ::
            .int (3 * p : ℤ) :: .int (2 * r : ℤ) :: .int (digitOffset p (2 * r)) ::
            .int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            .int (p : ℤ) :: .int (r : ℤ) :: rest)
        (fun _ => 4 * Cm (3 * r * p) + K * (r + 1) * (p + 1) ^ 2)

/-- The mathematical content of Lemma 2.5 for `kronVec`. -/
def KronFinalSpec : Prop :=
  ∀ {p r : ℕ}, r = 2 ^ (Nat.clog 2 r) → 2 ≤ r → r < 2 ^ (p - 1) →
    ∀ {u v : List (ℤ × ℤ)}, InDiscVec p r u → InDiscVec p r v →
    InDiscVec p r (kronVec p r u v) ∧
      ∀ j : Fin r, (2 : ℝ) ^ p * ‖fxC p ((kronVec p r u v).getD j (0, 0)) -
        ((r : ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2

end Work.KronP
