import Submission.E8Numerics
import Submission.E8Orbit

/-!
# A kernel-fast arithmetic engine for the `E₈` characters

The certification of the character of `L(ω₁+ω₈)` (and, eventually, of the tensor-square
constituents) is a *kernel computation*: hypotheses of the form "the candidate multiplicity
function satisfies Freudenthal's recursion" are proved by `decide`.  The bottleneck measured in
SESSION 11/12 is not the arithmetic itself but the *accessory* definitions:

* `CartanMatrix.E₈ i j` is a `Matrix` literal `!![...]`, and evaluating an entry goes through
  `Vector.get`/`List.get` — about `25 ms` per access, i.e. about `0.8 s` per simple reflection, and
  hence `≈ 0.5 s` per dominant-conjugate computation;
* `coords` (a matrix-vector product with the literal `E8inv`) has the same problem;
* `Finset.sum` over `Fin n` costs roughly `4 ms` per summand.

This file provides hand-written replacements (`e8e`, `srefE`, `dcXE`, `mvn`, `md`, `qE`, `BintE`,
`mfunE`) which are *extensionally equal* to the originals (bridges proved below) but whose kernel
evaluation is two orders of magnitude faster (a few `μs` per operation).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

namespace Submission.E8Engine

open Submission.WeylReflect Submission.WeylWeights
open Submission.E8Character Submission.E8Orbit Submission.E8Casimir Submission.E8Numerics

/-- The `E₈` Cartan matrix, hand-coded (avoids `Vector.get`). -/
def e8e (i j : Fin 8) : ℤ :=
  if (i : ℕ) = 0 then
    (if (j : ℕ) = 0 then 2 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then -1 else (if (j : ℕ) = 3 then 0 else (if (j : ℕ) = 4 then 0 else (if (j : ℕ) = 5 then 0 else (if (j : ℕ) = 6 then 0 else 0)))))))
  else if (i : ℕ) = 1 then
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then 2 else (if (j : ℕ) = 2 then 0 else (if (j : ℕ) = 3 then -1 else (if (j : ℕ) = 4 then 0 else (if (j : ℕ) = 5 then 0 else (if (j : ℕ) = 6 then 0 else 0)))))))
  else if (i : ℕ) = 2 then
    (if (j : ℕ) = 0 then -1 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then 2 else (if (j : ℕ) = 3 then -1 else (if (j : ℕ) = 4 then 0 else (if (j : ℕ) = 5 then 0 else (if (j : ℕ) = 6 then 0 else 0)))))))
  else if (i : ℕ) = 3 then
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then -1 else (if (j : ℕ) = 2 then -1 else (if (j : ℕ) = 3 then 2 else (if (j : ℕ) = 4 then -1 else (if (j : ℕ) = 5 then 0 else (if (j : ℕ) = 6 then 0 else 0)))))))
  else if (i : ℕ) = 4 then
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then 0 else (if (j : ℕ) = 3 then -1 else (if (j : ℕ) = 4 then 2 else (if (j : ℕ) = 5 then -1 else (if (j : ℕ) = 6 then 0 else 0)))))))
  else if (i : ℕ) = 5 then
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then 0 else (if (j : ℕ) = 3 then 0 else (if (j : ℕ) = 4 then -1 else (if (j : ℕ) = 5 then 2 else (if (j : ℕ) = 6 then -1 else 0)))))))
  else if (i : ℕ) = 6 then
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then 0 else (if (j : ℕ) = 3 then 0 else (if (j : ℕ) = 4 then 0 else (if (j : ℕ) = 5 then -1 else (if (j : ℕ) = 6 then 2 else -1)))))))
  else
    (if (j : ℕ) = 0 then 0 else (if (j : ℕ) = 1 then 0 else (if (j : ℕ) = 2 then 0 else (if (j : ℕ) = 3 then 0 else (if (j : ℕ) = 4 then 0 else (if (j : ℕ) = 5 then 0 else (if (j : ℕ) = 6 then -1 else 2)))))))

lemma e8e_eq (i j : Fin 8) : e8e i j = (CartanMatrix.E₈ i j : ℤ) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The simple reflection with the hand-coded Cartan matrix. -/
def srefE (i : Fin 8) (v : Fin 8 → ℤ) : Fin 8 → ℤ := fun j => v j - v i * e8e i j

lemma srefE_eq (i : Fin 8) (v : Fin 8 → ℤ) : srefE i v = sref i v := by
  funext j
  rw [srefE, sref_apply, e8e_eq]
  simp

/-- The `n`-step dominant-conjugate algorithm with the fast reflection. -/
def dclE : ℕ → (Fin 8 → ℤ) → (Fin 8 → ℤ)
  | 0, v => v
  | n + 1, v => match pickNegF v with
      | some i => dclE n (srefE i v)
      | none => v

/-- The kernel-fast dominant conjugate. -/
def dcXE (v : Fin 8 → ℤ) : Fin 8 → ℤ := dclE 130 v

lemma dclE_eq : ∀ (n : ℕ) (v : Fin 8 → ℤ), dclE n v = dcl n v := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    rw [dclE, dcl]
    cases h : pickNegF v with
    | none => rfl
    | some i =>
      simp only [h]
      rw [ih, srefE_eq]

lemma dcXE_eq (v : Fin 8 → ℤ) : dcXE v = dcX v := by
  rw [dcXE, dcX, dclE_eq]

/-- The hand-coded `E₈⁻¹` matrix-vector product. -/
def mvn (v : Fin 8 → ℤ) : Fin 8 → ℤ := fun i =>
  if (i : ℕ) = 0 then 4*v 0 + 5*v 1 + 7*v 2 + 10*v 3 + 8*v 4 + 6*v 5 + 4*v 6 + 2*v 7
  else if (i : ℕ) = 1 then 5*v 0 + 8*v 1 + 10*v 2 + 15*v 3 + 12*v 4 + 9*v 5 + 6*v 6 + 3*v 7
  else if (i : ℕ) = 2 then 7*v 0 + 10*v 1 + 14*v 2 + 20*v 3 + 16*v 4 + 12*v 5 + 8*v 6 + 4*v 7
  else if (i : ℕ) = 3 then 10*v 0 + 15*v 1 + 20*v 2 + 30*v 3 + 24*v 4 + 18*v 5 + 12*v 6 + 6*v 7
  else if (i : ℕ) = 4 then 8*v 0 + 12*v 1 + 16*v 2 + 24*v 3 + 20*v 4 + 15*v 5 + 10*v 6 + 5*v 7
  else if (i : ℕ) = 5 then 6*v 0 + 9*v 1 + 12*v 2 + 18*v 3 + 15*v 4 + 12*v 5 + 8*v 6 + 4*v 7
  else if (i : ℕ) = 6 then 4*v 0 + 6*v 1 + 8*v 2 + 12*v 3 + 10*v 4 + 8*v 5 + 6*v 6 + 3*v 7
  else 2*v 0 + 3*v 1 + 4*v 2 + 6*v 3 + 5*v 4 + 4*v 5 + 3*v 6 + 2*v 7

def invE (i j : Fin 8) : ℤ :=
  if (i : ℕ) = 0 then
    (if (j : ℕ) = 0 then 4 else (if (j : ℕ) = 1 then 5 else (if (j : ℕ) = 2 then 7 else (if (j : ℕ) = 3 then 10 else (if (j : ℕ) = 4 then 8 else (if (j : ℕ) = 5 then 6 else (if (j : ℕ) = 6 then 4 else 2)))))))
  else if (i : ℕ) = 1 then
    (if (j : ℕ) = 0 then 5 else (if (j : ℕ) = 1 then 8 else (if (j : ℕ) = 2 then 10 else (if (j : ℕ) = 3 then 15 else (if (j : ℕ) = 4 then 12 else (if (j : ℕ) = 5 then 9 else (if (j : ℕ) = 6 then 6 else 3)))))))
  else if (i : ℕ) = 2 then
    (if (j : ℕ) = 0 then 7 else (if (j : ℕ) = 1 then 10 else (if (j : ℕ) = 2 then 14 else (if (j : ℕ) = 3 then 20 else (if (j : ℕ) = 4 then 16 else (if (j : ℕ) = 5 then 12 else (if (j : ℕ) = 6 then 8 else 4)))))))
  else if (i : ℕ) = 3 then
    (if (j : ℕ) = 0 then 10 else (if (j : ℕ) = 1 then 15 else (if (j : ℕ) = 2 then 20 else (if (j : ℕ) = 3 then 30 else (if (j : ℕ) = 4 then 24 else (if (j : ℕ) = 5 then 18 else (if (j : ℕ) = 6 then 12 else 6)))))))
  else if (i : ℕ) = 4 then
    (if (j : ℕ) = 0 then 8 else (if (j : ℕ) = 1 then 12 else (if (j : ℕ) = 2 then 16 else (if (j : ℕ) = 3 then 24 else (if (j : ℕ) = 4 then 20 else (if (j : ℕ) = 5 then 15 else (if (j : ℕ) = 6 then 10 else 5)))))))
  else if (i : ℕ) = 5 then
    (if (j : ℕ) = 0 then 6 else (if (j : ℕ) = 1 then 9 else (if (j : ℕ) = 2 then 12 else (if (j : ℕ) = 3 then 18 else (if (j : ℕ) = 4 then 15 else (if (j : ℕ) = 5 then 12 else (if (j : ℕ) = 6 then 8 else 4)))))))
  else if (i : ℕ) = 6 then
    (if (j : ℕ) = 0 then 4 else (if (j : ℕ) = 1 then 6 else (if (j : ℕ) = 2 then 8 else (if (j : ℕ) = 3 then 12 else (if (j : ℕ) = 4 then 10 else (if (j : ℕ) = 5 then 8 else (if (j : ℕ) = 6 then 6 else 3)))))))
  else
    (if (j : ℕ) = 0 then 2 else (if (j : ℕ) = 1 then 3 else (if (j : ℕ) = 2 then 4 else (if (j : ℕ) = 3 then 6 else (if (j : ℕ) = 4 then 5 else (if (j : ℕ) = 5 then 4 else (if (j : ℕ) = 6 then 3 else 2)))))))

lemma E8inv_eq_fun : E8inv = invE := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The hand-coded `8`-term dot product. -/
def md (x y : Fin 8 → ℤ) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 +
  x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7

lemma md_eq (x y : Fin 8 → ℤ) : md x y = ∑ i, x i * y i := by
  simp [md, Fin.sum_univ_eight]

lemma mvn_eq (v : Fin 8 → ℤ) : mvn v = Matrix.mulVec E8inv v := by
  rw [E8inv_eq_fun]
  funext i
  fin_cases i <;>
    (simp (config := { decide := true }) only
      [mvn, Matrix.mulVec, dotProduct, Fin.sum_univ_eight, invE, ↓reduceIte])

/-- The 120 positive roots, hand-coded as a `Fin 120`-indexed **balanced** decision tree
(avoids both `List.get` and the linear scan of a 120-branch chain). -/
def pRn (j : Fin 120) : Fin 8 → ℤ := fun i =>
  (if (j : ℕ) < 60 then
    (if (j : ℕ) < 30 then
      (if (j : ℕ) < 15 then
        (if (j : ℕ) < 7 then
          (if (j : ℕ) < 3 then
            (if (j : ℕ) < 1 then
              (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 2)))))))
            else
              (if (j : ℕ) < 2 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 2 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 5 then
              (if (j : ℕ) < 4 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 2 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            else
              (if (j : ℕ) < 6 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 2 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 11 then
            (if (j : ℕ) < 9 then
              (if (j : ℕ) < 8 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            else
              (if (j : ℕ) < 10 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 2 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 13 then
              (if (j : ℕ) < 12 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            else
              (if (j : ℕ) < 14 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            )
          )
        )
      else
        (if (j : ℕ) < 22 then
          (if (j : ℕ) < 18 then
            (if (j : ℕ) < 16 then
              (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 2 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
            else
              (if (j : ℕ) < 17 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 20 then
              (if (j : ℕ) < 19 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            else
              (if (j : ℕ) < 21 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 2 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 26 then
            (if (j : ℕ) < 24 then
              (if (j : ℕ) < 23 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 25 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            )
          else
            (if (j : ℕ) < 28 then
              (if (j : ℕ) < 27 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 29 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            )
          )
        )
      )
    else
      (if (j : ℕ) < 45 then
        (if (j : ℕ) < 37 then
          (if (j : ℕ) < 33 then
            (if (j : ℕ) < 31 then
              (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
            else
              (if (j : ℕ) < 32 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 35 then
              (if (j : ℕ) < 34 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            else
              (if (j : ℕ) < 36 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 41 then
            (if (j : ℕ) < 39 then
              (if (j : ℕ) < 38 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            else
              (if (j : ℕ) < 40 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 43 then
              (if (j : ℕ) < 42 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 2 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 44 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          )
        )
      else
        (if (j : ℕ) < 52 then
          (if (j : ℕ) < 48 then
            (if (j : ℕ) < 46 then
              (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
            else
              (if (j : ℕ) < 47 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            )
          else
            (if (j : ℕ) < 50 then
              (if (j : ℕ) < 49 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 51 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 56 then
            (if (j : ℕ) < 54 then
              (if (j : ℕ) < 53 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            else
              (if (j : ℕ) < 55 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 58 then
              (if (j : ℕ) < 57 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            else
              (if (j : ℕ) < 59 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            )
          )
        )
      )
    )
  else
    (if (j : ℕ) < 90 then
      (if (j : ℕ) < 75 then
        (if (j : ℕ) < 67 then
          (if (j : ℕ) < 63 then
            (if (j : ℕ) < 61 then
              (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 1)))))))
            else
              (if (j : ℕ) < 62 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 65 then
              (if (j : ℕ) < 64 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 66 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 71 then
            (if (j : ℕ) < 69 then
              (if (j : ℕ) < 68 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            else
              (if (j : ℕ) < 70 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 73 then
              (if (j : ℕ) < 72 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            else
              (if (j : ℕ) < 74 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            )
          )
        )
      else
        (if (j : ℕ) < 82 then
          (if (j : ℕ) < 78 then
            (if (j : ℕ) < 76 then
              (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else -1)))))))
            else
              (if (j : ℕ) < 77 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else -1)))))))
              )
            )
          else
            (if (j : ℕ) < 80 then
              (if (j : ℕ) < 79 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else 0)))))))
              )
            else
              (if (j : ℕ) < 81 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 86 then
            (if (j : ℕ) < 84 then
              (if (j : ℕ) < 83 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 85 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else -1)))))))
              )
            )
          else
            (if (j : ℕ) < 88 then
              (if (j : ℕ) < 87 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else -1)))))))
              )
            else
              (if (j : ℕ) < 89 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else 0)))))))
              )
            )
          )
        )
      )
    else
      (if (j : ℕ) < 105 then
        (if (j : ℕ) < 97 then
          (if (j : ℕ) < 93 then
            (if (j : ℕ) < 91 then
              (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else -1)))))))
            else
              (if (j : ℕ) < 92 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 95 then
              (if (j : ℕ) < 94 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else -1)))))))
              )
            else
              (if (j : ℕ) < 96 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 101 then
            (if (j : ℕ) < 99 then
              (if (j : ℕ) < 98 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 100 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 103 then
              (if (j : ℕ) < 102 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 104 then
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          )
        )
      else
        (if (j : ℕ) < 112 then
          (if (j : ℕ) < 108 then
            (if (j : ℕ) < 106 then
              (if (i : ℕ) = 0 then -1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
            else
              (if (j : ℕ) < 107 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else -1)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then -1 else 1)))))))
              )
            )
          else
            (if (j : ℕ) < 110 then
              (if (j : ℕ) < 109 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 1 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 111 then
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          )
        else
          (if (j : ℕ) < 116 then
            (if (j : ℕ) < 114 then
              (if (j : ℕ) < 113 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then -1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 1 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then -1 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            else
              (if (j : ℕ) < 115 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 1 else (if (i : ℕ) = 2 then 1 else (if (i : ℕ) = 3 then -1 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 1 else (if (i : ℕ) = 4 then -1 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 0)))))))
              )
            )
          else
            (if (j : ℕ) < 118 then
              (if (j : ℕ) < 117 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 1 else (if (i : ℕ) = 5 then -1 else (if (i : ℕ) = 6 then 0 else 0)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 1 else (if (i : ℕ) = 6 then -1 else 0)))))))
              )
            else
              (if (j : ℕ) < 119 then
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 1 else -1)))))))
              else
                (if (i : ℕ) = 0 then 0 else (if (i : ℕ) = 1 then 0 else (if (i : ℕ) = 2 then 0 else (if (i : ℕ) = 3 then 0 else (if (i : ℕ) = 4 then 0 else (if (i : ℕ) = 5 then 0 else (if (i : ℕ) = 6 then 0 else 1)))))))
              )
            )
          )
        )
      )
    )
  )

lemma posR_eq_ofFn : posR = List.ofFn pRn := by decide

lemma pRn_eq : pRn = pR := by decide

/-! ## The fast quadratic form, `Bint`, the candidate character, and `brk` -/

/-- The integral squared length `⟪v,v⟫`, fast. -/
def qE (v : Fin 8 → ℤ) : ℤ := md v (mvn v)

lemma qE_eq_qq (v : Fin 8 → ℤ) : qE v = qq v := by
  simp only [qE, md_eq, qq, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ,
    mvn_eq, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The height `⟪v,ρ⟫` (= sum of the simple-root coordinates), fast. -/
def htO (v : Fin 8 → ℤ) : ℤ := md (fun _ => 1) (mvn v)

lemma htO_eq (v : Fin 8 → ℤ) : htO v = htOf v := by
  simp only [htO, md_eq, htOf, coords_eq, mvn_eq, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The norm test, fast. -/
def normOkE (v : Fin 8 → ℤ) : Bool := normTable (qE v)

/-- **The candidate character of `L(ω₁+ω₈)`**, fast. -/
def mfunE (v : Fin 8 → ℤ) : ℤ := if normOkE v then tab (dcXE v) else 0

lemma normOkE_eq (v : Fin 8 → ℤ) : normOkE v = normOk v := by
  simp only [normOkE, normOk, qE_eq_qq]

theorem mfunE_eq_mfun (v : Fin 8 → ℤ) : mfunE v = mfun v := by
  simp only [mfunE, normOkE_eq, dcXE_eq, mfun, mfunAux]

/-- `Bint ν = ∑ᵢ ∑ⱼ (νᵢ+1) · (A⁻¹)ᵢⱼ · (νⱼ+1)`, fast. -/
def BintE (ν : Fin 8 → ℤ) : ℤ := md (fun i => ν i + 1) (mvn (fun i => ν i + 1))

lemma BintE_eq (ν : Fin 8 → ℤ) : BintE ν = Bint ν := by
  simp only [BintE, md_eq, Bint, mvn_eq, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `brk μ j = ⟪μ, α_j∨⟫`, fast (`pR` replaced by `mvn`). -/
def brkE (μ : Fin 8 → ℤ) (j : Fin 120) : ℤ := md μ (mvn (pR j))

lemma brkE_eq (μ : Fin 8 → ℤ) (j : Fin 120) : brkE μ j = brk μ j := by
  simp only [brkE, brk, md_eq]
  congr 1
  funext i
  have h : mvn (pR j) = coords (pR j) := by rw [mvn_eq, ← coords_eq]
  rw [h]

/-- `brk` with the fast root lookup. -/
def brkF (μ : Fin 8 → ℤ) (j : Fin 120) : ℤ := md μ (mvn (pRn j))

lemma brkF_eq (μ : Fin 8 → ℤ) (j : Fin 120) : brkF μ j = brk μ j := by
  rw [brkF, congrFun pRn_eq j]
  exact brkE_eq μ j

/-- Coordinatewise scalar multiplication, `(k • x) i = k * x i`: unlike `nsmul` it evaluates the
vector `x` only once. -/
def smulE (k : ℕ) (x : Fin 8 → ℤ) : Fin 8 → ℤ := fun i => (k : ℤ) * x i

lemma smulE_eq (k : ℕ) (x : Fin 8 → ℤ) : smulE k x = k • x := by
  funext i
  simp [smulE, Pi.smul_apply, nsmul_eq_mul]

/-- The summand of the Freudenthal recursion, as a function of the weight `η = ν + k·α_j`.
Bundling it this way shares the computation of `η` between the two occurrences (the kernel does
not share across the two textual occurrences in the raw recursion statement). -/
def Gfun (m : (Fin 8 → ℤ) → ℤ) (η : Fin 8 → ℤ) (j : Fin 120) : ℤ := brkF η j * m η

/-- `brk` with the root passed as an argument (so it is not recomputed). -/
def brkR (μ r : Fin 8 → ℤ) : ℤ := md μ (mvn r)

lemma brkR_eq (μ : Fin 8 → ℤ) (j : Fin 120) : brkR μ (pRn j) = brk μ j := by
  rw [brkR, congrFun pRn_eq j]
  exact brkE_eq μ j

/-- The summand of the Freudenthal recursion with the root as an argument. -/
def GfunR (m : (Fin 8 → ℤ) → ℤ) (η r : Fin 8 → ℤ) : ℤ := brkR η r * m η

/-- The inner Freudenthal sum, accumulating the shifted weight `μ` recursively so that `μ` is a
*variable* in the body (the kernel does not share the value of a `let`, so passing it as a
parameter is the only way to avoid recomputing it at every access). -/
def freudJ (m : (Fin 8 → ℤ) → ℤ) : ℕ → (Fin 8 → ℤ) → (Fin 8 → ℤ) → ℤ
  | 0, _, _ => 0
  | (n + 1), μ, r => GfunR m (μ + r) r + freudJ m n (μ + r) r

/-- The Freudenthal recursion sum over all positive roots. -/
def freudS (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) (N : ℕ) : ℤ :=
  (List.finRange 120).foldl (fun a j => a + freudJ m N ν (pRn j)) 0

/-- The Freudenthal recursion sum, with the fast root lookup. -/
def freud (m : (Fin 8 → ℤ) → ℤ) (ν : Fin 8 → ℤ) (N : ℕ) : ℤ :=
  2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 N, Gfun m (ν + k • pRn j) j


/-! ## The bilinear form and the quadratic formula for the norm of `ν + k·αⱼ`

`⟪ν + kα, ν + kα⟫ = ⟪ν,ν⟫ + 2k⟪ν,α⟫ + k²⟪α,α⟫`, and for a root `α` one has `⟪α,α⟫ = 2`.  This
lets the *norm test* of the Freudenthal summand be evaluated by a short arithmetic expression
instead of by building the weight `ν + k·αⱼ` (whose construction is the kernel bottleneck). -/

/-- The symmetric bilinear form `⟪x,y⟫ = x ⬝ A⁻¹ y`, fast. -/
def bq (x y : Fin 8 → ℤ) : ℤ := md x (mvn y)

lemma bq_eq (x y : Fin 8 → ℤ) : bq x y = ∑ i, ∑ l, x i * E8inv i l * y l := by
  simp only [bq, md_eq, mvn_eq, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma E8inv_symm (i j : Fin 8) : E8inv i j = E8inv j i := by
  fin_cases i <;> fin_cases j <;> decide

lemma bq_add_left (x y z : Fin 8 → ℤ) : bq (x + y) z = bq x z + bq y z := by
  rw [bq_eq, bq_eq, bq_eq]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma bq_add_right (x y z : Fin 8 → ℤ) : bq x (y + z) = bq x y + bq x z := by
  rw [bq_eq, bq_eq, bq_eq]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma bq_smul_left (k : ℕ) (x y : Fin 8 → ℤ) : bq (k • x) y = (k : ℤ) * bq x y := by
  rw [bq_eq, bq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

lemma bq_smul_right (k : ℕ) (x y : Fin 8 → ℤ) : bq x (k • y) = (k : ℤ) * bq x y := by
  rw [bq_eq, bq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

/-- The quadratic formula for the norm of `ν + k·r` (no symmetry of the form is used: the two
cross terms are kept separately). -/
lemma qE_add_smul (x z : Fin 8 → ℤ) (k : ℕ) :
    qE (x + k • z) = qE x + (k : ℤ) * (bq x z + bq z x) + (k : ℤ) ^ 2 * qE z := by
  show bq (x + k • z) (x + k • z)
    = bq x x + (k : ℤ) * (bq x z + bq z x) + (k : ℤ) ^ 2 * bq z z
  rw [bq_add_left, bq_add_right, bq_add_right, bq_smul_left, bq_smul_right,
    bq_smul_left, bq_smul_right]
  ring

lemma bq_pRn_eq (ν : Fin 8 → ℤ) (j : Fin 120) : bq ν (pRn j) = brkF ν j := rfl

/-- A positive root has squared length `2`. -/
lemma qE_pRn (j : Fin 120) : qE (pRn j) = 2 := by
  rw [qE_eq_qq, congrFun pRn_eq j]
  exact pR_qZ j

/-- The **quadratic formula for the norm** of `ν + k·αⱼ`: a short arithmetic expression, evaluated
without ever building the weight `ν + k·αⱼ`. -/
def quad (ν : Fin 8 → ℤ) (j : Fin 120) (k : ℕ) : ℤ :=
  qE ν + (k : ℤ) * (bq ν (pRn j) + bq (pRn j) ν) + 2 * (k : ℤ) ^ 2

lemma quad_eq_qE (ν : Fin 8 → ℤ) (j : Fin 120) (k : ℕ) :
    quad ν j k = qE (ν + k • pRn j) := by
  rw [quad, qE_add_smul, qE_pRn]
  ring

end Submission.E8Engine
