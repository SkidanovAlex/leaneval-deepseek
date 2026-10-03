/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

Vocabulary for the proof of the Freiheitssatz (Magnus 1930) along the lines of
McCool--Schupp / Putman: the exponent sum `sigma t`, the "Magnus rewriting" `rewrite t` of a
word with respect to a letter `t`, its expansion `expand t`, and the homomorphism
`zeta t : F((α \ {t}) × ℤ) →* F α` with `zeta t (s, i) = t ^ i * s * t ^ (-i)`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The exponent sum of the letters `p` of a word that are equal to `t`, with signs. -/
noncomputable def letterSign (t : α) (p : α × Bool) : ℤ := by
  classical
  exact if p.1 = t then (if p.2 then 1 else -1) else 0

/-- The exponent sum in `t` of a word, computed on lists. -/
noncomputable def sigmaList (t : α) (L : List (α × Bool)) : ℤ := (L.map (letterSign t)).sum

/-- The exponent sum in the generator `t`, as a homomorphism `F α →* Multiplicative ℤ`. -/
noncomputable def sigma (t : α) : FreeGroup α →* Multiplicative ℤ := by
  classical
  exact FreeGroup.lift fun a => if a = t then Multiplicative.ofAdd (1 : ℤ) else 1

/-- The "Magnus rewriting" of a word with respect to the letter `t`: the `t`-letters are dropped and
every remaining letter is recorded together with the running exponent sum in `t` before it
(starting from `i`). -/
noncomputable def rewriteAux (t : α) (i : ℤ) (L : List (α × Bool)) :
    List (({a : α // a ≠ t} × ℤ) × Bool) := by
  classical
  exact match L with
    | [] => []
    | p :: L' =>
        if h : p.1 = t then
          rewriteAux t (i + (if p.2 then 1 else -1)) L'
        else
          let q : {a : α // a ≠ t} := ⟨p.1, h⟩
          let r : ({a : α // a ≠ t} × ℤ) × Bool := ((q, i), p.2)
          r :: rewriteAux t i L'

/-- The Magnus rewriting with the indices starting at `0`. -/
noncomputable def rewrite (t : α) (L : List (α × Bool)) : List (({a : α // a ≠ t} × ℤ) × Bool) :=
  rewriteAux t 0 L

/-- The expansion of a letter `((s,i),b)` is `t ^ i * s ^ (b) * t ^ (-i)`. -/
noncomputable def expandLetter (t : α) (p : ({a : α // a ≠ t} × ℤ) × Bool) : FreeGroup α :=
  (FreeGroup.of t) ^ (p.1.2) * ((FreeGroup.of (p.1.1 : α)) ^ (if p.2 then (1 : ℤ) else -1)) *
    (FreeGroup.of t) ^ (-(p.1.2))

/-- The expansion of a rewritten word. -/
noncomputable def expand (t : α) (v : List (({a : α // a ≠ t} × ℤ) × Bool)) : FreeGroup α :=
  (v.map (expandLetter t)).prod

/-- The map `F((α \ {t}) × ℤ) →* F α` sending `(s,i)` to `t ^ i * s * t ^ (-i)`. -/
def zeta (t : α) : FreeGroup ({a : α // a ≠ t} × ℤ) →* FreeGroup α :=
  FreeGroup.lift fun p => (FreeGroup.of t) ^ (p.2) * FreeGroup.of (p.1 : α) * (FreeGroup.of t) ^ (-(p.2))

end Work.OROneRel
