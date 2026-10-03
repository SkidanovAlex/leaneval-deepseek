import Mathlib
import Submission.Work.OROneRel.mrslDefs
import Submission.Work.OROneRel.rewriteAux_append

/-!
# Expansion of a decorated word (the inverse of the Magnus rewriting)

For a decorated word `D` (a list over `({x : β // x ≠ t} × ℤ) × Bool`) the *expansion* puts back
the `t`-frame: the letter `((x, i), b)` becomes `t ^ i * x ^ b * t ^ (-i)`, and consecutive frames
are merged.  The result is the word

`expWord t D = t ^ (i₁) · x₁ ^ (b₁) · t ^ (i₂ - i₁) · x₂ ^ (b₂) · … · t ^ (-i_m)`,

whose Magnus rewriting (`rewrite t`) is `D` again, and which is reduced as soon as `D` is.

The main statements of this file are

* `expAux_eq_expMid` — the expansion is the "middle" expansion followed by the final `t`-run;
* `rewriteAux_expAux` (`rewriteAux t a (expAux t a D) = D`) — the two operations are inverse;
* `expMid_shift` — shifting all decorations by `c` shifts the initial value of the expansion.

The companion statements — `mk (expAux t a D) = t ^ (-a) * expand t D`, "the expansion of a reduced
decorated word is reduced", and the cyclic reduction of the expansion of a cyclically reduced
decorated word — do *not* live in this file: they are
`Work.OROneRel.mrsl_expAux_mk`, `Work.OROneRel.mrsl_expAux_isReduced` and
`Work.OROneRel.mrsl_expAux_cyclicReduction`, which import this file (so that they may use the
reduction theory below without an import cycle).
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-! ### Definitions -/

/-- The last decoration of a decorated word (`a` itself for the empty word). -/
def lastDec (t : β) : ℤ → List (({x : β // x ≠ t} × ℤ) × Bool) → ℤ
  | a, [] => a
  | _, ((_, i), _) :: rest => lastDec t i rest

/-- The expansion of a decorated word, without its trailing `t`-run. -/
def expMid (t : β) : ℤ → List (({x : β // x ≠ t} × ℤ) × Bool) → List (β × Bool)
  | _, [] => []
  | a, ((c, i), b) :: rest => runLetters t (i - a) ++ (c.1, b) :: expMid t i rest

/-- The expansion of a decorated word: the inverse of the Magnus rewriting `rewrite t`. -/
def expAux (t : β) : ℤ → List (({x : β // x ≠ t} × ℤ) × Bool) → List (β × Bool)
  | a, [] => runLetters t (-a)
  | a, ((c, i), b) :: rest => runLetters t (i - a) ++ (c.1, b) :: expAux t i rest

/-- The expansion of a decorated word, starting at decoration `0`. -/
def expWord (t : β) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) : List (β × Bool) := expAux t 0 D

/-! ### Computation rules -/

theorem lastDec_nil (t : β) (a : ℤ) :
    lastDec t a ([] : List (({x : β // x ≠ t} × ℤ) × Bool)) = a := rfl

theorem lastDec_cons (t : β) (a i : ℤ) (c : {x : β // x ≠ t}) (b : Bool)
    (rest : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    lastDec t a (((c, i), b) :: rest) = lastDec t i rest := rfl

@[simp] theorem expMid_nil (t : β) (a : ℤ) :
    expMid t a ([] : List (({x : β // x ≠ t} × ℤ) × Bool)) = [] := rfl

@[simp] theorem expMid_cons (t : β) (a i : ℤ) (c : {x : β // x ≠ t}) (b : Bool)
    (rest : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    expMid t a (((c, i), b) :: rest) = runLetters t (i - a) ++ (c.1, b) :: expMid t i rest := rfl

@[simp] theorem expAux_nil (t : β) (a : ℤ) :
    expAux t a ([] : List (({x : β // x ≠ t} × ℤ) × Bool)) = runLetters t (-a) := rfl

@[simp] theorem expAux_cons (t : β) (a i : ℤ) (c : {x : β // x ≠ t}) (b : Bool)
    (rest : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    expAux t a (((c, i), b) :: rest) = runLetters t (i - a) ++ (c.1, b) :: expAux t i rest := rfl

/-- The expansion is the "middle" expansion followed by the final `t`-run. -/
theorem expAux_eq_expMid (t : β) (a : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    expAux t a D = expMid t a D ++ runLetters t (-(lastDec t a D)) := by
  induction D generalizing a with
  | nil => rw [expAux_nil, expMid_nil, lastDec_nil, List.nil_append]
  | cons p rest ih =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [expAux_cons, expMid_cons, lastDec_cons, ih i, List.append_assoc, List.cons_append]

/-- The Magnus rewriting inverts the expansion. -/
theorem rewriteAux_expAux (t : β) (a : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    rewriteAux t a (expAux t a D) = D := by
  induction D generalizing a with
  | nil => rw [expAux_nil, rewriteAux_runLetters]
  | cons p rest ih =>
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [expAux_cons, rewriteAux_append, rewriteAux_runLetters, List.nil_append,
      sigmaList_runLetters, show a + (i - a) = i from by ring]
    rw [rewriteAux.eq_2, dif_neg (show ¬((c.1, b).1 = t) from fun h => c.2 h), ih i]

/-- Shifting all decorations by `c` shifts the initial value of the expansion. -/
theorem expMid_shift (t : β) (a c : ℤ) (D : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    expMid t a (D.map (fun p => ((p.1.1, p.1.2 + c), p.2))) = expMid t (a - c) D := by
  induction D generalizing a with
  | nil => rw [List.map_nil, expMid_nil, expMid_nil]
  | cons p rest ih =>
    obtain ⟨⟨x₀, i⟩, b⟩ := p
    rw [List.map_cons, expMid_cons, expMid_cons, ih (i + c), show i + c - c = i from by ring,
      show (i + c) - a = i - (a - c) from by ring]

end Work.OROneRel
