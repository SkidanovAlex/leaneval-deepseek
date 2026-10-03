/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus rewriting with respect to a homomorphism `F α →* ℤ`

The exponent-sum-zero case of the Magnus--Moldavanskii step (`eps t u = 0` for a *letter* `t`) is
handled by the rewriting `magRew t` of `MagnusRewrite.lean` and `rewriteAux t` of
`FreiheitssatzDefs.lean`, whose decorations are the exponent sums in `t`.

For the *complementary* case of the Magnus step -- no letter of the relator has vanishing exponent
sum -- the rewriting must be taken with respect to an arbitrary homomorphism `cohom c : F α →* ℤ`
given by integer weights `c : α → ℤ` on the generators: one chooses `c` with `cohom c u = 1`
(i.e. `c` kills the relator) and an element `τ` with `cohom c τ = 1`, and the symbols of the
rewriting then stand for the conjugates `τ ^ i * x * τ ^ (-i - c x)`.

This file contains definitions only (no `sorry`), so that lemma requests may import it.

The shared reduced-word function `wordOf` (and `mk_wordOf`) lives in
`Submission.Work.OROneRel.wordOfDefs`, imported below: it is used by this file and by the Weinbaum/pad
development, and keeping a single copy is what allows a file to import both.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The homomorphism `F α →* Multiplicative ℤ` given by the integer weights `c` on the generators. -/
noncomputable def cohom (c : α → ℤ) : FreeGroup α →* Multiplicative ℤ :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (c a)

@[simp] theorem cohom_of (c : α → ℤ) (a : α) :
    cohom c (FreeGroup.of a) = Multiplicative.ofAdd (c a) := by
  classical
  rw [cohom, FreeGroup.lift_apply_of]

/-- The weight of a word, computed on lists. -/
noncomputable def lsig (c : α → ℤ) (L : List (α × Bool)) : ℤ :=
  (L.map fun p => if p.2 then c p.1 else -c p.1).sum

/-- The Magnus map attached to the weights `c` and the element `τ`: the symbol `(x, i)` is sent to
the conjugate `τ ^ i * x * τ ^ (-i - c x)`. -/
noncomputable def rhoC (τ : FreeGroup α) (c : α → ℤ) : FreeGroup (α × ℤ) →* FreeGroup α :=
  FreeGroup.lift fun p => τ ^ p.2 * FreeGroup.of p.1 * τ ^ (-(p.2) - c p.1)

/-- The decoration of a word by the running weight.  The letter `(x, true)` read at running weight
`i` becomes the symbol `((x, i), true)` (whose expansion is the frame `τ ^ i * x * τ ^ (-i - c x)`,
i.e. the frame running from level `i` to `i + c x`), while the letter `(x, false)` read at running
weight `i` becomes the symbol `((x, i - c x), false)`: the expansion of `(x, j)⁻¹` is
`τ ^ (j + c x) * x⁻¹ * τ ^ (-j)`, which is the frame running from level `i` down to `i - c x`.  With
this convention `rhoC_decor` telescopes: the product of the expansions of the decorated letters is
`τ ^ i * (the word) * τ ^ (-(i + lsig))`. -/
noncomputable def decor (c : α → ℤ) : ℤ → List (α × Bool) → List ((α × ℤ) × Bool)
  | _, [] => []
  | i, (a, true) :: L => ((a, i), true) :: decor c (i + c a) L
  | i, (a, false) :: L => ((a, i - c a), false) :: decor c (i - c a) L

/-- The Magnus rewriting of an element, over the full symbol type `α × ℤ`. -/
noncomputable def rew (c : α → ℤ) (w : FreeGroup α) : FreeGroup (α × ℤ) :=
  letI := Classical.decEq α
  FreeGroup.mk (decor c 0 (wordOf w))

/-- The set of levels at which symbols of the rewriting of `u` occur. -/
def levSet (c : α → ℤ) (u : FreeGroup α) : Set ℤ :=
  {i | ∃ (x : α) (b : Bool), ((x, i), b) ∈ decor c 0 (wordOf u)}

theorem mem_levSet {c : α → ℤ} {u : FreeGroup α} {i : ℤ} :
    i ∈ levSet c u ↔ ∃ (x : α) (b : Bool), ((x, i), b) ∈ decor c 0 (wordOf u) :=
  Iff.rfl

/-- The (finite) symbol type of the rewriting: the symbols `(x,i)` whose level `i` occurs in the
rewriting of `u`.  This is the generating type of the base group of the Magnus decomposition of
`⟨α | u ^ l⟩`. -/
abbrev magBeta (c : α → ℤ) (u : FreeGroup α) : Type u := {p : α × ℤ // p.2 ∈ levSet c u}

/-- The word of the rewriting, as a list over the restricted symbol type. -/
noncomputable def rewList (c : α → ℤ) (u : FreeGroup α) : List (magBeta c u × Bool) :=
  letI := Classical.decEq α
  (decor c 0 (wordOf u)).attach.map (fun p =>
    (⟨p.1.1, mem_levSet.mpr ⟨p.1.1.1, p.1.2, p.2⟩⟩, p.1.2))

/-- The word of the rewriting, as an element of the free group on the restricted symbol type. -/
noncomputable def rewIn (c : α → ℤ) (u : FreeGroup α) : FreeGroup (magBeta c u) :=
  letI := Classical.decEq α
  FreeGroup.mk (rewList c u)

/-- The inclusion of the restricted symbol type into `α × ℤ`, as a homomorphism of free groups. -/
def magIncl (c : α → ℤ) (u : FreeGroup α) : FreeGroup (magBeta c u) →* FreeGroup (α × ℤ) :=
  FreeGroup.map fun p => p.1

theorem map_rewList (c : α → ℤ) (u : FreeGroup α) :
    (rewList c u).map (fun p => (((p.1 : magBeta c u) : α × ℤ), p.2)) = decor c 0 (wordOf u) := by
  classical
  rw [rewList, List.map_map]
  trans (decor c 0 (wordOf u)).attach.map Subtype.val
  · congr 1
  · exact List.attach_map_subtype_val _

theorem magIncl_rewIn (c : α → ℤ) (u : FreeGroup α) :
    magIncl c u (rewIn c u) = rew c u := by
  classical
  show FreeGroup.map (fun p : magBeta c u => (p : α × ℤ)) (FreeGroup.mk (rewList c u)) =
    FreeGroup.mk (decor c 0 (wordOf u))
  rw [FreeGroup.map.mk]
  congr 1
  exact map_rewList c u

end Work.OROneRel
