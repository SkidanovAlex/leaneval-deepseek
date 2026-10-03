/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The padding construction for the "no zero exponent sum" case of Weinbaum's theorem

This file contains only definitions and the most elementary facts.

Given a relator `r : FreeGroup α` and a function `c : α → ℤ`, we consider the *padded* free group
`F (Option α)`, where `none` is a fresh letter `z` and `some a` is the letter `a`, and the
homomorphism

`padHom c : F α →* F (Option α),  padHom c a = a * z ^ (c a) * a`

(the *padding*).  The `padHom c`-image of a relator is called `padRel c r = padHom c r`.

Why this shape: if `r` is cyclically reduced and not a proper power, and `¬ IsProperPower r`, then
for a suitable choice of `c` the padded relator `padRel c r` has the following properties, which
are exactly what is needed to reduce the case of Weinbaum's theorem in which every letter has
nonzero exponent sum to the exponent-sum-zero case (the file
`Submission/Work/OROneRel/weinbaumAt_of_expSum_ne_zero`):

* `padHom c` is injective (it is the composition of a retraction with the "square each generator"
  homomorphism), so a nontrivial subword stays nontrivial;
* because every block `a z ^ (c a) a` starts and ends with its own letter, the block concatenation
  of a reduced word is reduced: there is no cancellation, so the length of a padded word is exactly
  the sum of the lengths of the blocks, and a subword of a power of `r` is sent to a subword of a
  power of `padRel c r`;
* `expSum none (padRel c r) = 1` for the choice below, i.e. the fresh letter `z` has *zero*
  exponent sum in the padded relator;
* the fresh letter `none` occurs in `padRel c r`.

The choice of `c` used below is `c x = σ_t r`, `c t = -σ_x r` for two distinct letters `x ≠ t` of
`r` (and `c = 0` elsewhere); then `Σ_a σ_a r * c a = 0`, which is exactly the exponent-sum
condition for the fresh letter.
-/
import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.weinbaumMonoDefs
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.case2_substitution
import Submission.Work.OROneRel.exists_common_power

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The padded generating type: `none` is the fresh padding letter, `some a` is `a`. -/
abbrev PadT (α : Type u) := Option α

/-- The image of the generator `a` under the padding: `a * z ^ (c a) * a`. -/
noncomputable def padGen (c : α → ℤ) (a : α) : FreeGroup (PadT α) :=
  FreeGroup.of (some a) * (FreeGroup.of (none : PadT α)) ^ (c a) * FreeGroup.of (some a)

/-- The padding homomorphism `F α →* F (Option α)`: `a ↦ a * z ^ (c a) * a`. -/
noncomputable def padHom (c : α → ℤ) : FreeGroup α →* FreeGroup (PadT α) :=
  FreeGroup.lift (padGen c)

/-- The projection killing the padding letter: `z ↦ 1`, `a ↦ a`. -/
noncomputable def padProj : FreeGroup (PadT α) →* FreeGroup α :=
  FreeGroup.lift (fun o : Option α => Option.elim o 1 (fun a => FreeGroup.of a))

/-- The padded relator. -/
noncomputable def padRel (c : α → ℤ) (r : FreeGroup α) : FreeGroup (PadT α) := padHom c r

/-- The padding exponents attached to two distinct letters `x ≠ t` of a relator `r`:
`c x = σ_t r`, `c t = -σ_x r`, and `c a = 0` for every other letter.  With this choice the fresh
padding letter has exponent sum `Σ_a σ_a r * c a = 0` in the padded relator. -/
noncomputable def padC (r : FreeGroup α) (x t : α) : α → ℤ := by
  classical
  exact fun a => if a = x then (expSum t r).toAdd else if a = t then -((expSum x r).toAdd) else 0

/-- The blocks of the padding: the padded image of a single letter of a word, as a list. -/
noncomputable def padBlock (c : α → ℤ) (p : α × Bool) : List (PadT α × Bool) := by
  classical
  exact (if p.2 then padGen c p.1 else (padGen c p.1)⁻¹).toWord

/-- The padding of a word, as a list of letters. -/
noncomputable def padList (c : α → ℤ) (L : List (α × Bool)) : List (PadT α × Bool) :=
  (L.map (padBlock c)).flatten

theorem padHom_of (c : α → ℤ) (a : α) :
    padHom c (FreeGroup.of a) = padGen c a := FreeGroup.lift_apply_of

theorem padProj_of (a : α) : padProj (FreeGroup.of (some a) : FreeGroup (PadT α)) =
    FreeGroup.of a := FreeGroup.lift_apply_of

theorem padProj_none : padProj (FreeGroup.of (none : PadT α)) = 1 := FreeGroup.lift_apply_of

theorem padProj_padHom (c : α → ℤ) :
    padProj.comp (padHom c) = FreeGroup.lift (fun a : α => (FreeGroup.of a) ^ (2 : ℕ)) := by
  classical
  refine FreeGroup.ext_hom _ _ (fun a => ?_)
  show padProj (padHom c (FreeGroup.of a)) = _
  rw [padHom_of, padGen]
  show padProj (FreeGroup.of (some a) * (FreeGroup.of (none : PadT α)) ^ (c a) *
    FreeGroup.of (some a)) = _
  rw [map_mul, map_mul, map_zpow, padProj_of, padProj_none, one_zpow, mul_one,
    FreeGroup.lift_apply_of]
  rw [pow_two]

end Work.OROneRel
