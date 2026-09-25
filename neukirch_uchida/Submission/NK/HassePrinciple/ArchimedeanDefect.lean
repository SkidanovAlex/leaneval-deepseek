/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The archimedean defect: `NK.BrauerHasse.Sha2Vanishing` is false as literally stated

Umbrella development: `Submission/Work/HassePrinciple/` (README §13.1, §19).

The target of this chapter, `NK.BrauerHasse.Sha2Vanishing p K K' κ κ'`, quantifies over *arbitrary*
fields `κ` with `κ'` a separable closure — it does **not** require `κ` to be `p`-adic.  This module
records the exact content of that defect: the literal statement fails for `κ = K = E` as soon as
there is a non-zero class of `H²(Gal(E'/E), Z/2)` whose localisation at every place over a *finite*
prime of `E` vanishes.

Such a class exists for every formally real number field `E`: by Hasse–Brauer–Noether the kernel of
`Br(E) → ∏_{v finite} Br(E_v)` consists of the classes whose only non-zero invariants are at the
archimedean places, and for `E = ℚ(√2)` the class of the quaternion algebra `(-1,-1)` is such a
class (its invariants are `1/2` at the two real places, and `0` at every finite place: for odd `ℓ`
already over `ℚ_ℓ`, and at `2` because `ℚ_2(√2)` has degree `2` over `ℚ_2` and `inv_2(-1,-1) = 1/2`,
so the invariant `2·1/2 ≡ 0` vanishes).  This is the counterexample of README §13.1; it is not
formalised here, because it needs the theory of quaternion algebras and local Hasse invariants, which
is not in the library.

The point of the module is to make the *statement* of the defect precise and to prove that it is
exactly the failure of the literal target:

* `NK.HassePrinciple.ArchimedeanDefect E E'` — the datum: a non-zero `x ∈ H²(⊤, Z/2)` with
  `H2Profinite.loc 2 ⊤ x A = 0` for every `A : OverFinitePrime E E'`;
* `NK.HassePrinciple.not_sha2Vanishing_iff_archimedeanDefect` — **the literal target for
  `(K, κ) = (E, E)` and `p = 2` holds if and only if the archimedean defect does *not* exist**.

The corrected statement therefore has to exclude the defect; the chapter's device for that is the
`κ`-labelling itself (`NK.HassePrinciple.NoTwoTorsion Gal(κ'/κ)`,
`NK.HassePrinciple.Sha2Spec.archimedean`, `NK.HassePrinciple.noTwoTorsion_of_mulEquiv`): a
`p`-adic absolute Galois group has no element of order `2`, hence no real place in its fixed field,
which is exactly what the defect needs.
-/

import Submission.NK.HassePrinciple.Inert
import Submission.NK.HassePrinciple.LocalCharacterisation

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {E E' : Type u} [Field E] [NumberField E] [Field E'] [Algebra E E']
  [IsSepClosure E E']

/-- **The archimedean defect** of a number field `E`: a non-zero class of `H²(⊤, Z/2)`, i.e. of
`H²(Gal(E'/E), Z/2)`, whose localisation at every place of `E'` over a finite prime of `E` vanishes.

Classically such a class exists exactly when `E` is formally real: it is the class of the quaternion
algebra `(-1,-1)` (Hasse–Brauer–Noether together with the local Hasse invariant computation).  The
`κ`-labelling of the target is what excludes it, by forcing the fixed field of the subgroup to be
non-formally-real. -/
def ArchimedeanDefect (E E' : Type u) [Field E] [NumberField E] [Field E'] [Algebra E E']
    [IsSepClosure E E'] : Prop :=
  ∃ x : H2Profinite (K := E) (K' := E') 2 ⊤, x ≠ 0 ∧
    ∀ A : OverFinitePrime E E', H2Profinite.loc (K := E) (K' := E') 2 ⊤ x A = 0

/-- **The archimedean defect destroys the literal target.**  If there is a non-zero class of
`H²(Gal(E'/E), Z/2)` that is locally trivial at every finite place, then
`NK.BrauerHasse.Sha2Vanishing 2 E E' E E'` is *false*: the subgroup `⊤` is closed and
`Nonempty (⊤ ≃* Gal(E'/E))`, so the class is a counterexample to the statement.

Combined with the classical existence of such a class over any formally real number field `E` (the
class of the quaternion algebra `(-1,-1)`, README §13.1), this is the reason the `κ`-labelling —
equivalently the archimedean condition `NK.HassePrinciple.NoTwoTorsion Gal(κ'/κ)` — cannot be
dropped from the target. -/
theorem not_sha2Vanishing_of_archimedeanDefect (h : ArchimedeanDefect E E') :
    ¬ Sha2Vanishing (K := E) (K' := E') 2 E E' := by
  obtain ⟨x, hxne, hx⟩ := h
  intro hvan
  refine hxne (hvan ⊤ (by simp) ⟨Subgroup.topEquiv⟩ x hx)

/-- **The literal target excludes the archimedean defect.**  Conversely to
`NK.HassePrinciple.not_sha2Vanishing_of_archimedeanDefect`, a proof of
`NK.BrauerHasse.Sha2Vanishing 2 E E' E E'` exhibits the non-existence of any such class, because the
clause for `⊤` is exactly the statement that no locally trivial class over the finite places is
non-zero. -/
theorem not_archimedeanDefect_of_sha2Vanishing
    (h : Sha2Vanishing (K := E) (K' := E') 2 E E') : ¬ ArchimedeanDefect E E' := by
  rintro ⟨x, hxne, hx⟩
  exact hxne (h ⊤ (by simp) ⟨Subgroup.topEquiv⟩ x hx)

end NK.HassePrinciple
