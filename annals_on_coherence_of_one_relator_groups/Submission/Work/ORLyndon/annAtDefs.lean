import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.lyndonIndependence_of_relatorNorm_le_one

/-!
# The set-indexed annihilator of the root Fox vector

For a one-relator presentation `G = ⟨X | r⟩` with `r = u ^ l` and a set `E` of generators, the
predicate

`Work.ORLyndon.annAt K r u E`

says that *no* non-zero element of `K[G]` annihilates the `x`-components `(∂u/∂x)_x` of the **root**
Fox vector for *all* `x ∈ E`:

`∀ b, (∀ x ∈ E, b * (∂u/∂x) = 0) → b = 0`.

This is the shape in which the Cohen--Lyndon induction of this area is run.  Its point is that the
predicate is *set-indexed*, so that:

* it is **monotone in `E`** (`annAt_mono`): a statement about fewer letters is stronger and implies
  the statement about more letters, so a descent through the Magnus steps may *drop* the letters it
  cannot reach and still conclude `annAt` for all the letters of the root;
* its transfer through the exponent-sum-zero Magnus step
  (`Work.ORLyndon.annAt_of_epsZero_top`) is **unconditional**: a letter of the root whose top
  decorated symbol is regular *in the base* is regular in the root, and *all* the letters of the root
  can be handled at once, the framing letter being simply added to the set (`E ↦ insert t E`);
* the induction terminates because the *terminal* root (relator norm `≤ 1`) is a single letter whose
  Fox component is a unit, so that `annAt` holds for every set containing that letter
  (`Work.ORLyndon.annAt_of_unit`).

The connection with the statement consumed by the rest of the chapter
(`Work.ORLyndon.LyndonIndependence`) is `Work.ORLyndon.vector_zero_of_annAt_letters`: the annihilator
of the *vector* `(∂u/∂x)_x` is trivial as soon as `annAt K r u (relatorLetters u)` holds, since the
condition `b • (∂u/∂x)_x = 0` is the conjunction of its components.

## Main definitions

* `Work.ORLyndon.annAt` -- the set-indexed annihilator statement.

## Main results

* `Work.ORLyndon.annAt_mono`, `Work.ORLyndon.annAt_of_unit`,
  `Work.ORLyndon.annAt_of_forall_component`, `Work.ORLyndon.annAt_of_vector`;
* `Work.ORLyndon.vector_zero_of_annAt_letters` -- the bridge to the `(I)` input of
  `Work.ORLyndon.lyndon_independence_of_rootVec_inj`;
* `Work.ORLyndon.annAt_of_relatorNorm_le_one` -- the base case of the induction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

/-- **The set-indexed annihilator of the root Fox vector.**  Every element of the group algebra
`K[⟨X | r⟩]` which annihilates the component `(∂u/∂x)_x` of the root Fox vector for **every**
`x ∈ E` is zero.  (The root `u` is the root of the relator, `r = u ^ l`; the statement is meaningful
without fixing `l`, which enters only through the identification of the root.) -/
def annAt (K : Type v) [Field K] {X : Type u} [DecidableEq X] (r u : FreeGroup X)
    (E : Set X) : Prop :=
  ∀ b : MonoidAlgebra K (OneRelatorGroup r), (∀ x ∈ E, b * rootVec K r u x = 0) → b = 0

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- `annAt` is **monotone** in the set of letters: more letters means more hypotheses in the
condition, hence a weaker statement, hence a statement about fewer letters implies one about more. -/
theorem annAt_mono {r u : FreeGroup X} {E E' : Set X} (h : E ⊆ E') (h' : annAt K r u E) :
    annAt K r u E' := by
  intro b hb
  exact h' b fun x hx => hb x (h hx)

/-- `annAt` holds for a set of letters containing a letter whose Fox component is a **unit**. -/
theorem annAt_of_unit {r u : FreeGroup X} {E : Set X} {x : X} (hx : x ∈ E)
    (hu : IsUnit (rootVec K r u x)) : annAt K r u E := by
  intro b hb
  obtain ⟨w, hw⟩ := hu
  calc b = (b * (w : MonoidAlgebra K (OneRelatorGroup r))) * (↑w⁻¹ : MonoidAlgebra K _) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (b * rootVec K r u x) * (↑w⁻¹ : MonoidAlgebra K _) := by rw [hw]
    _ = 0 := by rw [hb x hx, zero_mul]

/-- `annAt` for a set containing a letter of right-regular Fox component. -/
theorem annAt_of_component {r u : FreeGroup X} {E : Set X} {x : X} (hx : x ∈ E)
    (h : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b * rootVec K r u x = 0 → b = 0) :
    annAt K r u E :=
  fun b hb => h b (hb x hx)

/-- `annAt` for a nonempty set of letters all of whose Fox components are right regular. -/
theorem annAt_of_forall_component {r u : FreeGroup X} {E : Set X} (hne : E.Nonempty)
    (h : ∀ x ∈ E, ∀ b : MonoidAlgebra K (OneRelatorGroup r),
      b * rootVec K r u x = 0 → b = 0) :
    annAt K r u E := by
  intro b hb
  exact h _ hne.choose_spec b (hb _ hne.choose_spec)

/-- A unit of a ring is a right non-zero-divisor. -/
theorem annAt_regular_of_unit {R : Type*} [Ring R] {x : R} (h : IsUnit x) :
    ∀ c : R, c * x = 0 → c = 0 := by
  rintro c hc
  obtain ⟨u, rfl⟩ := h
  have h1 : (c * (u : R)) * (↑u⁻¹ : R) = 0 := by rw [hc, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h1

/-- **The bridge to the `(I)` input of the endgame.**  If `annAt` holds for the letters of the root,
then the annihilator of the *vector* `(∂u/∂x)_x` in `K[G]` is trivial: the equation
`b • (∂u/∂x)_x = 0` is equivalent to the vanishing of all its components. -/
theorem vector_zero_of_annAt_letters {r u : FreeGroup X}
    (h : annAt K r u (Work.OROneRel.relatorLetters u)) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0 := by
  intro b hb
  refine h b fun x _ => ?_
  have h1 := congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup r) => v x) hb
  simpa only [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] using h1

/-- **The base case of the Cohen--Lyndon induction.**  For a cyclically reduced root of relator norm
`≤ 1` which is not a proper power, the root is a single letter up to sign, whose Fox component is a
unit; hence `annAt` holds for the letters of the root. -/
theorem annAt_of_relatorNorm_le_one {r u : FreeGroup X} {l : ℕ} (hl : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    annAt K r u (Work.OROneRel.relatorLetters u) := by
  classical
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, hle⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hle
    subst hpow
    rw [Work.OROneRel.relatorLetters_letterPow]
    exact annAt_of_unit (Set.mem_singleton a) (isUnit_rootVec_letterPow _ a s)

end Work.ORLyndon
