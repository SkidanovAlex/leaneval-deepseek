import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.App1.Defs` — vocabulary for Peterfalvi's Appendix I

Appendix I studies the action of an element `t` of prime order `d` on a group `M`, with `X` a
`d'`-subgroup of `M` normalised by `t`.  The two objects are

* `V = C_X(t) = X ⊓ Subgroup.centralizer {t}`, and
* `K = {[t,x] | x ∈ X} = {t⁻¹ x⁻¹ t x | x ∈ X}` (Peterfalvi's `[t,x] = t⁻¹x⁻¹tx`),

together with the orbit `t^X = {x⁻¹ t x | x ∈ X}` of `t` under conjugation by `X`.  Appendix I (1)
asserts `|t^X| = |K| = |X : V|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

open Submission.Blueprint

variable {G : Type} [Group G]

/-- `t^X = {x⁻¹ t x | x ∈ X}`, the orbit of `t` under conjugation by the subgroup `X`
(Peterfalvi's notation `t^X`, i.e. `{t^x : x ∈ X}` with `t^x = x⁻¹tx`). -/
def conjOrbit (X : Subgroup G) (t : G) : Set G := {u | ∃ x ∈ X, x⁻¹ * t * x = u}

/-- Peterfalvi's `K = {[t,x] | x ∈ X}` with `[t,x] = t⁻¹x⁻¹tx`. -/
def commutatorSet (t : G) (X : Subgroup G) : Set G :=
  {u | ∃ x ∈ X, u = t⁻¹ * x⁻¹ * t * x}

/-- `V = C_X(t) = X ⊓ C_G(t)`. -/
abbrev centralizerIn (X : Subgroup G) (t : G) : Subgroup G :=
  X ⊓ Subgroup.centralizer ({t} : Set G)

theorem mem_conjOrbit {X : Subgroup G} {t u : G} :
    u ∈ conjOrbit X t ↔ ∃ x ∈ X, x⁻¹ * t * x = u := Iff.rfl

theorem mem_commutatorSet {X : Subgroup G} {t u : G} :
    u ∈ commutatorSet t X ↔ ∃ x ∈ X, u = t⁻¹ * x⁻¹ * t * x := Iff.rfl

theorem t_mem_conjOrbit {X : Subgroup G} {t : G} : t ∈ conjOrbit X t :=
  ⟨1, X.one_mem, by simp⟩

/-- The map `u ↦ t⁻¹u` sends the orbit of `t` onto `K`. -/
theorem image_conjOrbit_eq_commutatorSet (X : Subgroup G) (t : G) :
    (fun u => t⁻¹ * u) '' conjOrbit X t = commutatorSet t X := by
  ext u
  constructor
  · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x⁻¹ * t * x, ⟨x, hx, rfl⟩, by group⟩

end Work.DoubleTransitivity
