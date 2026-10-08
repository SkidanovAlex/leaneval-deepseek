import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX of Peterfalvi I: the irreducible `F₂`-representations of `GL(3,2)`

Peterfalvi I, App. IX (pp. 230–233) determines the irreducible representations of
`GL(3,F₂) = (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)` over `F₂`: up to similarity there are
four, of degrees `1`, `3`, `3` and `8` (the trivial one, the natural one, its dual, and the
action on the trace-zero matrices by conjugation).

The form used in Ch. IV §4 only needs the *degrees*: every irreducible `F₂[GL(3,2)]`-module has
dimension `1`, `3` or `8`. This file states that as `AppIXProp`.
-/

set_option autoImplicit false

namespace Work.Hering

/-- The group `GL(3,F₂)`, as the linear automorphism group of `(Fin 3 → ZMod 2)`. -/
abbrev GL32 : Type := (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)

/-- **Appendix IX of Peterfalvi I (p. 230)**, degree form: every irreducible `F₂`-representation
of `GL(3,2)` has degree `1`, `3` or `8`. -/
def AppIXProp : Prop :=
  ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)),
    (∃ m : M, m ≠ 0) →
    (∀ W : Submodule (ZMod 2) M,
      (∀ g : GL32, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    Module.finrank (ZMod 2) M = 1 ∨ Module.finrank (ZMod 2) M = 3 ∨
      Module.finrank (ZMod 2) M = 8

end Work.Hering
