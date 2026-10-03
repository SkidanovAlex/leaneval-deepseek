import Mathlib

/-!
# Projective resolutions of bounded length (noncommutative rings)

Mathlib's `CategoryTheory.projectiveDimension` (and hence `Work.ORCoherence.globalDim`) is defined
through `Ext`, and there is no library statement converting an explicit projective resolution into
a bound on the projective dimension.  This file provides the missing notion.

* `Work.ORLyndon.HasProjDimLE R M n`: the left `R`-module `M` admits a projective resolution of
  length at most `n`, defined recursively through syzygies (`n = 0` means `M` is projective; `n+1`
  means that `M` is a quotient of a projective module whose kernel has projective dimension at most
  `n`).

The bridge to Mathlib,

* `Work.ORLyndon.hasProjectiveDimensionLE_of_hasProjDimLE`:
  `HasProjDimLE R M n → CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n`,

is proved by dimension shifting along the short exact sequences of the resolution, using
`CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

universe u v

/-- `HasProjDimLE R M n`: the left `R`-module `M` admits a projective resolution of length at
most `n`.  This is defined recursively through syzygies: `n = 0` means that `M` is projective,
and `n + 1` means that `M` is a quotient of a projective module whose kernel admits a projective
resolution of length at most `n`. -/
def HasProjDimLE (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] : ℕ → Prop
  | 0 => Module.Projective R M
  | n + 1 =>
      ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Projective R P)
        (f : P →ₗ[R] M), Function.Surjective f ∧ HasProjDimLE R (LinearMap.ker f) n

@[simp] theorem hasProjDimLE_zero {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] : HasProjDimLE R M 0 ↔ Module.Projective R M := Iff.rfl

@[simp] theorem hasProjDimLE_succ {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] (n : ℕ) :
    HasProjDimLE R M (n + 1) ↔
      ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Projective R P)
        (f : P →ₗ[R] M), Function.Surjective f ∧ HasProjDimLE R (LinearMap.ker f) n :=
  Iff.rfl

end Work.ORLyndon
