/-
# The flatness criterion for right modules via `Tor₁`-vanishing

For a ring `R` (possibly noncommutative) and a right `R`-module `X`:

if `Tor₁^{R}(X, N) = 0` for every left `R`-module `N` (in the sense of
`Work.ORFlatness.Tor1Vanishes`, i.e. the syzygy of a projective presentation of `X` is
injective after tensoring with `N`), then `X` is right flat: tensoring on the left by `X`
preserves injective maps of left `R`-modules (`Work.ORFlatness.RightFlat`).

This is the mirror of the corresponding statement for left modules,
`Work.ORFlatness.leftFlat_iff_forall_tor1Vanishes` (whose two directions are
`Work.ORFlatness.Tor1Vanishes.of_leftFlat` and the `←` direction of the criterion).  Here we
only record the direction used in the flatness theorem of Jaikin-Zapirain--Linton
(Theorem 5.6, right-module form): the mirror of Theorem 5.6 produces `Tor₁`-vanishing of
`S ⊗_K C` against all left modules (see `Work.ORFlatness.tor1Vanishes_diagonal_jl_right`),
and this criterion converts it into flatness of the right `K[G]`-module `S ⊗_K C`
(`Work.ORFlatness.rightFlat_diagonal_jl`).

The converse (right flatness implies `Tor₁^{R}(X, N) = 0` for all `N`) is of course also
true, but its formalisation requires the identification of the two ways of computing `Tor₁`
(resolving the first variable, as in the definition of `Tor1Vanishes`, versus resolving the
second), which is not needed anywhere in this development.
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.injective_of_tor1Vanishes_right

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (R : Type u) [Ring R]

/-- If `Tor₁^R(X, N) = 0` for every left `R`-module `N`, then the right `R`-module `X` is right
flat.  (Mirror of the `←` direction of `Work.ORFlatness.leftFlat_iff_forall_tor1Vanishes;
the proof is the mirror of the one for left modules, using
`Work.ORFlatness.injective_of_tor1Vanishes_right`.) -/
theorem rightFlat_of_forall_tor1Vanishes {X : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N], Tor1Vanishes R X N) :
    RightFlat R X := by
  intro M N _ _ _ _ g hg
  exact injective_of_tor1Vanishes_right g (Submodule.mkQ g.range) hg (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm X (h (N ⧸ g.range))

end Work.ORFlatness
