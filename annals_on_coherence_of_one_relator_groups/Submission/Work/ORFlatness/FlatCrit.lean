/-
# The flatness criterion via `Tor₁`-vanishing

For a ring `R` (possibly noncommutative) and a left `R`-module `M`:

`M` is flat  ⟺  `Tor₁^{R}(X, M) = 0` for every right `R`-module `X`

in the sense of `Work.ORFlatness.LeftFlat` and `Work.ORFlatness.Tor1Vanishes`.  This is
the form in which the flatness results of Jaikin-Zapirain--Linton are used: their
Theorem 5.3/5.6 produce the vanishing of `Tor₁` against a family of test modules, and the
criterion converts it into flatness.
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.range_map_eq_ker_map
import Submission.Work.ORFlatness.injective_of_tor1Vanishes
import Submission.Work.ORFlatness.projPres_exists

set_option autoImplicit false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (R : Type u) [Ring R]

/-- A left flat module has `Tor₁` vanishing against every right module. -/
theorem Tor1Vanishes.of_leftFlat {M : Type u} [AddCommGroup M] [Module R M]
    (h : LeftFlat R M) (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] :
    Tor1Vanishes R X M := by
  obtain ⟨P⟩ := projPres_exists (R := R) X
  exact ⟨P, h (Submodule.subtype P.K) Subtype.val_injective⟩

/-- The flatness criterion: a left `R`-module is flat if and only if `Tor₁^{R}(X, M) = 0`
for every right `R`-module `X`. -/
theorem leftFlat_iff_forall_tor1Vanishes {M : Type u} [AddCommGroup M] [Module R M] :
    LeftFlat R M ↔ ∀ (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X], Tor1Vanishes R X M := by
  constructor
  · exact fun h X _ _ => Tor1Vanishes.of_leftFlat R h X
  · intro h
    refine fun {X Y} _ _ _ _ f hf => ?_
    exact injective_of_tor1Vanishes f (Submodule.mkQ f.range) hf (Submodule.mkQ_surjective _)
      (Submodule.ker_mkQ _).symm M (h (Y ⧸ f.range))

end Work.ORFlatness
