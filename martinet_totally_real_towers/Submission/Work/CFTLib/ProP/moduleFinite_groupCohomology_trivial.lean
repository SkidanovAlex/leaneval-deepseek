import Mathlib
import Submission.CFTLib.Interfaces

/-!
# Finite generation of the group cohomology of a finite group

For a finite group `H` and any degree `n`, the group cohomology
`Hⁿ(H, 𝔽_p) = groupCohomology (Rep.trivial (ZMod p) H (ZMod p)) n`
of the trivial `H`-module `𝔽_p` is a finitely generated `𝔽_p`-module.

This is immediate from the description of cohomology as the cohomology of the complex of
inhomogeneous cochains: in degree `n` the coefficients live in `(Fin n → H) → 𝔽_p`, which is a
*finite* type because `H` and `𝔽_p` are finite.  The `n`-cocycles are a submodule of that finite
module (hence finitely generated), and `Hⁿ` is a quotient of the cocycles, hence finitely generated
as well.

(Here `ZMod p` is only required to be nonzero, so that it is a finite type; primality of `p` is
irrelevant for this finiteness statement.)
-/

namespace Work.CFTLib.ProP

open CategoryTheory

theorem moduleFinite_groupCohomology_trivial (p n : ℕ) [NeZero p] (H : Type) [Group H] [Finite H] :
    Module.Finite (ZMod p) (groupCohomology (Rep.trivial (ZMod p) H (ZMod p)) n) := by
  let A : Rep (ZMod p) H := Rep.trivial (ZMod p) H (ZMod p)
  -- The `n`-cocycles are a submodule of the finite module `(Fin n → H) → 𝔽_p`.
  have hcyc : Module.Finite (ZMod p) ↥((groupCohomology.inhomogeneousCochains A).cycles n) :=
    Module.Finite.of_injective ((groupCohomology.inhomogeneousCochains A).iCycles n).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  -- `Hⁿ` is a quotient of the cocycles, via the (surjective) homology projection.
  exact Module.Finite.of_surjective ((groupCohomology.inhomogeneousCochains A).homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end Work.CFTLib.ProP
