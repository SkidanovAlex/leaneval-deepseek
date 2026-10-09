import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the `C₂`-lattice chain (S3)

This file fixes the notions used to state and prove

`Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice_chain`,

the purely lattice-theoretic input to the `C₂`-lattice Hasse principle: every finite free
`ℤ`-lattice with an action of an involution is built from a split lattice by a finite chain of
index-two extensions.

Everything here is stated for an arbitrary `AddCommGroup` `V` with a `Module Coeff V` structure,
where `Coeff = ℤ` (as `ULift ℤ`) is the coefficient ring used throughout `SSGRoute`.

* `TwoStep L L'` — `L'` is obtained from `L` by adjoining a single generator `m` whose class in
  `L'/L` is killed by `2`; consequently `L'/L ≅ ℤ/2`.
* `CoeffSubmoduleLift` — an auxiliary device comparing `ℤ`-submodules and `Coeff`-submodules.
-/

namespace Work.SSGRoute.E1aFinal

open CategoryTheory

noncomputable section

/-- `TwoStep L L'` says that `L ≤ L'` are `Coeff`-submodules of `V` and that `L'` is generated
over `L` by a single element `m` whose class in `L'/L` is killed by `2`:
`∀ x ∈ L', x ∈ L ∨ x - m ∈ L` and `m ∉ L`.  Together with `2 • m ∈ L` this says `L'/L ≅ ℤ/2`. -/
def TwoStep {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L L' : Submodule SSGRoute.PTExt.Coeff V) : Prop :=
  L ≤ L' ∧ ∃ m ∈ L', m ∉ L ∧ ∀ x ∈ L', x ∈ L ∨ x - m ∈ L

end

end Work.SSGRoute.E1aFinal
