import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.FlatCrit

universe u

set_option linter.style.haveILetI false

namespace Work.ORFlatness

/-- Discharging the "reduction" hypothesis of the flatness theorem: for `R = K[G]` with `K` commutative, a left `K[G]`-module `M` is flat (`Work.ORFlatness.LeftFlat`) as soon as `Tor₁^{K[G]}(X, M) = 0` for every **right** `K[G]`-module `X` that carries a compatible `K`-module structure (i.e. a `Module K X` with `IsScalarTower K K[G]ᵐᵒᵖ X` and `SMulCommClass K K[G]ᵐᵒᵖ X`).

Proof: use the criterion `Work.ORFlatness.leftFlat_iff_forall_tor1Vanishes`; for an arbitrary right module `X` instantiate `h` at `X` equipped with the `K`-structure obtained by restricting scalars along `algebraMap K (MonoidAlgebra K G)`, i.e. `k • x := (algebraMap K (MonoidAlgebra K G) k) • x` (an action on the right of `x` since `X` is a `(MonoidAlgebra K G)ᵐᵒᵖ`-module). The two compatibility instances hold because `K` is central in `K[G]` (`Algebra.commutes`). Note that `Tor1Vanishes` does not depend on the chosen `K`-structure. -/
theorem leftFlat_of_testFamily (K : Type u) [CommRing K] (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M]
    (h : ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G)ᵐᵒᵖ X]
        [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ X] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ X],
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) X M) :
    Work.ORFlatness.LeftFlat (MonoidAlgebra K G) M := by
  rw [leftFlat_iff_forall_tor1Vanishes]
  intro X _ _
  -- Equip the right `K[G]`-module `X` with the `K`-structure coming from the algebra map.
  -- `(MonoidAlgebra K G)ᵐᵒᵖ` is a `K`-algebra (via `MulOpposite.instAlgebra`), so restricting
  -- scalars along `algebraMap K ((MonoidAlgebra K G)ᵐᵒᵖ)` gives the required `Module K X`;
  -- this action is `k • x = op (algebraMap K (MonoidAlgebra K G) k) • x`.
  letI : Module K X := Module.restrictScalars K (MonoidAlgebra K G)ᵐᵒᵖ X
  -- `IsScalarTower` holds by construction of the restricted scalar action.
  letI : IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ X :=
    IsScalarTower.of_compHom K (MonoidAlgebra K G)ᵐᵒᵖ X
  -- `SMulCommClass` is then automatic from the scalar tower, using centrality of `K` in `K[G]`.
  haveI : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ X := inferInstance
  -- `Tor1Vanishes` only depends on the `(MonoidAlgebra K G)ᵐᵒᵖ`-module structure of `X`,
  -- so the hypothesis applies verbatim.
  exact h X

end Work.ORFlatness
