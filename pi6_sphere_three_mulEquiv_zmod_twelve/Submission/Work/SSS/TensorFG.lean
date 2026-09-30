import Mathlib
import Submission.Work.SSS.Filtration

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of the homology of `K ⊗ M` for a free complex `K`

For the last step of the computation of the E² page of the Serre spectral sequence one needs: the
homology of `C_*(B) ⊗ H_t(F)` is finitely generated in degree `s` when `H_s(B)`, `H_{s-1}(B)` and
`H_t(F)` are, `C_*(B)` being degreewise free.  This is the universal coefficient theorem
`H_s(K ⊗ M) ≅ H_s(K) ⊗ M ⊕ Tor(H_{s-1}(K), M)` read in the Serre class of finitely generated
groups (`Tor` of two finitely generated abelian groups is finitely generated).

This file contains the definition of the tensor complex `tensorComplex K M` (the tensor product of
`K` with the complex concentrated in degree `0` at `M`) and the statement of the finiteness theorem
(proved in the sibling file `Submission/Work/SSS/tensorHomology.lean`).
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

/-- The chain complex `K ⊗ M`: the tensor product of a chain complex `K` of `ℤ`-modules with the
complex concentrated in degree `0` at a `ℤ`-module `M`.  Its `n`-th term is `K.X n ⊗ M` and its
differential is `d ⊗ id`. -/
def tensorComplex (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  K ⊗ (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj M

end

end Work.SSS
