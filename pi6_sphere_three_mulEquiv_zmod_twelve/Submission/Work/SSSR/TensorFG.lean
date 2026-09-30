import Mathlib
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

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

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
noncomputable section

/-- The chain complex `K ⊗ M`: the tensor product of a chain complex `K` of `ℤ`-modules with the
complex concentrated in degree `0` at a `ℤ`-module `M`.  Its `n`-th term is `K.X n ⊗ M` and its
differential is `d ⊗ id`. -/
def tensorComplex (R : Type) [CommRing R] [Nontrivial R] (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  K ⊗ (HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℕ) 0).obj M

end

end Work.SSSR
