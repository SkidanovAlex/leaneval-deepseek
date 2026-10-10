import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local triviality at a level `L` of `Ω` (vocabulary for the all-levels form of E9)

`PTDefs.IsLocTrivial` says that a class of `H¹(Gal(K/k), M)` restricts to `0` in `H¹(D_w, M)` for
every place `w` of `K`.  The node `E9` (`DESIGN_FIX2.md` §1-2) is stated with the *all-levels*
hypothesis, so it needs the same notion at every intermediate level `L` of a fixed algebraic
closure `Ω ⊇ K`: `h ∈ H¹(Gal(L/k), M)` is locally trivial if it dies on the stabiliser
(= decomposition group) of every place of `L`.
-/

open CategoryTheory

noncomputable section

namespace SSGRoute.PTExt

/-- **Local triviality at a level `L`**: `h ∈ H¹(Gal(L/k), res M)` restricts to `0` in the
cohomology of the decomposition group of every place of `L`. -/
def IsLocTrivialLevel {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {s : ℕ}
    (h : extH (Rep.res (galRes k K L) M) s) : Prop :=
  ∀ w : NK.GlobalCFT.Place L,
    extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) h = 0

end SSGRoute.PTExt

end
