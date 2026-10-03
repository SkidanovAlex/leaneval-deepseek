import Submission.Work.ORCoherence.Map
import Submission.Work.ORCoherence.Tensor.balanced_map_add
import Submission.Work.ORCoherence.Tensor.balanced_map_comp
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.Exact

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u

/-- The functor `S ⊗[R] -` from left `R`-modules to left `S`-modules, for `f : R →+* S`
(injective in the applications, but not required here). -/
noncomputable def tensorFunctor {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (Balanced f M)
  map g := ModuleCat.ofHom (Balanced.map f g.hom)
  map_id M := ModuleCat.hom_ext
    (LinearMap.ext (fun x => congr($(Balanced.map_id f (M := M)) x)))
  map_comp g h := ModuleCat.hom_ext
    (LinearMap.ext (fun x => congr($(Tensor.balanced_map_comp f g.hom h.hom) x)))

instance {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (tensorFunctor f).Additive where
  map_add := fun {X Y} {a b : X ⟶ Y} => by
    ext x
    exact congr($(Tensor.balanced_map_add f a.hom b.hom) x)

/-- `Tor n (S ⊗[R] -) (M)`, the `n`-th left derived functor of the functor `S ⊗[R] -`
applied to the left `R`-module `M`. This is `Tor_n^R(S, M)`, where `S` is regarded as a right
`R`-module via `f`. -/
noncomputable def Tor {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (M : ModuleCat.{u} R) : ModuleCat.{u} S :=
  ((tensorFunctor f).leftDerived n).obj M

/-- The hypothesis `Tor_2^R(S, M) = 0` for every left `R`-module `M`: the right `R`-module `S`
has weak dimension at most one. -/
def TorVanishes {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : Prop :=
  ∀ (M : ModuleCat.{u} R), IsZero (Tor f 2 M)

end Work.ORCoherence
