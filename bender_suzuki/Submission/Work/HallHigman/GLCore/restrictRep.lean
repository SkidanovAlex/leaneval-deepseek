/-
Restriction of a representation to an invariant submodule.  Used by Step 4c of the GL-core
design (`Work.HallHigman.GLCore.exists_square_eq_card_centerQuotient`): the Fourier/Schur
argument is applied not to `V` itself but to a minimal nonzero `𝒬`-invariant submodule `W`,
which is `𝒬`-simple, and the representation of `𝒬` on `W` is `restrictRep σ W _`.
-/
import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

variable {E : Type*} [Monoid E] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The representation of `E` on a `σ`-invariant submodule `W ≤ V`, obtained by restricting `σ`
to `W`. -/
def restrictRep (σ : E →* Module.End K V) (W : Submodule K V)
    (hW : ∀ e : E, ∀ x ∈ W, σ e x ∈ W) : E →* Module.End K W where
  toFun e := (σ e).restrict (hW e)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' := by
    intro a b
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply, map_mul]

/-- Evaluation of the restricted representation: on vectors it is `σ`. -/
theorem restrictRep_apply (σ : E →* Module.End K V) (W : Submodule K V)
    (hW : ∀ e : E, ∀ x ∈ W, σ e x ∈ W) (e : E) (x : W) :
    ((restrictRep σ W hW e) x : V) = σ e x := rfl

/-- The restriction of a scalar endomorphism is the corresponding scalar. -/
theorem restrictRep_eq_algebraMap_of_eq_smul_one (σ : E →* Module.End K V) (W : Submodule K V)
    (hW : ∀ e : E, ∀ x ∈ W, σ e x ∈ W) {e : E} {c : K}
    (he : σ e = algebraMap K (Module.End K V) c) :
    restrictRep σ W hW e = algebraMap K (Module.End K W) c := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [restrictRep_apply, he, Module.algebraMap_end_apply K K V,
    Module.algebraMap_end_apply K K ↥W]
  rfl

end Work.HallHigman
