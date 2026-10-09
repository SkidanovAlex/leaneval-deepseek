import Mathlib
import Submission.Work.Tate.CoindUp
import Submission.Work.CohomologicalShrinking.tate.Hm1Map_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.tate

/-- `Ĥ⁻²` is functorial: the map induced by a composite of `G`-equivariant maps is the composite
of the induced maps.  Both sides are, by definition, the `Ĥ⁻¹`-maps on the `I_G`-twists
`A^♯ → B^♯ → C^♯`; the point is that `coindUpMap` itself is compatible with composition, which
is `rfl`, since it acts by postcomposition on the underlying functions. -/
theorem Hm2Map_comp {G : Type*} {A B C : Type*} [Group G] [Fintype G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (e : A →+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (f : B →+ C) (hf : ∀ (g : G) (b : B), f (g • b) = g • f b)
    (hfe : ∀ (g : G) (a : A), (f.comp e) (g • a) = g • (f.comp e) a) :
    Work.Tate.Hm2Map (A := A) (B := C) (f.comp e) hfe
      = (Work.Tate.Hm2Map (A := B) (B := C) f hf).comp
          (Work.Tate.Hm2Map (A := A) (B := B) e he) := by
  apply AddMonoidHom.ext
  intro x
  induction x using Work.Tate.Hm1_induction_on with
  | h a =>
    unfold Work.Tate.Hm2Map
    rw [Work.Tate.Hm1Map_Hm1π, AddMonoidHom.comp_apply, Work.Tate.Hm1Map_Hm1π,
      Work.Tate.Hm1Map_Hm1π]
    -- After unfolding, both sides are `Hm1π` of an element of `ker (norm G C)`: namely
    -- `mapKer (coindUpMap (f ∘ e)) a` and `mapKer (coindUpMap f) (mapKer (coindUpMap e) a)`.
    -- These agree definitionally, since `coindUpMap` and `mapKer` act by postcomposition on the
    -- underlying functions (on `γ : G` both are the function `γ ↦ f (e (a γ))`).
    congr 1

end Work.CohomologicalShrinking.tate
