import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- For a morphism `f : A ⟶ B` in the category `Rep k G` of `k`-linear representations of a monoid
`G`, the kernel of the underlying additive map of `f` coincides with the range of the underlying
additive map of the kernel inclusion `kernel.ι f`.  Equivalently: the categorical kernel of `f` is
computed on the underlying additive groups. -/
theorem ker_hom_eq_range_kernel_iota_of_rep {k : Type} [Ring k] {G : Type} [Monoid G]
    {A B : Rep k G} (f : A ⟶ B) :
    ((Rep.Hom.hom f).toAddMonoidHom).ker
      = ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι f)).toAddMonoidHom).range := by
  let l : A →ₗ[k] B := (Rep.Hom.hom f).toLinearMap
  let W : Submodule k A := LinearMap.ker l
  -- `W` is a subrepresentation: it is stable under the `G`-action because `f` is equivariant.
  have hW : ∀ g : G, W ≤ W.comap (A.ρ g) := by
    intro g x hx
    rw [Submodule.mem_comap]
    rw [LinearMap.mem_ker] at hx ⊢
    rw [show l (A.ρ g x) = B.ρ g (l x) from by simpa [l] using Rep.hom_comm_apply f g x]
    rw [hx, map_zero]
  let incl : A.subrepresentation W hW ⟶ A := Rep.subtype A W hW
  -- The inclusion of the subrepresentation `W` is killed by `f`.
  have hzero : incl ≫ f = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hxi : (Rep.Hom.hom incl) x = (x : A) := by simp [incl]
    show (Rep.Hom.hom (incl ≫ f)) x = (Rep.Hom.hom (0 : A.subrepresentation W hW ⟶ B)) x
    rw [Rep.comp_apply]
    show (Rep.Hom.hom f) ((Rep.Hom.hom incl) x) = 0
    rw [hxi]
    exact LinearMap.mem_ker.mp x.2
  refine le_antisymm ?_ ?_
  · -- `range (kernel.ι f) ≤ ker f`: the kernel inclusion is killed by `f`.
    intro v hv
    rw [AddMonoidHom.mem_ker] at hv
    have hvW : v ∈ W := by rw [LinearMap.mem_ker]; simpa [l] using hv
    -- lift `v` through the universal property of the kernel
    refine AddMonoidHom.mem_range.mpr
      ⟨(CategoryTheory.Limits.kernel.lift f incl hzero) ⟨v, hvW⟩, ?_⟩
    simp [incl]
  · -- `ker f ≤ range (kernel.ι f)`: this is the universal property of the kernel.
    intro x hx
    rw [AddMonoidHom.mem_ker]
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    simp

theorem ker_hom_eq_range_kernel_iota {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω} [Normal k K] {ι : Type} {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (f : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι ⟶ M) : ((Rep.Hom.hom f).toAddMonoidHom).ker = ((Rep.Hom.hom (CategoryTheory.Limits.kernel.ι f)).toAddMonoidHom).range := by
  exact ker_hom_eq_range_kernel_iota_of_rep f

end Work.SSGRoute
