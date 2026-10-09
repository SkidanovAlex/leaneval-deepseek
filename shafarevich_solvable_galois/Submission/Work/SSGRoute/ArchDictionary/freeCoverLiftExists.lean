import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting a morphism of `G`-modules to their free covers

For `G` a group, `Coeff = ULift ℤ` and `M', M : Rep Coeff G`, the free covers
`Rep.free Coeff G M'.V` and `Rep.free Coeff G M.V` (the `Coeff[G]`-modules on the underlying
sets of `M'` and `M`) fit into the commuting square

```
Rep.free Coeff G M'.V  --φ-->  Rep.free Coeff G M.V
        |                              |
   freeLift M' id                 freeLift M id
        v                              v
        M'  -------- u.hom -------->   M
```

The map `φ` is the unique `G`-equivariant map induced, via the universal property of the free
module, by the assignment `a ↦ single (u a) 1` on the basis of `Rep.free Coeff G M'.V`.

The statement is the requested lemma `freeCoverLiftExists`.
-/

open CategoryTheory

namespace Work.SSGRoute.ArchDictionary

/-- **Evaluation of a free lift on a basis vector.**  For a representation `A` of `G` and a
function `f : α → A`, the `G`-equivariant map `Rep.freeLift k G A f` on the free module
`α →₀ k[G]` sends the basis vector `single i 1` to `f i`. -/
lemma rep_freeLift_basis {k : Type} [CommRing k] {G : Type} [Group G] {α : Type}
    (A : Rep.{0} k G) (f : α → A.V) (i : α) :
    (Rep.freeLift k G A f).hom (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : k))) = f i := by
  show (Representation.freeLift A.ρ f)
      (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : k))) = f i
  exact congrFun (LinearEquiv.apply_symm_apply (Representation.freeLiftLEquiv A.ρ α) f) i

theorem freeCoverLiftExists (G : Type) [Group G] (M' M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (u : M' ⟶ M) :
    ∃ φ : Rep.free SSGRoute.PTExt.Coeff G M'.V ⟶ Rep.free SSGRoute.PTExt.Coeff G M.V,
      ∀ x : Rep.free SSGRoute.PTExt.Coeff G M'.V,
        (Rep.freeLift SSGRoute.PTExt.Coeff G M (fun m : M.V => m)) (φ.hom x)
          = u.hom ((Rep.freeLift SSGRoute.PTExt.Coeff G M' (fun m : M'.V => m)) x) := by
  refine ⟨Rep.freeLift SSGRoute.PTExt.Coeff G (Rep.free SSGRoute.PTExt.Coeff G M.V)
      (fun a : M'.V => Finsupp.single (u.hom a)
        (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))), ?_⟩
  intro x
  -- It suffices to prove the identity of `Rep`-morphisms `free Coeff G M'.V ⟶ M`.
  have key : (Rep.freeLift SSGRoute.PTExt.Coeff G (Rep.free SSGRoute.PTExt.Coeff G M.V)
        (fun a : M'.V => Finsupp.single (u.hom a)
          (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))))
      ≫ (Rep.freeLift SSGRoute.PTExt.Coeff G M (fun m : M.V => m))
      = (Rep.freeLift SSGRoute.PTExt.Coeff G M' (fun m : M'.V => m)) ≫ u := by
    apply Rep.free_ext
    intro i
    show (Rep.freeLift SSGRoute.PTExt.Coeff G M (fun m : M.V => m)).hom
        ((Rep.freeLift SSGRoute.PTExt.Coeff G (Rep.free SSGRoute.PTExt.Coeff G M.V)
          (fun a : M'.V => Finsupp.single (u.hom a)
            (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff)))).hom
          (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))))
      = u.hom ((Rep.freeLift SSGRoute.PTExt.Coeff G M' (fun m : M'.V => m)).hom
          (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))))
    rw [rep_freeLift_basis (A := Rep.free SSGRoute.PTExt.Coeff G M.V)
      (f := fun a : M'.V => Finsupp.single (u.hom a)
        (MonoidAlgebra.single (1 : G) (1 : SSGRoute.PTExt.Coeff))) i]
    rw [rep_freeLift_basis (A := M) (f := fun m : M.V => m) (i := u.hom i)]
    rw [rep_freeLift_basis (A := M') (f := fun m : M'.V => m) (i := i)]
  exact congrArg (fun f : Rep.free SSGRoute.PTExt.Coeff G M'.V ⟶ M => f.hom x) key

end Work.SSGRoute.ArchDictionary
