import Mathlib

-- `letI` is needed to install `Submodule.module` as the working `ℤ`-module structure on `↥A`;
-- the `haveI/letI` style linter's suggestion to use `let` would remove the instance.
set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- A `ℤ`-submodule `A` of a `ℤ`-module `M` spanned by a linearly independent set `B` is a free
`ℤ`-module: `B`, viewed inside `A`, is a basis of `A`.

The proof builds the basis with `Module.Basis.mk`.  The one formal subtlety is that on the
subtype `↥A` there are two `ℤ`-module structures: `Submodule.module` (used by
`Submodule.subtype`) and the canonical `AddCommGroup.toIntModule` (the one picked by instance
search).  On a `ℤ`-module these coincide up to proof (`Subsingleton (Module ℤ ↥A)`); we work with
`Submodule.module` throughout (introduced as a local instance) and transport the final statement
along this `Subsingleton` instance. -/
theorem moduleFree_of_linearIndepOn_span {M : Type*} [AddCommGroup M] [Module ℤ M]
    {A : Submodule ℤ M} {B : Set M} (hli : LinearIndepOn ℤ id B) (hsp : Submodule.span ℤ B = A) :
    Module.Free ℤ ↥A := by
  -- Use the module structure on `↥A` inherited from `M` (that of `Submodule.subtype`).
  letI instA : Module ℤ ↥A := A.module
  -- The family `B ⊆ A`.
  have hmem (b : B) : (b : M) ∈ A := hsp ▸ Submodule.subset_span b.2
  let v : B → A := fun b => ⟨(b : M), hmem b⟩
  -- `B` is linearly independent, also when regarded as a family in `A`.
  have hliM : LinearIndependent ℤ (fun b : B => (b : M)) := hli
  have hcomp : LinearIndependent ℤ ((Submodule.subtype A) ∘ v) := hliM
  have hliSub : LinearIndependent ℤ v :=
    LinearIndependent.of_comp (Submodule.subtype A) hcomp
  -- The family `v` spans `A`.
  have hrange : (Submodule.subtype A) '' Set.range v = B := by
    rw [← Set.range_comp (Submodule.subtype A) v]
    rw [show (Submodule.subtype A) ∘ v = (Subtype.val : B → M) from rfl]
    exact Subtype.range_coe
  have htop : (⊤ : Submodule ℤ ↥A) ≤ Submodule.span ℤ (Set.range v) := by
    refine le_of_eq ?_.symm
    refine Submodule.map_injective_of_injective (Submodule.subtype_injective A) ?_
    rw [Submodule.map_span, hrange, hsp, Submodule.map_subtype_top]
  -- Hence `v` is a basis of `A` and `A` is free.
  have hfree : Module.Free ℤ ↥A :=
    Module.Free.of_basis (Module.Basis.mk hliSub htop)
  -- Transport across the (unique) `ℤ`-module structure on `↥A`.
  exact Eq.mp (congrArg (fun i => @Module.Free ℤ ↥A _ _ i)
    (Subsingleton.elim instA (AddCommGroup.toIntModule ↥A))) hfree

end Work.ANALYTIC.CechPt
