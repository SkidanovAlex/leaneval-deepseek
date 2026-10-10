import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The augmentation resolution `0 → I → k[G] → k → 0` and the derivation bridge

This file sets up the objects used to identify `Ш¹(k,M)` with the locally trivial classes of
`Ext¹_{Gal(K/k)}(ℤ, M)` (node `E1b`, `Work.SSGRoute.ext_sha1_bridge`).

For a group `G` and `Coeff = ULift ℤ`:

* `regRep G` is `k[G]` with the left regular action (Mathlib's `Rep.leftRegular Coeff G`), whose
  carrier is `MonoidAlgebra Coeff G`;
* `augHom G : regRep G ⟶ unitRep G` is the augmentation `ε` (`γ ↦ 1`);
* `augSub G = ker ε` (the augmentation ideal) as a submodule, `augI G` as a subrepresentation and
  `augSES G : ShortComplex (Rep Coeff G)` the short complex `0 → I → k[G] → k → 0`;
* `augDiff γ = (γ - 1 : I)`.

The *derivation bridge* is `cocycleLin`: a crossed homomorphism `φ : G → M` (for the action
`M.ρ`) gives the `Coeff`-linear map `Σ c_γ γ ↦ Σ c_γ • φ γ` on `k[G]`, which descends to the
augmentation ideal `I` and is `G`-equivariant there; conversely every representation morphism
`I ⟶ M` is of that form, and `γ - 1 ↦ φ γ`.
-/

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute
namespace ExtH1

variable (G : Type) [Group G]

/-- `k[G]` with the left regular action, as a `Rep Coeff G`. -/
noncomputable abbrev regRep : Rep.{0,0,0} Coeff G := Rep.leftRegular Coeff G

/-- The basis element `γ` of `k[G]`. -/
noncomputable abbrev ebas (γ : G) : regRep G := MonoidAlgebra.single γ 1

/-- The augmentation `k[G] → k`, the `k`-linear map `γ ↦ 1`. -/
noncomputable abbrev augHom : regRep G ⟶ unitRep G := Rep.leftRegularHom (unitRep G) 1

/-- The augmentation ideal `I = ker ε` as a submodule of `k[G]`. -/
noncomputable abbrev augSub : Submodule Coeff (regRep G) :=
  LinearMap.ker (augHom G).hom.toLinearMap

/-- The augmentation ideal is invariant under the action of `G`. -/
theorem augSub_le_comap (g : G) : augSub G ≤ (augSub G).comap ((regRep G).ρ g) := by
  intro x hx
  rw [Submodule.mem_comap]
  rw [show ((regRep G).ρ g) x ∈ augSub G ↔ (augHom G).hom (((regRep G).ρ g) x) = 0 from Iff.rfl]
  rw [Rep.hom_comm_apply, show (augHom G).hom x = 0 from hx]
  simp

/-- The augmentation ideal `I`, as a subrepresentation of `k[G]`. -/
noncomputable abbrev augI : Rep.{0,0,0} Coeff G :=
  Rep.subrepresentation (regRep G) (augSub G) (augSub_le_comap G)

/-- The inclusion `I → k[G]`. -/
noncomputable abbrev augIncl : augI G ⟶ regRep G :=
  Rep.subtype (regRep G) (augSub G) (augSub_le_comap G)

/-- The augmentation is surjective. -/
theorem epi_augHom : Epi (augHom G) := by
  rw [Rep.epi_iff_surjective]
  intro x
  refine ⟨MonoidAlgebra.single 1 x, ?_⟩
  rw [Rep.leftRegularHom_hom_single]
  simp

/-- The augmentation of a basis element is `1`. -/
theorem augHom_ebas (γ : G) : (augHom G).hom (ebas G γ) = 1 := by
  rw [show ebas G γ = MonoidAlgebra.single γ (1 : Coeff) from rfl,
    Rep.leftRegularHom_hom_single]
  simp

/-- `γ - 1` lies in the augmentation ideal. -/
noncomputable def augDiff (γ : G) : augI G :=
  ⟨ebas G γ - ebas G 1, by
    rw [show ebas G γ - ebas G 1 ∈ augSub G ↔
        (augHom G).hom (ebas G γ - ebas G 1) = 0 from Iff.rfl,
      map_sub, augHom_ebas G, augHom_ebas G]
    simp⟩

/-- `augIncl (γ - 1) = γ - 1`. -/
@[simp] theorem augIncl_augDiff (γ : G) :
    augIncl G (augDiff G γ) = ebas G γ - ebas G 1 := rfl

/-- The inclusion `I → k[G]` composed with the augmentation is zero. -/
theorem augIncl_comp_augHom : augIncl G ≫ augHom G = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Rep.hom_comp, Rep.zero_hom, Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.comp_apply, LinearMap.zero_apply]
  convert (LinearMap.mem_ker.mp (x : ↥(augSub G)).2) using 2
  show (Rep.subtype (regRep G) (augSub G) (augSub_le_comap G)).hom.toLinearMap x = (x : regRep G)
  rfl

/-- The short complex `0 → I → k[G] → k → 0`. -/
noncomputable abbrev augSES : ShortComplex (Rep.{0,0,0} Coeff G) :=
  ShortComplex.mk (augIncl G) (augHom G) (augIncl_comp_augHom G)

/-- The inclusion `I → k[G]` is a monomorphism. -/
instance instMonoAugIncl : Mono (augIncl G) := by
  rw [Rep.mono_iff_injective]
  intro a b hab
  exact Subtype.ext hab

/-! ## The derivation bridge -/

/-- The `Coeff`-linear map `Σ c_γ γ ↦ Σ c_γ • φ γ` on `k[G]`. -/
noncomputable def cocycleLin (M : Type) [AddCommGroup M] [Module Coeff M] (φ : G → M) :
    (MonoidAlgebra Coeff G) →ₗ[Coeff] M :=
  (Finsupp.linearCombination Coeff φ).comp
    (MonoidAlgebra.coeffLinearEquiv Coeff (S := Coeff) (M := G)).toLinearMap

end ExtH1
end Work.SSGRoute
