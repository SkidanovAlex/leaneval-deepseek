import Mathlib
import Submission.Work.SSS.pbTransportDefs
import Submission.Work.SSS.transportTransAux

/-!
# `targetChainMap` is a right inverse of the "post" factor of the path transport

For a Serre fibration `p : E → B`, a path `γ : b₀ → b₁` and a degree `t`, the chain map
`Work.SSS.targetChainMap p γ` is the inclusion of the fibre `p⁻¹(b₁)` into the pullback
`Pullback p γ.toContinuousMap` along the target endpoint.  Its effect on homology followed by the
"post" part `Work.SSS.transportPost p hp γ t` of the fibre transport is the identity of
`H_t(p⁻¹(b₁); ℤ)`.

The two ingredients are:

* `inclTarget_eq` — the inclusion of the fibre over the *target* of the path factors through the
  endpoint homeomorphisms `homeoFibreEq p γ.target'` (from `p⁻¹(γ 1)` to `p⁻¹b₁`) and
  `pullbackFibreHomeo p γ.toContinuousMap 1` (from `p⁻¹(γ 1)` to the fibre over `1` of the
  pullback) and the inclusion of the latter fibre into the pullback;
* `targetChainMap_homologyMap_eq` — the resulting description of the homology map of
  `targetChainMap` as the inverse of the two endpoint homeomorphism isomorphisms followed by the
  homology isomorphism `pbB`, whose `.inv` is the first factor of `transportPost`.

The final step is the cancellation `pbB.hom ≫ pbB.inv = 𝟙`, `C.inv ≫ C.hom = 𝟙`,
`D.inv ≫ D.hom = 𝟙` of the isomorphisms that make up `transportPost`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The inclusion of the fibre of the pullback over `1` into the pullback, as a continuous map. -/
def inclOneC (p : C(E, B)) (δ : C(unitInterval, B)) : C(pbOneC p δ, pbSpaceC p δ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the fibre over `1` of the pullback agrees with the canonical inclusion of a
subspace. -/
lemma ofHom_inclOneC (p : C(E, B)) (δ : C(unitInterval, B)) :
    TopCat.ofHom (inclOneC p δ)
      = Work.Cohomology.subtypeIncl (TopCat.of (pbSpaceC p δ)) (pbOneC p δ) := rfl

/-- **The inclusion of the fibre over the target of the path, factored through the endpoint
homeomorphisms.**  The inclusion `p⁻¹(b₁) → Pullback p γ` is the composite of the inverse of
`homeoFibreEq p γ.target'`, the inverse of `pullbackFibreHomeo p γ.toContinuousMap 1`, and the
inclusion of the fibre of the pullback over `1`. -/
lemma inclTarget_eq (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    inclTarget p γ =
      (inclOneC p γ.toContinuousMap).comp
        (((pullbackFibreHomeo p γ.toContinuousMap 1).symm :
            C(Work.StemsB.fibre p (γ 1), pbOneC p γ.toContinuousMap)).comp
          (((homeoFibreEq p γ.target').symm :
            C(Work.StemsB.fibre p b₁, Work.StemsB.fibre p (γ 1))))) := by
  ext e
  refine Subtype.ext ?_
  rfl

/-- The inverse of the homology isomorphism induced by a homeomorphism is the homology map of the
inverse homeomorphism. -/
lemma HZHomeoIso_inv_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (j : ℕ) :
    (HZHomeoIso e j).inv = HZmap (e.symm : C(Y, X)) j := by
  rw [show (HZHomeoIso e j).inv = (HZHomeoIso e j).symm.hom from rfl, HZHomeoIso_symm',
    HZHomeoIso_hom_HZmap]

/-- The homology map of the inclusion of the fibre over `1` of the pullback is `pbB`. -/
lemma HZmap_inclOneC (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : ℕ) :
    HZmap (inclOneC p δ) t = (pbB p hp δ t).hom := by
  rw [pbB_hom_eq, HZmap, Work.Cohomology.inclChains]
  rfl

/-- **The homology map of `targetChainMap` in terms of the fibre endpoint isomorphisms.** -/
theorem targetChainMap_homologyMap_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    HomologicalComplex.homologyMap (targetChainMap p γ) t
      = (HZHomeoIso (homeoFibreEq p γ.target') t).inv
        ≫ (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) t).inv
        ≫ (pbB p hp γ.toContinuousMap t).hom := by
  rw [show HomologicalComplex.homologyMap (targetChainMap p γ) t = HZmap (inclTarget p γ) t
      from rfl]
  rw [HZmap_congr (inclTarget_eq p γ) t, HZmap_comp, HZmap_comp]
  rw [HZHomeoIso_inv_hom, HZHomeoIso_inv_hom, ← HZmap_inclOneC p hp γ.toContinuousMap t]
  simp only [Category.assoc]

theorem targetChainMap_comp_transportPost {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.SSS.targetChainMap p γ) t) (Work.SSS.transportPost p hp γ t) = CategoryTheory.CategoryStruct.id ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).homology t) := by
  rw [transportPost, targetChainMap_homologyMap_eq p hp γ t]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

end

end Work.SSS
