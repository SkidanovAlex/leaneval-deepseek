import Mathlib
import Submission.Work.SSSR.pbTransportDefs
import Submission.Work.SSSR.transportTransAux
import Submission.Work.SSSR.Stems.hurewiczMapN_surjective
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial
namespace Work.SSSR

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The inclusion of the fibre of the pullback over `1` into the pullback, as a continuous map. -/
def inclOneC (p : C(E, B)) (δ : C(unitInterval, B)) : C(pbOneC p δ, pbSpaceC p δ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The inclusion of the fibre over the target of the path, factored through the endpoint
homeomorphisms.**  The inclusion `p⁻¹(b₁) → Pullback p γ` is the composite of the inverse of
`homeoFibreEq p γ.target'`, the inverse of `pullbackFibreHomeo p γ.toContinuousMap 1`, and the
inclusion of the fibre of the pullback over `1`. -/
lemma inclTarget_eq (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    inclTarget p γ =
      (inclOneC p γ.toContinuousMap).comp
        (((pullbackFibreHomeo p γ.toContinuousMap 1).symm :
            C(Work.SSSR.StemsB.fibre p (γ 1), pbOneC p γ.toContinuousMap)).comp
          (((homeoFibreEq p γ.target').symm :
            C(Work.SSSR.StemsB.fibre p b₁, Work.SSSR.StemsB.fibre p (γ 1))))) := by
  ext e
  refine Subtype.ext ?_
  rfl

/-- The inverse of the homology isomorphism induced by a homeomorphism is the homology map of the
inverse homeomorphism. -/
lemma HZHomeoIso_inv_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (j : ℕ) :
    (HZHomeoIso (R := R) e j).inv = HZmap (e.symm : C(Y, X)) j := by
  rw [show (HZHomeoIso e j).inv = (HZHomeoIso e j).symm.hom from rfl, HZHomeoIso_symm',
    HZHomeoIso_hom_HZmap]

/-- The homology map of the inclusion of the fibre over `1` of the pullback is `pbB`. -/
lemma HZmap_inclOneC (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : ℕ) :
    HZmap (inclOneC p δ) t = (pbB (R := R) p hp δ t).hom := by
  rw [pbB_hom_eq, HZmap, Work.SSSR.Cohomology.inclChains]
  rfl

/-- **The homology map of `targetChainMap` in terms of the fibre endpoint isomorphisms.** -/
theorem targetChainMap_homologyMap_eq (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    HomologicalComplex.homologyMap (targetChainMap (R := R) p γ) t
      = (HZHomeoIso (homeoFibreEq p γ.target') t).inv
        ≫ (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) t).inv
        ≫ (pbB p hp γ.toContinuousMap t).hom := by
  rw [show HomologicalComplex.homologyMap (targetChainMap p γ) t = HZmap (inclTarget p γ) t
      from rfl]
  rw [HZmap_congr (inclTarget_eq p γ) t, HZmap_comp, HZmap_comp]
  rw [HZHomeoIso_inv_hom, HZHomeoIso_inv_hom, ← HZmap_inclOneC p hp γ.toContinuousMap t]
  simp only [Category.assoc]

theorem targetChainMap_comp_transportPost {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.SSSR.targetChainMap (R := R) p γ) t) (Work.SSSR.transportPost p hp γ t) = CategoryTheory.CategoryStruct.id ((Work.SSSR.Stems.hChain (Work.SSSR.StemsB.fibre p b₁)).homology t) := by
  rw [transportPost, targetChainMap_homologyMap_eq p hp γ t]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

end

end Work.SSSR
