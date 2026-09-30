import Mathlib
import Submission.Work.SSSR.pbTransportDefs
import Submission.Work.SSSR.transportTransAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The source inclusion factors through the fibre over `0` of the pullback.**  The inclusion of
the fibre `p⁻¹b₀` into the pullback of `p` along `γ`, `e ↦ (e, 0)`, is the canonical homeomorphism
of the fibres over `b₀` and `γ 0`, followed by the inverse homeomorphism between the fibre of the
pullback over `0` and the fibre of `p` over `γ 0`, followed by the inclusion of the fibre over `0`
into the pullback. -/
theorem inclSource_eq (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    TopCat.ofHom (inclSource p γ) =
      TopCat.ofHom (↑(homeoFibreEq p γ.source'.symm) :
          C(Work.SSSR.StemsB.fibre p b₀, Work.SSSR.StemsB.fibre p (γ 0)))
      ≫ TopCat.ofHom (↑((pullbackFibreHomeo p γ.toContinuousMap 0).symm) :
          C(Work.SSSR.StemsB.fibre p (γ 0), pbZeroC p γ.toContinuousMap))
      ≫ Work.SSSR.Cohomology.subtypeIncl (TopCat.of (pbSpaceC p γ.toContinuousMap))
          (pbZeroC p γ.toContinuousMap) := by
  ext e
  exact Subtype.ext (Prod.ext rfl (Subtype.ext rfl))

/-- **The source chain map factors through the fibre over `0` of the pullback.**  The chain-level
form of `inclSource_eq`. -/
theorem sourceChainMap_eq (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    sourceChainMap p γ =
      Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p b₀))
        (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
        (TopCat.ofHom (↑(homeoFibreEq p γ.source'.symm) :
          C(Work.SSSR.StemsB.fibre p b₀, Work.SSSR.StemsB.fibre p (γ 0))))
      ≫ Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
          (TopCat.of (pbZeroC p γ.toContinuousMap))
          (TopCat.ofHom (↑((pullbackFibreHomeo p γ.toContinuousMap 0).symm) :
            C(Work.SSSR.StemsB.fibre p (γ 0), pbZeroC p γ.toContinuousMap)))
      ≫ Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p γ.toContinuousMap))
          (pbZeroC p γ.toContinuousMap) := by
  have h := congrArg (fun (φ : TopCat.of (Work.SSSR.StemsB.fibre p b₀) ⟶
      TopCat.of (pbSpaceC p γ.toContinuousMap)) =>
      Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p b₀))
        (TopCat.of (pbSpaceC p γ.toContinuousMap)) φ)
    (inclSource_eq p γ)
  simp only [Work.SSSR.Cohomology.chainMap, Functor.map_comp] at h
  exact h

/-- **The homology map of the source chain map is the first three factors of the transport.**  It
equals the endpoint identification `pathSrc` from the fibre over `b₀` to the fibre over `γ 0`,
followed by the inverse of the fibre homeomorphism over `0` of the pullback, followed by the
homology isomorphism induced by the inclusion of the fibre over `0`. -/
theorem sourceChainMap_homologyMap_eq (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    HomologicalComplex.homologyMap (sourceChainMap p γ) t
      = (pathSrc (R := R) p γ t).hom
        ≫ (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) t).inv
        ≫ (pbA p hp γ.toContinuousMap t).hom := by
  rw [sourceChainMap_eq p γ]
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have hA : HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p b₀))
        (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
        (TopCat.ofHom (↑(homeoFibreEq p γ.source'.symm) :
          C(Work.SSSR.StemsB.fibre p b₀, Work.SSSR.StemsB.fibre p (γ 0))))) t
      = (pathSrc p γ t).hom := by
    rw [show HomologicalComplex.homologyMap
        (Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p b₀))
          (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
          (TopCat.ofHom (↑(homeoFibreEq p γ.source'.symm) :
            C(Work.SSSR.StemsB.fibre p b₀, Work.SSSR.StemsB.fibre p (γ 0))))) t
        = HZmap (↑(homeoFibreEq p γ.source'.symm) :
            C(Work.SSSR.StemsB.fibre p b₀, Work.SSSR.StemsB.fibre p (γ 0))) t from rfl]
    rw [← HZHomeoIso_hom_HZmap, pathSrc, eqToIso_fibre_eq]
  have hB : HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
        (TopCat.of (pbZeroC p γ.toContinuousMap))
        (TopCat.ofHom (↑((pullbackFibreHomeo p γ.toContinuousMap 0).symm) :
          C(Work.SSSR.StemsB.fibre p (γ 0), pbZeroC p γ.toContinuousMap)))) t
      = (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 0) t).inv := by
    rw [show HomologicalComplex.homologyMap
        (Work.SSSR.Cohomology.chainMap R (TopCat.of (Work.SSSR.StemsB.fibre p (γ 0)))
          (TopCat.of (pbZeroC p γ.toContinuousMap))
          (TopCat.ofHom (↑((pullbackFibreHomeo p γ.toContinuousMap 0).symm) :
            C(Work.SSSR.StemsB.fibre p (γ 0), pbZeroC p γ.toContinuousMap)))) t
        = HZmap (↑((pullbackFibreHomeo p γ.toContinuousMap 0).symm) :
            C(Work.SSSR.StemsB.fibre p (γ 0), pbZeroC p γ.toContinuousMap)) t from rfl]
    rw [← HZHomeoIso_hom_HZmap, ← HZHomeoIso_symm]
    exact Iso.symm_hom _
  have hC : HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p γ.toContinuousMap))
        (pbZeroC p γ.toContinuousMap)) t
      = (pbA p hp γ.toContinuousMap t).hom :=
    (pbA_hom_eq p hp γ.toContinuousMap t).symm
  rw [hA, hB, hC]

theorem transportIsoPath_hom_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ) :
    (Work.SSSR.transportIsoPath p hp γ t).hom = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.SSSR.sourceChainMap (R := R) p γ) t) (Work.SSSR.transportPost p hp γ t) := by
  rw [transportIsoPath_eq p hp γ t, pathCore_eq p hp γ t]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [pullbackTransportIso_eq_pbIso p hp γ.toContinuousMap t, pbIso_hom_eq]
  rw [sourceChainMap_homologyMap_eq p hp γ t]
  rw [show (pathTgt p γ t).hom = (HZHomeoIso (homeoFibreEq p γ.target') t).hom from by
    rw [pathTgt, eqToIso_fibre_eq]]
  simp only [transportPost, Category.assoc]

end

end Work.SSSR
