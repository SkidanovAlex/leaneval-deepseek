import Mathlib
import Submission.Work.SSS.edgeTransport
import Submission.Work.SSS.Transport.Basic
import Submission.Work.SSS.FirstPage.HomElts

/-!
# The fibre inclusions of the pullback along a path, as isomorphisms on homology

Support definitions for `Submission/Work/SSS/transport_eq_topEnd.lean`: the two end-fibre
inclusions of the pullback of a Serre fibration along a path, their homology isomorphisms
`pbA`, `pbB`, the identification `pullbackTransportIso = pbA ≪≫ pbB.symm`, and the "post" factor
`transportPost` of the path transport.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The pullback of `p` along a path of the interval, as a type. -/
abbrev pbSpaceC (p : C(E, B)) (δ : C(unitInterval, B)) : Type :=
  Work.StemsB.Pullback p δ

/-- The fibre of the pullback over `0`. -/
abbrev pbZeroC (p : C(E, B)) (δ : C(unitInterval, B)) : Set (pbSpaceC p δ) :=
  {x | Work.StemsB.pullbackSnd p δ x = 0}

/-- The fibre of the pullback over `1`. -/
abbrev pbOneC (p : C(E, B)) (δ : C(unitInterval, B)) : Set (pbSpaceC p δ) :=
  {x | Work.StemsB.pullbackSnd p δ x = 1}

/-- The image of the homology class of a cycle under the homology map of a chain map, expressed
through the `cyclesMk` representative of the image. -/
theorem homologyMap_homologypi_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (n : ℕ) (c : K.cycles n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n))
        ((ModuleCat.Hom.hom (K.homologyπ n)) c)
      = (ModuleCat.Hom.hom (L.homologyπ n))
          (L.cyclesMk ((ModuleCat.Hom.hom (φ.f n)) ((ModuleCat.Hom.hom (K.iCycles n)) c))
            ((ComplexShape.down ℕ).next n) rfl
            (by
              show (ModuleCat.Hom.hom (L.d n ((ComplexShape.down ℕ).next n)))
                  ((ModuleCat.Hom.hom (φ.f n)) ((ModuleCat.Hom.hom (K.iCycles n)) c)) = 0
              rw [chainMap_comm_apply_C, iCycles_d_C, map_zero])) := by
  have h1 : (ModuleCat.Hom.hom (K.homologyπ n)) c
      = (ModuleCat.Hom.hom (K.homologyπ n))
          (K.cyclesMk ((ModuleCat.Hom.hom (K.iCycles n)) c) ((ComplexShape.down ℕ).next n) rfl
            (iCycles_d_C K n ((ComplexShape.down ℕ).next n) c)) := by
    rw [cyclesMk_iCycles_C]
  rw [h1, homologyMap_homologypi_C, cyclesMap_cyclesMk_C]

/-- The inclusion of the fibre over `0` of the pullback along a path is an isomorphism on
homology. -/
theorem hZisoC (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t) := by
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p δ) :=
    fun i => Work.StemsB.hasHLP_pullback p δ (hp i)
  exact Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.Serre.isZero_relChains_fibre_of_contraction
      (Work.StemsB.pullbackSnd p δ) hq 0 Work.StemsB.unitContrZero
      Work.StemsB.unitContrZero_zero Work.StemsB.unitContrZero_one
      Work.StemsB.unitContrZero_fixes m) t

/-- The inclusion of the fibre over `1` of the pullback along a path is an isomorphism on
homology. -/
theorem hWisoC (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t) := by
  have hq : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p δ) :=
    fun i => Work.StemsB.hasHLP_pullback p δ (hp i)
  exact Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.Serre.isZero_relChains_fibre_of_contraction
      (Work.StemsB.pullbackSnd p δ) hq 1 Work.StemsB.unitContrOne
      Work.StemsB.unitContrOne_zero Work.StemsB.unitContrOne_one
      Work.StemsB.unitContrOne_fixes m) t

/-- The inclusion of the fibre over `0` of the pullback, as an isomorphism on homology. -/
def pbA (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.PiS.HZ (pbZeroC p δ) t ≅ Work.PiS.HZ (pbSpaceC p δ) t := by
  haveI := hZisoC p hp δ t
  exact asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t)

/-- The inclusion of the fibre over `1` of the pullback, as an isomorphism on homology. -/
def pbB (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.PiS.HZ (pbOneC p δ) t ≅ Work.PiS.HZ (pbSpaceC p δ) t := by
  haveI := hWisoC p hp δ t
  exact asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t)

/-- The transport of the pullback of `p` along `δ`, in the explicit shape of the two fibre
inclusions. -/
def pbIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.PiS.HZ (pbZeroC p δ) t ≅ Work.PiS.HZ (pbOneC p δ) t :=
  pbA p hp δ t ≪≫ (pbB p hp δ t).symm

/-- **The transport of the pullback is the composite of the two fibre inclusions.** -/
theorem pullbackTransportIso_eq_pbIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : ℕ) :
    pullbackTransportIso p hp δ t = pbIso p hp δ t := by
  refine Iso.ext ?_
  simp only [pbIso, pbA, pbB, pullbackTransportIso, Iso.trans_hom, asIso_hom, Iso.symm_hom]

/-- The forward map of `pbA` is the homology map of the inclusion. -/
theorem pbA_hom_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbA p hp δ t).hom = HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t := by
  simp only [pbA, asIso_hom]

/-- The forward map of `pbB` is the homology map of the inclusion. -/
theorem pbB_hom_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbB p hp δ t).hom = HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t := by
  simp only [pbB, asIso_hom]

/-- The forward map of `pbIso` is the first inclusion followed by the inverse of the second. -/
theorem pbIso_hom_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbIso p hp δ t).hom = (pbA p hp δ t).hom ≫ (pbB p hp δ t).inv := by
  simp only [pbIso, Iso.trans_hom, Iso.symm_hom]


/-- The part of the transport after the pullback transport. -/
def transportPost (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B}
    (γ : Path b₀ b₁) (t : ℕ) :
    Work.PiS.HZ (pbSpaceC p γ.toContinuousMap) t ⟶
      Work.PiS.HZ (Work.StemsB.fibre p b₁) t :=
  (pbB p hp γ.toContinuousMap t).inv ≫
    (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) t).hom ≫
    (HZHomeoIso (homeoFibreEq p γ.target') t).hom

end

end Work.SSS
