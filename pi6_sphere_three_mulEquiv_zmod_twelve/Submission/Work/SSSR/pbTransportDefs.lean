import Mathlib
import Submission.Work.SSSR.edgeTransport
import Submission.Work.SSSR.Transport.Basic
import Submission.Work.SSSR.FirstPage.HomElts
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The pullback of `p` along a path of the interval, as a type. -/
abbrev pbSpaceC (p : C(E, B)) (δ : C(unitInterval, B)) : Type :=
  Work.SSSR.StemsB.Pullback p δ

/-- The fibre of the pullback over `0`. -/
abbrev pbZeroC (p : C(E, B)) (δ : C(unitInterval, B)) : Set (pbSpaceC p δ) :=
  {x | Work.SSSR.StemsB.pullbackSnd p δ x = 0}

/-- The fibre of the pullback over `1`. -/
abbrev pbOneC (p : C(E, B)) (δ : C(unitInterval, B)) : Set (pbSpaceC p δ) :=
  {x | Work.SSSR.StemsB.pullbackSnd p δ x = 1}

/-- The inclusion of the fibre over `0` of the pullback along a path is an isomorphism on
homology. -/
theorem hZisoC (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) : IsIso (HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t) := by
  have hq : Work.SSSR.StemsB.IsSerreFibration (Work.SSSR.StemsB.pullbackSnd p δ) :=
    fun i => Work.SSSR.StemsB.hasHLP_pullback p δ (hp i)
  exact Work.SSSR.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.SSSR.Serre.isZero_relChains_fibre_of_contraction
      (Work.SSSR.StemsB.pullbackSnd p δ) hq 0 Work.SSSR.StemsB.unitContrZero
      Work.SSSR.StemsB.unitContrZero_zero Work.SSSR.StemsB.unitContrZero_one
      Work.SSSR.StemsB.unitContrZero_fixes m) t

/-- The inclusion of the fibre over `1` of the pullback along a path is an isomorphism on
homology. -/
theorem hWisoC (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) : IsIso (HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t) := by
  have hq : Work.SSSR.StemsB.IsSerreFibration (Work.SSSR.StemsB.pullbackSnd p δ) :=
    fun i => Work.SSSR.StemsB.hasHLP_pullback p δ (hp i)
  exact Work.SSSR.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.SSSR.Serre.isZero_relChains_fibre_of_contraction
      (Work.SSSR.StemsB.pullbackSnd p δ) hq 1 Work.SSSR.StemsB.unitContrOne
      Work.SSSR.StemsB.unitContrOne_zero Work.SSSR.StemsB.unitContrOne_one
      Work.SSSR.StemsB.unitContrOne_fixes m) t

/-- The inclusion of the fibre over `0` of the pullback, as an isomorphism on homology. -/
def pbA (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.SSSR.PiS.HZ R (pbZeroC p δ) t ≅ Work.SSSR.PiS.HZ R (pbSpaceC p δ) t := by
  haveI := hZisoC (R := R) p hp δ t
  exact asIso (HomologicalComplex.homologyMap
    (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t)

/-- The inclusion of the fibre over `1` of the pullback, as an isomorphism on homology. -/
def pbB (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.SSSR.PiS.HZ R (pbOneC p δ) t ≅ Work.SSSR.PiS.HZ R (pbSpaceC p δ) t := by
  haveI := hWisoC (R := R) p hp δ t
  exact asIso (HomologicalComplex.homologyMap
    (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t)

/-- The transport of the pullback of `p` along `δ`, in the explicit shape of the two fibre
inclusions. -/
def pbIso (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B)) (t : ℕ) :
    Work.SSSR.PiS.HZ R (pbZeroC p δ) t ≅ Work.SSSR.PiS.HZ R (pbOneC p δ) t :=
  pbA p hp δ t ≪≫ (pbB p hp δ t).symm

/-- **The transport of the pullback is the composite of the two fibre inclusions.** -/
theorem pullbackTransportIso_eq_pbIso (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p)
    (δ : C(unitInterval, B)) (t : ℕ) :
    pullbackTransportIso p hp δ t = pbIso (R := R) p hp δ t := by
  refine Iso.ext ?_
  simp only [pbIso, pbA, pbB, pullbackTransportIso, Iso.trans_hom, asIso_hom, Iso.symm_hom]

/-- The forward map of `pbA` is the homology map of the inclusion. -/
theorem pbA_hom_eq (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbA p hp δ t).hom = HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbZeroC p δ)) t := by
  simp only [pbA, asIso_hom]

/-- The forward map of `pbB` is the homology map of the inclusion. -/
theorem pbB_hom_eq (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbB p hp δ t).hom = HomologicalComplex.homologyMap
      (Work.SSSR.Cohomology.inclChains R (TopCat.of (pbSpaceC p δ)) (pbOneC p δ)) t := by
  simp only [pbB, asIso_hom]

/-- The forward map of `pbIso` is the first inclusion followed by the inverse of the second. -/
theorem pbIso_hom_eq (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : ℕ) :
    (pbIso p hp δ t).hom = (pbA (R := R) p hp δ t).hom ≫ (pbB p hp δ t).inv := by
  simp only [pbIso, Iso.trans_hom, Iso.symm_hom]


/-- The part of the transport after the pullback transport. -/
def transportPost (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b₀ b₁ : B}
    (γ : Path b₀ b₁) (t : ℕ) :
    Work.SSSR.PiS.HZ R (pbSpaceC p γ.toContinuousMap) t ⟶
      Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₁) t :=
  (pbB p hp γ.toContinuousMap t).inv ≫
    (HZHomeoIso (pullbackFibreHomeo p γ.toContinuousMap 1) t).hom ≫
    (HZHomeoIso (homeoFibreEq p γ.target') t).hom

end

end Work.SSSR
