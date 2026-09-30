import Mathlib
import Submission.Work.SSSR.edgeTransport
import Submission.Work.SSSR.pbTransportDefs
import Submission.Work.SSSR.Transport.Basic
import Submission.Work.SSSR.FirstPage.HomElts
import Submission.Work.SSSR.spread_boundary_apply
import Submission.Work.SSSR.transportIsoPath_hom_eq
import Submission.Work.SSSR.targetChainMap_comp_transportPost
import Submission.Work.SSSR.Stems.hurewiczMapN_surjective
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The image of the homology class of a `cyclesMk` under the homology map of a chain map. -/
theorem homologyMap_homologypi_cyclesMk' {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L)
    (n j : ℕ) (hj : (ComplexShape.down ℕ).next n = j) (x : K.X n)
    (hx : (ModuleCat.Hom.hom (K.d n j)) x = 0)
    (hy : (ModuleCat.Hom.hom (L.d n j)) ((ModuleCat.Hom.hom (φ.f n)) x) = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n))
        ((ModuleCat.Hom.hom (K.homologyπ n)) (K.cyclesMk x j hj hx))
      = (ModuleCat.Hom.hom (L.homologyπ n)) (L.cyclesMk ((ModuleCat.Hom.hom (φ.f n)) x) j hj hy) := by
  rw [homologyMap_homologypi_C, cyclesMap_cyclesMk_C]

/-- **The pointwise form of the transport factorisation.** -/
theorem transportIsoPath_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (x : (Work.SSSR.Stems.hChain (Work.SSSR.StemsB.fibre p b₀)).homology t) :
    (Work.SSSR.transportIsoPath p hp γ t).hom x
      = (ModuleCat.Hom.hom (transportPost p hp γ t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap (R := R) p γ) t)) x) := by
  rw [transportIsoPath_hom_eq p hp γ t]
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t
        ≫ transportPost p hp γ t)) x
      = (ModuleCat.Hom.hom (transportPost p hp γ t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t)) x)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- **The post factor inverts the target inclusion on homology.** -/
theorem transportPost_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (w : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₁) t) :
    (ModuleCat.Hom.hom (transportPost p hp γ t))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t)) w) = w := by
  have h1 := congrArg (fun (φ : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₁) t ⟶
      Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b₁) t) => (ModuleCat.Hom.hom φ) w)
    (targetChainMap_comp_transportPost p hp γ t)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  change (ModuleCat.Hom.hom (transportPost p hp γ t))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t)) w) = w at h1
  exact h1

end

end Work.SSSR
