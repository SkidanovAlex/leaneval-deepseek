import Mathlib
import Submission.Work.SSSR.transportTransAux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.TransHalf

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
/-- The forward map of `inclIso` is the homology map induced by the inclusion of the fibre. -/
theorem inclIso_hom {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) (δ : C(unitInterval, B))
    (t : unitInterval) (j : ℕ) :
    (Work.SSSR.inclIso (R := R) p hp δ t j).hom =
      Work.SSSR.inclHZ (Work.SSSR.StemsB.Pullback p δ)
        {x : Work.SSSR.StemsB.Pullback p δ | Work.SSSR.StemsB.pullbackSnd p δ x = t} j :=
  rfl

/-- **Generic cancellation of a common morphism.**  If the transports `i₀ ≫ i₁⁻¹` and
`α ≫ h₀ ≫ h₁⁻¹ ≫ β⁻¹` agree after the identifications `α`, `β` of the sources, then they agree. -/
theorem isoCancelAux {C : Type*} [Category C] {A B A' B' D E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A' ≅ E) (h₁ : B' ≅ E) (j : E ⟶ D)
    (α : A ≅ A') (β : B ≅ B')
    (e₀ : α.hom ≫ h₀.hom ≫ j = i₀.hom) (e₁ : β.hom ≫ h₁.hom ≫ j = i₁.hom) :
    i₀.hom ≫ i₁.inv = α.hom ≫ h₀.hom ≫ h₁.inv ≫ β.inv := by
  have hkey : h₁.inv ≫ β.inv ≫ i₁.hom = j := by
    rw [← e₁]
    simp only [Iso.inv_hom_id_assoc]
  calc i₀.hom ≫ i₁.inv
      = α.hom ≫ h₀.hom ≫ j ≫ i₁.inv := by rw [← e₀]; simp only [Category.assoc]
    _ = α.hom ≫ h₀.hom ≫ (h₁.inv ≫ β.inv ≫ i₁.hom) ≫ i₁.inv := by rw [hkey]
    _ = α.hom ≫ h₀.hom ≫ h₁.inv ≫ β.inv := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism form of `isoCancelAux`. -/
theorem isoCancelAuxIso {C : Type*} [Category C] {A B A' B' D E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A' ≅ E) (h₁ : B' ≅ E) (j : E ⟶ D)
    (α : A ≅ A') (β : B ≅ B')
    (e₀ : α.hom ≫ h₀.hom ≫ j = i₀.hom) (e₁ : β.hom ≫ h₁.hom ≫ j = i₁.hom) :
    i₀ ≪≫ i₁.symm = α ≪≫ h₀ ≪≫ h₁.symm ≪≫ β.symm :=
  Iso.ext (isoCancelAux i₀ i₁ h₀ h₁ j α β e₀ e₁)

/-- The first half of the transport of the pullback of `p` along the concatenation `γ.trans δ`
agrees with the transport along `γ` conjugated by the homeomorphisms induced by the
reparametrisation `φ : (e,t) ↦ (e, t/2)` of the pullback (on the fibres over `0` and over `1`;
the second is the homeomorphism onto the fibre of the pullback over the junction point `1/2`). -/
theorem halfLeft_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.SSSR.StemsB.IsSerreFibration p) {b b' b'' : B}
    (γ : Path b b') (δ : Path b' b'') (j : ℕ) :
    Work.SSSR.halfLeft p hp γ δ j =
      CategoryTheory.Iso.trans
        (CategoryTheory.Iso.symm (Work.SSSR.HZHomeoIso (Work.SSSR.phiZeroHomeo p γ δ) j))
        (CategoryTheory.Iso.trans (Work.SSSR.pathTrans (R := R) p hp γ j)
          (Work.SSSR.HZHomeoIso (Work.SSSR.phiTwelfthHomeo p γ δ) j)) := by
  have e₀ : (Work.SSSR.HZHomeoIso (Work.SSSR.phiZeroHomeo p γ δ) j).inv ≫
        (Work.SSSR.inclIso p hp γ.toContinuousMap 0 j).hom ≫
        Work.SSSR.HZmap (R := R) (Work.SSSR.phiMap p γ δ) j
      = (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap 0 j).hom := by
    have sq := Work.SSSR.inclHZ_phiMap_zero (R := R) p γ δ j
    rw [← Work.SSSR.HZHomeoIso_hom_HZmap] at sq
    rw [inclIso_hom, inclIso_hom, sq, Iso.inv_hom_id_assoc]
  have e₁ : (Work.SSSR.HZHomeoIso (Work.SSSR.phiTwelfthHomeo p γ δ) j).inv ≫
        (Work.SSSR.inclIso p hp γ.toContinuousMap 1 j).hom ≫
        Work.SSSR.HZmap (R := R) (Work.SSSR.phiMap p γ δ) j
      = (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap midI j).hom := by
    have sq := Work.SSSR.inclHZ_phiMap_mid (R := R) p γ δ j
    rw [← Work.SSSR.HZHomeoIso_hom_HZmap] at sq
    rw [inclIso_hom, inclIso_hom, sq, Iso.inv_hom_id_assoc]
  have hc := isoCancelAuxIso
      (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap 0 j)
      (Work.SSSR.inclIso p hp (γ.trans δ).toContinuousMap midI j)
      (Work.SSSR.inclIso p hp γ.toContinuousMap 0 j)
      (Work.SSSR.inclIso p hp γ.toContinuousMap 1 j)
      (Work.SSSR.HZmap (Work.SSSR.phiMap p γ δ) j)
      (Work.SSSR.HZHomeoIso (Work.SSSR.phiZeroHomeo p γ δ) j).symm
      (Work.SSSR.HZHomeoIso (Work.SSSR.phiTwelfthHomeo p γ δ) j).symm e₀ e₁
  rw [Work.SSSR.halfLeft, Work.SSSR.pbTrans, hc]
  rw [Work.SSSR.pathTrans, Work.SSSR.pbTrans]
  simp only [Iso.symm_symm_eq, Iso.trans_assoc]

end Work.SSSR.TransHalf
