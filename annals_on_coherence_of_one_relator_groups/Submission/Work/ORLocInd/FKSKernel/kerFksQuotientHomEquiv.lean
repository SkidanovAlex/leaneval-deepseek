/-
# The kernel of `⟨X | u ^ l⟩ →* ⟨X | u⟩` is `⟪u⟫ / ⟪u ^ l⟫`

This file supplies the first reduction needed for the algebraic FKS structure theorem
(`Work.ORLocInd.FKSKernelStructure`, see `Submission/Work/ORLocInd/FKSKernel/fksKernelStructure.lean`):

> `ker (fksQuotientHom P) ≃* ⟪u⟫ / ⟪u ^ l⟫`,

where `⟪u⟫ = Subgroup.normalClosure {P.u}` and `⟪u ^ l⟫ = Subgroup.normalClosure {P.u ^ P.l}` are the
normal closures in the free group `FreeGroup P.α`, and `fksQuotientHom P` is the canonical map
`G →* ⟨X | u⟩` of `Work.ORLocInd.FKSStruc`.

Since `PresentedGroup {r} = FreeGroup α ⧸ Subgroup.normalClosure {r}`, the map `fksQuotientHom P`
is the map of quotients `F ⧸ ⟪u ^ l⟫ →* F ⧸ ⟪u⟫` induced by the identity of `F` (transported to `G`
along `P.equiv`).  Its kernel is therefore the image of `⟪u⟫` in `F ⧸ ⟪u ^ l⟫`, which by the first
isomorphism theorem is `⟪u⟫ / (⟪u ^ l⟫ ⊓ ⟪u⟫) = ⟪u⟫ / ⟪u ^ l⟫`, because `u ^ l ∈ ⟪u⟫`.

The two ingredients are

* `Work.ORLocInd.FKSKernel.kerCompMulEquiv`: the kernel of `φ ∘ e` for an isomorphism `e` is the
  kernel of `φ` (used to transport along `P.equiv`);
* `Work.ORLocInd.FKSKernel.quotientKerSubgroupEquivMap`: the subgroup-restricted first isomorphism
  theorem `K ⧸ (ker f).subgroupOf K ≃* K.map f`.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORLocInd.FKSKernel.kerCompMulEquiv
import Submission.Work.ORLocInd.FKSKernel.quotientKerSubgroupEquivMap

set_option autoImplicit false

universe u

namespace Work.ORLocInd.FKSKernel

/-- The map of presented groups `⟨X | u ^ l⟩ →* ⟨X | u⟩` induced by the identity of the free group
`FreeGroup P.α`: it is the quotient map `F ⧸ ⟪u ^ l⟫ →* F ⧸ ⟪u⟫`, which exists because
`⟪u ^ l⟫ ≤ ⟪u⟫`. -/
noncomputable def fksQuotientAux {G : Type u} [Group G] (P : RootPresentation G) :
    PresentedGroup ({P.u ^ P.l} : Set (FreeGroup P.α)) →*
      PresentedGroup ({P.u} : Set (FreeGroup P.α)) :=
  QuotientGroup.map (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α)))
    (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) (MonoidHom.id (FreeGroup P.α))
    (Subgroup.normalClosure_le_normal fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.pow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton P.u)) P.l)

/-- `fksQuotientHom P` is exactly `fksQuotientAux P`, transported to `G` along `P.equiv`. -/
theorem fksQuotientHom_eq {G : Type u} [Group G] (P : RootPresentation G) :
    fksQuotientHom P = (fksQuotientAux P).comp P.equiv.symm.toMonoidHom := by
  unfold Work.ORLocInd.fksQuotientHom
  show (PresentedGroup.toGroup _).comp _ = (fksQuotientAux P).comp _
  congr 1
  apply PresentedGroup.ext
  intro a
  show PresentedGroup.mk {P.u} (FreeGroup.of a) =
    (QuotientGroup.map (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α)))
      (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) (MonoidHom.id (FreeGroup P.α)) _)
      ((QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
        (FreeGroup.of a))
  rw [QuotientGroup.map_mk']
  rfl

/-- The kernel of the map of presented groups `⟨X | u ^ l⟩ →* ⟨X | u⟩` is the image of `⟪u⟫` in
`F ⧸ ⟪u ^ l⟫` (`QuotientGroup.ker_map`). -/
theorem fksQuotientAux_ker {G : Type u} [Group G] (P : RootPresentation G) :
    (fksQuotientAux P).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) := by
  unfold fksQuotientAux
  change (QuotientGroup.map (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α)))
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) (MonoidHom.id (FreeGroup P.α)) _).ker
      = Subgroup.map
        (QuotientGroup.mk'
          (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α)))
  rw [QuotientGroup.ker_map]
  rw [Subgroup.comap_id]

theorem kerFksQuotientHomEquiv {G : Type u} [Group G] (P : Work.ORLocInd.RootPresentation G) :
    Nonempty ((fksQuotientHom P).ker ≃*
      (↥(Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α)))
        ⧸ (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))).subgroupOf
            (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))))) := by
  -- Step 1: transport the kernel along the isomorphism `P.equiv : ⟨X | u ^ l⟩ ≃* G`.
  have h1 : (fksQuotientHom P).ker =
      ((fksQuotientAux P).comp P.equiv.symm.toMonoidHom).ker := by
    rw [fksQuotientHom_eq P]
    rfl
  obtain ⟨e1⟩ := kerCompMulEquiv P.equiv.symm (fksQuotientAux P)
  -- Step 2: the kernel of the map of presented groups is the image of `⟪u⟫` in `F ⧸ ⟪u ^ l⟫`.
  have h2 : (fksQuotientAux P).ker =
      Subgroup.map
        (QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) :=
    fksQuotientAux_ker P
  -- Step 3: the subgroup-restricted first isomorphism theorem identifies that image with
  -- `⟪u⟫ / (⟪u ^ l⟫ ⊓ ⟪u⟫) = ⟪u⟫ / ⟪u ^ l⟫`.
  obtain ⟨e3⟩ := quotientKerSubgroupEquivMap
    (QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
    (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α)))
  have hker : (MonoidHom.ker
        (QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))).subgroupOf
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α)))
      = (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))).subgroupOf
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) := by
    rw [QuotientGroup.ker_mk']
  have hh1 : (fksQuotientHom P).ker ≃*
      ((fksQuotientAux P).comp P.equiv.symm.toMonoidHom).ker :=
    MulEquiv.subgroupCongr h1
  have hh2 : (fksQuotientAux P).ker ≃*
      Subgroup.map
        (QuotientGroup.mk' (Subgroup.normalClosure ({P.u ^ P.l} : Set (FreeGroup P.α))))
        (Subgroup.normalClosure ({P.u} : Set (FreeGroup P.α))) :=
    MulEquiv.subgroupCongr h2
  exact ⟨(hh1.trans e1).trans (hh2.trans ((e3.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hker)))⟩

end Work.ORLocInd.FKSKernel
