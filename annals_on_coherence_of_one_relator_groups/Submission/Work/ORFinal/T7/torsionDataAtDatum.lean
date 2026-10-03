import Mathlib
import Submission.Work.ORFinal.Final
import Submission.Work.ORFinal.TorsionData.torsionDataOf
import Submission.Work.ORLocInd.Main
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORTorsion.Defs
import Submission.Work.OROneRel.exists_root

namespace Work.ORFinal.T7

open Work

/-- **A `TorsionData` with prescribed root.**  The construction of
`Work.ORFinal.TorsionData.torsionDataOf`, but returning the structure itself (rather than just a
`Nonempty`) so that the root `u` is retained definitionally. -/
theorem exists_torsionData_eq (K : Type*) [Field K] [CharZero K] (G : Type*) [Group G]
    (U : Type*) [Ring U] [Nontrivial U] [Algebra K U] (L : Work.ORLinnell.LinnellDatum K G U)
    (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex] (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (u : G) (hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure {u})) :
    ∃ T : Work.ORTorsion.TorsionData K G U, T.u = u := by
  classical
  refine ⟨⟨L.gen, Work.ORFinal.TorsionData.Dsub L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u, hq, ?_⟩,
    rfl⟩
  · intro H h
    exact L.gen_mem H h
  · intro H₁ H₂ h
    exact Work.ORFinal.TorsionData.Dsub_mono L h
  · intro H
    exact L.isDivisionClosed H
  · intro H A hA hclosed
    exact L.minimal H A.toSubring (fun h => hA h) (fun k => A.algebraMap_mem k) hclosed
  · intro H n g hg a ha hsum i
    exact L.independence H n g hg a ha hsum i
  · intro g H x hx
    exact L.conjugation g H x hx
  · intro H
    exact Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_divisionOn K G U L G'
      (inferInstance : G'.Normal) (inferInstance : G'.FiniteIndex)
      (fun x hx => hdiv G' hG'tf x hx) H
  · intro H φ hφ
    exact Work.ORFinal.TorsionData.laurentBaseOf L G' hG'tf hdiv H φ hφ

/-- **The quotient of a one-relator group by the normal closure of its root is locally
indicable.**  Here `G = ⟨Fin n | r⟩` with `r = u ^ l` (`l ≥ 1`) and `u` not a proper power; the
quotient `G ⧸ ⟨⟨u⟩⟩` is the torsion-free one-relator group `⟨Fin n | u⟩`, which is locally
indicable by Brodskii's theorem. -/
theorem locallyIndicable_quotient_normalClosure_presentRho (n : ℕ) (r u : FreeGroup (Fin n))
    (l : ℕ) (hl : 1 ≤ l) (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u) :
    Work.ORLocInd.Group.LocallyIndicable
      (PresentedGroup ({r} : Set (FreeGroup (Fin n))) ⧸
        Subgroup.normalClosure {Work.ORLyndon.presentRho r u}) := by
  classical
  -- `u` is not a proper power in the `ORLocInd` sense either
  have hpp' : ¬ Work.ORLocInd.IsProperPower u :=
    fun h => hpp (Work.ORLocInd.orOneRel_isProperPower_of_isProperPower h)
  -- `⟨Fin n | u⟩` is a torsion-free one-relator group, hence locally indicable (Brodskii)
  have hLIu : Work.ORLocInd.Group.LocallyIndicable
      (PresentedGroup ({u} : Set (FreeGroup (Fin n)))) :=
    Work.ORLocInd.torsionFree_oneRelator_locallyIndicable
      (Work.OROneRel.group_oneRelator_presentedGroup u)
      (Work.ORLocInd.isTorsionFree_presentedGroup_of_not_isProperPower u hpp'
        Work.OROneRel.oneRelatorCombinatorics)
  -- the normal closure of `r` is contained in that of `u`, because `r = u ^ l`
  have hle : Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))
      ≤ Subgroup.normalClosure ({u} : Set (FreeGroup (Fin n))) := by
    refine Subgroup.normalClosure_le_normal (fun x hx => ?_)
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hpow ▸ Subgroup.pow_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton u)) l
  -- the image of the normal closure of `u` is the normal closure of the image of `u`
  have hMap : ((Subgroup.normalClosure ({u} : Set (FreeGroup (Fin n)))).map
        (QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n))))))
      = Subgroup.normalClosure
          ({QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))) u} :
          Set (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n))))) := by
    rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), Set.image_singleton]
  -- Noether's third isomorphism theorem: `⟨Fin n | r⟩ / ⟨⟨u⟩⟩ ≃* ⟨Fin n | u⟩`
  have e : ((FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))) ⧸
        (Subgroup.normalClosure ({u} : Set (FreeGroup (Fin n)))).map
          (QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n))))))
      ≃* (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({u} : Set (FreeGroup (Fin n)))) :=
    QuotientGroup.quotientQuotientEquivQuotient _ _ hle
  have e1 : ((FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))) ⧸
        (Subgroup.normalClosure ({u} : Set (FreeGroup (Fin n)))).map
          (QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n))))))
      ≃* ((FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))) ⧸
        Subgroup.normalClosure
          ({QuotientGroup.mk' (Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))) u} :
          Set (FreeGroup (Fin n) ⧸ Subgroup.normalClosure ({r} : Set (FreeGroup (Fin n)))))) :=
    QuotientGroup.quotientMulEquivOfEq hMap
  exact Work.ORLocInd.Group.LocallyIndicable.of_mulEquiv (e.symm.trans e1) hLIu

theorem torsionDataAtDatum (L : Type) [Field L] [CharZero L] (ψ : L →+* ℝ) (n : ℕ)
    (r u : FreeGroup (Fin n)) (l : ℕ) (hr : r ≠ 1) (hl : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hdiv : Work.ORFinal.DivLoc L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      ((algebraMap ℝ ℂ).comp ψ))
    (hin : Work.ORBridgeLinnell.HughesFreeInput L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
      (Work.ORBridgeLinnell.countableEnvelope (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
      ((algebraMap ℝ ℂ).comp ψ)) :
    letI := Work.ORBridgeLinnell.kAlgebra
      (Work.ORBridgeLinnell.countableEnvelope (PresentedGroup ({r} : Set (FreeGroup (Fin n)))))
      ((algebraMap ℝ ℂ).comp ψ)
    ∃ T : Work.ORTorsion.TorsionData L (PresentedGroup ({r} : Set (FreeGroup (Fin n))))
        (Work.ORBridgeLinnell.countableEnvelope (PresentedGroup ({r} : Set (FreeGroup (Fin n))))).U,
      T.u = Work.ORLyndon.presentRho r u := by
  classical
  let ψc : L →+* ℂ := (algebraMap ℝ ℂ).comp ψ
  let G := PresentedGroup ({r} : Set (FreeGroup (Fin n)))
  let E := Work.ORBridgeLinnell.countableEnvelope G
  letI : Algebra L E.U := Work.ORBridgeLinnell.kAlgebra E ψc
  -- the Linnell datum of the M1 bridge
  let Ld : Work.ORLinnell.LinnellDatum L G E.U :=
    Work.ORBridgeLinnell.linnellDatumOfEnvelope E ψc hin
  -- the division property for torsion-free subgroups, from `DivLoc` and N4
  have hdiv' : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H →
      ∀ x : ↥(Ld.D H), x ≠ 0 → IsUnit x := by
    intro H htf x hx
    have hLI : Work.ORLocInd.Group.LocallyIndicable H :=
      Work.ORLocInd.torsionFree_subgroup_locallyIndicable
        (Work.OROneRel.group_oneRelator_presentedGroup r)
        Work.OROneRel.oneRelatorCombinatorics H htf
    exact hdiv H hLI x hx
  -- node N4: a normal, finite-index, torsion-free subgroup
  obtain ⟨G', hG'N, hG'fi, hG'tf, -⟩ :=
    Work.ORLocInd.exists_normal_finiteIndex_torsionFree_locallyIndicable
      (Work.OROneRel.group_oneRelator_presentedGroup r)
      Work.OROneRel.oneRelatorCombinatorics
  haveI : G'.Normal := hG'N
  haveI : G'.FiniteIndex := hG'fi
  -- local indicability of the quotient `G ⧸ ⟨⟨u⟩⟩`
  have hq : Work.ORLocInd.Group.LocallyIndicable (G ⧸ Subgroup.normalClosure
      {Work.ORLyndon.presentRho r u}) :=
    locallyIndicable_quotient_normalClosure_presentRho n r u l hl hpow hpp
  obtain ⟨T, hT⟩ := exists_torsionData_eq L G E.U Ld G' hG'tf hdiv'
    (Work.ORLyndon.presentRho r u) hq
  exact ⟨T, hT⟩

end Work.ORFinal.T7
