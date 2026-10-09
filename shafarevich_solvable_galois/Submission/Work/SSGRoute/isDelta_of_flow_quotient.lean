import Mathlib
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.CohomologicalShrinking.Refined
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `IsDelta` transported to the concrete quotient `F(n)/F(n)^{(k,1)}`

`Work.SSGRoute.IsDelta G n k 1 δ` is a statement about the *model* quotient
`flowQuotient 2 G n k 1 = ⊤ ⧸ (F(n)^{(k,1)}).subgroupOf ⊤`, with the action `flowAction 2 G n k 1 δ`
descended from the permutation action of `G` on the free `G`-operator group `F(n) = FreeGroup (Fin n × G)`.

This file makes the comparison with the honest quotient `F(n) ⧸ F(n)^{(k,1)}` and with the map
induced by the involution `freeGroupCongr (freeOperatorGenPerm n δ)` explicit (this is the shape in
which the hypothesis is consumed downstream), and derives the transported statement.

The comparison isomorphism `flowIso` and its compatibility `flowIso_comm` are the same bookkeeping
as in `Submission/Work/SSGRoute/deltaDifference_of_antifixed.lean`; they are reproduced here so that
this module is independent of the (larger) lifting development.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open Work.Shrinking

set_option maxHeartbeats 1000000

variable (G : Type*) [Group G] (n : ℕ)

/-- The quotient `Q_σ = F(n)/F(n)^{(σ)}` of the flow group, compared with the honest quotient of the
free group `F(n) = FreeGroup (Fin n × G)` by the refined term. -/
noncomputable def flowIso (i j : ℕ) :
    flowQuotient 2 G n i j ≃* (FreeGroup (Fin n × G) ⧸ flowTerm 2 G n i j) :=
  QuotientGroup.congr (G := ↥(⊤ : Subgroup (FreeGroup (Fin n × G))))
    (H := FreeGroup (Fin n × G))
    ((flowTerm 2 G n i j).subgroupOf (⊤ : Subgroup (FreeGroup (Fin n × G))))
    (flowTerm 2 G n i j) (Subgroup.topEquiv) (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [Subgroup.mem_subgroupOf] using hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩)

theorem flowIso_apply_mk (i j : ℕ)
    (y : ↥(⊤ : Subgroup (FreeGroup (Fin n × G)))) :
    flowIso G n i j (QuotientGroup.mk' _ y)
      = QuotientGroup.mk' _ (Subgroup.topEquiv y) :=
  QuotientGroup.congr_mk' _ _ _ _ y

/-- The action of `G` on `Q_σ` is the quotient action of the permutation action on the free
`G`-operator group. -/
theorem flowAction_eq_quotAut (i j : ℕ) (δ : G) (x : flowQuotient 2 G n i j) :
    flowAction 2 G n i j δ x =
      Work.Shrinking.quotAut (⊤ : Subgroup (FreeGroup (Fin n × G))) (flowTerm 2 G n i j) δ
        (Subgroup.map_top_of_surjective _
          (MulDistribMulAction.toMulAut G (FreeGroup (Fin n × G)) δ).surjective)
        (map_refinedTerm_eq 2 (MulDistribMulAction.toMulAut G (FreeGroup (Fin n × G)) δ) i j) x :=
  rfl

theorem flowAction_mk (i j : ℕ) (δ : G)
    (y : ↥(⊤ : Subgroup (FreeGroup (Fin n × G)))) :
    flowAction 2 G n i j δ (QuotientGroup.mk' _ y)
      = QuotientGroup.mk' _
          (⟨FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) y.1,
            Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (FreeGroup (Fin n × G)))) := by
  rw [flowAction_eq_quotAut, Work.Shrinking.quotAut_mk]
  refine congrArg _ (Subtype.ext ?_)
  show (Work.Shrinking.subAut (⊤ : Subgroup (FreeGroup (Fin n × G))) δ
      (Subgroup.map_top_of_surjective _
        (MulDistribMulAction.toMulAut G (FreeGroup (Fin n × G)) δ).surjective) y).1
    = FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) y.1
  rw [Work.Shrinking.subAut_coe]
  rfl

/-- The refined term is stable under the involution of the free basis; hence the induced map on the
honest quotient is available. -/
theorem refinedTerm_comap_le (i j : ℕ) (δ : G) :
    flowTerm 2 G n i j ≤ Subgroup.comap
      (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)).toMonoidHom
      (flowTerm 2 G n i j) := by
  intro y hy
  rw [Subgroup.mem_comap]
  show (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)) y
    ∈ refinedTerm 2 (FreeGroup (Fin n × G)) i j
  rw [← Work.CohomologicalShrinking.map_refinedTerm_eq 2
    (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)) i j]
  exact Subgroup.mem_map_of_mem _ (show y ∈ refinedTerm 2 (FreeGroup (Fin n × G)) i j from hy)

/-- The action of the involution on the honest quotient `F(n)/F(n)^{(σ)}`. -/
noncomputable def sigmaMap (i j : ℕ) (δ : G) :
    (FreeGroup (Fin n × G) ⧸ flowTerm 2 G n i j) →*
      (FreeGroup (Fin n × G) ⧸ flowTerm 2 G n i j) :=
  QuotientGroup.map (flowTerm 2 G n i j) (flowTerm 2 G n i j)
    (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)).toMonoidHom
    (refinedTerm_comap_le G n i j δ)

theorem sigmaMap_apply_mk (i j : ℕ) (δ : G) (z : FreeGroup (Fin n × G)) :
    sigmaMap G n i j δ (QuotientGroup.mk' (flowTerm 2 G n i j) z)
      = QuotientGroup.mk' (flowTerm 2 G n i j)
          (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) z) := by
  rw [sigmaMap]
  exact QuotientGroup.map_mk' _ _ _ _ z

/-- The comparison isomorphism intertwines the operator action on `Q_σ` with the action induced by
the involution of the free basis. -/
theorem flowIso_comm (i j : ℕ) (δ : G) (x : flowQuotient 2 G n i j) :
    flowIso G n i j (flowAction 2 G n i j δ x) = sigmaMap G n i j δ (flowIso G n i j x) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n i j).subgroupOf (⊤ : Subgroup (FreeGroup (Fin n × G)))) x
  have hL : flowIso G n i j (flowAction 2 G n i j δ (QuotientGroup.mk' _ y))
      = QuotientGroup.mk' (flowTerm 2 G n i j)
          (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) y.1) := by
    rw [flowAction_mk, flowIso_apply_mk]
    rfl
  have hR : sigmaMap G n i j δ (flowIso G n i j (QuotientGroup.mk' _ y))
      = QuotientGroup.mk' (flowTerm 2 G n i j)
          (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ) y.1) := by
    rw [flowIso_apply_mk]
    exact sigmaMap_apply_mk G n i j δ y.1
  exact hL.trans hR.symm

/-- `sigmaMap` is the map written with the `refinedTerm` spelling of the statement. -/
theorem sigmaMap_eq_map (i j : ℕ) (δ : G)
    (y : FreeGroup (Fin n × G) ⧸ flowTerm 2 G n i j) :
    sigmaMap G n i j δ y =
      QuotientGroup.map (refinedTerm 2 (FreeGroup (Fin n × G)) i j)
        (refinedTerm 2 (FreeGroup (Fin n × G)) i j)
        (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)).toMonoidHom
        (Subgroup.map_le_iff_le_comap.mp (le_of_eq
          (Work.CohomologicalShrinking.map_refinedTerm_eq 2
            (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm (G := G) n δ)) i j))) y := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (flowTerm 2 G n i j) y
  rw [sigmaMap_apply_mk, QuotientGroup.map_mk', QuotientGroup.mk'_apply]
  rfl

end Work.SSGRoute

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open Work.Shrinking

/-- `Work.SSGRoute.IsDelta` is insensitive to the model of the quotient: an anti-fixed element of
the honest quotient `F(n) ⧸ F(n)^{(k,1)}` for the map induced by the involution
`freeGroupCongr (freeOperatorGenPerm n δ)` is a `δ`-difference. -/
theorem isDelta_of_flow_quotient {G : Type*} [Group G] (n k : ℕ) (δ : G) (hδ : δ * δ = 1)
    (h : Work.SSGRoute.IsDelta G n k 1 δ) :
    ∀ a : FreeGroup (Fin n × G) ⧸ Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup (Fin n × G)) k 1,
      (QuotientGroup.map _ _
          (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm n δ)).toMonoidHom
          (Subgroup.map_le_iff_le_comap.mp (le_of_eq
            (Work.CohomologicalShrinking.map_refinedTerm_eq 2
              (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm n δ)) k 1)))) a = a⁻¹ →
      ∃ r : FreeGroup (Fin n × G) ⧸
          Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup (Fin n × G)) k 1,
        a = ((QuotientGroup.map _ _
              (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm n δ)).toMonoidHom
              (Subgroup.map_le_iff_le_comap.mp (le_of_eq
                (Work.CohomologicalShrinking.map_refinedTerm_eq 2
                  (FreeGroup.freeGroupCongr (Work.Shrinking.freeOperatorGenPerm n δ)) k 1)))) r)⁻¹ * r := by
  intro a ha
  have ha' : sigmaMap G n k 1 δ a = a⁻¹ := by
    rw [sigmaMap_eq_map G n k 1 δ a]
    exact ha
  have hax : flowAction 2 G n k 1 δ ((flowIso G n k 1).symm a)
      = ((flowIso G n k 1).symm a)⁻¹ := by
    apply (flowIso G n k 1).injective
    rw [flowIso_comm, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply, ha']
  obtain ⟨r, hr⟩ := h ((flowIso G n k 1).symm a) hax
  refine ⟨flowIso G n k 1 r, ?_⟩
  rw [← sigmaMap_eq_map G n k 1 δ (flowIso G n k 1 r)]
  calc a = flowIso G n k 1 ((flowIso G n k 1).symm a) := (MulEquiv.apply_symm_apply _ _).symm
    _ = flowIso G n k 1 ((flowAction 2 G n k 1 δ r)⁻¹ * r) := by rw [hr]
    _ = (flowIso G n k 1 (flowAction 2 G n k 1 δ r))⁻¹ * flowIso G n k 1 r := by rw [map_mul, map_inv]
    _ = (sigmaMap G n k 1 δ (flowIso G n k 1 r))⁻¹ * flowIso G n k 1 r := by rw [flowIso_comm]

end Work.SSGRoute
