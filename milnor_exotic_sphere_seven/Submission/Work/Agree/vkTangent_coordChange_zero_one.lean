import Mathlib
import Submission.Work.Agree.VkCharts
import Submission.Work.Milnor.VBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

namespace Work.Agree

/-!
# The `(0,1)`-transition of the two-chart tangent bundle of `D(ξ) = Vk (-2)`

The tangent bundle of the glued disc bundle `Vk (-2)` presented over the two-chart cover
`Work.Agree.vkCover` has transition function `(vkTangent h).coordChange 0 1 b`; on the overlap of
the two charts this is the Jacobian of the glueing map `vMap (-2)`, evaluated at the `X`-chart
coordinate `chartOfX 0 b` of `b`.  The proof unfolds the reindexed tangent bundle to Mathlib's
`tangentBundleCore`, identifies the two extended charts with `chartOfX 0 = homX.symm` and
`chartOfY 0 = homY.symm`, and uses that `homY.symm ∘ ιX` agrees with `vMap (-2)` on the open
glueing locus `vOpens`.
-/

noncomputable section

theorem vkTangent_coordChange_zero_one
    (h : ∀ x : Submission.Milnor.Vk (-2), ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
            (Submission.Milnor.Vk (-2))).baseSet
        (Work.Agree.vkCover i))
    {b : Submission.Milnor.Vk (-2)}
    (hb : b ∈ (Work.Agree.vkTangent h).baseSet 0 ∩ (Work.Agree.vkTangent h).baseSet 1) :
    (Work.Agree.vkTangent h).coordChange 0 1 b
      = fderiv ℝ (Submission.Milnor.vMap (-2))
          ((Submission.Milnor.vData (-2)).chartOfX 0 b) := by
  -- The chart of the glued space at `ιX 0` is `chartOfX 0`.
  have hX : chartAt Submission.Milnor.MSpace8 ((Submission.Milnor.vData (-2)).ιX 0)
      = (Submission.Milnor.vData (-2)).chartOfX (0 : Submission.Milnor.MSpace8) := by
    change (Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιX 0) = _
    have h := Quotient.out_eq ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8))
    have hrel : (Submission.Milnor.vData (-2)).rel
        (Quotient.out ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8)))
        (Sum.inl (0 : Submission.Milnor.MSpace8)) :=
      @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
        (Submission.Milnor.vData (-2)).setoid _ _ h
    rcases ho : Quotient.out ((Submission.Milnor.vData (-2)).ιX (0 : Submission.Milnor.MSpace8))
      with p | p
    · rw [ho] at hrel
      have hpq : p = 0 := hrel
      subst hpq
      exact Submission.Glue.Data.chartAt_of_out_inl (Submission.Milnor.vData (-2)) ho
    · rw [ho] at hrel
      exfalso
      obtain ⟨hp, -⟩ := hrel
      have hp' : (0 : Submission.Milnor.MSpace8) ∈ Submission.Milnor.vOpens := hp
      rw [Submission.Milnor.mem_vOpens] at hp'
      exact hp' rfl
  -- The chart of the glued space at `ιY 0` is `chartOfY 0`.
  have hY : chartAt Submission.Milnor.MSpace8 ((Submission.Milnor.vData (-2)).ιY 0)
      = (Submission.Milnor.vData (-2)).chartOfY (0 : Submission.Milnor.MSpace8) := by
    change (Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιY 0) = _
    have h := Quotient.out_eq ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8))
    have hrel : (Submission.Milnor.vData (-2)).rel
        (Quotient.out ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8)))
        (Sum.inr (0 : Submission.Milnor.MSpace8)) :=
      @Quotient.exact (Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8)
        (Submission.Milnor.vData (-2)).setoid _ _ h
    rcases ho : Quotient.out ((Submission.Milnor.vData (-2)).ιY (0 : Submission.Milnor.MSpace8))
      with p | p
    · rw [ho] at hrel
      exfalso
      obtain ⟨hp, hq⟩ := hrel
      have hp' : p.1 ≠ 0 := hp
      have hq' : (Submission.Milnor.vMap (-2) p).1 = 0 := by
        have h2 : (((Submission.Milnor.vData (-2)).φ p : Submission.Milnor.MSpace8)).1 = 0 :=
          congrArg (fun z : Submission.Milnor.MSpace8 => z.1) hq
        rw [← h2]; rfl
      exact absurd hq' (Submission.Milnor.invBase_ne_zero hp')
    · rw [ho] at hrel
      have hpq : p = 0 := hrel
      subst hpq
      exact Submission.Glue.Data.chartAt_of_out_inr (Submission.Milnor.vData (-2)) ho
  -- `chartOfX 0 = homX.symm` and `chartOfY 0 = homY.symm` (the model space chart is the identity).
  have hX' : (Submission.Milnor.vData (-2)).chartOfX (0 : Submission.Milnor.MSpace8)
      = (Submission.Milnor.vData (-2)).homX.symm := by
    rw [Submission.Glue.Data.chartOfX, chartAt_self_eq, OpenPartialHomeomorph.trans_refl]
  have hY' : (Submission.Milnor.vData (-2)).chartOfY (0 : Submission.Milnor.MSpace8)
      = (Submission.Milnor.vData (-2)).homY.symm := by
    rw [Submission.Glue.Data.chartOfY, chartAt_self_eq, OpenPartialHomeomorph.trans_refl]
  -- The two base sets are the two pieces of the glueing.
  have hbase0 : (Work.Agree.vkTangent h).baseSet 0
      = Set.range (Submission.Milnor.vData (-2)).ιX := by
    rw [Work.Agree.vkTangent, Work.TangentClasses.RealBundle.reindex_baseSet,
      Work.TangentClasses.tangentBundle_baseSet]
    rw [show (Work.Agree.vkCover 0).1
        = (Submission.Milnor.vData (-2)).chartOfX (0 : Submission.Milnor.MSpace8) from hX]
    rw [hX', OpenPartialHomeomorph.symm_source, Submission.Glue.Data.homX_target]
  have hbase1 : (Work.Agree.vkTangent h).baseSet 1
      = Set.range (Submission.Milnor.vData (-2)).ιY := by
    rw [Work.Agree.vkTangent, Work.TangentClasses.RealBundle.reindex_baseSet,
      Work.TangentClasses.tangentBundle_baseSet]
    rw [show (Work.Agree.vkCover 1).1
        = (Submission.Milnor.vData (-2)).chartOfY (0 : Submission.Milnor.MSpace8) from hY]
    rw [hY', OpenPartialHomeomorph.symm_source, Submission.Glue.Data.homY_target]
  -- Reduce to the transition function of `tangentBundle mMSpace8 (Vk (-2))` between the two charts.
  rw [Work.Agree.vkTangent, Work.TangentClasses.RealBundle.reindex_coordChange]
  have h0 : Work.Agree.vkCover 0
      = achart Submission.Milnor.MSpace8 ((Submission.Milnor.vData (-2)).ιX 0) := by
    rw [Work.Agree.vkCover_zero]; rfl
  have h1 : Work.Agree.vkCover 1
      = achart Submission.Milnor.MSpace8 ((Submission.Milnor.vData (-2)).ιY 0) := by
    rw [Work.Agree.vkCover_one]; rfl
  rw [h0, h1, Work.TangentClasses.tangentBundle_coordChange_achart]
  -- The chart transition `chartOfY 0 ∘ (chartOfX 0).symm` is `homY.symm ∘ ιX`.
  have hcoe : (⇑(extChartAt Work.Milnor.mMSpace8 ((Submission.Milnor.vData (-2)).ιY 0)) ∘
      ⇑(extChartAt Work.Milnor.mMSpace8 ((Submission.Milnor.vData (-2)).ιX 0)).symm)
      = fun p => (Submission.Milnor.vData (-2)).homY.symm
          ((Submission.Milnor.vData (-2)).ιX p) := by
    funext p
    simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id]
    rw [hX, hY, hX', hY']
    simp [Submission.Glue.Data.homX_apply, OpenPartialHomeomorph.symm_symm]
  -- The point at which the derivative is taken.
  have hpt : ⇑(extChartAt Work.Milnor.mMSpace8 ((Submission.Milnor.vData (-2)).ιX 0)) b
      = (Submission.Milnor.vData (-2)).chartOfX 0 b := by
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    rw [hX]
  rw [hcoe, hpt, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  -- `homY.symm ∘ ιX` agrees with `vMap (-2)` near the point, since that point lies in `vOpens`.
  refine Filter.EventuallyEq.fderiv_eq ?_
  have hb0 : b ∈ Set.range (Submission.Milnor.vData (-2)).ιX := by
    rw [← hbase0]; exact hb.1
  have hb1 : b ∈ Set.range (Submission.Milnor.vData (-2)).ιY := by
    rw [← hbase1]; exact hb.2
  obtain ⟨x, rfl⟩ := hb0
  obtain ⟨y, hy⟩ := hb1
  have hxU : x ∈ Submission.Milnor.vOpens := ((Submission.Glue.Data.ιY_eq_ιX_iff _).mp hy).1
  have hmem : (Submission.Milnor.vData (-2)).chartOfX 0
      ((Submission.Milnor.vData (-2)).ιX x) ∈ Submission.Milnor.vOpens := by
    rw [hX', Submission.Glue.Data.homX_symm_apply]
    exact hxU
  filter_upwards [Submission.Milnor.vOpens.2.mem_nhds hmem] with p hp
  rw [(Submission.Glue.Data.ιX_eq_ιY_iff _).mpr ⟨hp, rfl⟩,
    Submission.Glue.Data.homY_symm_apply]
  rfl

end

end Work.Agree
