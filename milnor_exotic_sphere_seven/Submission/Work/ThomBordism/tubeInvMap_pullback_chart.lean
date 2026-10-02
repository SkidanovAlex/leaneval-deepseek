import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs
import Submission.Work.ThomBordism.ambientLocalDefs2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem tubeInvMap_pullback_chart (V : Work.ThomBordism.Man8) (k : ℕ)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C) (Work.ThomBordism.tubeInvPunct E C)
        (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap ⟨fun p : Work.Tubular.NormalTotal E =>
            Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
          (Work.Tubular.normalNonzero E) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun p hp => Set.mem_compl_singleton_iff.mpr
            (Work.ThomBordism.chartAffine_cap_ne_zero E C x hp))
          ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) : Work.Thom.RelCoh ℤ (8 + k)
          (↑(TopCat.of (Work.Tubular.NormalTotal E))) (Work.Tubular.normalNonzero E))
      = Work.ThomBordism.ambientStandardClass E C x := by
  -- the chart map, seen as a map of pairs on the normal bundle
  set g : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩ with hg
  -- the translation `y ↦ y - E.e x` on the tube
  set tr : C(↥C.U, Work.Tubular.Euc (8 + k)) :=
    ⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x,
      continuous_subtype_val.sub continuous_const⟩ with htr
  have hkey : ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      g (Work.ThomBordism.tubeInvMap E C y) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun y hy => Set.mem_compl_singleton_iff.mpr
      (Work.ThomBordism.chartAffine_cap_ne_zero E C x hy)
  have hkey' : ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      tr y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun y hy => by
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact sub_ne_zero.mpr (Work.ThomBordism.tubeInvPunct_sub E C x hy)
  -- functoriality: the pullback of the composite is the composite of the pullbacks
  rw [show (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
        (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
        (fun y hy => hy) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap g (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (fun p hp => Set.mem_compl_singleton_iff.mpr
            (Work.ThomBordism.chartAffine_cap_ne_zero E C x hp))
          ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)))
      = (Work.Thom.relCohMap (g.comp (Work.ThomBordism.tubeInvMap E C))
          (Work.ThomBordism.tubeInvPunct E C) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hkey ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) from
    Work.Thom.relCohMap_compA_apply (Work.ThomBordism.tubeInvPunct E C)
      (Work.Tubular.normalNonzero E) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (Work.ThomBordism.tubeInvMap E C) g
      (fun y hy => hy)
      (fun p hp => Set.mem_compl_singleton_iff.mpr
        (Work.ThomBordism.chartAffine_cap_ne_zero E C x hp))
      hkey ℤ (8 + k) (Work.ThomBordism.stdModelGen (8 + k))]
  -- the composite of the tube inverse with the chart map is the translation
  have hmap₁ : g.comp (Work.ThomBordism.tubeInvMap E C) = tr := by
    apply ContinuousMap.ext
    intro y
    rw [ContinuousMap.comp_apply]
    show Work.ThomBordism.chartAffine E x
        (Work.ThomBordism.cap E ε (C.inv (y : Work.Tubular.Euc (8 + k))))
      = (y : Work.Tubular.Euc (8 + k)) - E.e x
    rw [Work.ThomBordism.cap_inv E C y.2, Work.ThomBordism.chartAffine_inv E C x y.2]
  have hdef : Work.ThomBordism.ambientStandardClass E C x
      = (Work.Thom.relCohMap tr (Work.ThomBordism.tubeInvPunct E C)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hkey' ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) := rfl
  rw [hdef, Work.Thom.relCohMap_congrA (Work.ThomBordism.tubeInvPunct E C)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmap₁ hkey hkey' ℤ (8 + k)]

end Work.ThomBordism
