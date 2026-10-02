import Mathlib
import Submission.Work.Thom.realification_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- **The punctured total space of a bundle with a globally defined trivial chart.**

Let `Z` be a real vector bundle given by gluing data on the base `B` with model fibre `F`, and let
`i` be a chart of `Z` which covers the whole base (`Z.baseSet i = Set.univ`) and which is the
identity in the sense that the transition function from `i` to the preferred chart of `b` is the
identity for every `b : B` (`hid`).  Then the complement of the zero section of `Z` is
`B × (F ∖ 0)`, by the `i`-th chart, which is a homeomorphism onto `B × F` because its source and
target are everything.

This is the general form of "the punctured trivial bundle is a product"; it is used below for the
realification of the trivial complex bundle, whose single chart has `baseSet = univ` and
`coordChange = id`. -/
theorem exists_punctHomeo_of_chart {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type} (Z : VectorBundleCore ℝ B F ι) (i : ι)
    (hbase : Z.baseSet i = Set.univ)
    (hid : ∀ b : B, ⇑(Z.coordChange (Z.indexAt b) i b) = id) :
    ∃ e : ↥(zeroComplement Z) ≃ₜ (B × {v : F // v ≠ 0}),
      ∀ p, (e : ↥(zeroComplement Z) → B × {v : F // v ≠ 0}) p
        = (p.1.proj, ⟨(show F from p.1.2), (mem_zeroComplement p.1).mp p.2⟩) := by
  classical
  have hsrc : (Z.localTriv i).source = Set.univ := by
    rw [Bundle.Trivialization.source_eq, ← Z.baseSet_at, hbase, Set.preimage_univ]
  have htgt : (Z.localTriv i).target = Set.univ := by
    rw [Bundle.Trivialization.target_eq, ← Z.baseSet_at, hbase, Set.univ_prod_univ]
  let Θ : Z.TotalSpace ≃ₜ (B × F) :=
    (Z.localTriv i).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv hsrc htgt
  have hΘ : ∀ p : Z.TotalSpace, Θ p = (p.proj, (show F from p.snd)) := by
    intro p
    change (Z.localTriv i) p = (p.proj, (show F from p.snd))
    rw [VectorBundleCore.localTriv_apply]
    refine Prod.ext rfl ?_
    exact congrFun (hid p.proj) p.snd
  have hΘsymm : ∀ q : B × F, Θ.symm q = (⟨q.1, (show F from q.2)⟩ : Z.TotalSpace) := by
    intro q
    rw [Homeomorph.symm_apply_eq]
    exact (hΘ ⟨q.1, (show F from q.2)⟩).symm
  refine ⟨{ toFun := fun p =>
              (p.1.proj, ⟨(show F from p.1.2), (mem_zeroComplement p.1).mp p.2⟩)
            invFun := fun q => ⟨⟨q.1, (show F from (q.2 : F))⟩, by
              rw [mem_zeroComplement]
              exact q.2.2⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, ?_⟩
  · intro p
    rfl
  · intro q
    rfl
  · refine Continuous.prodMk (RealBundle.continuous_proj Z |>.comp continuous_subtype_val) ?_
    refine Continuous.subtype_mk ?_ _
    have h3 : Continuous ((fun q : B × F => q.2) ∘
        (fun p : ↥(zeroComplement Z) => Θ (p : Z.TotalSpace))) :=
      continuous_snd.comp (Θ.continuous.comp continuous_subtype_val)
    have hfun : (fun p : ↥(zeroComplement Z) => (Θ (p : Z.TotalSpace)).2)
        = fun p : ↥(zeroComplement Z) => (show F from (p : Z.TotalSpace).snd) := by
      funext p
      rw [hΘ]
    exact hfun ▸ h3
  · refine Continuous.subtype_mk ?_ _
    have h5 : Continuous (fun q : B × {v : F // v ≠ 0} => (q.1, (q.2 : F))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have h6 : Continuous (fun q : B × {v : F // v ≠ 0} => Θ.symm (q.1, (q.2 : F))) :=
      Θ.symm.continuous.comp h5
    have hfun : (fun q : B × {v : F // v ≠ 0} => Θ.symm (q.1, (q.2 : F)))
        = fun q : B × {v : F // v ≠ 0} =>
            (⟨q.1, (show F from (q.2 : F))⟩ : Z.TotalSpace) := by
      funext q
      rw [hΘsymm]
    exact hfun ▸ h6
  · intro p
    rfl

/-- The single chart of the realification of the trivial complex bundle is trivial: its
transition function from the preferred chart is the identity. -/
theorem realification_trivial_coordChange (m : ℕ) (B : Type) [TopologicalSpace B]
    (i : PUnit) (b : B) :
    ⇑((realification (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)).coordChange
        ((realification (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m))
          PUnit)).indexAt b) i b) = id := by
  rw [realification_coordChange]
  rfl


theorem exists_punctTrivHomeo (m : ℕ) (B : Type) [TopologicalSpace B] :
    ∃ e : ↥(Work.Thom.zeroComplement (Work.Thom.realification
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit))) ≃ₜ
      (B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}),
      ∀ p, (e : ↥(Work.Thom.zeroComplement (Work.Thom.realification
          (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit))) →
          B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) p
        = (p.1.proj, ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
            (Work.Thom.mem_zeroComplement p.1).mp p.2⟩) := by
  classical
  refine exists_punctHomeo_of_chart
    (Z := realification (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit))
    (i := (default : PUnit)) ?_ ?_
  · rw [realification_baseSet]
    rfl
  · intro b
    exact realification_trivial_coordChange m B (default : PUnit) b

end

end Work.LerayHirsch
