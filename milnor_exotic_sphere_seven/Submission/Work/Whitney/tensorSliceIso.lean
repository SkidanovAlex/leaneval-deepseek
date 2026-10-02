import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.Iso
import Submission.Work.Thom.trivialChern
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The transition functions of `L ⊗ K` against the fixed index `K.indexAt b` -/

/-- **The transition function of `L ⊗ K` from `(L.indexAt b, K.indexAt b)` to `(i, K.indexAt b)` is
the transition function of `L`**: the second factor is the identity by `coordChange_self`. -/
theorem tensorLine_coordChange_eq_fst {ι ι' : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (K : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι') (i : ι) (b : B) :
    (Work.Gen.tensorLine L K).coordChange ((Work.Gen.tensorLine L K).indexAt b)
        (i, K.indexAt b) b = L.coordChange (L.indexAt b) i b := by
  have hK : K.coordChange (K.indexAt b) (K.indexAt b) b
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    exact K.coordChange_self (K.indexAt b) b (K.mem_baseSet_at b) v
  change (Work.Gen.scl (L.coordChange (L.indexAt b) i b)
      * Work.Gen.scl (K.coordChange (K.indexAt b) (K.indexAt b) b))
      • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) = L.coordChange (L.indexAt b) i b
  rw [hK, Work.Gen.scl_id, mul_one, ← Work.Gen.scl_smul_id (L.coordChange (L.indexAt b) i b)]

/-- The mirror of `tensorLine_coordChange_eq_fst`, for `K ⊗ L`. -/
theorem tensorLine_coordChange_eq_snd {ι ι' : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (K : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι') (i : ι) (b : B) :
    (Work.Gen.tensorLine K L).coordChange ((Work.Gen.tensorLine K L).indexAt b)
        (K.indexAt b, i) b = L.coordChange (L.indexAt b) i b := by
  have hK : K.coordChange (K.indexAt b) (K.indexAt b) b
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
    apply ContinuousLinearMap.ext
    intro v
    exact K.coordChange_self (K.indexAt b) b (K.mem_baseSet_at b) v
  change (Work.Gen.scl (K.coordChange (K.indexAt b) (K.indexAt b) b)
      * Work.Gen.scl (L.coordChange (L.indexAt b) i b))
      • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) = L.coordChange (L.indexAt b) i b
  rw [hK, Work.Gen.scl_id, one_mul, ← Work.Gen.scl_smul_id (L.coordChange (L.indexAt b) i b)]

/-! ## The slice of a line bundle over a point of the other factor -/

/-- **The chart of the pullback of a line bundle along a constant map, at its preferred index, is
everything.** -/
theorem const_baseSet_indexAt {B₀ : Type} [TopologicalSpace B₀] {ι' : Type}
    (N : VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) ι') (b : B₀) :
    (Work.Thom.bundleComap N (ContinuousMap.const B b)).baseSet (N.indexAt b) = Set.univ := by
  refine Set.eq_univ_of_forall (fun x => ?_)
  exact N.mem_baseSet_at b

/-- **Slicing a tensor power of line bundles along a constant map: the first factor.**
`L ⊗ K ≅ L` when `K` is the pullback of a line bundle along a constant map (so that its preferred
chart is all of the base): the identity gauge is a bundle isomorphism. -/
theorem nonempty_bundleIso_tensorLine_const_left {B₀ : Type} [TopologicalSpace B₀]
    {ι ι' : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (N : VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) ι') (b : B₀) :
    Nonempty (Work.Thom.BundleIso
      (Work.Gen.tensorLine L (Work.Thom.bundleComap N (ContinuousMap.const B b))) L) := by
  have hbase : ∀ i : ι,
      (Work.Gen.tensorLine L (Work.Thom.bundleComap N (ContinuousMap.const B b))).baseSet
        (i, N.indexAt b) = L.baseSet i := by
    intro i
    rw [Work.Gen.tensorLine_baseSet, const_baseSet_indexAt, Set.inter_univ]
  have hconj : ∀ (i : ι) (b' : B),
      ContinuousLinearMap.comp
        ((Work.Gen.tensorLine L (Work.Thom.bundleComap N (ContinuousMap.const B b))).coordChange
          ((Work.Gen.tensorLine L (Work.Thom.bundleComap N (ContinuousMap.const B b))).indexAt b')
          (i, N.indexAt b) b')
        ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
      = ContinuousLinearMap.comp
        ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
        (L.coordChange (L.indexAt b') i b') := by
    intro i b'
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
    exact tensorLine_coordChange_eq_fst L (Work.Thom.bundleComap N (ContinuousMap.const B b)) i b'
  obtain ⟨e⟩ := Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt L
    (Work.Gen.tensorLine L (Work.Thom.bundleComap N (ContinuousMap.const B b)))
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) (fun i => (i, N.indexAt b)) hbase hconj
  exact ⟨e.symm⟩

/-- **Slicing a tensor power of line bundles along a constant map: the second factor.**
`K ⊗ L ≅ L` when `K` is the pullback of a line bundle along a constant map. -/
theorem nonempty_bundleIso_tensorLine_const_right {B₀ : Type} [TopologicalSpace B₀]
    {ι ι' : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (N : VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) ι') (b : B₀) :
    Nonempty (Work.Thom.BundleIso
      (Work.Gen.tensorLine (Work.Thom.bundleComap N (ContinuousMap.const B b)) L) L) := by
  have hbase : ∀ i : ι,
      (Work.Gen.tensorLine (Work.Thom.bundleComap N (ContinuousMap.const B b)) L).baseSet
        (N.indexAt b, i) = L.baseSet i := by
    intro i
    rw [Work.Gen.tensorLine_baseSet, const_baseSet_indexAt, Set.univ_inter]
  have hconj : ∀ (i : ι) (b' : B),
      ContinuousLinearMap.comp
        ((Work.Gen.tensorLine (Work.Thom.bundleComap N (ContinuousMap.const B b)) L).coordChange
          ((Work.Gen.tensorLine (Work.Thom.bundleComap N (ContinuousMap.const B b)) L).indexAt b')
          (N.indexAt b, i) b')
        ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
      = ContinuousLinearMap.comp
        ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) :
          EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))
        (L.coordChange (L.indexAt b') i b') := by
    intro i b'
    rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
    exact tensorLine_coordChange_eq_snd L (Work.Thom.bundleComap N (ContinuousMap.const B b)) i b'
  obtain ⟨e⟩ := Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt L
    (Work.Gen.tensorLine (Work.Thom.bundleComap N (ContinuousMap.const B b)) L)
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1))) (fun i => (N.indexAt b, i)) hbase hconj
  exact ⟨e.symm⟩

theorem tensorSliceIso (N : ℕ)
    {B₀ B : Type} [TopologicalSpace B₀] [TopologicalSpace B]
    {ι₀ ι : Type} [Fintype ι₀] [Fintype ι]
    (M₀ : Fin N → VectorBundleCore ℂ B₀ (EuclideanSpace ℂ (Fin 1)) ι₀)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (b : B) (x : B₀) :
    (∀ i : Fin N, Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap
          (Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
            (Work.Thom.bundleComap (M i) ContinuousMap.snd))
          (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b)))
        (M₀ i)))
    ∧ (∀ i : Fin N, Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap
          (Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
            (Work.Thom.bundleComap (M i) ContinuousMap.snd))
          (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B)))
        (M i))) := by
  constructor
  · intro i
    have h₁ : Work.Thom.bundleComap (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
        (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b)) = M₀ i := by
      rw [Work.Thom.bundleComap_comp]
      rw [show ContinuousMap.fst.comp
            (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
          = ContinuousMap.id B₀ from by ext y; rfl]
      exact Work.Thom.bundleComap_id (M₀ i)
    have h₂ : Work.Thom.bundleComap (Work.Thom.bundleComap (M i) ContinuousMap.snd)
        (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
        = Work.Thom.bundleComap (M i) (ContinuousMap.const B₀ b) := by
      rw [Work.Thom.bundleComap_comp]
      rw [show ContinuousMap.snd.comp
            (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
          = ContinuousMap.const B₀ b from by ext y; rfl]
    have hEq : Work.Thom.bundleComap
        (Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
          (Work.Thom.bundleComap (M i) ContinuousMap.snd))
        (ContinuousMap.prodMk (ContinuousMap.id B₀) (ContinuousMap.const B₀ b))
        = Work.Gen.tensorLine (M₀ i)
            (Work.Thom.bundleComap (M i) (ContinuousMap.const B₀ b)) := by
      rw [Work.Gen.tensorLine_bundleComap, h₁, h₂]
    obtain ⟨e⟩ := nonempty_bundleIso_tensorLine_const_left (M₀ i) (M i) b
    exact ⟨(Work.Thom.BundleIso.ofEq hEq).trans e⟩
  · intro i
    have h₁ : Work.Thom.bundleComap (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
        (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B))
        = Work.Thom.bundleComap (M₀ i) (ContinuousMap.const B x) := by
      rw [Work.Thom.bundleComap_comp]
      rw [show ContinuousMap.fst.comp
            (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B))
          = ContinuousMap.const B x from by ext y; rfl]
    have h₂ : Work.Thom.bundleComap (Work.Thom.bundleComap (M i) ContinuousMap.snd)
        (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B)) = M i := by
      rw [Work.Thom.bundleComap_comp]
      rw [show ContinuousMap.snd.comp
            (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B))
          = ContinuousMap.id B from by ext y; rfl]
      exact Work.Thom.bundleComap_id (M i)
    have hEq : Work.Thom.bundleComap
        (Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) ContinuousMap.fst)
          (Work.Thom.bundleComap (M i) ContinuousMap.snd))
        (ContinuousMap.prodMk (ContinuousMap.const B x) (ContinuousMap.id B))
        = Work.Gen.tensorLine (Work.Thom.bundleComap (M₀ i) (ContinuousMap.const B x))
            (M i) := by
      rw [Work.Gen.tensorLine_bundleComap, h₁, h₂]
    obtain ⟨e⟩ := nonempty_bundleIso_tensorLine_const_right (L := M i) (N := M₀ i) (b := x)
    exact ⟨(Work.Thom.BundleIso.ofEq hEq).trans e⟩

end

end Work.Whitney
