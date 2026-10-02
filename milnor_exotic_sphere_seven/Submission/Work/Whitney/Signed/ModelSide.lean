import Mathlib
import Submission.Work.Whitney.Signed.KronAdj
import Submission.Work.Thom.Pair
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The model side of the rank-one model product formula

`Work.Whitney.Signed.modelSidePairing` states that the model class `Mn (k+1) Y`, evaluated on a
`(k+1)`-chain `W` whose boundary is the cap image of a relative `k`-chain `B` of the disc pair plus
a chain `L` carried by the lower band, equals the disc model class `stepDisc Y k (Mn k Y)` evaluated
on `B`.

This file proves it.  The route is the transgression pairing
(`Work.Cohomology.kronecker_pairδ_apply`): `Mn (k+1) Y` is *by definition*
(`Work.Thom.Mn`/`step`) the transgression of the class `relToAbs (stepSph Y k (Mn k Y))` under the
identification `Y × Sᵏ ≅ ↥(Sph Y (k+1))`, so evaluating it on `W` is evaluating a lift of that class
on `∂W`; the lift is chosen as the pull-back of a band-relative representative `z` of `stepSph`, so
that it vanishes on the lower band (killing the `L`-part) and its values on the cap are computed by
`Work.Thom.stepSph_spec`.
-/

namespace Work.Whitney

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The **identification of the sphere bundle with `Y × Sᵏ`**, as a continuous map (the inverse of
`Work.Thom.prodSubsetHomeoA`). -/
def sphUnflat (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    C(↥(Sph Y (k + 1)), Y × MSph (k + 1)) :=
  ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1))) (mSph (k + 1))).symm :
    C(↥(Sph Y (k + 1)), Y × MSph (k + 1)))

/-- The identification of the sphere bundle with `Y × Sᵏ`, as a `TopCat` morphism. -/
def sphUnflatHom (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    TopCat.of ↥(Sph Y (k + 1)) ⟶ TopCat.of (Y × MSph (k + 1)) :=
  TopCat.ofHom (sphUnflat Y k)

/-- The inverse of `sphUnflat`, as a `TopCat` morphism. -/
def sphFlatHom (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    TopCat.of (Y × MSph (k + 1)) ⟶ TopCat.of ↥(Sph Y (k + 1)) :=
  TopCat.ofHom ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1))) (mSph (k + 1)) :
    C(Y × MSph (k + 1), ↥(Sph Y (k + 1)))))

/-- The pull-back of a cochain of `Y × Sᵏ` to the sphere bundle along the identification
`sphUnflat`. -/
noncomputable def sphPushCochain (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k) : Cochain ℤ (ssB ↥(Sph Y (k + 1))) k :=
  (((dualChainMap ℤ (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1)))
    (sphUnflatHom Y k)).f k).hom z : Cochain ℤ (ssB ↥(Sph Y (k + 1))) k)

/-- **Evaluation of the pushed cochain on a generator.** -/
theorem sphPushCochain_apply_gen (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (τ : (ssB ↥(Sph Y (k + 1))) _⦋k⦌) :
    (sphPushCochain Y k z) (gen (TopCat.of ↥(Sph Y (k + 1))) k τ)
      = z (gen (TopCat.of (Y × MSph (k + 1))) k
          ((TopCat.toSSet.map (sphUnflatHom Y k)).app (Opposite.op ⦋k⦌) τ)) := by
  have h := cochain_push_apply (sphUnflatHom Y k) k z
    (gen (TopCat.of ↥(Sph Y (k + 1))) k τ)
  rw [pushChain_gen] at h
  exact h.symm

/-- The pushed cochain is a cocycle if `z` is (in the complex-differential spelling). -/
theorem sphPushCochain_d (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (hz : cochainDiff ℤ (ssB (Y × MSph (k + 1))) z = 0) :
    ((singularCochainComplex ℤ (TopCat.of ↥(Sph Y (k + 1)))).d k (k + 1)).hom
      (sphPushCochain Y k z) = 0 := by
  have hcomm := HomologicalComplex.Hom.comm
    (dualChainMap ℤ (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1))) (sphUnflatHom Y k))
    k (k + 1)
  have h := congrArg (fun (g : (singularCochainComplex ℤ (TopCat.of (Y × MSph (k + 1)))).X k ⟶
      (singularCochainComplex ℤ (TopCat.of ↥(Sph Y (k + 1)))).X (k + 1)) => g.hom z) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have h' : (ModuleCat.Hom.hom
      ((dualChainMap ℤ (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1)))
        (sphUnflatHom Y k)).f (k + 1)))
      ((ModuleCat.Hom.hom ((singularCochainComplex ℤ (TopCat.of (Y × MSph (k + 1)))).d k (k + 1))) z)
      = 0 := by
    have hz3 : ((singularCochainComplex ℤ (TopCat.of (Y × MSph (k + 1)))).d k (k + 1)).hom z = 0 := by
      rw [singularCochain_d_eq]
      exact hz
    have := congrArg (fun w => (ModuleCat.Hom.hom
      ((dualChainMap ℤ (TopCat.of ↥(Sph Y (k + 1))) (TopCat.of (Y × MSph (k + 1)))
        (sphUnflatHom Y k)).f (k + 1))) w) hz3
    simpa using this
  change (ModuleCat.Hom.hom ((singularCochainComplex ℤ (TopCat.of ↥(Sph Y (k + 1)))).d k (k + 1)))
    ((ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of ↥(Sph Y (k + 1)))
      (TopCat.of (Y × MSph (k + 1))) (sphUnflatHom Y k)).f k)) z) = 0
  rw [h]
  exact h'


/-- The identification of `Y × Sᵏ` with the sphere bundle, as a continuous map. -/
def sphFlat (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    C(Y × MSph (k + 1), ↥(Sph Y (k + 1))) :=
  ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1))) (mSph (k + 1)) :
    C(Y × MSph (k + 1), ↥(Sph Y (k + 1)))))

/-- `sphFlat` is a section of `sphUnflat`. -/
theorem sphFlat_comp_sphUnflat (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    (sphFlat Y k).comp (sphUnflat Y k) = ContinuousMap.id ↥(Sph Y (k + 1)) := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply]
  exact Equiv.apply_symm_apply (prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1)))
      (mSph (k + 1))).toEquiv x

/-- `sphUnflat` is a retraction of `sphFlat`. -/
theorem sphUnflat_comp_sphFlat (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    (sphUnflat Y k).comp (sphFlat Y k) = ContinuousMap.id (Y × MSph (k + 1)) := by
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply, ContinuousMap.id_apply]
  exact Equiv.symm_apply_apply (prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1)))
      (mSph (k + 1))).toEquiv q

/-- The sphere bundle lives in the total space. -/
theorem sphFlat_comp_subtypeMap (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    (sphFlat Y k).comp (sphUnflat Y k)
      = ContinuousMap.id ↥(Sph Y (k + 1)) := sphFlat_comp_sphUnflat Y k

/-- **The cap in the two pictures**: `capFull` is the inclusion of the sphere bundle composed with
`sphFlat ∘ capMapPairSph`. -/
theorem capFull_eq_comp (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    capFull Y k
      = (subtypeMap (Sph Y (k + 1))).comp ((sphFlat Y k).comp (capMapPairSph Y k)) := by
  apply ContinuousMap.ext
  intro q
  rfl

/-- The band, seen in `Y × Sᵏ`, is carried into the band `SphB` of the sphere bundle by
`sphUnflat`. -/
theorem sphUnflat_mem_SphB (Y : Type) [TopologicalSpace Y] (k : ℕ) {p : Y × EuclideanSpace ℝ (Fin (k + 1))}
    (hp : p ∈ BandFull Y k) : sphUnflat Y k ⟨p, hp.1⟩ ∈ SphB Y k := by
  show (sphUnflat Y k ⟨p, hp.1⟩).2.1 ∈ mLower k
  rw [show sphUnflat Y k ⟨p, hp.1⟩
      = (prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (k + 1))) (mSph (k + 1))).symm
          ⟨p, hp.1⟩ from rfl, prodSubsetHomeoA_symm_apply]
  exact hp


/-- Smallness is monotone in the subset. -/
theorem IsSmall.mono {X : TopCat} {S T : Set X} (hST : S ⊆ T) {n : ℕ} {σ : Simplex X n}
    (h : IsSmall S (∅ : Set X) σ) : IsSmall T (∅ : Set X) σ := by
  rw [isSmall_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl (h.trans hST)
  · exact Or.inr h

/-- **The pushed cochain vanishes on a generator supported in the band.** -/
theorem sphPushCochain_gen_eq_zero (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (hz : z ∈ relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) k)
    (σ : Simplex (TopCat.of ↥(Sph Y (k + 1))) k)
    (hσ : IsSmall (SphB Y k) (∅ : Set (Y × MSph (k + 1)))
      ((TopCat.toSSet.map (sphUnflatHom Y k)).app (Opposite.op ⦋k⦌) σ)) :
    (sphPushCochain Y k z) (gen (TopCat.of ↥(Sph Y (k + 1))) k σ) = 0 := by
  rw [sphPushCochain_apply_gen]
  obtain ⟨τ, hτ⟩ := exists_simplex_subtypeIncl_of_isSmall hσ
  rw [← hτ]
  show genEval ℤ (TopCat.toSSet.obj (TopCat.of (Y × MSph (k + 1)))) z
    ((TopCat.toSSet.map (subtypeIncl (TopCat.of (Y × MSph (k + 1))) (SphB Y k))).app
      (Opposite.op ⦋k⦌) τ) = 0
  exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (Y × MSph (k + 1))) (SphB Y k) z hz τ

/-- The pushed cochain is a cocycle in the `cochainDiff` spelling. -/
theorem sphPushCochain_cocycle (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (z : Cochain ℤ (ssB (Y × MSph (k + 1))) k)
    (hz : cochainDiff ℤ (ssB (Y × MSph (k + 1))) z = 0) :
    cochainDiff ℤ (ssB ↥(Sph Y (k + 1))) (sphPushCochain Y k z) = 0 := by
  have h := sphPushCochain_d Y k z hz
  rw [singularCochain_d_eq] at h
  exact h


end

end Work.Whitney
