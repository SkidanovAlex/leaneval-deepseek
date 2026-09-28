import Mathlib
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.thomClassTrivialEuclideanA
import Submission.Work.Thom.ATools

set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The trivial bundle with an arbitrary finite-dimensional fibre

The producer `Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial` needs a Thom class of the
*trivial* bundle `↥U × F → ↥U` with the given model fibre `F`.  For the standard fibre
`EuclideanSpace ℝ (Fin n)` such a Thom class is `Work.Thom.thomClassTrivialEuclideanA`.  Here we
transport it to an arbitrary finite-dimensional `F` along a continuous linear equivalence
`F ≃L[ℝ] EuclideanSpace ℝ (Fin n)` (Mathlib's `ContinuousLinearEquiv.ofFinrankEq`, which needs only
a dimension equality — *not* a linear isometry, which need not exist).

The transport is `Work.Thom.cupMap_transfer_bwdA` along the homeomorphism of the Thom pairs
`(E_F, E_F ∖ 0) ≃ₜ (E_{ℝⁿ}, E_{ℝⁿ} ∖ 0)` of the two trivial bundles induced by the fibre equivalence
(composed of `Work.Thom.trivProductHomeo` on either end and the product homeomorphism in the
middle); `Work.Thom.bijective_relCohMap_of_homeomorphA` supplies the bijectivity of the pullback on
relative cohomology. -/

/-- The product homeomorphism `B × F ≃ₜ B × F'` induced by a continuous linear equivalence of the
fibres. -/
noncomputable def prodCLEHomeo (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') : B × F ≃ₜ B × F' where
  toFun q := (q.1, e q.2)
  invFun q := (q.1, e.symm q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (e.continuous.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)

@[simp] theorem prodCLEHomeo_apply (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') (q : B × F) : prodCLEHomeo B e q = (q.1, e q.2) := rfl

@[simp] theorem prodCLEHomeo_symm_apply (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') (q : B × F') : (prodCLEHomeo B e).symm q = (q.1, e.symm q.2) := rfl

/-- The homeomorphism of the total spaces of the trivial bundles with fibres `F` and `F'`
induced by a continuous linear equivalence `F ≃L[ℝ] F'`. -/
noncomputable def trivHomeoA (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') : (RealBundle.trivial B F PUnit).TotalSpace ≃ₜ
      (RealBundle.trivial B F' PUnit).TotalSpace :=
  (trivProductHomeo B F PUnit).trans
    ((prodCLEHomeo B e).trans (trivProductHomeo B F' PUnit).symm)

/-- Reading `trivHomeoA` through the product trivialisation of the *target* trivial bundle: it is
the inverse product homeomorphism composed with the chart of the source. -/
theorem trivProductHomeo_symm_trivHomeoA (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') (y : (RealBundle.trivial B F' PUnit).TotalSpace) :
    trivProductHomeo B F PUnit ((trivHomeoA B e).symm y)
      = (prodCLEHomeo B e).symm (trivProductHomeo B F' PUnit y) := by
  change (trivProductHomeo B F PUnit)
      (((trivProductHomeo B F PUnit).trans ((prodCLEHomeo B e).trans
        (trivProductHomeo B F' PUnit).symm)).symm y) = _
  rw [Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.apply_symm_apply]

/-- `trivHomeoA` identifies the complements of the zero sections of the two trivial bundles. -/
theorem trivHomeoA_symm_zeroComplement (B : Type) [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') (y : (RealBundle.trivial B F' PUnit).TotalSpace) :
    y ∈ zeroComplement (RealBundle.trivial B F' PUnit) ↔
      (trivHomeoA B e).symm y ∈ zeroComplement (RealBundle.trivial B F PUnit) := by
  rw [trivProductHomeo_zeroComplement B F' PUnit y,
    trivProductHomeo_zeroComplement B F PUnit ((trivHomeoA B e).symm y),
    trivProductHomeo_symm_trivHomeoA, prodCLEHomeo_symm_apply]
  exact (not_congr (ContinuousLinearEquiv.map_eq_zero_iff e.symm)).symm

/-- **The Thom class of the trivial bundle with an arbitrary model fibre `F`**, transported along a
continuous linear equivalence `F ≃L[ℝ] F'` from the Thom class of the trivial bundle with fibre
`F'`. -/
theorem thomClassTrivialOfCLE {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : F ≃L[ℝ] F') (n : ℕ)
    (hT : Nonempty (ThomClass (RealBundle.trivial B F' PUnit) n)) :
    Nonempty (ThomClass (RealBundle.trivial B F PUnit) n) := by
  obtain ⟨T⟩ := hT
  have he := trivHomeoA_symm_zeroComplement B e
  have hf : ∀ y ∈ zeroComplement (RealBundle.trivial B F' PUnit),
      (trivHomeoA B e).symm y ∈ zeroComplement (RealBundle.trivial B F PUnit) :=
    fun y hy => (he y).mp hy
  have hfbij : ∀ m, Function.Bijective (relCohMap (trivHomeoA B e).symm
      (zeroComplement (RealBundle.trivial B F' PUnit))
      (zeroComplement (RealBundle.trivial B F PUnit)) hf ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorphA
      (zeroComplement (RealBundle.trivial B F' PUnit))
      (zeroComplement (RealBundle.trivial B F PUnit))
      (trivHomeoA B e).symm (fun y => trivHomeoA_symm_zeroComplement B e y) ℤ m
  have hπ : (bundleProj (RealBundle.trivial B F PUnit)).comp
      ((trivHomeoA B e).symm : C((RealBundle.trivial B F' PUnit).TotalSpace,
        (RealBundle.trivial B F PUnit).TotalSpace)) =
      bundleProj (RealBundle.trivial B F' PUnit) := by
    apply ContinuousMap.ext
    intro y
    have key : (trivProductHomeo B F PUnit ((trivHomeoA B e).symm y)).1
        = (trivProductHomeo B F' PUnit y).1 := by
      rw [trivProductHomeo_symm_trivHomeoA, prodCLEHomeo_symm_apply]
    have h3 : (trivProductHomeo B F PUnit ((trivHomeoA B e).symm y)).1
        = ((trivHomeoA B e).symm y).proj := by rw [trivProductHomeo_apply]
    have h4 : (trivProductHomeo B F' PUnit y).1 = y.proj := by
      rw [trivProductHomeo_apply]
    show (bundleProj (RealBundle.trivial B F PUnit) ((trivHomeoA B e).symm y))
        = (bundleProj (RealBundle.trivial B F' PUnit) y)
    rw [bundleProj_apply, bundleProj_apply]
    exact h3.symm.trans (key.trans h4)
  obtain ⟨τ', -, hτ'⟩ := cupMap_transfer_bwdA
    ((trivHomeoA B e).symm : C((RealBundle.trivial B F' PUnit).TotalSpace,
      (RealBundle.trivial B F PUnit).TotalSpace))
    (zeroComplement (RealBundle.trivial B F PUnit))
    (zeroComplement (RealBundle.trivial B F' PUnit)) hf hfbij
    (bundleProj (RealBundle.trivial B F PUnit))
    (bundleProj (RealBundle.trivial B F' PUnit)) hπ n T.τ T.isThom
  exact ⟨⟨τ', hτ'⟩⟩

/-- The producer of local Thom data (see `Work.Thom.nonempty_localThom_of_subset_baseSet`) for an
arbitrary finite-dimensional real fibre `F` (rather than `EuclideanSpace ℝ (Fin n)`): needed for the
*realification* of a complex bundle (`Work.Thom.realification`, whose real fibre is a complex vector
space `F` with `finrank ℝ F = 2 * finrank ℂ F`) and, more generally, for any bundle whose fibre is
not the standard `EuclideanSpace`.  Intended proof: the fibre-general producer
`Work.Thom.nonempty_localThom_of_subset_baseSet_of_trivial` reduces everything to
`Nonempty (ThomClass (RealBundle.trivial ↥U F PUnit) n)`, which is transported from
`Work.Thom.thomClassTrivialEuclideanA (finrank ℝ F) ↥U` along a continuous linear equivalence
`F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F))` (Mathlib's `ContinuousLinearEquiv.ofFinrankEq`,
`Topology/Algebra/Module/FiniteDimension.lean`; NOT a linear isometry equivalence, which need not
exist) and the induced homeomorphism `↥U × F ≃ₜ ↥U × EuclideanSpace ℝ (Fin k)` of the total spaces
of the trivial bundles, using `Work.Thom.cupMap_transfer_iffA` / `_fwdA` / `_bwdA` and
`Work.Thom.bijective_relCohMap_of_homeomorphA` from `Submission/Work/Thom/ATools.lean`. -/
theorem localThom_genFibre {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} (n : ℕ) (hn : 1 ≤ n)
    (hF : Module.finrank ℝ F = n)
    (Z : Work.TangentClasses.RealBundle B F ι) (i : ι) (U : Set B) (hU : U ⊆ Z.baseSet i) :
    Nonempty (Work.Thom.LocalThom Z n U) := by
  refine nonempty_localThom_of_subset_baseSet_of_trivial Z i U hU ?_
  have hfr : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]; exact hF
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F) (F := EuclideanSpace ℝ (Fin n)) hfr
  exact thomClassTrivialOfCLE (B := ↥U) e n (thomClassTrivialEuclideanA n ↥U hn)

end

end Work.Thom
