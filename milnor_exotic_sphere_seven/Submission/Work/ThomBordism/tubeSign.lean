import Submission.Work.ThomBordism.Grassmann.eulerClassOddRank
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.thomSpaceTorsionDetected
import Submission.Work.ThomBordism.absThomComparePhiZ
import Submission.Work.ThomBordism.absThomCompareNatural
import Submission.Work.ThomBordism.absThomCompareUniversal
import Submission.Work.ThomBordism.thomClassPullbackBundleComapRank
import Submission.Work.ThomBordism.normLikeTautological

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

/-!
# The two ingredients of the sign bookkeeping of `Work.ThomBordism.tubeDataPerFamily`

* `negMap_thomClass` — the fibrewise negation of a real bundle of **odd** rank negates any Thom
  class (extracted from `Work.ThomBordism.Grassmann.eulerClassOddRank`, where it is an internal
  step).
* `PhiG` — the comparison map `OpenThom γ (8+k) ≃ₗ TSCoh k 10` of the universal Thom target,
  *defined* (not chosen) as `PhiZ` with the degree identity `8+k = k+8` moved to the **output**, so
  that `Nat.add_comm 8 k ▸ PhiG a` and `PhiZ γ (8+k) a` are exchanged by a single cast.
-/

open CategoryTheory
open Work.TangentClasses

namespace Work.ThomBordism

noncomputable section

/-- **A change of degrees of the cohomology of a cochain complex, as a `ℤ`-linear equivalence.** -/
def homCast {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b) :
    K.homology a ≃ₗ[ℤ] K.homology b where
  toFun x := h ▸ x
  invFun y := h.symm ▸ y
  left_inv x := by cases h; rfl
  right_inv y := by cases h; rfl
  map_add' x y := by cases h; rfl
  map_smul' c x := by cases h; rfl

@[simp] theorem homCast_apply {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : K.homology a) : homCast h x = h ▸ x := rfl

/-- `homCast h` and the cast `h ▸ ·` agree, including on the inverse. -/
theorem homCast_symm_apply {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (y : K.homology a) : (homCast h).symm (homCast h y) = y :=
  LinearEquiv.symm_apply_apply _ _

end

end Work.ThomBordism

namespace Work.ThomBordism.Grassmann

open Work.Thom

/-- **The fibrewise negation negates any Thom class of a bundle of odd rank.**
(This is the internal step `hneg` of `Work.ThomBordism.Grassmann.eulerClassOddRank`, extracted as a
standalone theorem.) -/
theorem negMap_thomClass {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F]
    (Z : RealBundle B F ι) {n : ℕ} (hrank : Z.rank = n) (T : Work.Thom.ThomClass Z n) (hn : Odd n) :
    (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z)
      (negMap_mem Z) ℤ n).hom T.τ = -T.τ := by
  classical
  set z : Work.Thom.OpenThom Z n :=
    (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z)
      (negMap_mem Z) ℤ n).hom T.τ + T.τ with hz
  set w : Work.Thom.OpenThom Z (0 + n) := (Nat.zero_add n).symm ▸ z with hw
  obtain ⟨c, hc⟩ := (T.isThom 0).2 w
  have hchart : ∀ (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i),
      Work.Thom.localThomMap Z n W ((Work.Thom.PieceRes Z W n).hom T.τ) 0
        ((Work.Thom.CohMap (Work.Thom.subtypeMap W) ℤ 0).hom c) = 0 := by
    intro i W hW
    have hF : Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [finrank_euclideanSpace_fin]; exact hrank
    obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :=
      ⟨ContinuousLinearEquiv.ofFinrankEq hF⟩
    have hz0 : (Work.Thom.PieceRes Z W n).hom z = 0 := by
      rw [hz, map_add, negPiece_restrict Z n hn e i W hW T.τ, neg_add_cancel]
    have hw0 : (Work.Thom.PieceRes Z W (0 + n)).hom w = 0 := by
      rw [hw, pieceRes_cast Z W (Nat.zero_add n).symm z, hz0]
      exact eqRec_zero (β := fun m => ↥(Work.Thom.PieceCoh Z W m)) (Nat.zero_add n).symm
    have h2 := Work.Thom.thomMap_restrict Z n 0 W T.τ c
    rw [hc] at h2
    rw [hw, hw0] at h2
    exact h2.symm
  have hchild := fun (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i) =>
    localThomMapChartInjective Z hrank T i W hW
  have hc0 : c = 0 :=
    Work.Thom.Coh_zero_cover_injective_gen (fun i : ι => Z.baseSet i)
      (fun i => Z.isOpen_baseSet i) (fun x => ⟨Z.indexAt x, Z.mem_baseSet_at x⟩) c
      (fun i => hchild i (Z.baseSet i) subset_rfl
        (by rw [hchart i (Z.baseSet i) subset_rfl, map_zero]))
  have hw0 : w = 0 := by
    rw [← hc, hc0, map_zero]
  have hz0 : z = 0 := by
    have h1 : (Nat.zero_add n).symm ▸ z = 0 := hw ▸ hw0
    refine eqRec_injective (β := fun m => ↥(Work.Thom.OpenThom Z m)) (Nat.zero_add n).symm z 0 ?_
    rw [h1]
    exact (eqRec_zero (β := fun m => ↥(Work.Thom.OpenThom Z m)) (Nat.zero_add n).symm).symm
  have h : (Work.Thom.relCohMap (negMap Z) (Work.Thom.zeroComplement Z)
      (Work.Thom.zeroComplement Z) (negMap_mem Z) ℤ n).hom T.τ + T.τ = 0 := by
    rw [← hz]
    exact hz0
  exact eq_neg_of_add_eq_zero_left h

/-- The rank of the tautological bundle is `k`. -/
theorem tautological_rank (k m : ℕ) : (tautologicalBundle k m).rank = k := by
  rw [Work.TangentClasses.RealBundle.rank]
  simp [tautologicalBundle, Amb]

/-- **The fibrewise negation of the tautological bundle negates the tautological Thom class** (for
odd `k`). -/
theorem tautological_negMap_thomClass (k m : ℕ) (hodd : Odd k) :
    (Work.Thom.relCohMap (negMap (tautologicalBundle k m))
      (Work.Thom.zeroComplement (tautologicalBundle k m))
      (Work.Thom.zeroComplement (tautologicalBundle k m))
      (negMap_mem (tautologicalBundle k m)) ℤ k).hom
        (tautologicalThomClass k m).τ = -(tautologicalThomClass k m).τ :=
  negMap_thomClass _ (tautological_rank k m) (tautologicalThomClass k m) hodd

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism

open Work.TangentClasses

/-- The chosen norm-like function of the tautological bundle. -/
noncomputable def tautNormLike (k m : ℕ) : NormLike (Grassmann.tautologicalBundle k m) :=
  Classical.choice (normLikeTautological k m)

/-- **The comparison map `Φ` of the universal Thom target**, `OpenThom γ (8+k) ≃ₗ TSCoh k 10`:
the canonical comparison `PhiZ` at degree `8 + k`, followed by the degree change `8 + k = k + 8` on
the *output*. -/
noncomputable def PhiG (k : ℕ) (h2 : 2 ≤ 8 + k) :
    Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k) ≃ₗ[ℤ] Grassmann.TSCoh k 10 :=
  (PhiZ (Grassmann.tautologicalBundle k 10) (tautNormLike k 10) h2).trans
    (homCast (K := Work.Cohomology.singularCochainComplex ℤ
      (TopCat.of (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace)))
      (Nat.add_comm 8 k))

theorem PhiG_apply (k : ℕ) (h2 : 2 ≤ 8 + k)
    (a : Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k)) :
    PhiG k h2 a = homCast (K := Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace)))
        (Nat.add_comm 8 k)
        (PhiZ (Grassmann.tautologicalBundle k 10) (tautNormLike k 10) h2 a) := rfl

/-- The computation rule of `PhiG`: undoing the degree change returns `PhiZ` at degree `8 + k`. -/
theorem PhiG_cast_symm (k : ℕ) (h2 : 2 ≤ 8 + k)
    (a : Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k)) :
    (homCast (K := Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace)))
        (Nat.add_comm 8 k)).symm (PhiG k h2 a)
      = PhiZ (Grassmann.tautologicalBundle k 10) (tautNormLike k 10) h2 a := by
  rw [PhiG, LinearEquiv.trans_apply]
  exact LinearEquiv.symm_apply_apply _ _

end Work.ThomBordism
