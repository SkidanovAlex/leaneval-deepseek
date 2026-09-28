import Mathlib
import Submission.Work.StemsB.ModelThomRatDefs
import Submission.Work.StemsB.SuspensionStepR
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.StemsB.modelSphereBundleStepRat
import Submission.Work.StemsB.bijective_relCohMap_discFullRat
import Submission.Work.StemsB.capRelCohIsoRat
import Submission.Work.StemsB.modelThomRatOne
import Submission.Work.Thom.ModelThomStep

set_option synthInstance.maxHeartbeats 400000

/-!
# The inductive step of the rational model Thom induction

`Submission/Work/Thom/ModelThomStep.lean` proves, over `ℤ`, the inductive step of the construction
of the model Thom class of the trivial bundle: from a class of rank `n` it builds one of rank
`n + 1`, controlling the *specific* cup map `x ↦ π^*(x) ⌣ τ` throughout.  The chain is

`(B × ℝⁿ, B × Sⁿ⁻¹)` --inclusion--> `(B × Dⁿ, B × Sⁿ⁻¹)` --cap map--> `(B × Sⁿ, B × lower)`

followed by the suspension isomorphism `δ ∘ relToAbs`.  Every ingredient is available over an
arbitrary commutative ring (`suspensionStep_bijective_R`/`_cup'_R`, `cupMap_transfer_fwdR`/`_bwdR`,
`modelSphereBundleStepRat`, `bijective_relCohMap_discFullRat`, `capRelCohIsoRat`,
`bijective_relCohMap_of_homeomorphR`), and the base case `n = 1` is `Work.StemsB.modelThomRatOne`.

This file replays the `ℤ` proof over `ℚ` and assembles `Work.StemsB.ModelThomRatall`: the rational
model Thom class of every rank.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.StemsB

open CategoryTheory

noncomputable section

/-- **The inductive step of the rational model induction.**  From a model Thom class of rank `n`
(`n ≥ 1`) we build one of rank `n + 1`, with the same control over the cup map. -/
theorem modelThomRatStep (B : Type) [TopologicalSpace B] (n : ℕ) (hn : 1 ≤ n)
    (h : ModelThomRat B n) : ModelThomRat B (n + 1) := by
  obtain ⟨τn, hτn⟩ := h
  set Aset : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mSph (n + 1)} with hAset
  set A₁set : Set (B × EuclideanSpace ℝ (Fin (n + 1))) :=
    {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mLower n} with hA₁set
  have hA₁A : A₁set ⊆ Aset := fun p hp => Work.Thom.mLower_subset_mSph n hp
  obtain ⟨hρ, hres⟩ := modelSphereBundleStepRat ℚ B n
  -- Step A: the model class is a class of the disc pair
  let τdisc : Work.Thom.RelCoh ℚ n (B × Work.Thom.MBall n)
      {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n} :=
    (Work.Thom.relCohMap (Work.Thom.discFullMap B n)
      {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n}
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ Work.Thom.mSph n}
      (Work.Thom.discFullMap_mem B n) ℚ n).hom τn
  have hτdisc : ∀ k, Function.Bijective (fun x : Work.Thom.Coh ℚ k B =>
      (Work.Thom.mixedCupC ℚ {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n} k n)
        ((Work.Thom.CohMap ⟨Prod.fst, continuous_fst⟩ ℚ k).hom x) τdisc) :=
    cupMap_transfer_fwdR ℚ (Work.Thom.discFullMap B n)
      {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ Work.Thom.mSph n}
      {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n}
      (Work.Thom.discFullMap_mem B n) (bijective_relCohMap_discFullRat B n)
      (projFstRat B n) ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl) n τn hτn
  -- Step B: the cap map identifies the disc pair of rank `n` with `(B × Sⁿ, B × lower)`
  obtain ⟨τsph, _, hτsph⟩ :=
    cupMap_transfer_bwdR ℚ (Work.Thom.capMapPairSph B n)
      {p : B × Work.Thom.MSph (n + 1) | p.2.1 ∈ Work.Thom.mLower n}
      {q : B × Work.Thom.MBall n | q.2.1 ∈ Work.Thom.mSph n}
      (Work.Thom.capMapPairSph_mem_mLower n) (capRelCohIsoRat ℚ B n)
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τdisc hτdisc
  -- Step C: the product of subtypes is the subtype of the product
  obtain ⟨τA, _, hτA⟩ :=
    cupMap_transfer_bwdR ℚ
      (Work.Thom.prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (Work.Thom.mSph (n + 1)) :
        C(B × Work.Thom.MSph (n + 1),
          {p : B × EuclideanSpace ℝ (Fin (n + 1)) | p.2 ∈ Work.Thom.mSph (n + 1)}))
      (Work.Thom.subSubset A₁set Aset)
      {p : B × Work.Thom.MSph (n + 1) | p.2.1 ∈ Work.Thom.mLower n}
      (Work.Thom.prodSubsetHomeo_mem n)
      (fun m => bijective_relCohMap_of_homeomorphR ℚ
        {p : B × Work.Thom.MSph (n + 1) | p.2.1 ∈ Work.Thom.mLower n}
        (Work.Thom.subSubset A₁set Aset)
        (Work.Thom.prodSubsetHomeo B (EuclideanSpace ℝ (Fin (n + 1))) (Work.Thom.mSph (n + 1)))
        (fun q => Iff.rfl) m)
      ((projFstRat B (n + 1)).comp (Work.Thom.subtypeMap Aset))
      ⟨Prod.fst, continuous_fst⟩ (by ext q; rfl)
      n τsph hτsph
  -- Step D: apply the suspension isomorphism
  have hCohπ : ∀ (k : ℕ) (b : Work.Thom.Coh ℚ k B),
      (Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
          ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)
        = (Work.Thom.CohMap ((projFstRat B (n + 1)).comp
            (Work.Thom.subtypeMap Aset)) ℚ k).hom b := fun k b =>
    LinearMap.congr_fun (Work.Thom.CohMap_linear_comp (Work.Thom.subtypeMap Aset)
      (projFstRat B (n + 1)) ℚ k) b
  refine ⟨((pairδCR ℚ Aset n).hom)
    ((Work.Thom.relToAbs ℚ (Work.Thom.subSubset A₁set Aset) n).hom τA), fun k => ?_⟩
  have hΘk : Function.Bijective
      (((pairδCR ℚ Aset (k + n)).hom).comp
        ((Work.Thom.relToAbs ℚ (Work.Thom.subSubset A₁set Aset) (k + n)).hom)) := by
    have h0 := suspensionStep_bijective_R ℚ A₁set Aset (k + n - 1) hρ hres
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k + n)] at h0
    exact h0
  have key : ∀ b : Work.Thom.Coh ℚ k B,
      (((pairδCR ℚ Aset (k + n)).hom) ((Work.Thom.relToAbs ℚ
          (Work.Thom.subSubset A₁set Aset) (k + n)).hom
        ((Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
          ((Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
            ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)) τA)))
        = ((-1 : ℚ) ^ k) •
            ((Work.Thom.mixedCupC ℚ Aset k (n + 1))
              ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)
              (((pairδCR ℚ Aset n).hom)
                ((Work.Thom.relToAbs ℚ (Work.Thom.subSubset A₁set Aset) n).hom τA))) := by
    intro b
    have h0 := suspensionStep_cup'_R ℚ A₁set Aset k n
      ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b) τA
    simpa using h0
  have hcupA : Function.Bijective (fun b : Work.Thom.Coh ℚ k B =>
      (Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
        ((Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
          ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)) τA) := by
    have h := hτA k
    rwa [show (fun b : Work.Thom.Coh ℚ k B =>
          (Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
            ((Work.Thom.CohMap ((projFstRat B (n + 1)).comp
              (Work.Thom.subtypeMap Aset)) ℚ k).hom b) τA)
        = (fun b : Work.Thom.Coh ℚ k B =>
          (Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
            ((Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
              ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)) τA)
        from funext (fun b => by rw [hCohπ k b])] at h
  have hsmul_inj : Function.Injective
      (fun y : Work.Thom.RelCoh ℚ (k + n + 1)
        (B × EuclideanSpace ℝ (Fin (n + 1))) Aset => ((-1 : ℚ) ^ k) • y) := by
    intro a b hab
    have h2 := congrArg (fun z => ((-1 : ℚ) ^ k) • z) hab
    simp only at h2
    rw [smul_smul, smul_smul, negOnePow_mul_selfR ℚ k] at h2
    simpa using h2
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · have h' : (((pairδCR ℚ Aset (k + n)).hom) ((Work.Thom.relToAbs ℚ
        (Work.Thom.subSubset A₁set Aset) (k + n)).hom
          ((Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
            ((Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
              ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom a)) τA)))
        = (((pairδCR ℚ Aset (k + n)).hom) ((Work.Thom.relToAbs ℚ
        (Work.Thom.subSubset A₁set Aset) (k + n)).hom
          ((Work.Thom.mixedCupC ℚ (Work.Thom.subSubset A₁set Aset) k n)
            ((Work.Thom.CohMap (Work.Thom.subtypeMap Aset) ℚ k).hom
              ((Work.Thom.CohMap (projFstRat B (n + 1)) ℚ k).hom b)) τA))) := by
      rw [key a, key b]
      exact congrArg (fun z => ((-1 : ℚ) ^ k) • z) hab
    exact hcupA.1 (hΘk.1 h')
  · obtain ⟨u, hu⟩ := hΘk.2 (((-1 : ℚ) ^ k) • b)
    obtain ⟨c, hc⟩ := hcupA.2 u
    dsimp only at hc
    refine ⟨c, hsmul_inj ?_⟩
    simp only []
    rw [← key c, hc]
    simpa only [LinearMap.comp_apply] using hu

/-- **The rational model Thom class of every rank** (an `ℚ`-general form): `ModelThomRat B n` for
all `n ≥ 1`. -/
theorem modelThomRatAll (B : Type) [TopologicalSpace B] {n : ℕ} (hn : 1 ≤ n) :
    ModelThomRat B n := by
  induction n with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      exact modelThomRatOne B
    · exact modelThomRatStep B j (by omega) (ih (by omega))

end

end Work.StemsB
