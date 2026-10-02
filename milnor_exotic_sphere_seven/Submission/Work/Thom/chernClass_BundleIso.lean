import Mathlib
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.realification_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι ι' : Type}

/-- The descent maps of two isomorphic bundles are related by the induced homeomorphism of the
punctured total spaces. -/
theorem descent_square_iso {m j : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
    (e : BundleIso Z Z') :
    (⇑((CohMap ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom)) =
      (⇑((CohMap (punctHomeo Z Z' e :
          C(↥(zeroComplement (realification Z)), ↥(zeroComplement (realification Z')))) ℤ (2*j)).hom)) ∘
        (⇑((CohMap ((bundleProj (realification Z')).comp
          (subtypeMap (zeroComplement (realification Z')))) ℤ (2 * j)).hom)) := by
  funext x
  rw [Function.comp_apply, CohMap_comp_apply]
  congr 1

/-- **Isomorphism-invariance of the Chern classes**, given the two functoriality inputs. -/
theorem chernClass_BundleIso_of
    (hB : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type}
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
      (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι')
      (e : BundleIso Z Z'),
      Nonempty (BundleIso (tautQuotientCore Z)
        (bundleComap (tautQuotientCore Z') (punctHomeo Z Z' e :
          C(↥(zeroComplement (realification Z)), ↥(zeroComplement (realification Z')))))))
    (hC : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
      (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
      (e : BundleIso Z Z') (hm : 1 ≤ m),
      (thomClassRank m hm Z).eulerClass = (thomClassRank m hm Z').eulerClass) :
    ∀ (m : ℕ) {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
      (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
      (e : BundleIso Z Z') (j : ℕ), chernClass m j Z = chernClass m j Z' := by
  intro m
  induction m with
  | zero =>
    intro B _ ι ι' _ _ Z Z' e j
    rw [chernClass_zero_rank, chernClass_zero_rank]
    rfl
  | succ m ih =>
    intro B _ ι ι' _ _ Z Z' e j
    by_cases hle : j ≤ m
    · rw [chernClass_succ_of_le Z hle, chernClass_succ_of_le Z' hle]
      set d := (bundleProj (realification Z)).comp (subtypeMap (zeroComplement (realification Z)))
        with hd
      set d' := (bundleProj (realification Z')).comp (subtypeMap (zeroComplement (realification Z')))
        with hd'
      set Θ : C(↥(zeroComplement (realification Z)), ↥(zeroComplement (realification Z'))) :=
        (punctHomeo Z Z' e : C(↥(zeroComplement (realification Z)),
          ↥(zeroComplement (realification Z')))) with hΘ
      have hfun : ⇑((CohMap d ℤ (2*j)).hom) =
          ⇑((CohMap Θ ℤ (2*j)).hom) ∘ ⇑((CohMap d' ℤ (2*j)).hom) := by
        rw [hd, hd', hΘ]
        exact descent_square_iso Z Z' e
      set eZ := LinearEquiv.ofBijective ((CohMap d ℤ (2*j)).hom)
        (bijective_proj_zeroComplementA (realification Z) (finrank_real_euclidean_complex (m+1))
          (thomClassRank (m+1) (Nat.succ_le_succ (Nat.zero_le m)) Z) (by omega)) with heZ
      set eZ' := LinearEquiv.ofBijective ((CohMap d' ℤ (2*j)).hom)
        (bijective_proj_zeroComplementA (realification Z') (finrank_real_euclidean_complex (m+1))
          (thomClassRank (m+1) (Nat.succ_le_succ (Nat.zero_le m)) Z') (by omega)) with heZ'
      obtain ⟨e'⟩ := hB Z Z' e
      have hih := ih (tautQuotient Z) (bundleComap (tautQuotient Z') Θ) e' j
      have hgy : (CohMap Θ ℤ (2 * j)).hom (chernClass m j (tautQuotient Z')) =
          chernClass m j (tautQuotient Z) := by
        rw [← chernClass_comap (tautQuotient Z') Θ]
        exact hih.symm
      have key : eZ (eZ'.symm (chernClass m j (tautQuotient Z'))) =
          chernClass m j (tautQuotient Z) := by
        have h2 : (CohMap d' ℤ (2*j)).hom (eZ'.symm (chernClass m j (tautQuotient Z'))) =
            chernClass m j (tautQuotient Z') := by
          change eZ' (eZ'.symm (chernClass m j (tautQuotient Z'))) = _
          rw [LinearEquiv.apply_symm_apply]
        show (CohMap d ℤ (2*j)).hom (eZ'.symm (chernClass m j (tautQuotient Z'))) =
          chernClass m j (tautQuotient Z)
        rw [hfun, Function.comp_apply, h2]
        exact hgy
      calc eZ.symm (chernClass m j (tautQuotient Z))
          = eZ.symm (eZ (eZ'.symm (chernClass m j (tautQuotient Z')))) := by rw [key]
        _ = eZ'.symm (chernClass m j (tautQuotient Z')) := LinearEquiv.symm_apply_apply _ _
    · by_cases htop : j = m + 1
      · subst htop
        rw [chernClass_succ_top' Z, chernClass_succ_top' Z']
        exact hC Z Z' e (Nat.succ_le_succ (Nat.zero_le m))
      · rw [chernClass_succ_of_gt Z (by omega), chernClass_succ_of_gt Z' (by omega)]

end

end Work.Thom
