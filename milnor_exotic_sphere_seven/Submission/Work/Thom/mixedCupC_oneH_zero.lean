import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.sph3DiscMixedDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.RelCupTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace Work.Thom

open CategoryTheory

/-- Transporting a cohomology class along an equality of degrees commutes with `homologyπ`. -/
theorem cast_homologyπ_cc {R : Type} [CommRing R] (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ}
    (h : a = b) (x : K.cycles a) :
    h ▸ ((K.homologyπ a).hom x) = (K.homologyπ b).hom (h ▸ x) := by
  cases h; rfl

/-- Transporting a cycle along an equality of degrees commutes with `iCycles`. -/
theorem cast_iCycles_cc {R : Type} [CommRing R] (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ}
    (h : a = b) (x : K.cycles a) :
    h ▸ ((K.iCycles a).hom x) = (K.iCycles b).hom (h ▸ x) := by
  cases h; rfl

/-- Transporting a relative cohomology class along an equality of degrees and back is the
identity. -/
theorem relCoh_symm_cast_cast {X : TopCat} (A : Set X) {p q : ℕ} (h : p = q)
    (x : Work.Cohomology.relCohomology ℤ X A p) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

/-- **The mixed cup product with the unit class `1 ∈ H⁰` is the identity** on relative
cohomology. -/
theorem mixedCup_oneH_zero (X : TopCat) (A : Set X) (n : ℕ)
    (y : Work.Cohomology.relCohomology ℤ X A n) :
    Work.Cohomology.mixedCup X A 0 n (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj X)) y
      = (Nat.zero_add n).symm ▸ y := by
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf ℤ X A n y
  obtain ⟨hmem, h, hcup⟩ :=
    Work.Cohomology.mixedCup_apply X A 0 n (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b
      (Work.Cohomology.cochainDiff_unitCochain ℤ (TopCat.toSSet.obj X)) hb
  rw [show Work.Cohomology.oneH ℤ (TopCat.toSSet.obj X)
        = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X))
            (Work.Cohomology.cochainDiff_unitCochain ℤ (TopCat.toSSet.obj X)) from rfl]
  rw [hcup]
  have hmain : (Nat.zero_add n) ▸ Work.Cohomology.relClassOf ℤ X A
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
          (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h
      = Work.Cohomology.relClassOf ℤ X A b hb := by
    have hcyc : (Nat.zero_add n) ▸ Work.Cohomology.relCocycleOf ℤ X A
          ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h
        = Work.Cohomology.relCocycleOf ℤ X A b hb := by
      apply Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex ℤ X A) n
      rw [← cast_iCycles_cc (Work.Cohomology.relComplex ℤ X A) (Nat.zero_add n)
            (Work.Cohomology.relCocycleOf ℤ X A
              ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
                (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)]
      rw [Work.Cohomology.iCycles_relCocycleOf ℤ X A
            ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
              (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h,
          Work.Cohomology.iCycles_relCocycleOf ℤ X A b hb]
      apply Subtype.ext
      rw [Work.Cohomology.eqRec_relKern_coe]
      exact (Work.Cohomology.cupUnit ℤ (TopCat.toSSet.obj X) b.1).1
    show (Nat.zero_add n) ▸ ((Work.Cohomology.relComplex ℤ X A).homologyπ (0 + n)).hom
        (Work.Cohomology.relCocycleOf ℤ X A
          ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)
      = Work.Cohomology.relClassOf ℤ X A b hb
    rw [cast_homologyπ_cc (Work.Cohomology.relComplex ℤ X A) (Nat.zero_add n)
          (Work.Cohomology.relCocycleOf ℤ X A _ h), hcyc]
    rfl
  have h2 : (Nat.zero_add n).symm ▸ ((Nat.zero_add n) ▸ Work.Cohomology.relClassOf ℤ X A
        ⟨Work.Cohomology.cup ℤ (TopCat.toSSet.obj X)
          (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)
      = (Nat.zero_add n).symm ▸ Work.Cohomology.relClassOf ℤ X A b hb :=
    congrArg (fun w => (Nat.zero_add n).symm ▸ w) hmain
  rwa [relCoh_symm_cast_cast A (Nat.zero_add n) _] at h2

theorem mixedCupC_oneH_zero {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (y : Work.Thom.RelCoh ℤ n X A) :
    (Work.Thom.mixedCupC ℤ A 0 n)
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) y
      = (Nat.zero_add n).symm ▸ y :=
  mixedCup_oneH_zero (TopCat.of X) A n y

end Work.Thom
