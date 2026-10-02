import Mathlib
import Submission.Work.Cohomology.cup1defs
import Submission.Work.Cohomology.cup1Identity
import Submission.Work.Cohomology.cupZeroLeft
import Submission.Work.Cohomology.cupZeroRight

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

lemma eqRec_symm_eqRec_self3 {M : ℕ → Type*} {a b : ℕ} (h : a = b) (x : M a) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

lemma eqRec_smul3 (M : ℕ → Type*) [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
    {a b : ℕ} (h : a = b) (c : R) (z : M a) : h ▸ (c • z) = c • (h ▸ z) := by cases h; rfl

lemma cup1IdentityA (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hh : n + m - 1 + 1 = n + m)
    (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    hh ▸ (cochainDiff R X (cup1 R X n m α β)) =
      cup R X α β - ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ cup R X β α) := by
  have h1 := cup1Identity R X n m hn hm α β hα hβ
  rwa [show (Nat.sub_add_cancel (by omega : 1 ≤ n + m)) = hh from Subsingleton.elim _ _] at h1

lemma cupClassComm (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    (Nat.add_comm n m) ▸
        (cohomologyClassOf R X (cup R X α β) (cochainDiff_cup_of_cocycles R X α β hα hβ)) =
      ((-1 : R) ^ (n * m)) •
        (cohomologyClassOf R X (cup R X β α) (cochainDiff_cup_of_cocycles R X β α hβ hα)) := by
  have hA : cochainDiff R X (cup R X α β) = 0 := cochainDiff_cup_of_cocycles R X α β hα hβ
  have hB : cochainDiff R X (cup R X β α) = 0 := cochainDiff_cup_of_cocycles R X β α hβ hα
  have hB' : cochainDiff R X ((Nat.add_comm m n) ▸ cup R X β α) = 0 :=
    cochainDiff_cast R X (Nat.add_comm m n) (cup R X β α) hB
  obtain hh : n + m - 1 + 1 = n + m := Nat.sub_add_cancel (by omega : 1 ≤ n + m)
  have e1 : (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).hom
        (cochainDiff R X (cup1 R X n m α β)) = hh ▸ (cochainDiff R X (cup1 R X n m α β)) :=
    XIsoOfEq_hom_apply R X hh (cochainDiff R X (cup1 R X n m α β))
  have e2 : cochainDiff R X (cup1 R X n m α β) =
      ((SSetCochainComplex R X).d (n + m - 1) ((n + m - 1) + 1)).hom (cup1 R X n m α β) :=
    (SSetCochainComplex_d_apply R X (n + m - 1) (cup1 R X n m α β)).symm
  have e3 : (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).hom
        (((SSetCochainComplex R X).d (n + m - 1) ((n + m - 1) + 1)).hom (cup1 R X n m α β)) =
      ((SSetCochainComplex R X).d (n + m - 1) (n + m)).hom (cup1 R X n m α β) := by
    have hdc := HomologicalComplex.d_comp_XIsoOfEq_hom (SSetCochainComplex R X) hh (n + m - 1)
    have h2 := congrArg (fun (g : (SSetCochainComplex R X).X (n + m - 1) ⟶
        (SSetCochainComplex R X).X (n + m)) => g.hom (cup1 R X n m α β)) hdc
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  have hkey : cup R X α β - ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ cup R X β α)
      = ((SSetCochainComplex R X).d (n + m - 1) (n + m)).hom (cup1 R X n m α β) :=
    calc cup R X α β - ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ cup R X β α)
        = hh ▸ (cochainDiff R X (cup1 R X n m α β)) :=
          (cup1IdentityA R X n m hn hm hh α β hα hβ).symm
      _ = (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).hom
            (cochainDiff R X (cup1 R X n m α β)) := e1.symm
      _ = (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).hom
            (((SSetCochainComplex R X).d (n + m - 1) ((n + m - 1) + 1)).hom (cup1 R X n m α β)) := by
          rw [e2]
      _ = ((SSetCochainComplex R X).d (n + m - 1) (n + m)).hom (cup1 R X n m α β) := e3
  set zx : (SSetCochainComplex R X).cycles (n + m) := cocycleOf R X (cup R X α β) hA with hzx
  set zy : (SSetCochainComplex R X).cycles (n + m) :=
    cocycleOf R X ((Nat.add_comm m n) ▸ cup R X β α) hB' with hzy
  have hcyc : (SSetCochainComplex R X).iCycles (n + m)
      (zx - ((-1 : R) ^ (n * m)) • zy) =
      ((SSetCochainComplex R X).d (n + m - 1) (n + m)).hom (cup1 R X n m α β) := by
    rw [hzx, hzy, map_sub, map_smul, iCycles_cocycleOf, iCycles_cocycleOf, hkey]
  have hzero : (SSetCochainComplex R X).homologyπ (n + m)
      (zx - ((-1 : R) ^ (n * m)) • zy) = 0 :=
    homologyπ_eq_zero_of_d R X (n + m) (n + m - 1)
      (zx - ((-1 : R) ^ (n * m)) • zy) (cup1 R X n m α β) hcyc
  have hhz : (SSetCochainComplex R X).homologyπ (n + m) zx =
      ((-1 : R) ^ (n * m)) • (SSetCochainComplex R X).homologyπ (n + m) zy := by
    rw [← sub_eq_zero, ← map_smul, ← map_sub]
    exact hzero
  have hclass : cohomologyClassOf R X (cup R X α β) hA =
      ((-1 : R) ^ (n * m)) • cohomologyClassOf R X ((Nat.add_comm m n) ▸ cup R X β α) hB' := by
    show (SSetCochainComplex R X).homologyπ (n + m) (cocycleOf R X (cup R X α β) hA) =
      ((-1 : R) ^ (n * m)) •
        (SSetCochainComplex R X).homologyπ (n + m) (cocycleOf R X ((Nat.add_comm m n) ▸ cup R X β α) hB')
    rw [← hzx, ← hzy]
    exact hhz
  have hBcast : cohomologyClassOf R X ((Nat.add_comm m n) ▸ cup R X β α) hB' =
      (Nat.add_comm m n) ▸ cohomologyClassOf R X (cup R X β α) hB :=
    (cohomologyClassOf_cast R X (Nat.add_comm m n) (cup R X β α) hB).symm
  have hmain : cohomologyClassOf R X (cup R X α β) hA =
      ((-1 : R) ^ (n * m)) •
        ((Nat.add_comm m n) ▸ cohomologyClassOf R X (cup R X β α) hB) := by
    rw [hclass, hBcast]
  rw [show (Nat.add_comm n m) = (Nat.add_comm m n).symm from Subsingleton.elim _ _]
  calc ((Nat.add_comm m n).symm) ▸ (cohomologyClassOf R X (cup R X α β) hA)
      = ((Nat.add_comm m n).symm) ▸ (((-1 : R) ^ (n * m)) •
          ((Nat.add_comm m n) ▸ cohomologyClassOf R X (cup R X β α) hB)) := by rw [hmain]
    _ = ((-1 : R) ^ (n * m)) • (((Nat.add_comm m n).symm) ▸
          ((Nat.add_comm m n) ▸ cohomologyClassOf R X (cup R X β α) hB)) :=
        eqRec_smul3 R (fun k => (SSetCochainComplex R X).homology k) _ _ _
    _ = ((-1 : R) ^ (n * m)) • cohomologyClassOf R X (cup R X β α) hB := by
        congr 1
        exact eqRec_symm_eqRec_self3 (M := fun k => (SSetCochainComplex R X).homology k)
          (Nat.add_comm m n) _

theorem gradedComm (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (x : (SSetCochainComplex R X).homology n) (y : (SSetCochainComplex R X).homology m) :
    (Nat.add_comm n m) ▸ (cupH' R X n m x y) =
      ((-1 : R) ^ (n * m)) • cupH' R X m n y x := by
  rcases n with _ | n
  · obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X 0 x
    obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf R X m y
    rw [cupH'_apply' R X α β hα hβ, cupH'_apply' R X β α hβ hα]
    rw [show ((-1 : R) ^ (0 * m)) = 1 from by simp, one_smul]
    exact (cohomologyClassOf_cast R X (Nat.add_comm 0 m) (cup R X α β)
        (cochainDiff_cup_of_cocycles R X α β hα hβ)).trans
      (cohomologyClassOf_congr R X (cupZeroLeft R X m α β hα)
        (cochainDiff_cast R X (Nat.add_comm 0 m) (cup R X α β)
          (cochainDiff_cup_of_cocycles R X α β hα hβ))
        (cochainDiff_cup_of_cocycles R X β α hβ hα))
  · rcases m with _ | m
    · obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X (n + 1) x
      obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf R X 0 y
      rw [cupH'_apply' R X α β hα hβ, cupH'_apply' R X β α hβ hα]
      rw [show ((-1 : R) ^ ((n + 1) * 0)) = 1 from by simp, one_smul]
      exact (cohomologyClassOf_cast R X (Nat.add_comm (n + 1) 0) (cup R X α β)
          (cochainDiff_cup_of_cocycles R X α β hα hβ)).trans
        (cohomologyClassOf_congr R X (cupZeroRight R X (n + 1) α β hβ)
          (cochainDiff_cast R X (Nat.add_comm (n + 1) 0) (cup R X α β)
            (cochainDiff_cup_of_cocycles R X α β hα hβ))
          (cochainDiff_cup_of_cocycles R X β α hβ hα))
    · obtain ⟨α, hα, rfl⟩ := exists_cohomologyClassOf R X (n + 1) x
      obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf R X (m + 1) y
      rw [cupH'_apply' R X α β hα hβ, cupH'_apply' R X β α hβ hα]
      exact cupClassComm R X (n + 1) (m + 1) (by omega) (by omega) α β hα hβ

end

end Work.Cohomology
