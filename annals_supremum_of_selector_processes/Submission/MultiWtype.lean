import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiMass
import Submission.MultiAdd
import Submission.MultiW2

/-!
# TASK (child): prove `Submission.Multi.multi_w_type` below (TYPE-indexed multi-w).
# remain; you may add helpers.  This is the index-generic version of Submission/MultiW2.lean's
# multi_w needed by the discretization (index = finite type of functions).  READ MultiAdd.lean and
# MultiW2.lean (both PROVEN) and re-derive the same proofs with the index a finite TYPE I
# ([Fintype I]) instead of a Finset Λ of multisets.
## Definitions to add (namespace Submission.Multi):
#   lamSumI (lam : I → X → ℝ) (i : I) (m : X → ℕ) : ℝ := ∑ x : X, (m x : ℝ) * lam i x
#   supI {I} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ) : ℝ := max' over
#       (Finset.univ : Finset I).image (fun i => lamSumI lam i m), default 0 if empty
#   EsupI (M : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ) : ℝ :=
#       ∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m * supI (I := I) lam m
#   threshFamilyI (N : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ) : Finset (X → ℕ) :=
#       (msizeExact (X := X) N).filter (fun S : X → ℕ => Lw * EsupI (X := X) N μ I lam ≤
#          supI (I := I) lam S)
# (Lw is Multi.Lw = (Kbig:ℝ)*10^12; eN N = Multi.eN N; Kbig in MultiMass.lean; msizeExact in
#  Multi.lean; Esup/supLam/lamSum in MultiAdd.lean.)
## THEOREMS (fixed names/signatures):
-/
/-!
# TASK (child): prove `Submission.Multi.multi_w_type` below (TYPE-indexed multi-w).
This is the index-generic version of Submission/MultiW2.lean's multi_w (index = finite
TYPE I instead of a Finset of multisets).  No gaps may remain; helpers may be added.
The four index lemmas (le_supI, supI_le_of_forall, supI_att, EsupI_mul_le) and the theorem
multi_w_type below mirror the Finset-indexed proofs in MultiAdd.lean / MultiW2.lean
(which are PROVEN): supLam/le_supLam/supLam_le_of_forall/supLam_att/Esup/Esup_mul_le are
re-derived here with the index a finite type I.  The deep part applies MSys.multi'_w to the
Finset Flw of threshold multisets exactly as in MultiW2.multi_w.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open scoped BigOperators NNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

variable {X : Type*} [Fintype X]

noncomputable def lamSumI {I : Type*} (lam : I → X → ℝ) (i : I) (m : X → ℕ) : ℝ :=
  ∑ x : X, (m x : ℝ) * lam i x

noncomputable def supI {I : Type*} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ) : ℝ := by
  classical
  let l : Finset ℝ := (Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)
  exact if h : l.Nonempty then l.max' h else 0

noncomputable def EsupI (M : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I]
    (lam : I → X → ℝ) : ℝ :=
  ∑ m ∈ msizeExact (X := X) M, mass (X := X) M μ m * supI (I := I) lam m

noncomputable def threshFamilyI (N : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I]
    (lam : I → X → ℝ) : Finset (X → ℕ) :=
  (msizeExact (X := X) N).filter (fun S : X → ℕ => Lw * EsupI (X := X) N μ I lam ≤ supI (I := I) lam S)

lemma le_supI {I : Type*} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ) (i : I) :
    lamSumI lam i m ≤ supI (I := I) lam m := by
  classical
  unfold supI
  by_cases h : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)).Nonempty
  · simp [h]
    exact Finset.le_max' ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)) (lamSumI lam i m)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · exfalso
    exact h ⟨lamSumI lam i m, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

lemma supI_le_of_forall {I : Type*} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i : I, lamSumI lam i m ≤ c) : supI (I := I) lam m ≤ c := by
  classical
  unfold supI
  by_cases hne : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)).Nonempty
  · simp [hne]
    intro a
    exact h a
  · simp [hne, hc]

lemma supI_att {I : Type*} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ)
    (hne : (Finset.univ : Finset I).Nonempty) : ∃ i : I, lamSumI lam i m = supI (I := I) lam m := by
  classical
  unfold supI
  have him : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)).Nonempty := by
    rcases hne with ⟨i, hi⟩
    exact ⟨lamSumI lam i m, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hm := Finset.max'_mem ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m)) him
  rcases (Finset.mem_image.mp hm) with ⟨i, hi, hEq⟩
  refine ⟨i, ?_⟩
  simp [him]
  exact hEq

lemma supI_nonneg {I : Type*} [Fintype I] (lam : I → X → ℝ) (m : X → ℕ)
    (hlam0 : ∀ i : I, ∀ x : X, 0 ≤ lam i x) : 0 ≤ supI (I := I) lam m := by
  classical
  by_cases hI : (Finset.univ : Finset I).Nonempty
  · rcases hI with ⟨i, hi⟩
    have h0 : 0 ≤ lamSumI lam i m := by
      unfold lamSumI
      exact Finset.sum_nonneg (by intro x hx; exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (hlam0 i x))
    exact le_trans h0 (le_supI lam m i)
  · have hI' : (Finset.univ : Finset I) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    unfold supI
    simp [hI']

lemma lamSumI_add {I : Type*} (lam : I → X → ℝ) (i : I) (m1 m2 : X → ℕ) :
    lamSumI lam i (addM m1 m2) = lamSumI lam i m1 + lamSumI lam i m2 := by
  unfold lamSumI addM
  calc
    (∑ x : X, ((m1 x + m2 x : ℕ) : ℝ) * lam i x)
        = ∑ x : X, ((m1 x : ℝ) * lam i x + (m2 x : ℝ) * lam i x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Nat.cast_add]
          ring
    _ = (∑ x : X, (m1 x : ℝ) * lam i x) + (∑ x : X, (m2 x : ℝ) * lam i x) := by
          rw [Finset.sum_add_distrib]

lemma lamSumI_zero {I : Type*} (lam : I → X → ℝ) (i : I) :
    lamSumI lam i (fun _ : X => 0) = 0 := by
  unfold lamSumI
  simp

lemma supI_zero {I : Type*} [Fintype I] (lam : I → X → ℝ) :
    supI (I := I) lam (fun _ : X => 0) = 0 := by
  classical
  apply le_antisymm
  · exact supI_le_of_forall lam (fun _ : X => 0) le_rfl (by
      intro i
      rw [lamSumI_zero lam i])
  · by_cases hI : (Finset.univ : Finset I).Nonempty
    · rcases hI with ⟨i, hi⟩
      have h0 : 0 ≤ lamSumI lam i (fun _ : X => 0) := by simp [lamSumI_zero lam i]
      exact le_trans h0 (le_supI lam (fun _ : X => 0) i)
    · have hI' : (Finset.univ : Finset I) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      unfold supI
      simp [hI']

lemma supI_subadd {I : Type*} [Fintype I] (lam : I → X → ℝ) (m1 m2 : X → ℕ) :
    supI (I := I) lam (addM m1 m2) ≤ supI (I := I) lam m1 + supI (I := I) lam m2 := by
  classical
  by_cases hI : (Finset.univ : Finset I).Nonempty
  · rcases hI with ⟨i0, hi0⟩
    unfold supI
    by_cases hne_add : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i (addM m1 m2))).Nonempty
    · by_cases hne1 : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m1)).Nonempty
      · by_cases hne2 : ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m2)).Nonempty
        · simp [hne_add, hne1, hne2]
          intro i
          calc
            lamSumI lam i (addM m1 m2) = lamSumI lam i m1 + lamSumI lam i m2 := lamSumI_add lam i m1 m2
            _ ≤ ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m1)).max' hne1
                + ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m2)).max' hne2 := by
                  exact add_le_add
                    (Finset.le_max' ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m1)) (lamSumI lam i m1)
                      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
                    (Finset.le_max' ((Finset.univ : Finset I).image (fun i : I => lamSumI lam i m2)) (lamSumI lam i m2)
                      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
        · exfalso
          exact hne2 ⟨lamSumI lam i0 m2, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩
      · exfalso
        exact hne1 ⟨lamSumI lam i0 m1, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩
    · exfalso
      exact hne_add ⟨lamSumI lam i0 (addM m1 m2), Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩
  · have hI' : (Finset.univ : Finset I) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    unfold supI
    simp [hI']

lemma joint_eq_vSum (P Q : ℕ) (μ : X → ℝ) (v : (X → ℕ) → ℝ) :
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * v (addM a b))
      = (∑ W ∈ msizeExact (X := X) (P + Q), mass (X := X) (P + Q) μ W * v W) := by
  classical
  rw [pair_sum_eq_W_sum P Q μ v]
  apply Finset.sum_congr rfl
  intro W hW
  have hsz : sizeM W = P + Q := (mem_msizeExact_iff (X := X) (m := W) (M := P + Q)).mp hW
  calc
    (∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
        mass (X := X) P μ a * mass (X := X) Q μ (subMM W a) * v W)
        = (∑ a ∈ (msizeExact (X := X) P).filter (fun a : X → ℕ => subM a W),
            mass (X := X) P μ a * mass (X := X) Q μ (subMM W a)) * v W := by
            rw [← Finset.sum_mul]
    _ = mass (X := X) (P + Q) μ W * v W := by
            change FiberSum P Q μ W * v W = mass (X := X) (P + Q) μ W * v W
            rw [fiber_eq_mass P Q μ W hsz]

lemma vSum_add_le (P Q : ℕ) (μ : X → ℝ) (v : (X → ℕ) → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hsub : ∀ a b : X → ℕ, v (addM a b) ≤ v a + v b) :
    (∑ W ∈ msizeExact (X := X) (P + Q), mass (X := X) (P + Q) μ W * v W)
      ≤ (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * v a)
        + (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * v b) := by
  classical
  rw [← joint_eq_vSum P Q μ v]
  calc
    (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
        mass (X := X) P μ a * mass (X := X) Q μ b * v (addM a b))
        ≤ (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
            mass (X := X) P μ a * mass (X := X) Q μ b * (v a + v b)) := by
            apply Finset.sum_le_sum
            intro a ha
            apply Finset.sum_le_sum
            intro b hb
            have hm : 0 ≤ mass (X := X) P μ a * mass (X := X) Q μ b :=
              mul_nonneg (mass_nonneg P hμ0 a) (mass_nonneg Q hμ0 b)
            exact mul_le_mul_of_nonneg_left (hsub a b) hm
    _ = (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * v a)
        + (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * v b) := by
            have hsumP : (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) = 1 := by
              rw [mass_sum_eq_pow Q μ, hμ1]
              simp
            have hsumQ : (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) = 1 := by
              rw [mass_sum_eq_pow P μ, hμ1]
              simp
            let va : (X → ℕ) → ℝ := fun m => v m
            have h1 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * (va a + va b))
                  = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                    + (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va b) := by
                    simp [mul_add, Finset.sum_add_distrib]
            have h2 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                  = ∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a := by
                calc
                  (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                      mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                      = ∑ a ∈ msizeExact (X := X) P,
                          (mass (X := X) P μ a * va a) * (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          calc
                            (∑ b ∈ msizeExact (X := X) Q,
                                mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                                = ∑ b ∈ msizeExact (X := X) Q, (mass (X := X) P μ a * va a) * mass (X := X) Q μ b := by
                                    apply Finset.sum_congr rfl
                                    intro b hb
                                    ring
                            _ = (mass (X := X) P μ a * va a) * (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b) := by
                                    rw [Finset.mul_sum]
                      _ = ∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a := by
                            rw [hsumP]
                            simp
            have h3 :
                (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                    mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                  = ∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b := by
                calc
                  (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                      mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                      = ∑ b ∈ msizeExact (X := X) Q,
                          (mass (X := X) Q μ b * va b) * (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) := by
                          rw [Finset.sum_comm]
                          apply Finset.sum_congr rfl
                          intro b hb
                          calc
                            (∑ a ∈ msizeExact (X := X) P,
                                mass (X := X) P μ a * mass (X := X) Q μ b * va b)
                                = ∑ a ∈ msizeExact (X := X) P, (mass (X := X) Q μ b * va b) * mass (X := X) P μ a := by
                                    apply Finset.sum_congr rfl
                                    intro a ha
                                    ring
                            _ = (mass (X := X) Q μ b * va b) * (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a) := by
                                    rw [Finset.mul_sum]
                      _ = ∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b := by
                            rw [hsumQ]
                            simp
            calc
              (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                  mass (X := X) P μ a * mass (X := X) Q μ b * (v a + v b))
                  = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * (va a + va b)) := rfl
              _ = (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va a)
                    + (∑ a ∈ msizeExact (X := X) P, ∑ b ∈ msizeExact (X := X) Q,
                        mass (X := X) P μ a * mass (X := X) Q μ b * va b) := h1
              _ = (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * va a)
                    + (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * va b) := by
                    rw [h2, h3]
              _ = (∑ a ∈ msizeExact (X := X) P, mass (X := X) P μ a * v a)
                    + (∑ b ∈ msizeExact (X := X) Q, mass (X := X) Q μ b * v b) := rfl

lemma EsupI_add_le (P Q : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1) :
    EsupI (X := X) (P + Q) μ I lam ≤ EsupI (X := X) P μ I lam + EsupI (X := X) Q μ I lam := by
  classical
  unfold EsupI
  exact vSum_add_le P Q μ (supI lam) hμ0 hμ1 (by intro a b; exact supI_subadd lam a b)

lemma EsupI_nat_mul_le (k N : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1) :
    EsupI (X := X) (k * N) μ I lam ≤ (k : ℝ) * EsupI (X := X) N μ I lam := by
  classical
  induction k with
  | zero =>
      have hz : EsupI (X := X) 0 μ I lam = 0 := by
        unfold EsupI
        rw [msizeExact_zero]
        simp [supI_zero]
      simpa [hz] using (le_refl (0 : ℝ))
  | succ k ih =>
      calc
        EsupI (X := X) ((k + 1) * N) μ I lam
            = EsupI (X := X) (k * N + N) μ I lam := by
                have hidx : (k + 1) * N = k * N + N := by ring
                rw [hidx]
        _ ≤ EsupI (X := X) (k * N) μ I lam + EsupI (X := X) N μ I lam :=
                EsupI_add_le (k * N) N μ I lam hμ0 hμ1
        _ ≤ (k : ℝ) * EsupI (X := X) N μ I lam + (1 : ℝ) * EsupI (X := X) N μ I lam := by
                exact add_le_add ih (by simp)
        _ = ((k + 1 : ℕ) : ℝ) * EsupI (X := X) N μ I lam := by
                rw [Nat.cast_add]
                ring

lemma EsupI_mul_le (N : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ)
    (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ i : I, ∀ x : X, 0 ≤ lam i x) :
    EsupI (X := X) (Kbig * N) μ I lam ≤ (Kbig : ℝ) * EsupI (X := X) N μ I lam := by
  classical
  exact EsupI_nat_mul_le Kbig N μ I lam hμ0 hμ1

theorem multi_w_type (N : ℕ) (μ : X → ℝ) (I : Type*) [Fintype I] (lam : I → X → ℝ)
    (hNpos : 0 < N) (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ i : I, ∀ x : X, 0 ≤ lam i x) (hEpos : 0 < EsupI (X := X) N μ I lam) :
    ∃ 𝓒 : Finset (X → ℕ),
      mCover (↑(threshFamilyI N μ I lam) : Set (X → ℕ)) 𝓒 ∧
      mTotalCost (eN N) μ 𝓒 ≤ (2 : ℝ)⁻¹ := by
  classical
  by_contra hcon
  let EsupN : ℝ := EsupI (X := X) N μ I lam
  let Flw : Finset (X → ℕ) := threshFamilyI N μ I lam
  have hIne : (Finset.univ : Finset I).Nonempty := by
    by_contra hne0
    have hIe : (Finset.univ : Finset I) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne0
    have hE0 : EsupI (X := X) N μ I lam = 0 := by
      unfold EsupI
      apply Finset.sum_eq_zero
      intro m hm
      have hz : supI (I := I) lam m = 0 := by
        unfold supI
        simp [hIe]
      simp [hz]
    linarith
  have hLw : 0 < Lw := by
    unfold Lw Kbig
    norm_num
  have hd : 0 < Lw * EsupN := by
    unfold EsupN
    exact mul_pos hLw hEpos
  let i0 : I := Classical.choose hIne
  let iOf : (X → ℕ) → I := fun S => if hS : S ∈ Flw then
      Classical.choose (supI_att (I := I) lam S hIne) else i0
  have iOf_spec : ∀ S : X → ℕ, S ∈ Flw →
      lamSumI lam (iOf S) S = supI (I := I) lam S := by
    intro S hS
    unfold iOf
    rw [dif_pos hS]
    exact Classical.choose_spec (supI_att (I := I) lam S hIne)
  let lamS : (X → ℕ) → X → ℝ :=
    fun S x => (if hS : S ∈ Flw then lam (iOf S) x else 0) / (Lw * EsupN)
  have hlam0S : ∀ S, S ∈ Flw → ∀ x : X, 0 ≤ lamS S x := by
    intro S hS x
    unfold lamS
    rw [dif_pos hS]
    have h0 : 0 ≤ lam (iOf S) x := hlam0 (iOf S) x
    exact div_nonneg h0 (le_of_lt hd)
  have htot1S : ∀ S : X → ℕ, S ∈ Flw → 1 ≤ lamSum lamS S S := by
    intro S hS
    have hEq := iOf_spec S hS
    have hge0 : Lw * EsupI (X := X) N μ I lam ≤ supI (I := I) lam S := (Finset.mem_filter.mp hS).2
    have hge : Lw * EsupN ≤ lamSumI lam (iOf S) S := by
      unfold EsupN at hge0 ⊢
      rwa [hEq]
    calc
      lamSum lamS S S = ∑ x : X, (S x : ℝ) * ((lam (iOf S) x) / (Lw * EsupN)) := by
            unfold lamSum lamS
            apply Finset.sum_congr rfl
            intro x hx
            simp [hS]
      _ = (∑ x : X, (S x : ℝ) * lam (iOf S) x) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = lamSumI lam (iOf S) S / (Lw * EsupN) := by rfl
      _ ≥ 1 := by
            change (1 : ℝ) ≤ lamSumI lam (iOf S) S / (Lw * EsupN)
            rw [le_div_iff₀ hd]
            simpa using hge
  have hcon' : ¬ mSmall (eN N) μ (Flw : Set (X → ℕ)) := by
    intro hsm
    rcases hsm with ⟨𝓒, hcov, hcost⟩
    exact hcon ⟨𝓒, hcov, hcost⟩
  have hDeep := MSys.multi'_w N μ Flw lamS hμ0 hμ1 hlam0S htot1S hcon'
  have hpoint : ∀ m : X → ℕ, supLam Flw lamS m ≤ supI lam m / (Lw * EsupN) := by
    intro m
    have hc0 : 0 ≤ supI lam m / (Lw * EsupN) := by
      exact div_nonneg (supI_nonneg lam m hlam0) (le_of_lt hd)
    refine supLam_le_of_forall (Λ := Flw) (lam := lamS) (m := m)
      (c := supI lam m / (Lw * EsupN)) ?_ hc0
    intro S hS
    have hle : lamSumI lam (iOf S) m ≤ supI lam m := le_supI lam m (iOf S)
    calc
      lamSum lamS S m = ∑ x : X, (m x : ℝ) * ((lam (iOf S) x) / (Lw * EsupN)) := by
            unfold lamSum lamS
            apply Finset.sum_congr rfl
            intro x hx
            simp [hS]
      _ = (∑ x : X, (m x : ℝ) * lam (iOf S) x) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = lamSumI lam (iOf S) m / (Lw * EsupN) := by rfl
      _ ≤ supI lam m / (Lw * EsupN) := div_le_div_of_nonneg_right hle (le_of_lt hd)
  have hEdeep2 : Esup (X := X) (Kbig * N) μ Flw lamS ≤
      EsupI (X := X) (Kbig * N) μ I lam / (Lw * EsupN) := by
    unfold Esup EsupI
    calc
      (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * supLam Flw lamS m)
          ≤ (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * (supI lam m / (Lw * EsupN))) := by
            apply Finset.sum_le_sum
            intro m hm
            have hm0 : 0 ≤ mass (X := X) (Kbig * N) μ m := mass_nonneg' hμ0 (Kbig * N) m
            exact mul_le_mul_of_nonneg_left (hpoint m) hm0
      _ = (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * supI lam m) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro m hm
            ring
  have hadd := EsupI_mul_le (X := X) N μ I lam hμ0 hμ1 hlam0
  have hK1 : (1 : ℝ) ≤ (Kbig : ℝ) := by
    unfold Kbig
    norm_num
  have hlin1 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ EsupI (X := X) (Kbig * N) μ I lam := by
    have hE : Esup (X := X) (Kbig * N) μ Flw lamS ≤ EsupI (X := X) (Kbig * N) μ I lam / (Lw * EsupN) := hEdeep2
    have hE2 : EsupI (X := X) (Kbig * N) μ I lam / (Lw * EsupN) * (Lw * EsupN)
        = EsupI (X := X) (Kbig * N) μ I lam := by
      exact div_mul_cancel₀ _ (ne_of_gt hd)
    have hD : ((10 : ℝ) ^ 11)⁻¹ ≤ EsupI (X := X) (Kbig * N) μ I lam / (Lw * EsupN) :=
      le_trans hDeep hE
    have hD2 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ EsupI (X := X) (Kbig * N) μ I lam / (Lw * EsupN) * (Lw * EsupN) := by
      exact mul_le_mul_of_nonneg_right hD (le_of_lt hd)
    simpa [hE2, mul_assoc] using hD2
  have hlin2 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ (Kbig : ℝ) * EsupN := by
    unfold EsupN at hadd ⊢
    exact le_trans hlin1 hadd
  have hc0 : 0 < ((10 : ℝ) ^ 11)⁻¹ := by positivity
  have hineq : ((10 : ℝ) ^ 11)⁻¹ * Lw ≤ (Kbig : ℝ) := by
    have hE : 0 < EsupN := by unfold EsupN; exact hEpos
    have hd2 : 0 < EsupN := hE
    have hlin2' : ((10 : ℝ) ^ 11)⁻¹ * Lw * EsupN ≤ (Kbig : ℝ) * EsupN := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hlin2
    have hstep : ((10 : ℝ) ^ 11)⁻¹ * Lw ≤ (Kbig : ℝ) := by
      exact le_of_mul_le_mul_right hlin2' hE
    exact hstep
  have hnum : ((10 : ℝ) ^ 11)⁻¹ * Lw = (Kbig : ℝ) * (10 : ℝ) := by
    unfold Lw
    field_simp [show (10 : ℝ) ^ 11 ≠ 0 by positivity]
  rw [hnum] at hineq
  have hbig : (Kbig : ℝ) * (10 : ℝ) ≤ (Kbig : ℝ) := by exact hineq
  have hKpos : (0 : ℝ) < (Kbig : ℝ) := by unfold Kbig; norm_num
  have hbig' : (Kbig : ℝ) * (10 : ℝ) ≤ (Kbig : ℝ) * (1 : ℝ) := by
    simpa using hbig
  have : (10 : ℝ) ≤ 1 := le_of_mul_le_mul_left hbig' hKpos
  norm_num at this

end Multi
end Submission
