import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.cor3_1
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.GlaubermanZJ.thompsonJ_eq
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure
import Submission.Work.GlaubermanZJ.Thm41.NumBound
import Submission.Work.GlaubermanZJ.Thm41.replacement_step
import Submission.Work.GlaubermanZJ.Thm41.PcFinal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's Theorem 4.1 (the replacement theorem for odd primes), main proof

Glauberman, *A characteristic subgroup of a p-stable group*, Canad. J. Math. **20** (1968),
Theorem 4.1 (p. 1111): let `S` be a finite `p`-group (`p` odd), `A ∈ 𝒜(S)`, and let `B ⊴ S` have
nilpotence class at most two with `[B,B] ⊆ Z(J(S))`.  If `[B,A;3] ≠ 1`, or `p` is odd and
`[B,A,A] ≠ 1`, then there is `A* ∈ 𝒜(S)` with `A ∩ B ⊊ A* ∩ B` and `[A*,A,A] = 1`.

The proof follows Glauberman's.  After reducing to `S = A·B` (so that `[B,B]` is central in `S`),
one lets `r ≥ 1` be least with `[B,A;r] = 1` and `n ≥ 1` least with `[B,A;n]` abelian.

* If `[B,A;n+1] ≠ 1` (Glauberman's case (4.3)) then `r ≥ n+2`; taking
  `x ∈ [B,A;r-3]` not centralizing `[x,A]` and `M = [x,A] ⊆ [B,A;r-2] ⊆ [B,A;n]` (abelian, with
  `[M,A,A] ⊆ [B,A;r] = 1`) the replacement step applies.
* Otherwise `[B,A;n+1] = 1`, and Glauberman's numerical argument ((4.5)–(4.8),
  `iterComm_abelian_le_two`) gives `n ≤ 2`, whence `[B,A;3] = 1`.  Then `[B,A,A] ≠ 1` by the
  hypothesis, and `[x,A]` is abelian for every `x ∈ B` (case `[B,A;3] = 1`); the replacement step
  applies again.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped commutatorElement
open Subgroup

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- `A ≤ J(S)` for `A ∈ 𝒜(S)`, in the blueprint's vocabulary. -/
theorem isMaxAbelianSubgroup_le_ZJ_thompsonJ {S A : Subgroup G}
    (hA : IsMaxAbelianSubgroup S A) :
    A ≤ Submission.Blueprint.thompsonJ S := by
  obtain ⟨hAS, hAab, hAmax⟩ := hA
  exact le_blueprint_thompsonJ hAS hAab hAmax

/-- **Glauberman's Theorem 4.1 in the reduced situation** (where `[B,B]` is central in `S`). -/
theorem theorem4_1_central (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2)
    (S A B : Subgroup G) [Finite S] (hS : IsPGroup p S)
    (hA : IsMaxAbelianSubgroup S A) (hB : B ≤ S)
    (hBn : S ≤ Subgroup.normalizer (B : Set G))
    (hZ : ⁅B, B⁆ ≤ Work.PGroup.centerIn S)
    (hcomm : ⁅⁅⁅B, A⁆, A⁆, A⁆ ≠ ⊥ ∨ ⁅⁅B, A⁆, A⁆ ≠ ⊥) :
    ∃ A' : Subgroup G, IsMaxAbelianSubgroup S A' ∧ A ⊓ B < A' ⊓ B ∧
      ⁅⁅A', A⁆, A⁆ = ⊥ := by
  classical
  have hAcopy : IsMaxAbelianSubgroup S A := hA
  obtain ⟨hAS, hAab', hAmax⟩ := hA
  have hAab : IsMulCommutative A := isAbelianSubgroup_iff.mp hAab'
  have hAnB : A ≤ Subgroup.normalizer (B : Set G) := hAS.trans hBn
  have hAB_le_B : iterComm B A 1 ≤ B := by
    rw [iterComm_one]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hAnB
  -- Glauberman (4.1): `A ∩ B` centralizes `[B,A] = [B,A;1]`
  have h41 : A ⊓ B ≤ Subgroup.centralizer (iterComm B A 1 : Set G) := by
    rw [iterComm_one]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_inf_commutator_eq_bot hAS hB hAab hZ)
  -- existence of `r ≥ 1` with `[B,A;r] = 1`
  haveI : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  obtain ⟨N, hN⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).mp hnil
  have hexR : ∃ k : ℕ, 1 ≤ k ∧ iterComm B A k = ⊥ := by
    refine ⟨max N 1, le_max_right _ _, ?_⟩
    refine le_bot_iff.mp ?_
    calc iterComm B A (max N 1) ≤ S.lowerCentralSeries (max N 1) :=
          (iterComm_mono hB le_rfl _).trans (iterComm_le_lowerCentralSeries S A hAS _)
      _ ≤ S.lowerCentralSeries N :=
          Subgroup.lowerCentralSeries_antitone (S := S) (le_max_left _ _)
      _ = ⊥ := hN
  set r : ℕ := Nat.find hexR with hrdef
  have hr1 : 1 ≤ r := (Nat.find_spec hexR).1
  have hrbot : iterComm B A r = ⊥ := (Nat.find_spec hexR).2
  -- existence of `n ≥ 1` with `[B,A;n]` abelian
  have hexN : ∃ k : ℕ, 1 ≤ k ∧ IsMulCommutative (iterComm B A k) :=
    ⟨r, hr1, by rw [hrbot]; exact IsMulCommutative.of_comm fun _ _ => Subsingleton.elim _ _⟩
  set n : ℕ := Nat.find hexN with hndef
  have hn1 : 1 ≤ n := (Nat.find_spec hexN).1
  have hnab : IsMulCommutative (iterComm B A n) := (Nat.find_spec hexN).2
  have hnmin : ∀ k, 1 ≤ k → k < n → ¬ IsMulCommutative (iterComm B A k) := by
    intro k hk1 hkn hab
    exact Nat.find_min hexN (show k < Nat.find hexN from hkn) ⟨hk1, hab⟩
  by_cases hcase : iterComm B A (n + 1) = ⊥
  · -- Case 2: `[B,A;n+1] = 1`, hence `n ≤ 2` and `[B,A;3] = 1`
    have hn2 : n ≤ 2 :=
      iterComm_abelian_le_two n hAS hB hBn hAab hZ hn1 hnmin hcase
    have hV3 : iterComm B A 3 = ⊥ := by
      refine iterComm_eq_bot_of_le hAnB hcase ?_
      omega
    have hV3' : iterComm B A (2 + 1) = ⊥ := hV3
    have hV2ne : iterComm B A 2 ≠ ⊥ := by
      intro hV2
      rcases hcomm with h3 | h2
      · refine h3 ?_
        show iterComm B A 3 = ⊥
        rw [show (3:ℕ) = 2 + 1 from rfl, iterComm_succ, hV2, Subgroup.commutator_bot_left]
      · exact h2 hV2
    -- find `x ∈ B` with `[x,A] ⊄ C(A)`
    obtain ⟨x, hxB, hxM⟩ : ∃ x ∈ B, ¬ Work.PGroup.commClosure x A ≤
        Subgroup.centralizer (A : Set G) := by
      by_contra hcon
      push_neg at hcon
      have hle : iterComm B A 1 ≤ Subgroup.centralizer (A : Set G) := by
        rw [iterComm_one, Subgroup.commutator_le]
        intro u hu a ha
        exact hcon u hu (Work.PGroup.mem_commClosure ha)
      exact hV2ne (by
        rw [show (2:ℕ) = 1 + 1 from rfl, iterComm_succ]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
    have hM1 : Work.PGroup.commClosure x A ≤ iterComm B A 1 :=
      Work.PGroup.commClosure_le fun a ha =>
        Subgroup.commutator_mem_commutator (H₁ := B) (H₂ := A) hxB ha
    have hMAA : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      have h : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ ≤ iterComm B A 3 := by
        refine (Subgroup.commutator_mono (Subgroup.commutator_mono hM1 le_rfl) le_rfl).trans ?_
        exact le_of_eq (by simp only [iterComm_succ, iterComm_zero])
      exact h.trans_eq hV3
    refine Thm41.replacement_step (x := x) hAcopy (hM1.trans (hAB_le_B.trans hB)) ?_
      (hM1.trans hAB_le_B)
      (fun hMA => hxM (hMA.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab)))
      (h41.trans (Subgroup.centralizer_le hM1)) hMAA
    -- the only remaining goal: `commClosure x A` is abelian
    exact commClosure_abelian_of_iterComm_three_eq_bot
        p hp hpne S A B hS hAS hB hBn hAab hZ (by show iterComm B A 3 = ⊥; exact hV3) x hxB
  · -- Case 1: `[B,A;n+1] ≠ 1`, so `r ≥ n+2` (Glauberman's case (4.3))
    have hrge : n + 2 ≤ r := by
      by_contra hcon
      push_neg at hcon
      exact hcase (iterComm_eq_bot_of_le hAnB hrbot (by omega))
    have hr3 : 3 ≤ r := by omega
    have hVr1 : iterComm B A (r - 1) ≠ ⊥ := by
      intro h
      exact Nat.find_min hexR (show r - 1 < Nat.find hexR from by omega) ⟨by omega, h⟩
    have hVr2_notcent : ¬ iterComm B A (r - 2) ≤ Subgroup.centralizer (A : Set G) := by
      intro h
      apply hVr1
      rw [show r - 1 = (r - 2) + 1 from by omega, iterComm_succ,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h
    -- find `x ∈ [B,A;r-3]` with `[x,A] ⊄ C(A)`
    obtain ⟨x, hx3, hxM⟩ : ∃ x ∈ iterComm B A (r - 3), ¬ Work.PGroup.commClosure x A ≤
        Subgroup.centralizer (A : Set G) := by
      by_contra hcon
      push_neg at hcon
      apply hVr2_notcent
      rw [show r - 2 = (r - 3) + 1 from by omega, iterComm_succ, Subgroup.commutator_le]
      intro u hu a ha
      exact hcon u hu (Work.PGroup.mem_commClosure ha)
    have hM2 : Work.PGroup.commClosure x A ≤ iterComm B A (r - 2) := by
      refine (Work.PGroup.commClosure_le fun a ha =>
        Subgroup.commutator_mem_commutator hx3 ha).trans_eq ?_
      rw [show r - 2 = (r - 3) + 1 from by omega, iterComm_succ]
    have hMAA : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      have h : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ ≤ iterComm B A r := by
        refine (Subgroup.commutator_mono (Subgroup.commutator_mono hM2 le_rfl) le_rfl).trans ?_
        refine le_of_eq ?_
        rw [← iterComm_succ, show (r - 2) + 1 = r - 1 from by omega, ← iterComm_succ,
          show (r - 1) + 1 = r from by omega]
      exact h.trans_eq hrbot
    refine Thm41.replacement_step (x := x) hAcopy
      (hM2.trans ((iterComm_le B A hAnB (r - 2)).trans hB)) ?_
      (hM2.trans (iterComm_le B A hAnB (r - 2)))
      (fun hMA => hxM (hMA.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab)))
      (h41.trans (Subgroup.centralizer_le (hM2.trans (iterComm_le_of_le B A hAnB (by omega)))))
      hMAA
    -- the only remaining goal: `commClosure x A` is abelian
    exact Work.PGroup.isMulCommutative_of_le
        (Work.PGroup.isMulCommutative_of_le hnab (iterComm_le_of_le B A hAnB (by omega)))
        hM2

end Work.GlaubermanZJ
