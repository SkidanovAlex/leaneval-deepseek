/-
Copyright (c) 2024. All rights reserved.

# Base data for Higman (1963), Lemma 3

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96, Lemma 3: if `A` is a normal
abelian `X`-subgroup of a Suzuki 2-group and `C` a normal `X`-subgroup covering `A` with
`Φ(C) = Φ(A) = A²`, then `A` has exponent at most `4`.

This file collects the "homocyclic structure" data of a `ξ`-abelian-normal subgroup `A` that the
proof of Lemma 3 uses, packaged as the structure `HomocyclicData`, together with the existence
theorem.  It is imported both by the main file and by the auxiliary lemmas proved for it.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `q = |A ⊓ Ω₁(P)|`, the common order of the quotients of the chain of power subgroups of a
homocyclic `A`. -/
noncomputable def qcard (A : Subgroup P) : ℕ := Nat.card ↥(A ⊓ Work.Higman.omega1 P)

/-- The homocyclic structure of a `ξ`-abelian-normal subgroup `A`: its exponent is `2 ^ e`, its
`2 ^ i`-th power subgroups have order `q ^ (e - i)` (with `q = |A ⊓ Ω₁|`), the
`2 ^ (e-1)`-st power subgroup is `A ⊓ Ω₁`, and every `ξ`-invariant subgroup of `A` is one of the
power subgroups `A ^ (2 ^ i)`. -/
structure HomocyclicData (h : IsSuzuki2Grp P) (A : Subgroup P) where
  /-- The exponent of `A` is `2 ^ e`. -/
  e : ℕ
  /-- `A` has exponent dividing `2 ^ e`. -/
  hexp : ∀ a ∈ A, a ^ 2 ^ e = 1
  /-- `2 ^ e` is the exact exponent of `A`. -/
  horder : ∃ a ∈ A, orderOf a = 2 ^ e
  /-- `|A ^ (2 ^ i)| = q ^ (e - i)`. -/
  hcard : ∀ i ≤ e, Nat.card ↥(powSub A (2 ^ i)) = (qcard A) ^ (e - i)
  /-- `A ^ (2 ^ (e-1)) = A ⊓ Ω₁`. -/
  hT : powSub A (2 ^ (e - 1)) = A ⊓ omega1 P
  /-- Every `ξ`-invariant subgroup of `A` is a power subgroup. -/
  hstruct : ∀ B : Subgroup P, B ≤ A → B.map (h.xi : MulAut P).toMonoidHom = B →
      ∃ i, i ≤ e ∧ B = powSub A (2 ^ i)

/-- The homocyclic structure data exists for every `ξ`-abelian-normal subgroup. -/
theorem exists_homocyclicData (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    Nonempty (HomocyclicData h A) := by
  classical
  obtain ⟨hAn, hAinv, hAb⟩ := hA
  rcases eq_or_ne A ⊥ with hbot | hne
  · subst hbot
    refine ⟨⟨0, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a ha
      simpa using ha
    · exact ⟨1, Subgroup.mem_bot.mpr rfl, by simp⟩
    · intro i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simp [qcard, powSub_one_eq]
    · rw [show (0:ℕ) - 1 = 0 from rfl, pow_zero, powSub_one_eq]
      simp
    · intro B hB _
      refine ⟨0, le_rfl, ?_⟩
      rw [pow_zero, powSub_one_eq]
      exact le_bot_iff.mp hB
  · -- Non-trivial case.
    haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
    obtain ⟨e₁, he1₁, he2₁, hcard₁⟩ := higman_lemma1 h hAb hAinv
    obtain ⟨e₂, he1₂, hcard₂, hT₂, hstruct₂⟩ := homogeneous_structure h hAb hAinv
    have hcard₁' : Nat.card ↥A = qcard A ^ e₁ := hcard₁
    have hcard₂0 : Nat.card ↥A = qcard A ^ e₂ := by
      have h := hcard₂ 0 (Nat.zero_le _)
      simpa [powSub_one_eq, qcard] using h
    have he1pos : 1 ≤ e₁ := by
      rcases Nat.eq_zero_or_pos e₁ with hh | hh
      · exfalso
        apply hne
        rw [Subgroup.eq_bot_iff_forall]
        intro a ha
        simpa [hh] using he1₁ a ha
      · exact hh
    have h2card : 2 ≤ Nat.card ↥A := by
      have h := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial ↥A)
      omega
    have hq2 : 2 ≤ qcard A := by
      by_contra hc
      push Not at hc
      have hc1 : qcard A ≤ 1 := by omega
      have hle1 : qcard A ^ e₁ ≤ 1 := by
        calc qcard A ^ e₁ ≤ 1 ^ e₁ := Nat.pow_le_pow_left hc1 e₁
          _ = 1 := one_pow e₁
      omega
    have heq : e₁ = e₂ :=
      Nat.pow_right_injective hq2 (hcard₁'.symm.trans hcard₂0)
    refine ⟨⟨e₁, he1₁, he2₁, ?_, ?_, ?_⟩⟩
    · intro i hi
      rw [heq]
      exact hcard₂ i (heq ▸ hi)
    · rw [heq]
      exact hT₂
    · intro B hB hBinv
      obtain ⟨i, hi⟩ := hstruct₂ B hB hBinv
      by_cases hle : i ≤ e₁
      · exact ⟨i, hle, hi⟩
      · have hlt : e₁ < i := by omega
        refine ⟨e₁, le_rfl, ?_⟩
        rw [hi, powSub_eq_bot_of_exp (A := A) hAb hlt.le he1₁,
          powSub_eq_bot_of_exp (A := A) hAb le_rfl he1₁]

section Structure

lemma two_dvd_two_pow_pred {e : ℕ} (h3 : 3 ≤ e) : 2 ∣ 2 ^ (e - 1) :=
  ⟨2 ^ (e - 2), by rw [mul_comm, ← pow_succ]; congr 1; omega⟩

lemma four_dvd_two_pow_pred {e : ℕ} (h3 : 3 ≤ e) : 4 ∣ 2 ^ (e - 1) :=
  ⟨2 ^ (e - 3), by
    rw [show (4:ℕ) = 2 ^ 2 from by norm_num, ← pow_add]
    congr 1
    omega⟩

lemma mem_powSub_two_of_sq_eq_one {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hA : IsXiAbelNormal h A) (D : HomocyclicData h A) (h3 : 3 ≤ D.e)
    {z : P} (hzA : z ∈ A) (hz : z ^ 2 = 1) : z ∈ powSub A 2 := by
  have h1 : z ∈ powSub A (2 ^ (D.e - 1)) :=
    mem_powSub_of_sq_eq_one h hA D.hexp D.horder hzA hz
  exact powSub_le_of_dvd hA.abelian (two_dvd_two_pow_pred h3) h1

lemma mem_powSub_two_of_sq_mem_powSub_four {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (D : HomocyclicData h A) (h3 : 3 ≤ D.e) {z : P} (hzA : z ∈ A)
    (hz : z ^ 2 ∈ powSub A 4) : z ∈ powSub A 2 := by
  have hz' : z ^ 2 ∈ powSub (powSub A 2) 2 := by
    rwa [powSub_powSub hA.abelian 2 2]
  obtain ⟨w, hw, hwz⟩ := (mem_powSub_iff (powSub_comm hA.abelian 2)).mp hz'
  have hwA : w ∈ A := powSub_le (by norm_num : 0 < (2:ℕ)) hw
  have hcomm : Commute z w⁻¹ := hA.abelian z hzA w⁻¹ (A.inv_mem hwA)
  have hsq : (z * w⁻¹) ^ 2 = 1 := by
    calc (z * w⁻¹) ^ 2 = z ^ 2 * (w⁻¹) ^ 2 := hcomm.mul_pow 2
      _ = z ^ 2 * (w ^ 2)⁻¹ := by rw [pow_two (w⁻¹), ← mul_inv_rev w w, ← pow_two w]
      _ = z ^ 2 * (z ^ 2)⁻¹ := by rw [hwz]
      _ = 1 := mul_inv_cancel _
  have hzw : z * w⁻¹ ∈ A := A.mul_mem hzA (A.inv_mem hwA)
  have hmem : z * w⁻¹ ∈ powSub A 2 := mem_powSub_two_of_sq_eq_one h hA D h3 hzw hsq
  have : z = (z * w⁻¹) * w := by group
  rw [this]
  exact Subgroup.mul_mem _ hmem hw

lemma mem_powSub_two_of_pow_four_eq_one {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hA : IsXiAbelNormal h A) (D : HomocyclicData h A) (h3 : 3 ≤ D.e)
    {z : P} (hzA : z ∈ A) (hz : z ^ 4 = 1) : z ∈ powSub A 2 := by
  have hz2A : z ^ 2 ∈ A := Subgroup.pow_mem A hzA 2
  have hz22 : (z ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hz
  have h1 : z ^ 2 ∈ powSub A (2 ^ (D.e - 1)) :=
    mem_powSub_of_sq_eq_one h hA D.hexp D.horder hz2A hz22
  have h2 : z ^ 2 ∈ powSub A 4 := powSub_le_of_dvd hA.abelian (four_dvd_two_pow_pred h3) h1
  exact mem_powSub_two_of_sq_mem_powSub_four h hA D h3 hzA h2

end Structure


end Work.Higman
