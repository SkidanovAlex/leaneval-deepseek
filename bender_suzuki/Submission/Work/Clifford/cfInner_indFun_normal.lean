import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.autChar_mem_Irr
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.card_charOrbit
import Submission.Work.Clifford.cfInner_orbitSum_self
import Submission.Work.Induction.Bridge
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.CharCore.vchar_norm_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The number of elements of a subgroup, written as an indicator sum. -/
theorem sum_ite_mem_eq_card (K : Subgroup G) :
    (∑ x : G, (if x ∈ K then (1 : ℂ) else 0)) = (Nat.card ↥K : ℂ) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {N : Subgroup G} [N.Normal]

/-- **Value of an induced function on a normal subgroup.**  For `N ⊴ G`, an element `n ∈ N`
and any function `θ : N → ℂ`, `|N| · Ind_N^G θ n = ∑_{x : G} θ (x n x⁻¹)`. -/
theorem indFun_apply_of_normal (θ : N → ℂ) (n : N) :
    (Nat.card ↥N : ℂ) * indFun N θ n = ∑ x : G, conjFun N x θ n := by
  rw [indFun]
  rw [← mul_assoc, mul_inv_cancel₀ (by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩), one_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [dif_pos ((inferInstance : N.Normal).conj_mem (n : G) n.2 x)]
  rfl

end Work.Clifford

namespace Work.Clifford

theorem cfInner_indFun_normal {H : Type*} [Group H] [Fintype H] {N : Subgroup H} [N.Normal]
    [Fintype N] {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) :
    Work.Clifford.cfInner (Work.Clifford.indFun N θ) (Work.Clifford.indFun N θ)
      = (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) * (Nat.card ↥N : ℂ)⁻¹ := by
  have hclass : IsClassFun (indFun N θ) :=
    fun g h => Work.Induction.indFun_conj_apply N θ g h
  rw [cfInner_indFun (H := N) θ hclass]
  have hN0 : (Nat.card ↥N : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hval : ∀ n : N, indFun N θ n = (Nat.card ↥N : ℂ)⁻¹ * ∑ x : H, conjFun N x θ n := by
    intro n
    rw [← indFun_apply_of_normal (G := H) (N := N) θ n, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  have hres : resFun N (indFun N θ) = (Nat.card ↥N : ℂ)⁻¹ • (∑ x : H, conjFun N x θ) := by
    ext n
    rw [resFun_apply, hval n]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have horth : ∀ x : H, cfInner θ (conjFun N x θ) = (if x ∈ inertia N θ then (1 : ℂ) else 0) := by
    intro x
    rw [cfInner_eq_ite_of_mem_Irr hθ (conjFun_mem_Irr x hθ), mem_inertia]
    by_cases h : conjFun N x θ = θ
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hh => h hh.symm), if_neg h]
  rw [hres, cfInner_smul_right, cfInner_sum_right]
  rw [Finset.sum_congr rfl (fun x _ => horth x), sum_ite_mem_eq_card (inertia N θ)]
  rw [show starRingEnd ℂ ((Nat.card ↥N : ℂ)⁻¹) = (Nat.card ↥N : ℂ)⁻¹ from by simp]
  ring

end Work.Clifford
