import Mathlib
import Submission.Work.BrauerSuzuki.Dade.alpha_induced
import Submission.Work.BrauerSuzuki.Characters.vchar_of_norm_three
import Submission.Work.BrauerSuzuki.Characters.sum_sum_char_eq
import Submission.Work.CharCore.IrrDegreeAux
import Submission.Work.CharCore.column_orthogonality_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical

variable {G : Type*} [Group G] [Fintype G]

/-- The elementary algebra at the end of Dade's Theorem 6.8: the three relations
`1 + ε₁ a - ε₂ c = 0`, `1 + ε₁ b - ε₂ d = 0` and `1 + ε₁ b²/a - ε₂ d²/c = 0` with
`ε₁, ε₂ = ±1` and `a, c ≠ 0` force `a = b`. -/
private lemma dade_algebra {a b c d ε₁ ε₂ : ℂ} (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (ha : a ≠ 0) (hc : c ≠ 0)
    (h1 : 1 + ε₁ * a - ε₂ * c = 0) (h2 : 1 + ε₁ * b - ε₂ * d = 0)
    (h3 : 1 + ε₁ * b ^ 2 / a - ε₂ * d ^ 2 / c = 0) : a = b := by
  have hε₁0 : ε₁ ≠ 0 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
  have hε₂0 : ε₂ ≠ 0 := by rcases hε₂ with h | h <;> rw [h] <;> norm_num
  have hAc : ε₂ * c = 1 + ε₁ * a := by
    rw [sub_eq_zero] at h1
    exact h1.symm
  have hCd : ε₂ * d = 1 + ε₁ * b := by
    rw [sub_eq_zero] at h2
    exact h2.symm
  have hA : 1 + ε₁ * a ≠ 0 := by
    intro h0
    exact hc (by
      have hz : ε₂ * c = 0 := by rw [hAc, h0]
      exact (mul_eq_zero.mp hz).resolve_left hε₂0)
  -- `ε₂ d² / c = (1 + ε₁ b)² / (1 + ε₁ a)`
  have hkey : ε₂ * d ^ 2 / c = (1 + ε₁ * b) ^ 2 / (1 + ε₁ * a) := by
    rw [← hCd, ← hAc]
    field_simp
  have h3' : 1 + ε₁ * b ^ 2 / a - (1 + ε₁ * b) ^ 2 / (1 + ε₁ * a) = 0 := by
    rw [← hkey]
    exact h3
  have hpoly : ε₁ * (a - b) ^ 2 = 0 := by
    have h := h3'
    field_simp at h
    ring_nf at h ⊢
    linear_combination h
  have hab : (a - b) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hpoly with h | h
    · exact absurd h hε₁0
    · exact h
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hab)

/-- **Dade's Theorem 6.8, character-theoretic core.**  There is a non-principal irreducible
character `Λ` of `G` with `Λ ι = Λ 1`, i.e. `ι ∈ ker Λ`. -/
theorem iota_eq_degree (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    ∃ Λ : G → ℂ, Λ ∈ Work.CharCore.Irr G ∧ Λ ≠ (fun _ => (1 : ℂ)) ∧
      Λ (iota S d) = Λ 1 := by
  obtain ⟨Λ, Θ, ε₁, ε₂, hΛ, hΘ, hΛ1, hΘ1, hΛΘ, hε₁, hε₂, hνeq⟩ :=
    Work.BrauerSuzuki.Characters.vchar_of_norm_three (alphaInd_isVChar S d hn)
      (alphaInd_cfInner_self S d hn) (alphaInd_cfInner_principal S d hn)
  refine ⟨Λ, hΛ, hΛ1, ?_⟩
  have hΛclass : Work.CharCore.IsClassFun Λ := Work.CharCore.isClassFun_of_mem_Irr hΛ
  have hΘclass : Work.CharCore.IsClassFun Θ := Work.CharCore.isClassFun_of_mem_Irr hΘ
  have hΛ1ne : Λ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hΛ]
    exact Work.CharCore.irrDeg_ne_zero hΛ
  have hΘ1ne : Θ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hΘ]
    exact Work.CharCore.irrDeg_ne_zero hΘ
  -- the two evaluation relations (6.12)
  have heq1 : (1 : ℂ) + ε₁ * Λ 1 - ε₂ * Θ 1 = 0 := by
    have h := congrFun hνeq 1
    rw [alphaInd_one S d hn] at h
    simpa using h.symm
  have heq2 : (1 : ℂ) + ε₁ * Λ (iota S d) - ε₂ * Θ (iota S d) = 0 := by
    have h := congrFun hνeq (iota S d)
    rw [alphaInd_iota S d hn] at h
    simpa using h.symm
  -- the class of `ι`
  let C : ConjClasses G := ConjClasses.mk (iota S d)
  have hC : ∀ x : C.carrier, orderOf (x : G) = 2 := by
    intro x
    obtain ⟨c, hc⟩ := isConj_iff.mp
      ((Work.CharCore.mem_conjClass_carrier (iota S d) (x : G)).mp x.2)
    have h1 : orderOf (x : G) = orderOf (c * (x : G) * c⁻¹) :=
      (Work.BrauerSuzuki.Group.orderOf_conj_eq c (x : G)).symm
    rw [h1, hc, orderOf_iota]
  have hsum0 : (∑ x : C.carrier, ∑ y : C.carrier,
      alphaInd S d hn ((x : G) * (y : G))) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
    rw [alphaInd]
    refine indFun_alpha_eq_zero_of_not_conj S d hn (fun z hz => ?_)
    have h1 : z * ((x : G) * (y : G)) * z⁻¹ =
        (z * (x : G) * z⁻¹) * (z * (y : G) * z⁻¹) := by group
    rw [h1] at hz
    have hx2 : orderOf (z * (x : G) * z⁻¹) = 2 := by
      rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, hC x]
    have hy2 : orderOf (z * (y : G) * z⁻¹) = 2 := by
      rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, hC y]
    exact (involution_structure S d hn).2.2.2.2 _ _ hx2 hy2 hz
  -- rewrite the sum with the decomposition `α^G = 1 + ε₁ Λ - ε₂ Θ`
  have hsum_exp : (∑ x : C.carrier, ∑ y : C.carrier,
      alphaInd S d hn ((x : G) * (y : G)))
      = ∑ x : C.carrier, ∑ y : C.carrier,
          ((1 : ℂ) + ε₁ * Λ ((x : G) * (y : G)) - ε₂ * Θ ((x : G) * (y : G))) := by
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hνeq]
    simp
  -- and evaluate the three pieces
  have hιC : iota S d ∈ C.carrier :=
    (Work.CharCore.mem_conjClass_carrier (iota S d) (iota S d)).mpr
      (isConj_iff.mpr ⟨1, by simp⟩)
  have hΛrep : Λ (Work.CharCore.rep C) = Λ (iota S d) :=
    (Work.CharCore.IsClassFun.eq_rep hΛclass hιC).symm
  have hΘrep : Θ (Work.CharCore.rep C) = Θ (iota S d) :=
    (Work.CharCore.IsClassFun.eq_rep hΘclass hιC).symm
  have hΛsum := Work.BrauerSuzuki.Characters.sum_sum_char_eq hΛ C
  have hΘsum := Work.BrauerSuzuki.Characters.sum_sum_char_eq hΘ C
  have h1s : (∑ x : C.carrier, ∑ y : C.carrier, (1 : ℂ))
      = (Nat.card C.carrier : ℂ) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
    ring
  have h2s : (∑ x : C.carrier, ∑ y : C.carrier, ε₁ * Λ ((x : G) * (y : G)))
      = ε₁ * (((Nat.card C.carrier : ℂ) * Λ (iota S d)) ^ 2 / Λ 1) := by
    have h := hΛsum
    rw [hΛrep] at h
    rw [← h]
    simp only [Finset.mul_sum]
  have h3s : (∑ x : C.carrier, ∑ y : C.carrier, ε₂ * Θ ((x : G) * (y : G)))
      = ε₂ * (((Nat.card C.carrier : ℂ) * Θ (iota S d)) ^ 2 / Θ 1) := by
    have h := hΘsum
    rw [hΘrep] at h
    rw [← h]
    simp only [Finset.mul_sum]
  have hmain : (∑ x : C.carrier, ∑ y : C.carrier, alphaInd S d hn ((x : G) * (y : G)))
      = (Nat.card C.carrier : ℂ) ^ 2 *
        (1 + ε₁ * (Λ (iota S d)) ^ 2 / Λ 1 - ε₂ * (Θ (iota S d)) ^ 2 / Θ 1) := by
    rw [hsum_exp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [h1s, h2s, h3s]
    ring
  have hmul : (Nat.card C.carrier : ℂ) ^ 2 *
      (1 + ε₁ * (Λ (iota S d)) ^ 2 / Λ 1 - ε₂ * (Θ (iota S d)) ^ 2 / Θ 1) = 0 := by
    rw [← hmain, hsum0]
  have hCne : (Nat.card C.carrier : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨iota S d, hιC⟩, inferInstance⟩
  have heq3 : 1 + ε₁ * (Λ (iota S d)) ^ 2 / Λ 1 - ε₂ * (Θ (iota S d)) ^ 2 / Θ 1 = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h (pow_ne_zero 2 hCne)
    · exact h
  have hfinal := dade_algebra hε₁ hε₂ hΛ1ne hΘ1ne heq1 heq2 heq3
  exact hfinal.symm

end Work.BrauerSuzuki.Dade
