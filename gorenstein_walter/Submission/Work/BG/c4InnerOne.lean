import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_abstractCoherence

/-!
# Area BG: the four `±Irr` constituents of a norm-`4`, degree-`0` virtual character each
occur in it with coefficient `1`

Let `α ∈ ℤ[Irr K]` (a virtual character) with `‖α‖² = 4` and `α(1) = 0`, and suppose
`α = β₁ + β₂ + β₃ + β₄` with every `βᵢ ∈ ±Irr K`.  Then `⟨βᵢ, α⟩ = 1` for each `i`.

The argument is short and avoids all case analysis on the combinatorial shape of the
decomposition:

* `inner_eq_int_and_sq_le` produces, for each `βᵢ`, an integer `mᵢ` with `⟨α, βᵢ⟩ = mᵢ`
  and `mᵢ² ≤ 4`; conjugate symmetry (`inner_star_comm`) converts this into `⟨βᵢ, α⟩ = mᵢ`;
* the "extreme" values `mᵢ = ±2` are impossible: if `m = mᵢ = ±2` then
  `‖α - m • βᵢ‖² = 4 - m·m - m·m + m·m = 4 - m² = 0`, so positive definiteness
  (`eq_zero_of_inner_self_re_eq_zero`) gives `α = m • βᵢ` and hence
  `α(1) = m · βᵢ(1) ≠ 0`, against the hypothesis `α(1) = 0`.  So `mᵢ ∈ {-1, 0, 1}`;
* summing, `m₁ + m₂ + m₃ + m₄ = ⟨α, α⟩ = 4`, and four integers `≤ 1` summing to `4` are
  all equal to `1`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]

/-- Sesquilinear expansion of `‖φ - c • ψ‖²`. -/
private lemma inner_self_sub_smul (φ ψ : ClassFunction K ℂ) (c : ℂ) :
    ClassFunction.inner (φ - c • ψ) (φ - c • ψ)
      = ClassFunction.inner φ φ - star c * ClassFunction.inner φ ψ
        - c * ClassFunction.inner ψ φ + c * star c * ClassFunction.inner ψ ψ := by
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
  ring

/-- **Key estimate.** The inner product of a `±Irr` character `β` with a virtual character
`α ∈ ℤ[Irr K]` of norm `4` and degree `0` is an integer of absolute value at most `1`. -/
theorem inner_pmIrr_norm_four_le_one (α : ClassFunction K ℂ) (hZ : α ∈ ZIrr K)
    (hnorm : ClassFunction.inner α α = 4) (h0 : α 1 = 0)
    {β : ClassFunction K ℂ} (hβ : IsPmIrr β) :
    ∃ m : ℤ, ClassFunction.inner β α = (m : ℂ) ∧ m ^ 2 ≤ 1 := by
  obtain ⟨m, hm, hmle⟩ := inner_eq_int_and_sq_le hZ 4 (by rw [hnorm]; norm_num) hβ
  have hβα : ClassFunction.inner β α = (m : ℂ) := by
    rw [ClassFunction.inner_star_comm, hm, star_intCast]
  refine ⟨m, hβα, ?_⟩
  by_contra hgt
  push_neg at hgt
  -- `m` is an integer with `1 < m² ≤ 4`, hence `m = ±2`.
  have hmle' : m ^ 2 ≤ (4 : ℤ) := by simpa using hmle
  have hle2 : m ≤ 2 := by nlinarith [hmle', sq_nonneg (m - 2)]
  have hge2 : -2 ≤ m := by nlinarith [hmle', sq_nonneg (m + 2)]
  have hm2 : m = 2 ∨ m = -2 := by
    interval_cases m
    · exact Or.inr rfl
    · norm_num at hgt
    · norm_num at hgt
    · norm_num at hgt
    · exact Or.inl rfl
  have hm4 : m ^ 2 = 4 := by rcases hm2 with h | h <;> rw [h] <;> norm_num
  have hmC : (m : ℂ) * (m : ℂ) = 4 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hm4
    push_cast at this
    simpa [pow_two] using this
  -- `‖α - m • β‖² = 4 - m² = 0`, so `α = m • β` and `α(1) = m · β(1) ≠ 0`.
  have hsym : ClassFunction.inner α β = (m : ℂ) := by
    rw [ClassFunction.inner_star_comm, hβα, star_intCast]
  have hzero : ClassFunction.inner (α - (m : ℂ) • β) (α - (m : ℂ) • β) = 0 := by
    rw [inner_self_sub_smul, hnorm, IsPmIrr.inner_self hβ, hsym, hβα, star_intCast, hmC]
    norm_num
  have hsub : α - (m : ℂ) • β = 0 :=
    eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; simp)
  have hαeq : α = (m : ℂ) • β := sub_eq_zero.mp hsub
  have h1 : α 1 = (m : ℂ) * β 1 := by rw [hαeq, ClassFunction.smul_apply]
  rw [h0] at h1
  exact hβ.apply_one_ne_zero (by
    have h2 : (m : ℂ) * β 1 = 0 := h1.symm
    rcases hm2 with h | h
    · exact (mul_eq_zero.mp h2).resolve_left (by rw [h]; norm_num)
    · exact (mul_eq_zero.mp h2).resolve_left (by rw [h]; norm_num))

open OddOrder.RepresentationTheory Work.BG in
theorem c4InnerOne {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (α : ClassFunction K ℂ) (hZ : α ∈ ZIrr K)
    (hnorm : ClassFunction.inner α α = 4) (h0 : α 1 = 0)
    (β₁ β₂ β₃ β₄ : ClassFunction K ℂ)
    (h1 : Work.BG.IsPmIrr β₁) (h2 : Work.BG.IsPmIrr β₂) (h3 : Work.BG.IsPmIrr β₃)
    (h4 : Work.BG.IsPmIrr β₄)
    (heq : α = β₁ + β₂ + β₃ + β₄) :
    ClassFunction.inner β₁ α = 1 ∧ ClassFunction.inner β₂ α = 1 ∧
      ClassFunction.inner β₃ α = 1 ∧ ClassFunction.inner β₄ α = 1 := by
  obtain ⟨m₁, hβ₁α, hm₁⟩ := inner_pmIrr_norm_four_le_one α hZ hnorm h0 h1
  obtain ⟨m₂, hβ₂α, hm₂⟩ := inner_pmIrr_norm_four_le_one α hZ hnorm h0 h2
  obtain ⟨m₃, hβ₃α, hm₃⟩ := inner_pmIrr_norm_four_le_one α hZ hnorm h0 h3
  obtain ⟨m₄, hβ₄α, hm₄⟩ := inner_pmIrr_norm_four_le_one α hZ hnorm h0 h4
  -- The four coefficients sum to `‖α‖² = 4`.
  have hsumZ : m₁ + m₂ + m₃ + m₄ = 4 := by
    have h : ClassFunction.inner (β₁ + β₂ + β₃ + β₄) α = 4 := by rw [← heq]; exact hnorm
    simp only [ClassFunction.inner_add_left] at h
    rw [hβ₁α, hβ₂α, hβ₃α, hβ₄α] at h
    exact_mod_cast h
  -- Each coefficient lies in `{-1, 0, 1}`; four such integers summing to `4` are all `1`.
  have b1 : m₁ ≤ 1 := by nlinarith [hm₁, sq_nonneg (m₁ - 1)]
  have b2 : m₂ ≤ 1 := by nlinarith [hm₂, sq_nonneg (m₂ - 1)]
  have b3 : m₃ ≤ 1 := by nlinarith [hm₃, sq_nonneg (m₃ - 1)]
  have b4 : m₄ ≤ 1 := by nlinarith [hm₄, sq_nonneg (m₄ - 1)]
  have c1 : -1 ≤ m₁ := by nlinarith [hm₁, sq_nonneg (m₁ + 1)]
  have c2 : -1 ≤ m₂ := by nlinarith [hm₂, sq_nonneg (m₂ + 1)]
  have c3 : -1 ≤ m₃ := by nlinarith [hm₃, sq_nonneg (m₃ + 1)]
  have c4 : -1 ≤ m₄ := by nlinarith [hm₄, sq_nonneg (m₄ + 1)]
  have e1 : m₁ = 1 := by omega
  have e2 : m₂ = 1 := by omega
  have e3 : m₃ = 1 := by omega
  have e4 : m₄ = 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hβ₁α, e1]; norm_num
  · rw [hβ₂α, e2]; norm_num
  · rw [hβ₃α, e3]; norm_num
  · rw [hβ₄α, e4]; norm_num

end Work.BG
