import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Char.inner_alpha_beta
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.BSW.Cases.Order

open OddOrder.RepresentationTheory

/-- A virtual character `φ ∈ ZIrr G` with `⟨φ, φ⟩ = 3`, `⟨φ, 1_G⟩ = 1` and `φ(1) = 0` is of the
form `φ = 1_G + ψ₁ - ψ₂` with `ψ₁, ψ₂` distinct irreducible characters whose degrees differ by
`1` (`ψ₂(1) = ψ₁(1) + 1`).

Mathematically: writing `φ` in the orthonormal basis of irreducible characters, Parseval gives
`Σ_χ n_χ² = 3` with `n_χ ∈ ℤ`, the trivial character occurs with coefficient `1`, so exactly two
further characters occur, each with coefficient `±1`; evaluating at `1` (`φ(1) = 0`) with positive
degrees forces the two signs to be opposite and the larger degree to be the one with `-`. -/
theorem existsDecompThree {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hZ : φ ∈ OddOrder.RepresentationTheory.ZIrr G)
    (hnorm : OddOrder.RepresentationTheory.ClassFunction.inner φ φ = 3)
    (hone : OddOrder.RepresentationTheory.ClassFunction.inner φ
      (OddOrder.RepresentationTheory.trivialClassFunction G) = 1) (h0 : φ 1 = 0) :
    ∃ ψ₁ ψ₂ : OddOrder.RepresentationTheory.ClassFunction G ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ₁ ∧
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ₂ ∧ ψ₁ ≠ ψ₂ ∧
      φ = OddOrder.RepresentationTheory.trivialClassFunction G + ψ₁ - ψ₂ ∧
      ψ₂ 1 = ψ₁ 1 + 1 := by
  classical
  set T : ClassFunction G ℂ := trivialClassFunction G with hT
  have hTirr : IsIrreducibleCharacter T := trivialClassFunction_isIrreducible
  have hTmem : T ∈ irreducibleCharacters G := hTirr
  have hTZ : T ∈ ZIrr G := IsIrreducibleCharacter.mem_ZIrr hTirr
  have honeT : ClassFunction.inner φ T = 1 := by rw [hT]; exact hone
  -- the virtual character `ψ = φ - 1_G` has norm `2`
  set ψ : ClassFunction G ℂ := φ - T with hψ
  have hψZ : ψ ∈ ZIrr G := by
    rw [hψ]; exact Submodule.sub_mem _ hZ hTZ
  have hψnorm : ClassFunction.inner ψ ψ = 2 := by
    have hTφ : ClassFunction.inner T φ = 1 := by
      rw [ClassFunction.inner_star_comm, honeT, star_one]
    have hTT : ClassFunction.inner T T = 1 := by
      rw [irr_cf_inner hTmem hTmem, ite_eq_left rfl]
    rw [hψ, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hnorm, honeT, hTφ, hTT]
    norm_num
  obtain ⟨α, β, εα, εβ, hαI, hβI, hαβ, hεα, hεβ, hrepr⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hψZ hψnorm
  -- `φ = T + εα · α + εβ · β`
  have hφeq : φ = T + (εα : ℂ) • α + (εβ : ℂ) • β := by
    have h := hrepr
    rw [hψ] at h
    calc φ = T + (φ - T) := by abel
      _ = T + ((εα : ℂ) • α + (εβ : ℂ) • β) := by rw [h]
      _ = T + (εα : ℂ) • α + (εβ : ℂ) • β := by abel
  -- degrees of `α` and `β`
  obtain ⟨dα, hdα, hα1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hαI⟩ : IrreducibleCharacter G)
  obtain ⟨dβ, hdβ, hβ1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β, hβI⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at hα1 hβ1
  -- evaluating `φ(1) = 0`
  have hdegEval : (1 : ℂ) + (εα : ℂ) * (dα : ℂ) + (εβ : ℂ) * (dβ : ℂ) = 0 := by
    have h := h0
    rw [hφeq] at h
    simpa only [ClassFunction.add_apply, ClassFunction.smul_apply, hT,
      trivialClassFunction_apply, hα1, hβ1] using h
  rcases hεα with hεα | hεα <;> rcases hεβ with hεβ | hεβ
  · -- `(+1, +1)`: impossible since `1 + dα + dβ = 0` but `dα, dβ > 0`
    exfalso
    rw [hεα, hεβ] at hdegEval
    simp only [Int.cast_one, one_mul] at hdegEval
    have hnat : ((1 + dα + dβ : ℕ) : ℂ) = 0 := by push_cast; exact hdegEval
    have hzero : 1 + dα + dβ = 0 := Nat.cast_eq_zero.mp hnat
    omega
  · -- `(+1, -1)`: `φ = T + α - β`, and `dβ = dα + 1`
    refine ⟨α, β, hαI, hβI, hαβ, ?_, ?_⟩
    · rw [hφeq, hεα, hεβ]
      simp only [Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
      rw [hT]
      abel
    · rw [hβ1, hα1]
      rw [hεα, hεβ] at hdegEval
      simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hdegEval
      linear_combination -hdegEval
  · -- `(-1, +1)`: `φ = T + β - α`, and `dα = dβ + 1`
    refine ⟨β, α, hβI, hαI, hαβ.symm, ?_, ?_⟩
    · rw [hφeq, hεα, hεβ]
      simp only [Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
      rw [hT]
      abel
    · rw [hα1, hβ1]
      rw [hεα, hεβ] at hdegEval
      simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hdegEval
      linear_combination -hdegEval
  · -- `(-1, -1)`: impossible since `dα + dβ = 1` but `dα, dβ ≥ 1`
    exfalso
    rw [hεα, hεβ] at hdegEval
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hdegEval
    have h2 : (dα : ℂ) + (dβ : ℂ) = 1 := by linear_combination -hdegEval
    have hnat : dα + dβ = 1 := by exact_mod_cast h2
    omega

end Work.BSW.Cases.Order
