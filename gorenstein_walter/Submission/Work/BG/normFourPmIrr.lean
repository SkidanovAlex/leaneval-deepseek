import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.normFourSplit
import Submission.Work.BG.sumSqFourSplit

/-!
# Area BG: a norm-`4`, degree-`0` virtual character is a sum of four `±Irr` characters

`normFourPmIrr` is the leaf used by the BG §2 argument (cf. `deltaNormFour`): a virtual
character `δ ∈ ℤ[Irr K]` with squared norm `4` and `δ(1) = 0` decomposes as a sum of four
`±Irr` characters.

The proof is pure Fourier algebra assembled from the library leaves:
* `mem_ZIrr_inner_self_eq_sum_sq` writes `δ = ∑_{a ∈ s} c a · a` over irreducibles with
  `‖δ‖² = ∑_{a ∈ s} c a²`; the hypothesis `‖δ‖² = 4` becomes `∑ c a² = 4`;
* the integer-vector leaf `sumSqFourSplit` splits this either into a single element with
  `c a² = 4` (coefficient `±2`) or into two parts of squared norm `2` each;
* the single-element case is ruled out by `δ(1) = 0`: `δ = (±2) · α` would have
  `δ(1) = ±2 α(1) ≠ 0`;
* the two-part case is fed to `normFourSplit`, which produces `g₁, g₂ ∈ ℤ[Irr K]` of squared
  norm `2` with `δ = g₁ - g₂`, and `exists_signed_pair_of_mem_ZIrr_inner_self_eq_two` writes
  each of `g₁, g₂` as a signed pair of irreducibles;
* rearranging `ε₁α₁ + ε₂β₁ - (ε₃α₂ + ε₄β₂)` gives the required sum of four `±Irr` characters.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- A signed irreducible character `ε • α` (with `ε = ±1`) is a `±Irr` character. -/
lemma isPmIrr_zsmul_of_sq_eq_one {K : Type} [Group K] {α : ClassFunction K ℂ}
    (hα : IsIrreducibleCharacter α) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    IsPmIrr ((ε : ℂ) • α) := by
  rcases hε with rfl | rfl
  · left; simpa using hα
  · right; simpa using hα

/-- `φ` is a `±Irr` character iff `-φ` is. -/
lemma isPmIrr_neg_iff {K : Type} [Group K] (φ : ClassFunction K ℂ) :
    IsPmIrr (-φ) ↔ IsPmIrr φ := by
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · rw [neg_neg] at h; exact Or.inl h
  · rintro (h | h)
    · exact Or.inr (by rwa [neg_neg])
    · exact Or.inl h

open OddOrder.RepresentationTheory Work.BG in
theorem normFourPmIrr {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (δ : ClassFunction K ℂ) (hZ : δ ∈ ZIrr K)
    (hnorm : ClassFunction.inner δ δ = 4) (h0 : δ 1 = 0) :
    ∃ χ₁ χ₂ χ₃ χ₄ : ClassFunction K ℂ,
      IsPmIrr χ₁ ∧ IsPmIrr χ₂ ∧ IsPmIrr χ₃ ∧ IsPmIrr χ₄ ∧
        δ = χ₁ + χ₂ + χ₃ + χ₄ := by
  classical
  obtain ⟨c, hsupp, hrepr, hnorm_sum⟩ := mem_ZIrr_inner_self_eq_sum_sq hZ
  -- Integer form of the norm-`4` hypothesis.
  have hsum_int : ∑ a ∈ c.support, c a ^ 2 = 4 := by
    have hc : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = 4 := by
      push_cast
      rw [← hnorm_sum, hnorm]
    exact_mod_cast hc
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hsupp' : ∀ a ∈ c.support, IsIrreducibleCharacter a :=
    fun a ha => mem_irreducibleCharacters.mp (hsupp ha)
  rcases sumSqFourSplit hne hsum_int with
      ⟨α, hs, hsq⟩ | ⟨S, T, hS, hT, hdisj, hcover, hS2, hT2⟩
  · -- Single-constituent case `δ = (±2)·α` is impossible because `δ(1) = 0`.
    exfalso
    have hαirr : IsIrreducibleCharacter α := hsupp' α (by rw [hs]; simp)
    have hδeq : δ = (c α : ℂ) • α := by rw [hrepr, hs, Finset.sum_singleton]
    obtain ⟨d, hd, hα1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hαirr⟩ : IrreducibleCharacter K)
    simp only [IrreducibleCharacter.coe_mk] at hα1
    have hα1ne : α 1 ≠ 0 := by rw [hα1]; exact Nat.cast_ne_zero.mpr hd.ne'
    have hcval : c α = 2 ∨ c α = -2 := by
      have hfac : (c α - 2) * (c α + 2) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with h | h
      · left; omega
      · right; omega
    have hcnz : (c α : ℂ) ≠ 0 := by
      rcases hcval with h | h <;> rw [h] <;> norm_num
    rw [hδeq, ClassFunction.smul_apply] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hcnz h
    · exact hα1ne h
  · -- Two norm-`2` parts: `δ = g₁ - g₂`, each `gᵢ` a signed pair of irreducibles.
    obtain ⟨g₁, g₂, heq, _hg₁Z, _hg₂Z, hg₁n, hg₂n, _hdisjCF⟩ :=
      normFourSplit (s := c.support) (c := ⇑c) hsupp' hS hT hdisj hcover hS2 hT2
    obtain ⟨α₁, β₁, ε₁, η₁, hα₁, hβ₁, _hα₁β₁, hε₁, hη₁, hg₁eq⟩ :=
      exists_signed_pair_of_mem_ZIrr_inner_self_eq_two _hg₁Z hg₁n
    obtain ⟨α₂, β₂, ε₂, η₂, hα₂, hβ₂, _hα₂β₂, hε₂, hη₂, hg₂eq⟩ :=
      exists_signed_pair_of_mem_ZIrr_inner_self_eq_two _hg₂Z hg₂n
    refine ⟨(ε₁ : ℂ) • α₁, (η₁ : ℂ) • β₁, -((ε₂ : ℂ) • α₂), -((η₂ : ℂ) • β₂),
      isPmIrr_zsmul_of_sq_eq_one hα₁ hε₁,
      isPmIrr_zsmul_of_sq_eq_one hβ₁ hη₁,
      (isPmIrr_neg_iff ((ε₂ : ℂ) • α₂)).mpr (isPmIrr_zsmul_of_sq_eq_one hα₂ hε₂),
      (isPmIrr_neg_iff ((η₂ : ℂ) • β₂)).mpr (isPmIrr_zsmul_of_sq_eq_one hβ₂ hη₂),
      ?_⟩
    rw [hrepr, heq, hg₁eq, hg₂eq]
    abel

end Work.BG
