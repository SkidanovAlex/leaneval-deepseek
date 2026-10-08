import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.remark15Disjoint

/-!
# BG §2: `AbstractCoherenceProp` (the pure construction of Bender–Glauberman p. 206)

This file proves `Work.BG.s02_abstractCoherence : Work.BG.AbstractCoherenceProp`,
the purely combinatorial statement P-3 of the area-BG design (`BG/S02.lean`).

The mathematical content is the "critical-index" analysis: a single signed irreducible
`g₁` can always be found that is a constituent (with coefficient `1`) of *every* `D i`
(`i ≠ i1`); any index where this fails produces exactly the `FailConfig` of `S02.lean`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## Elementary consequences of the library's character theory API -/

/-- `IsPmIrr φ` means `φ = ±χ` for an irreducible character `χ`; in particular `φ ∈ ℤ[Irr K]`. -/
theorem IsPmIrr.mem_ZIrr {K : Type} [Group K] {φ : ClassFunction K ℂ} (h : IsPmIrr φ) :
    φ ∈ ZIrr K := by
  rcases h with h | h
  · exact IsIrreducibleCharacter.mem_ZIrr h
  · have := IsIrreducibleCharacter.mem_ZIrr h
    simpa using (Submodule.neg_mem (ZIrr K) this)

/-- A signed irreducible character has squared norm `1`. -/
theorem IsPmIrr.inner_self {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ : ClassFunction K ℂ} (h : IsPmIrr φ) :
    ClassFunction.inner φ φ = 1 := by
  rcases h with h | h
  · exact IsIrreducibleCharacter.inner_self_eq_one h
  · have := IsIrreducibleCharacter.inner_self_eq_one h
    rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right] at this
    simpa using this

/-- A signed irreducible character does not vanish at `1`. -/
theorem IsPmIrr.apply_one_ne_zero {K : Type} [Group K] {φ : ClassFunction K ℂ}
    (h : IsPmIrr φ) : φ 1 ≠ 0 := by
  rcases h with h | h
  · obtain ⟨d, hd, hgd⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨φ, h⟩ : IrreducibleCharacter K)
    rw [IrreducibleCharacter.coe_mk] at hgd
    rw [hgd]
    exact Nat.cast_ne_zero.mpr hd.ne'
  · obtain ⟨d, hd, hgd⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨-φ, h⟩ : IrreducibleCharacter K)
    rw [IrreducibleCharacter.coe_mk] at hgd
    intro h0
    have : ((-φ : ClassFunction K ℂ) : K → ℂ) 1 = 0 := by
      rw [ClassFunction.neg_apply, h0, neg_zero]
    rw [hgd] at this
    exact (Nat.cast_ne_zero.mpr hd.ne') this

/-- A virtual character of norm `1` is a signed irreducible character. -/
theorem isPmIrr_of_mem_ZIrr_inner_self_eq_one {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ : ClassFunction K ℂ} (hφ : φ ∈ ZIrr K)
    (hn : ClassFunction.inner φ φ = 1) : IsPmIrr φ := by
  obtain ⟨ε, ξ, hε, heq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hn
  rcases hε with h | h
  · left; rw [heq, h, one_smul]; exact ξ.2
  · right; rw [heq, h]; simpa using ξ.2

/-- **Signed Fourier coefficient bound.** The coefficient of a signed irreducible `g` in a
virtual character `φ` of norm `N` is an integer of absolute value at most `√N`. -/
theorem inner_eq_int_and_sq_le {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ : ClassFunction K ℂ} (hφ : φ ∈ ZIrr K) (N : ℕ)
    (hN : ClassFunction.inner φ φ = (N : ℂ)) {g : ClassFunction K ℂ} (hg : IsPmIrr g) :
    ∃ m : ℤ, ClassFunction.inner φ g = (m : ℂ) ∧ m ^ 2 ≤ (N : ℤ) := by
  obtain ⟨c, hsupp, hrepr, hnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have key : ∀ χ : IrreducibleCharacter K,
      ClassFunction.inner φ (χ : ClassFunction K ℂ) = (c (χ : ClassFunction K ℂ) : ℂ) :=
    fun χ => by rw [hrepr]; exact inner_eq_coeff_of_repr χ hsupp
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = (N : ℂ) := by rw [← hnorm, hN]
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = (N : ℤ) := by
    have h1 : ((∑ a ∈ c.support, c a ^ 2 : ℤ) : ℂ) = (N : ℂ) := by
      push_cast; exact hsumC
    exact_mod_cast h1
  have hle : ∀ χ : IrreducibleCharacter K, c (χ : ClassFunction K ℂ) ^ 2 ≤ (N : ℤ) := by
    intro χ
    rw [← hsumZ]
    by_cases hmem : (χ : ClassFunction K ℂ) ∈ c.support
    · exact Finset.single_le_sum (fun a _ => sq_nonneg (c a)) hmem
    · rw [Finsupp.notMem_support_iff.mp hmem, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      exact Finset.sum_nonneg fun a _ => sq_nonneg (c a)
  rcases hg with hirr | hneg
  · exact ⟨c (⟨g, hirr⟩ : IrreducibleCharacter K), key ⟨g, hirr⟩, hle ⟨g, hirr⟩⟩
  · refine ⟨-c (⟨-g, hneg⟩ : IrreducibleCharacter K), ?_, ?_⟩
    · have h := key ⟨-g, hneg⟩
      have hneg1 : ClassFunction.inner φ g = - ClassFunction.inner φ (-g) := by
        rw [ClassFunction.inner_neg_right]; ring
      rw [hneg1, h]; push_cast; ring
    · rw [show (-(c (⟨-g, hneg⟩ : IrreducibleCharacter K))) ^ 2
          = c (⟨-g, hneg⟩ : IrreducibleCharacter K) ^ 2 from by ring]
      exact hle ⟨-g, hneg⟩

/-- The inner product of two integer combinations of irreducibles, in coordinates. -/
theorem inner_repr_repr {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {c d : ClassFunction K ℂ →₀ ℤ}
    (hcsupp : ↑c.support ⊆ irreducibleCharacters K) (hdsupp : ↑d.support ⊆ irreducibleCharacters K) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (∑ a ∈ d.support, (d a : ℂ) • a)
      = ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) := by
  classical
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ClassFunction.inner_smul_left]
  congr 1
  rw [inner_sum_right]
  rw [Finset.sum_eq_single a]
  · rw [ClassFunction.inner_smul_right, star_intCast,
      irr_cf_inner (hcsupp (Finset.mem_coe.mpr ha)) (hcsupp (Finset.mem_coe.mpr ha)),
      ite_eq_left rfl, mul_one]
  · intro b hb hba
    rw [ClassFunction.inner_smul_right,
      irr_cf_inner (hcsupp (Finset.mem_coe.mpr ha)) (hdsupp (Finset.mem_coe.mpr hb)),
      ite_eq_right (fun h => hba h.symm), mul_zero]
  · intro hna
    rw [Finsupp.notMem_support_iff.mp hna, Int.cast_zero, zero_smul, ClassFunction.inner_zero_right]

/-- **Common signed constituent.** Two virtual characters of norm `2` or `3` with inner product
`1` have a signed irreducible constituent in common with coefficient `1` in each. -/
theorem exists_common_constituent {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {φ ψ : ClassFunction K ℂ} (hφ : φ ∈ ZIrr K) (hψ : ψ ∈ ZIrr K)
    (hφn : ClassFunction.inner φ φ = 2 ∨ ClassFunction.inner φ φ = 3)
    (hψn : ClassFunction.inner ψ ψ = 2 ∨ ClassFunction.inner ψ ψ = 3)
    (ho : ClassFunction.inner φ ψ = 1) :
    ∃ χ : ClassFunction K ℂ, IsPmIrr χ ∧ ClassFunction.inner φ χ = 1 ∧
      ClassFunction.inner ψ χ = 1 := by
  classical
  obtain ⟨c, hcsupp, hcrepr, hcnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  obtain ⟨d, hdsupp, hdrepr, hdnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hψ
  have hcsum : ∑ a ∈ c.support, c a ^ 2 = 2 ∨ ∑ a ∈ c.support, c a ^ 2 = 3 := by
    have hcsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 2 ∨ ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 3 := by
      rw [← hcnorm]; exact hφn
    have hz : (((∑ a ∈ c.support, c a ^ 2 : ℤ)) : ℂ) = 2 ∨
        (((∑ a ∈ c.support, c a ^ 2 : ℤ)) : ℂ) = 3 := by
      rcases hcsumC with h | h
      · left; push_cast; exact h
      · right; push_cast; exact h
    rcases hz with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hdsum : ∑ a ∈ d.support, d a ^ 2 = 2 ∨ ∑ a ∈ d.support, d a ^ 2 = 3 := by
    have hdsumC : ∑ a ∈ d.support, (d a : ℂ) ^ 2 = 2 ∨ ∑ a ∈ d.support, (d a : ℂ) ^ 2 = 3 := by
      rw [← hdnorm]; exact hψn
    have hz : (((∑ a ∈ d.support, d a ^ 2 : ℤ)) : ℂ) = 2 ∨
        (((∑ a ∈ d.support, d a ^ 2 : ℤ)) : ℂ) = 3 := by
      rcases hdsumC with h | h
      · left; push_cast; exact h
      · right; push_cast; exact h
    rcases hz with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hc3 : ∑ a ∈ c.support, c a ^ 2 ≤ 3 := by
    rcases hcsum with h | h <;> rw [h] <;> norm_num
  have hd3 : ∑ a ∈ d.support, d a ^ 2 ≤ 3 := by
    rcases hdsum with h | h <;> rw [h] <;> norm_num
  have hcsq : ∀ a, c a ^ 2 ≤ 3 := by
    intro a
    by_cases ha : a ∈ c.support
    · exact le_trans (Finset.single_le_sum (fun x _ => sq_nonneg (c x)) ha) hc3
    · rw [Finsupp.notMem_support_iff.mp ha]; norm_num
  have hdsq : ∀ a, d a ^ 2 ≤ 3 := by
    intro a
    by_cases ha : a ∈ d.support
    · exact le_trans (Finset.single_le_sum (fun x _ => sq_nonneg (d x)) ha) hd3
    · rw [Finsupp.notMem_support_iff.mp ha]; norm_num
  have hmixed : ClassFunction.inner φ ψ = ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) := by
    rw [hcrepr, hdrepr]; exact inner_repr_repr hcsupp hdsupp
  have hz : ∑ a ∈ c.support, c a * d a = 1 := by
    have h1 : ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) = 1 := by rw [← hmixed]; exact ho
    have : (((∑ a ∈ c.support, c a * d a : ℤ)) : ℂ) = 1 := by push_cast; exact h1
    exact_mod_cast this
  have hbdd : ∀ a ∈ c.support, c a * d a ≤ 1 := by
    intro a _
    have h1 : c a ≤ 1 := by
      nlinarith [hcsq a, sq_nonneg (c a - 2), sq_nonneg (c a + 2), sq_nonneg (c a)]
    have h2 : -1 ≤ c a := by
      nlinarith [hcsq a, sq_nonneg (c a - 2), sq_nonneg (c a + 2), sq_nonneg (c a)]
    have h3 : d a ≤ 1 := by
      nlinarith [hdsq a, sq_nonneg (d a - 2), sq_nonneg (d a + 2), sq_nonneg (d a)]
    have h4 : -1 ≤ d a := by
      nlinarith [hdsq a, sq_nonneg (d a - 2), sq_nonneg (d a + 2), sq_nonneg (d a)]
    nlinarith [h1, h2, h3, h4]
  have hex : ∃ a ∈ c.support, c a * d a = 1 := by
    by_contra hcon
    push Not at hcon
    have hle : ∑ a ∈ c.support, c a * d a ≤ 0 := by
      apply Finset.sum_nonpos
      intro a ha
      have := hbdd a ha
      have := hcon a ha
      omega
    omega
  obtain ⟨a, ha, ha1⟩ := hex
  have hca : c a = 1 ∨ c a = -1 := by
    have h1 : c a ≤ 1 := by
      nlinarith [hcsq a, sq_nonneg (c a - 2), sq_nonneg (c a + 2), sq_nonneg (c a)]
    have h2 : -1 ≤ c a := by
      nlinarith [hcsq a, sq_nonneg (c a - 2), sq_nonneg (c a + 2), sq_nonneg (c a)]
    have h0 : c a ≠ 0 := by intro h; rw [h] at ha1; simp at ha1
    omega
  have hamem : a ∈ irreducibleCharacters K := hcsupp (Finset.mem_coe.mpr ha)
  refine ⟨(c a : ℂ) • a, ?_, ?_, ?_⟩
  · rcases hca with h | h
    · left; rw [h]; simpa using hamem
    · right; rw [h]; simpa using hamem
  · rw [ClassFunction.inner_smul_right, star_intCast]
    have hφa : ClassFunction.inner φ a = (c a : ℂ) := by
      rw [hcrepr]; exact inner_eq_coeff_of_repr ⟨a, hamem⟩ hcsupp
    rw [hφa]; rcases hca with h | h <;> rw [h] <;> norm_num
  · rw [ClassFunction.inner_smul_right, star_intCast]
    have hψa : ClassFunction.inner ψ a = (d a : ℂ) := by
      rw [hdrepr]; exact inner_eq_coeff_of_repr ⟨a, hamem⟩ hdsupp
    rw [hψa, ← Int.cast_mul, ha1]; norm_num

/-- **Disjointness for small norms.** Two virtual characters of norms in `{1,2}` with equal
degrees and orthogonal have no common irreducible constituent. -/
theorem disjointSmall {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {α β : ClassFunction K ℂ}
    (hα : α ∈ ZIrr K) (hβ : β ∈ ZIrr K)
    (hαn : ClassFunction.inner α α = 1 ∨ ClassFunction.inner α α = 2)
    (hβn : ClassFunction.inner β β = 1 ∨ ClassFunction.inner β β = 2)
    (hd : α 1 = β 1) (ho : ClassFunction.inner α β = 0) : DisjointCF α β := by
  intro χ
  rcases hαn with hα1 | hα2
  · rcases isPmIrr_of_mem_ZIrr_inner_self_eq_one hα hα1 with hαirr | hαirr
    · by_cases hχ : (χ : ClassFunction K ℂ) = α
      · right; rw [hχ, OddOrder.RepresentationTheory.inner_conj_symm, ho, star_zero]
      · left
        rw [irreducibleCharacter_inner_eq_ite (⟨α, hαirr⟩ : IrreducibleCharacter K) χ]
        exact ite_eq_right (fun hh => hχ (congrArg Subtype.val hh).symm)
    · by_cases hχ : (χ : ClassFunction K ℂ) = -α
      · right
        rw [hχ, ClassFunction.inner_neg_right, OddOrder.RepresentationTheory.inner_conj_symm, ho,
          star_zero, neg_zero]
      · left
        rw [show α = -(-α) from (neg_neg α).symm, ClassFunction.inner_neg_left]
        rw [irreducibleCharacter_inner_eq_ite (⟨-α, hαirr⟩ : IrreducibleCharacter K) χ]
        rw [ite_eq_right (fun hh => hχ (congrArg Subtype.val hh).symm), neg_zero]
  · rcases hβn with hβ1 | hβ2
    · rcases isPmIrr_of_mem_ZIrr_inner_self_eq_one hβ hβ1 with hβirr | hβirr
      · by_cases hχ : (χ : ClassFunction K ℂ) = β
        · left; rw [hχ, ho]
        · right
          rw [irreducibleCharacter_inner_eq_ite (⟨β, hβirr⟩ : IrreducibleCharacter K) χ]
          exact ite_eq_right (fun hh => hχ (congrArg Subtype.val hh).symm)
      · by_cases hχ : (χ : ClassFunction K ℂ) = -β
        · left
          rw [hχ, ClassFunction.inner_neg_right, ho, neg_zero]
        · right
          rw [show β = -(-β) from (neg_neg β).symm, ClassFunction.inner_neg_left]
          rw [irreducibleCharacter_inner_eq_ite (⟨-β, hβirr⟩ : IrreducibleCharacter K) χ]
          rw [ite_eq_right (fun hh => hχ (congrArg Subtype.val hh).symm), neg_zero]
    · exact remark15Disjoint hα hβ hα2 hβ2 hd ho χ

/-- Expansion of the squared norm of a sum: `‖u + v‖² = ‖u‖² + ⟨u,v⟩ + ⟨v,u⟩ + ‖v‖²`. -/
theorem inner_add_add {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    (u v : ClassFunction K ℂ) :
    ClassFunction.inner (u + v) (u + v) = ClassFunction.inner u u + ClassFunction.inner u v +
      ClassFunction.inner v u + ClassFunction.inner v v := by
  rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_add_right]
  ring

/-- Three distinct elements force the index type to have at least three elements. -/
theorem card_three_le {ι : Type} [Fintype ι] [DecidableEq ι] {i1 i2 i3 : ι}
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) : 3 ≤ Fintype.card ι := by
  have h3 : ({i1, i2, i3} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13, h23]
  calc (3:ℕ) = ({i1, i2, i3} : Finset ι).card := h3.symm
    _ ≤ Fintype.card ι := Finset.card_le_univ _

/-! ## The main theorem -/

/-- **P-3.** The abstract construction of Bender–Glauberman p. 206. -/
theorem s02_abstractCoherence : Work.BG.AbstractCoherenceProp := by
  intro K hG hFin hFt hInv ι hFι hDec i1 i2 i3 hi12 hi13 hi23 a ha h1 hcard D hZ hD1 hdeg hgram hfail
  classical
  have hi2i1 : i2 ≠ i1 := hi12.symm
  have hi3i1 : i3 ≠ i1 := hi13.symm
  have hnormD : ∀ i, i ≠ i1 → ClassFunction.inner (D i) (D i) = 1 + (a i : ℂ) := by
    intro i hi
    rw [hgram i i hi hi, if_pos rfl, h1]; norm_num
  have hgram_off : ∀ i k, i ≠ i1 → k ≠ i1 → i ≠ k →
      ClassFunction.inner (D i) (D k) = 1 := by
    intro i k hi hk hik
    rw [hgram i k hi hk, if_neg hik, add_zero, h1]; norm_num
  have hnorm23 : ∀ i, i ≠ i1 →
      ClassFunction.inner (D i) (D i) = 2 ∨ ClassFunction.inner (D i) (D i) = 3 := by
    intro i hi
    rw [hnormD i hi]
    rcases ha i with h | h <;> rw [h] <;> norm_num
  have hDnormN : ∀ i, i ≠ i1 →
      ClassFunction.inner (D i) (D i) = ((a i + 1 : ℕ) : ℂ) := by
    intro i hi
    rw [hnormD i hi]; push_cast; ring
  obtain ⟨g₁, hg1pm, hDi2g1, hDi3g1⟩ :=
    exists_common_constituent (hZ i2) (hZ i3) (hnorm23 i2 hi2i1) (hnorm23 i3 hi3i1)
      (hgram_off i2 i3 hi2i1 hi3i1 hi23)
  have hg1Z : g₁ ∈ ZIrr K := hg1pm.mem_ZIrr
  have hg1norm : ClassFunction.inner g₁ g₁ = 1 := hg1pm.inner_self
  -- ### The key claim
  have hall : ∀ i, i ≠ i1 → ClassFunction.inner (D i) g₁ = 1 := by
    by_cases hc : a i2 = 1 ∧ a i3 = 1
    · obtain ⟨hai2, hai3⟩ := hc
      set g₂ : ClassFunction K ℂ := g₁ - D i2 with hg₂def
      set g₃ : ClassFunction K ℂ := g₁ - D i3 with hg₃def
      have hD2norm : ClassFunction.inner (D i2) (D i2) = 2 := by
        rw [hnormD i2 hi2i1, hai2]; norm_num
      have hD3norm : ClassFunction.inner (D i3) (D i3) = 2 := by
        rw [hnormD i3 hi3i1, hai3]; norm_num
      have hg1D2 : ClassFunction.inner g₁ (D i2) = 1 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm, hDi2g1, star_one]
      have hg1D3 : ClassFunction.inner g₁ (D i3) = 1 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm, hDi3g1, star_one]
      have hg2norm : ClassFunction.inner g₂ g₂ = 1 := by
        rw [hg₂def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
          ClassFunction.inner_sub_right, hg1norm, hg1D2, hDi2g1, hD2norm]
        ring
      have hg3norm : ClassFunction.inner g₃ g₃ = 1 := by
        rw [hg₃def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
          ClassFunction.inner_sub_right, hg1norm, hg1D3, hDi3g1, hD3norm]
        ring
      have hg2pm : IsPmIrr g₂ :=
        isPmIrr_of_mem_ZIrr_inner_self_eq_one (Submodule.sub_mem _ hg1Z (hZ i2)) hg2norm
      have hg3pm : IsPmIrr g₃ :=
        isPmIrr_of_mem_ZIrr_inner_self_eq_one (Submodule.sub_mem _ hg1Z (hZ i3)) hg3norm
      have hg2Z : g₂ ∈ ZIrr K := Submodule.sub_mem _ hg1Z (hZ i2)
      have hg3Z : g₃ ∈ ZIrr K := Submodule.sub_mem _ hg1Z (hZ i3)
      have hg1g2 : ClassFunction.inner g₁ g₂ = 0 := by
        rw [hg₂def, ClassFunction.inner_sub_right, hg1norm, hg1D2]; ring
      have hg1g3 : ClassFunction.inner g₁ g₃ = 0 := by
        rw [hg₃def, ClassFunction.inner_sub_right, hg1norm, hg1D3]; ring
      have hg2g3 : ClassFunction.inner g₂ g₃ = 0 := by
        rw [hg₂def, hg₃def, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
          ClassFunction.inner_sub_right, hg1norm, hg1D3, hDi2g1,
          hgram_off i2 i3 hi2i1 hi3i1 hi23]
        ring
      have hg3g2 : ClassFunction.inner g₃ g₂ = 0 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm, hg2g3, star_zero]
      have hg2deg : g₂ 1 = g₁ 1 := by
        rw [hg₂def, ClassFunction.sub_apply, hdeg i2, sub_zero]
      have hg3deg : g₃ 1 = g₁ 1 := by
        rw [hg₃def, ClassFunction.sub_apply, hdeg i3, sub_zero]
      -- ### Characterization of a "bad" index
      have hbad_char : ∀ j, j ≠ i1 → ClassFunction.inner (D j) g₁ ≠ 1 →
          IsPmIrr (D j + g₂ + g₃) ∧ (a j = 2) ∧
          ClassFunction.inner (D j) g₁ = 0 ∧
          ClassFunction.inner (D j) g₂ = -1 ∧
          ClassFunction.inner (D j) g₃ = -1 ∧
          ClassFunction.inner g₁ (D j + g₂ + g₃) = 0 ∧
          ClassFunction.inner g₂ (D j + g₂ + g₃) = 0 ∧
          ClassFunction.inner g₃ (D j + g₂ + g₃) = 0 := by
        intro j hj hbj
        have hj2 : j ≠ i2 := by intro h; exact hbj (by rw [h]; exact hDi2g1)
        have hj3 : j ≠ i3 := by intro h; exact hbj (by rw [h]; exact hDi3g1)
        have hDj2 : ClassFunction.inner (D j) (D i2) = 1 := hgram_off j i2 hj hi2i1 hj2
        have hDj3 : ClassFunction.inner (D j) (D i3) = 1 := hgram_off j i3 hj hi3i1 hj3
        obtain ⟨t, ht, htle⟩ := inner_eq_int_and_sq_le (hZ j) (a j + 1) (hDnormN j hj) hg1pm
        obtain ⟨s, hs, hsle⟩ := inner_eq_int_and_sq_le (hZ j) (a j + 1) (hDnormN j hj) hg2pm
        have hst : s = t - 1 := by
          have h := hs
          rw [hg₂def, ClassFunction.inner_sub_right, hDj2, ht] at h
          have h2 : (s : ℂ) = ((t - 1 : ℤ) : ℂ) := by push_cast; exact h.symm
          exact_mod_cast h2
        have hNle : ((a j + 1 : ℕ) : ℤ) ≤ 3 := by
          rcases ha j with h | h <;> rw [h] <;> norm_num
        have ht3 : t ^ 2 ≤ 3 := le_trans htle hNle
        have hs3 : s ^ 2 ≤ 3 := le_trans hsle hNle
        have htmem : t = -1 ∨ t = 0 ∨ t = 1 := by
          have h1 : t ≤ 1 := by
            nlinarith [ht3, sq_nonneg (t - 2), sq_nonneg (t + 2), sq_nonneg t]
          have h2 : -1 ≤ t := by
            nlinarith [ht3, sq_nonneg (t - 2), sq_nonneg (t + 2), sq_nonneg t]
          omega
        have hsmem : s = -1 ∨ s = 0 ∨ s = 1 := by
          have h1 : s ≤ 1 := by
            nlinarith [hs3, sq_nonneg (s - 2), sq_nonneg (s + 2), sq_nonneg s]
          have h2 : -1 ≤ s := by
            nlinarith [hs3, sq_nonneg (s - 2), sq_nonneg (s + 2), sq_nonneg s]
          omega
        have htne : t ≠ 1 := by intro h; exact hbj (by rw [ht, h]; norm_num)
        have ht0 : t = 0 := by
          rcases htmem with h | h | h
          · exfalso
            have hs2 : s = -2 := by rw [hst, h]; ring
            rcases hsmem with hh | hh | hh <;> omega
          · exact h
          · exact absurd h htne
        have hs1 : s = -1 := by rw [hst, ht0]; ring
        have hDjg1 : ClassFunction.inner (D j) g₁ = 0 := by rw [ht, ht0]; norm_num
        have hDjg2 : ClassFunction.inner (D j) g₂ = -1 := by rw [hs, hs1]; norm_num
        have hDjg3 : ClassFunction.inner (D j) g₃ = -1 := by
          rw [hg₃def, ClassFunction.inner_sub_right, hDjg1, hDj3]; norm_num
        have hg1Dj : ClassFunction.inner g₁ (D j) = 0 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm (D j) g₁, hDjg1, star_zero]
        have hg2Dj : ClassFunction.inner g₂ (D j) = -1 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm (D j) g₂, hDjg2]; norm_num
        have hg3Dj : ClassFunction.inner g₃ (D j) = -1 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm (D j) g₃, hDjg3]; norm_num
        have hD'Z : D j + g₂ + g₃ ∈ ZIrr K :=
          Submodule.add_mem _ (Submodule.add_mem _ (hZ j) hg2Z) hg3Z
        have hD'norm : ClassFunction.inner (D j + g₂ + g₃) (D j + g₂ + g₃)
            = (a j : ℂ) - 1 := by
          simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
          rw [hnormD j hj, hDjg2, hDjg3, hg2Dj, hg2norm, hg2g3, hg3Dj, hg3g2, hg3norm]
          ring
        have hg1D' : ClassFunction.inner g₁ (D j + g₂ + g₃) = 0 := by
          simp only [ClassFunction.inner_add_right]
          rw [hg1Dj, hg1g2, hg1g3]; ring
        have hg2D' : ClassFunction.inner g₂ (D j + g₂ + g₃) = 0 := by
          simp only [ClassFunction.inner_add_right]
          rw [hg2Dj, hg2norm, hg2g3]; ring
        have hg3D' : ClassFunction.inner g₃ (D j + g₂ + g₃) = 0 := by
          simp only [ClassFunction.inner_add_right]
          rw [hg3Dj, hg3g2, hg3norm]; ring
        rcases ha j with haj | haj
        · exfalso
          have h0 : ClassFunction.inner (D j + g₂ + g₃) (D j + g₂ + g₃) = 0 := by
            rw [hD'norm, haj]; norm_num
          have hD'zero : D j + g₂ + g₃ = 0 :=
            eq_zero_of_inner_self_re_eq_zero (by rw [h0]; rfl)
          have hdegeval : (D j + g₂ + g₃) 1 = 0 := by rw [hD'zero]; rfl
          simp only [ClassFunction.add_apply] at hdegeval
          rw [hdeg j, hg2deg, hg3deg] at hdegeval
          have hx : g₁ 1 = 0 := by
            have h2 : (2 : ℂ) * (g₁ 1) = 0 := by linear_combination hdegeval
            exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
          exact hg1pm.apply_one_ne_zero hx
        · exact ⟨isPmIrr_of_mem_ZIrr_inner_self_eq_one hD'Z (by rw [hD'norm, haj]; norm_num),
            haj, hDjg1, hDjg2, hDjg3, hg1D', hg2D', hg3D'⟩
      -- ### The bad index is unique
      have hbad_unique : ∀ j j', j ≠ i1 → j' ≠ i1 →
          ClassFunction.inner (D j) g₁ ≠ 1 → ClassFunction.inner (D j') g₁ ≠ 1 → j = j' := by
        intro j j' hj hj' hbj hbj'
        by_contra hne
        obtain ⟨hpj, haj, hjg1, hjg2, hjg3, hjg1o, hjg2o, hjg3o⟩ := hbad_char j hj hbj
        obtain ⟨hpj', haj', hj'g1, hj'g2, hj'g3, hj'g1o, hj'g2o, hj'g3o⟩ := hbad_char j' hj' hbj'
        have hjj' : ClassFunction.inner (D j) (D j') = 1 := hgram_off j j' hj hj' hne
        have hmix : ClassFunction.inner (D j + g₂ + g₃) (D j' + g₂ + g₃) = -1 := by
          simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
          have hg2Dj' : ClassFunction.inner g₂ (D j') = -1 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm (D j') g₂, hj'g2]; norm_num
          have hg3Dj' : ClassFunction.inner g₃ (D j') = -1 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm (D j') g₃, hj'g3]; norm_num
          rw [hjj', hjg2, hjg3, hg2Dj', hg2norm, hg2g3, hg3Dj', hg3g2, hg3norm]
          ring
        have hmix' : ClassFunction.inner (D j' + g₂ + g₃) (D j + g₂ + g₃) = -1 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm (D j + g₂ + g₃)
            (D j' + g₂ + g₃), hmix]; norm_num
        have hsum0 : ClassFunction.inner ((D j + g₂ + g₃) + (D j' + g₂ + g₃))
            ((D j + g₂ + g₃) + (D j' + g₂ + g₃)) = 0 := by
          rw [inner_add_add, hpj.inner_self, hmix, hmix', hpj'.inner_self]
          ring
        have hzero : (D j + g₂ + g₃) + (D j' + g₂ + g₃) = 0 :=
          eq_zero_of_inner_self_re_eq_zero (by rw [hsum0]; rfl)
        have heval : ((D j + g₂ + g₃) + (D j' + g₂ + g₃)) 1 = 0 := by rw [hzero]; rfl
        simp only [ClassFunction.add_apply] at heval
        rw [hdeg j, hdeg j', hg2deg, hg3deg] at heval
        have hx : g₁ 1 = 0 := by
          have h2 : (4 : ℂ) * (g₁ 1) = 0 := by linear_combination heval
          exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
        exact hg1pm.apply_one_ne_zero hx
      intro i hi
      by_contra hbad
      obtain ⟨hD'pm, haj, hDig1, hDig2, hDig3, hg1D', hg2D', hg3D'⟩ := hbad_char i hi hbad
      have hnei2 : i ≠ i2 := by intro h; exact hbad (by rw [h]; exact hDi2g1)
      have hnei3 : i ≠ i3 := by intro h; exact hbad (by rw [h]; exact hDi3g1)
      exact (hfail i hi hnei2 hnei3 haj)
        ⟨g₁, g₂, g₃, D i + g₂ + g₃, hg1pm, hg2pm, hg3pm, hD'pm,
          by rw [hg₂def]; abel,
          by rw [hg₃def]; abel,
          by abel,
          hg1g2, hg1g3, hg2g3, hg1D', hg2D', hg3D',
          fun i' hi' hnei' => by
            by_contra hbadi'
            exact hnei' (hbad_unique i' i hi' hi hbadi' hbad)⟩
    · have hcard_le : Fintype.card ι ≤ 3 := by
        by_contra hcon
        exact hc (hcard (by omega))
      have hcard_ge : 3 ≤ Fintype.card ι := card_three_le hi12 hi13 hi23
      have hcard_eq : Fintype.card ι = 3 := le_antisymm hcard_le hcard_ge
      have hset : ({i1, i2, i3} : Finset ι) = Finset.univ := by
        apply Finset.eq_univ_of_card
        have h3 : ({i1, i2, i3} : Finset ι).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hi23]
          · simp [hi12, hi13, hi23]
        rw [h3, hcard_eq]
      intro i hi
      have hmem : i ∈ ({i1, i2, i3} : Finset ι) := by rw [hset]; exact Finset.mem_univ i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact absurd h hi
      · rw [h]; exact hDi2g1
      · rw [h]; exact hDi3g1
  -- ### Assembly
  have hgnorm : ∀ k, ClassFunction.inner (g₁ - D k) (g₁ - D k) = (a k : ℂ) := by
    intro k
    by_cases hk : k = i1
    · subst hk; rw [hD1, sub_zero, hg1norm, h1]; norm_num
    · rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hg1norm]
      have hg1Dk : ClassFunction.inner g₁ (D k) = 1 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm, hall k hk, star_one]
      rw [hg1Dk, hall k hk, hnormD k hk]; ring
  have hgdeg : ∀ k, (g₁ - D k) 1 = g₁ 1 := by
    intro k; rw [ClassFunction.sub_apply, hdeg k, sub_zero]
  have hnormdisj : ∀ i, ClassFunction.inner (g₁ - D i) (g₁ - D i) = 1 ∨
      ClassFunction.inner (g₁ - D i) (g₁ - D i) = 2 := by
    intro i
    rcases ha i with h | h
    · left; rw [hgnorm i, h]; norm_num
    · right; rw [hgnorm i, h]; norm_num
  have hgorth : ∀ i k, i ≠ k → ClassFunction.inner (g₁ - D i) (g₁ - D k) = 0 := by
    intro i k hik
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hg1norm]
    rcases eq_or_ne i i1 with hi | hi
    · rw [hi, hD1]
      simp only [ClassFunction.inner_zero_left, ClassFunction.inner_zero_right, zero_sub,
        sub_zero]
      have hk : k ≠ i1 := fun h => hik (hi.trans h.symm)
      have hg1Dk : ClassFunction.inner g₁ (D k) = 1 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm, hall k hk, star_one]
      rw [hg1Dk]; ring
    · rcases eq_or_ne k i1 with hk | hk
      · rw [hk, hD1]
        simp only [ClassFunction.inner_zero_left, ClassFunction.inner_zero_right, zero_sub,
          sub_zero]
        rw [hall i hi]; ring
      · have hg1Dk : ClassFunction.inner g₁ (D k) = 1 := by
          rw [OddOrder.RepresentationTheory.inner_conj_symm, hall k hk, star_one]
        rw [hall i hi, hg1Dk, hgram_off i k hi hk hik]; ring
  refine ⟨fun i => g₁ - D i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨Submodule.sub_mem _ hg1Z (hZ i), hgnorm i⟩
  · intro i
    dsimp only
    rw [hD1, sub_zero]; abel
  · intro i k hik
    dsimp only
    exact disjointSmall (Submodule.sub_mem _ hg1Z (hZ i)) (Submodule.sub_mem _ hg1Z (hZ k))
      (hnormdisj i) (hnormdisj k) (by rw [hgdeg i, hgdeg k]) (hgorth i k hik)
  · dsimp only
    rw [hD1, sub_zero]
    exact hg1pm

end Work.BG
