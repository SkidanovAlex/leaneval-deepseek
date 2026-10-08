import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.remark15Disjoint
import Submission.Work.BG.s02_commonSupportSingleton

namespace Work.BG

open OddOrder.RepresentationTheory

variable {K : Type*} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]

/-- Evaluation of a finite linear combination of class functions. -/
private theorem sum_smul_apply {ι : Type*} (s : Finset ι) (F : ι → ClassFunction K ℂ) (v : ι → ℂ)
    (g : K) : (∑ i ∈ s, v i • F i) g = ∑ i ∈ s, v i * (F i) g := by
  rw [ClassFunction.sum_apply]
  exact Finset.sum_congr rfl fun i _ => ClassFunction.smul_apply (v i) (F i) g

/-- Mixed Parseval: `⟨Σ c_a • a, Σ d_b • b⟩ = Σ c_a d_a` for supports in `Irr`. -/
private theorem inner_repr_repr (c d : ClassFunction K ℂ →₀ ℤ)
    (hc : ↑c.support ⊆ irreducibleCharacters K) (hd : ↑d.support ⊆ irreducibleCharacters K) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (∑ b ∈ d.support, (d b : ℂ) • b)
      = ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) := by
  classical
  rw [inner_sum_left]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [ClassFunction.inner_smul_left, inner_sum_right]
  rw [Finset.sum_congr rfl (fun i _ => ClassFunction.inner_smul_right ((d i : ℤ) : ℂ) a i)]
  simp only [star_intCast]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [irr_cf_inner (hc (Finset.mem_coe.mpr ha)) (hd (Finset.mem_coe.mpr hx))])]
  rw [Finset.sum_congr rfl (fun x _ => by rw [mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq]
  by_cases hmem : a ∈ d.support
  · rw [ite_eq_left hmem]
  · rw [ite_eq_right hmem, Finsupp.notMem_support_iff.mp hmem]
    ring

/-- The value of an irreducible character at `1` is nonzero. -/
private theorem irr_apply_one_ne_zero {φ : ClassFunction K ℂ} (h : IsIrreducibleCharacter φ) :
    φ 1 ≠ 0 := by
  obtain ⟨n, hn0, hn, -⟩ := h.exists_natDegree_charValue_one_dvd_card
  rw [hn]
  exact fun hzero => hn0.ne' (Nat.cast_eq_zero.mp hzero)

/-- Integer coefficients of a finite vector with `Σ c a ^ 2 ≤ 3` and `c a ≠ 0` on the support
are all `±1`, and the support has at most `3` elements. -/
private theorem coeff_sign_of_sum_sq_le_three {α : Type*} [DecidableEq α] {s : Finset α} {c : α → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hle : ∑ a ∈ s, c a ^ 2 ≤ 3) :
    (∀ a ∈ s, c a = 1 ∨ c a = -1) ∧ s.card ≤ 3 := by
  have hle' : ∀ a ∈ s, c a ^ 2 ≤ 3 := fun a ha =>
    le_trans (Finset.single_le_sum (fun b _ => sq_nonneg (c b)) ha) hle
  have hsign : ∀ a ∈ s, c a = 1 ∨ c a = -1 := fun a ha => by
    have h1 : |c a| ≤ 1 := by
      by_contra h
      rw [not_le] at h
      have h2 : (2 : ℤ) ≤ |c a| := by omega
      have h4 : (4 : ℤ) ≤ c a ^ 2 := by
        rw [← sq_abs (c a)]
        nlinarith [h2]
      have := hle' a ha
      omega
    have h0 := hne a ha
    rcases abs_le.mp h1 with ⟨hlo, hhi⟩
    omega
  refine ⟨hsign, ?_⟩
  have hsum1 : ∑ a ∈ s, (1 : ℤ) ≤ ∑ a ∈ s, c a ^ 2 :=
    Finset.sum_le_sum fun a ha => by
      rcases hsign a ha with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum1
  have h3 : (s.card : ℤ) ≤ 3 := le_trans hsum1 hle
  omega

theorem s02_commonConstituent : Work.BG.CommonConstituentProp := by
  intro K hGrp hFin hFt hInv δ ε hδZ hεZ hδ1 hε1 hδnorm hεnorm hδε
  classical
  obtain ⟨c, hcsupp, hcrepr, hcnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hδZ
  obtain ⟨d, hdsupp, hdrepr, hdnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hεZ
  -- ## integer norm sums
  have hcsum : ∑ a ∈ c.support, c a ^ 2 = 2 ∨ ∑ a ∈ c.support, c a ^ 2 = 3 := by
    have h2 : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 2 ∨ ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 3 := by
      rcases hδnorm with h | h
      · left; rw [← hcnorm]; exact h
      · right; rw [← hcnorm]; exact h
    have h3 : (((∑ a ∈ c.support, c a ^ 2 : ℤ)) : ℂ) = (2 : ℂ) ∨
        (((∑ a ∈ c.support, c a ^ 2 : ℤ)) : ℂ) = (3 : ℂ) := by
      push_cast
      exact h2
    rcases h3 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hdsum : ∑ a ∈ d.support, d a ^ 2 = 2 ∨ ∑ a ∈ d.support, d a ^ 2 = 3 := by
    have h2 : ∑ a ∈ d.support, (d a : ℂ) ^ 2 = 2 ∨ ∑ a ∈ d.support, (d a : ℂ) ^ 2 = 3 := by
      rcases hεnorm with h | h
      · left; rw [← hdnorm]; exact h
      · right; rw [← hdnorm]; exact h
    have h3 : (((∑ a ∈ d.support, d a ^ 2 : ℤ)) : ℂ) = (2 : ℂ) ∨
        (((∑ a ∈ d.support, d a ^ 2 : ℤ)) : ℂ) = (3 : ℂ) := by
      push_cast
      exact h2
    rcases h3 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hcne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hdne : ∀ a ∈ d.support, d a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  have hc2' : ∑ a ∈ c.support, c a ^ 2 ≤ 3 := by
    rcases hcsum with h | h <;> rw [h] <;> norm_num
  have hd2' : ∑ a ∈ d.support, d a ^ 2 ≤ 3 := by
    rcases hdsum with h | h <;> rw [h] <;> norm_num
  obtain ⟨hcsign, -⟩ := coeff_sign_of_sum_sq_le_three (s := c.support) (c := c) hcne hc2'
  obtain ⟨hdsign, -⟩ := coeff_sign_of_sum_sq_le_three (s := d.support) (c := d) hdne hd2'
  -- ## mixed Parseval and the common-support sum
  have hmixed : ClassFunction.inner δ ε = ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) := by
    rw [hcrepr, hdrepr]
    exact inner_repr_repr c d hcsupp hdsupp
  have hsum1C : ∑ a ∈ c.support, (c a : ℂ) * (d a : ℂ) = 1 := by
    rw [← hmixed]; exact hδε
  have hsum1 : ∑ a ∈ c.support, c a * d a = 1 := by
    have hz : (((∑ a ∈ c.support, c a * d a : ℤ)) : ℂ) = (1 : ℂ) := by
      push_cast
      exact hsum1C
    exact_mod_cast hz
  have hsumS : ∑ a ∈ c.support ∩ d.support, c a * d a = 1 := by
    have hzero : ∀ x ∈ c.support, x ∉ c.support ∩ d.support → c x * d x = 0 := by
      intro x hx hxn
      have hxd : d x = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro hxm
        exact hxn (Finset.mem_inter.mpr ⟨hx, hxm⟩)
      rw [hxd, mul_zero]
    rw [Finset.sum_subset Finset.inter_subset_left hzero]
    exact hsum1
  -- ## degree conditions
  have hcdeg : ∑ a ∈ c.support, (c a : ℂ) * (a 1) = 0 := by
    have hev : (∑ a ∈ c.support, (c a : ℂ) • a) (1 : K)
        = ∑ a ∈ c.support, (c a : ℂ) * (a 1) :=
      sum_smul_apply c.support (fun a => a) (fun a => (c a : ℂ)) 1
    rw [← hev, ← hcrepr]
    exact hδ1
  have hddeg : ∑ a ∈ d.support, (d a : ℂ) * (a 1) = 0 := by
    have hev : (∑ a ∈ d.support, (d a : ℂ) • a) (1 : K)
        = ∑ a ∈ d.support, (d a : ℂ) * (a 1) :=
      sum_smul_apply d.support (fun a => a) (fun a => (d a : ℂ)) 1
    rw [← hev, ← hdrepr]
    exact hε1
  have hwmem : ∀ a ∈ c.support ∪ d.support, (a : ClassFunction K ℂ) 1 ≠ 0 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact irr_apply_one_ne_zero (hcsupp (Finset.mem_coe.mpr ha))
    · exact irr_apply_one_ne_zero (hdsupp (Finset.mem_coe.mpr ha))
  -- ## the combinatorial core
  obtain ⟨a₀, ha₀A, ha₀B, hSsing, hprod⟩ :=
    s02_commonSupportSingleton c.support d.support c d (fun a => a 1)
      hcne hdne hc2' hd2' hcdeg hddeg hwmem hsumS
  have ha₀irr : a₀ ∈ irreducibleCharacters K := hcsupp (Finset.mem_coe.mpr ha₀A)
  have hcoeffδ : ∀ x : ClassFunction K ℂ, x ∈ irreducibleCharacters K →
      ClassFunction.inner δ x = (c x : ℂ) := by
    intro x hx
    rw [hcrepr]
    simpa using inner_eq_coeff_of_repr (⟨x, hx⟩ : IrreducibleCharacter K) hcsupp
  have hcoeffε : ∀ x : ClassFunction K ℂ, x ∈ irreducibleCharacters K →
      ClassFunction.inner ε x = (d x : ℂ) := by
    intro x hx
    rw [hdrepr]
    simpa using inner_eq_coeff_of_repr (⟨x, hx⟩ : IrreducibleCharacter K) hdsupp
  refine ⟨(c a₀ : ℂ) • a₀, ?_, ?_, ?_, ?_, ?_⟩
  · -- `IsPmIrr`
    rcases hcsign a₀ ha₀A with hc1 | hcm1
    · left
      rw [hc1, Int.cast_one, one_smul]
      exact ha₀irr
    · right
      rw [hcm1, Int.cast_neg, Int.cast_one, neg_one_smul]
      simpa using ha₀irr
  · -- `⟨δ, χ⟩ = 1`
    rw [ClassFunction.inner_smul_right, hcoeffδ a₀ ha₀irr, star_intCast]
    rcases hcsign a₀ ha₀A with h | h <;> rw [h] <;> norm_num
  · -- `⟨ε, χ⟩ = 1`
    rw [ClassFunction.inner_smul_right, hcoeffε a₀ ha₀irr, star_intCast, ← Int.cast_mul, hprod,
      Int.cast_one]
  · -- disjointness of the two remainders
    intro φ
    have hchi : ClassFunction.inner ((c a₀ : ℂ) • a₀) (φ : ClassFunction K ℂ)
        = (c a₀ : ℂ) * (if a₀ = (φ : ClassFunction K ℂ) then 1 else 0) := by
      rw [ClassFunction.inner_smul_left, irr_cf_inner ha₀irr φ.mem_irreducibleCharacters]
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_left, hchi]
    by_cases hφ : a₀ = (φ : ClassFunction K ℂ)
    · left
      have h1 : ClassFunction.inner δ (φ : ClassFunction K ℂ) = (c a₀ : ℂ) := by
        have := hcoeffδ (φ : ClassFunction K ℂ) φ.mem_irreducibleCharacters
        rw [← hφ] at this ⊢
        exact this
      rw [h1, if_pos hφ, mul_one, sub_self]
    · by_cases hcφ : c (φ : ClassFunction K ℂ) = 0
      · left
        have h1 : ClassFunction.inner δ (φ : ClassFunction K ℂ) = 0 := by
          rw [hcoeffδ (φ : ClassFunction K ℂ) φ.mem_irreducibleCharacters, hcφ, Int.cast_zero]
        rw [h1, if_neg hφ, mul_zero, sub_zero]
      · right
        have hmemφ : (φ : ClassFunction K ℂ) ∈ c.support := Finsupp.mem_support_iff.mpr hcφ
        have hnotd : (φ : ClassFunction K ℂ) ∉ d.support := by
          intro hmd
          have hmem : (φ : ClassFunction K ℂ) ∈ c.support ∩ d.support :=
            Finset.mem_inter.mpr ⟨hmemφ, hmd⟩
          rw [hSsing] at hmem
          exact hφ (Finset.mem_singleton.mp hmem).symm
        have hd0 : d (φ : ClassFunction K ℂ) = 0 := Finsupp.notMem_support_iff.mp hnotd
        have h1 : ClassFunction.inner ε (φ : ClassFunction K ℂ) = 0 := by
          rw [hcoeffε (φ : ClassFunction K ℂ) φ.mem_irreducibleCharacters, hd0, Int.cast_zero]
        rw [h1, if_neg hφ, mul_zero, sub_zero]
  · -- uniqueness
    intro χ' hpm' hχ'1 hχ'2
    rcases hpm' with hirr | hirr
    · have hcχ' : c χ' = 1 := by
        have h : ((c χ' : ℤ) : ℂ) = 1 := by
          rw [← hcoeffδ χ' hirr]; exact hχ'1
        exact_mod_cast h
      have hdχ' : d χ' = 1 := by
        have h : ((d χ' : ℤ) : ℂ) = 1 := by
          rw [← hcoeffε χ' hirr]; exact hχ'2
        exact_mod_cast h
      have hmem : χ' ∈ c.support ∩ d.support :=
        Finset.mem_inter.mpr
          ⟨Finsupp.mem_support_iff.mpr (by simp [hcχ']),
           Finsupp.mem_support_iff.mpr (by simp [hdχ'])⟩
      rw [hSsing] at hmem
      have hχ'a₀ : χ' = a₀ := Finset.mem_singleton.mp hmem
      rw [hχ'a₀]
      have hca : c a₀ = 1 := by rw [← hχ'a₀]; exact hcχ'
      rw [hca, Int.cast_one, one_smul]
    · have hcψ : c (-χ') = -1 := by
        have h : ((c (-χ') : ℤ) : ℂ) = -1 := by
          have hψ : ClassFunction.inner δ (-χ') = -1 := by
            rw [ClassFunction.inner_neg_right, hχ'1]
          rw [← hcoeffδ (-χ') hirr]; exact hψ
        exact_mod_cast h
      have hdψ : d (-χ') = -1 := by
        have h : ((d (-χ') : ℤ) : ℂ) = -1 := by
          have hψ : ClassFunction.inner ε (-χ') = -1 := by
            rw [ClassFunction.inner_neg_right, hχ'2]
          rw [← hcoeffε (-χ') hirr]; exact hψ
        exact_mod_cast h
      have hmem : (-χ') ∈ c.support ∩ d.support :=
        Finset.mem_inter.mpr
          ⟨Finsupp.mem_support_iff.mpr (by simp [hcψ]),
           Finsupp.mem_support_iff.mpr (by simp [hdψ])⟩
      rw [hSsing] at hmem
      have hψa₀ : -χ' = a₀ := Finset.mem_singleton.mp hmem
      have hca : c a₀ = -1 := by rw [← hψa₀]; exact hcψ
      rw [hca, Int.cast_neg, Int.cast_one, neg_one_smul, ← hψa₀, neg_neg]

end Work.BG
