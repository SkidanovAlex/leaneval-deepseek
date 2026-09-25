import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.poly_weight_cap_block
import Submission.Work.BourgainPlan.Maximal.polyActIdx_card_le_one

/-!
# The block symbol is uniformly small

The crude scales of the per-block maximal estimate are controlled by the pointwise bound
`‖polyModelQBlock P m (2^k) θ‖ ≤ B · 2^{−mσ}`: on each dyadic block at most one arc is active
(uniqueness of the major-arc representation), and the active complete sum decays like `2^{−mσ}`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-! ## The partial-block expansion -/

/-- The partial-block expansion of the `m`-th model block at scale `k` (valid for `4m ≤ k`). -/
theorem star_polyModelQBlock_eq_sum (P : Polynomial ℤ) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    starRingEnd ℂ (polyModelQBlock P m (2^k) θ)
      = ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArc P q a l k θ) := by
  unfold polyModelQBlock
  rw [blockQ_eq_filter_le m k hk, map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [poly_majorArcBlock_two_pow_eq_sum, map_sum]
  have hstep : ∀ a : ℕ,
      starRingEnd ℂ (∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          (if Nat.gcd a q = 1 then polyModelTermArc P q a l k θ else 0))
        = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            starRingEnd ℂ (polyModelTermArc P q a l k θ) else 0) := by
    intro a
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l _ => conj_ite_zero _ (polyModelTermArc P q a l k θ))]
    exact sum_ite_gcd_eq' a q _ (fun l => starRingEnd ℂ (polyModelTermArc P q a l k θ))
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_filter]

/-- The active-index bound for the model block. -/
theorem norm_star_polyModelQBlock_le_actIdx (P : Polynomial ℤ) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    ‖starRingEnd ℂ (polyModelQBlock P m (2^k) θ)‖
      ≤ ∑ p ∈ polyActIdx P m k θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ := by
  rw [star_polyModelQBlock_eq_sum P hk θ]
  set Q : ℕ := Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) with hQdef
  have h1 : ‖∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff, starRingEnd ℂ (polyModelTermArc P q a l k θ)‖
      ≤ ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
              then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun q hq => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a ha => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l hl => ?_))
    rw [Complex.norm_conj]
    by_cases harc : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
    · rw [if_pos harc]
      unfold polyModelTermArc
      rw [if_pos harc]
      unfold polyModelTermPre
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_polyProfile_le_one P _ _)
    · rw [if_neg harc, polyModelTermArc_eq_zero_of_not_act P q a l θ harc, norm_zero]
  have h2 : ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
              then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0)
      ≤ ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
              then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q hq hnot => ?_)
    positivity
  have h3 : (∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
              then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0))
      = ∑ p ∈ polyActIdx P m k θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ := by
    rw [← sum_blockPair m (F := fun i : ℕ × ℕ => ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
        (if |(P.leadingCoeff:ℝ)*θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ polyArcRad P k
          then ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ else 0))]
    rw [← Finset.sum_product (blockPair m) (Finset.Icc (-1:ℤ) P.leadingCoeff)
      (fun p : (ℕ × ℕ) × ℤ =>
        (if |(P.leadingCoeff:ℝ)*θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ polyArcRad P k
          then ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ else 0))]
    rw [polyActIdx_eq_filter, polyAllIdx, ← Finset.sum_filter]
  linarith [h1, h2, h3]

/-! ## The weight cap on the `l`-window `Icc (-1) c` -/

/-- The weight cap, in the form needed on the `l`-window `Icc (-1) c` (note the terminal value
`l = c`, whose weight is brought back to `s = 0` by the modulus shift). -/
lemma polyWeight_cap_Icc (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) →
      Nat.gcd a q = 1 → l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P) := by
  obtain ⟨A, hApos, hA⟩ := poly_weight_cap_block P hc hd
  refine ⟨A, hApos, fun m q a l hm1 hm2 hg hl => ?_⟩
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  have hc0 : 0 ≤ P.leadingCoeff := le_of_lt hc
  have hcc : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff := Int.toNat_of_nonneg hc0
  have hcN : 1 ≤ P.leadingCoeff.toNat := by omega
  rcases eq_or_lt_of_le hl2 with hlc | hlt
  · -- the terminal value `l = c`: shift by one modulus `q * c`
    have hkey : a + l * q
        = (a + ((0 : ℕ) : ℤ) * q) + (1 : ℤ) * ((q * P.leadingCoeff.toNat : ℕ) : ℤ) := by
      rw [hlc]
      push_cast [hcc]
      ring
    rw [hkey, polyWeight_add_modulus_mul]
    exact hA m q a 0 hm1 hm2 hg (by omega)
  · rcases lt_or_ge l 0 with hln | hl0
    · -- `l = -1` (the only negative value in the window): shift by `-1` modulus
      have hl_eq : l = -1 := by omega
      have hkey : a + l * q
          = (a + (((P.leadingCoeff.toNat - 1 : ℕ)) : ℤ) * q)
            + (-1 : ℤ) * ((q * P.leadingCoeff.toNat : ℕ) : ℤ) := by
        rw [hl_eq]
        push_cast [hcc, Nat.cast_sub hcN]
        ring
      rw [hkey, polyWeight_add_modulus_mul]
      exact hA m q a (P.leadingCoeff.toNat - 1) hm1 hm2 hg (by omega)
    · -- `0 ≤ l < c`: use the value `l` itself
      have hkey : a + l * q = (a + (((l.toNat : ℕ)) : ℤ) * q) := by
        rw [Int.toNat_of_nonneg hl0]
      rw [hkey]
      refine hA m q a l.toNat hm1 hm2 hg ?_
      have h1 : (l.toNat : ℤ) = l := Int.toNat_of_nonneg hl0
      have h2 : (l.toNat : ℤ) < (P.leadingCoeff.toNat : ℤ) := by rw [h1, hcc]; exact hlt
      exact_mod_cast h2

/-! ## Small blocks have few active indices -/

/-- For `m ≤ 1` the `m`-th block has at most `16 * (c + 2)` active indices. -/
lemma polyActIdx_card_le_small (P : Polynomial ℤ) (hc : 0 ≤ P.leadingCoeff) {m k : ℕ}
    (hm : m ≤ 1) (θ : ℝ) :
    (polyActIdx P m k θ).card ≤ 16 * (P.leadingCoeff.toNat + 2) := by
  have hsub : polyActIdx P m k θ ⊆ (blockPair m) ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff := by
    intro p hp
    rw [mem_polyActIdx, mem_polyAllIdx] at hp
    rw [Finset.mem_product]
    exact hp.1
  have hbp : (blockPair m).card ≤ 16 := by
    have hsub2 : blockPair m ⊆ (Finset.range 4) ×ˢ (Finset.range 4) := by
      intro p hp
      obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      have h2' : p.1 < 4 := by
        calc p.1 < 2^(m+1) := h2
          _ ≤ 2^2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      exact ⟨by omega, by omega⟩
    calc (blockPair m).card ≤ ((Finset.range 4) ×ˢ (Finset.range 4)).card := Finset.card_le_card hsub2
      _ = 16 := by simp
  have hIcc : (Finset.Icc (-1:ℤ) P.leadingCoeff).card ≤ P.leadingCoeff.toNat + 2 := by
    rw [Int.card_Icc]
    have hcc : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff := Int.toNat_of_nonneg hc
    have h3 : P.leadingCoeff + 1 - (-1) = P.leadingCoeff + 2 := by ring
    rw [h3]
    omega
  calc (polyActIdx P m k θ).card
      ≤ ((blockPair m) ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff).card := Finset.card_le_card hsub
    _ = (blockPair m).card * (Finset.Icc (-1:ℤ) P.leadingCoeff).card := Finset.card_product _ _
    _ ≤ 16 * (P.leadingCoeff.toNat + 2) := by
        refine Nat.mul_le_mul hbp hIcc

/-! ## The cap for the block symbol -/

/-- **The block symbol is uniformly `2^{-mσ}`-small.** -/
theorem norm_polyModelQBlock_le_cap (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m k : ℕ) (θ : ℝ),
      ‖polyModelQBlock P m (2^k) θ‖ ≤ B * (2:ℝ)^(-(m:ℝ) * polySig P) := by
  obtain ⟨A, hApos, hA⟩ := polyWeight_cap_Icc P hc hd
  have hc0 : 0 ≤ P.leadingCoeff := le_of_lt hc
  refine ⟨(16 * (P.leadingCoeff.toNat + 2) + 1) * A + 1, by positivity, fun m k θ => ?_⟩
  have hdec : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ) * polySig P) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  by_cases hk : 4*m ≤ k
  · have h1 := norm_star_polyModelQBlock_le_actIdx P hk θ
    rw [Complex.norm_conj] at h1
    have hcard : (polyActIdx P m k θ).card ≤ 16 * (P.leadingCoeff.toNat + 2) := by
      by_cases h2m : 2*m+3 ≤ k
      · exact le_trans (polyActIdx_card_le_one P hd h2m θ) (by omega)
      · exact polyActIdx_card_le_small P hc0 (by omega) θ
    have hsum : ∑ p ∈ polyActIdx P m k θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖
        ≤ 16 * (P.leadingCoeff.toNat + 2) * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
      calc ∑ p ∈ polyActIdx P m k θ,
            ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖
          ≤ ∑ _p ∈ polyActIdx P m k θ, A * (2:ℝ)^(-(m:ℝ) * polySig P) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            rw [mem_polyActIdx, mem_polyAllIdx] at hp
            obtain ⟨⟨hpb, hpl⟩, _⟩ := hp
            obtain ⟨hm1, hm2, ha, hgcd⟩ := mem_blockPair.mp hpb
            exact hA m p.1.1 p.1.2 p.2 hm1 hm2 hgcd hpl
        _ = ((polyActIdx P m k θ).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (16 * (P.leadingCoeff.toNat + 2) : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast hcard
    have hfin : (16 * (P.leadingCoeff.toNat + 2) : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
        ≤ ((16 * (P.leadingCoeff.toNat + 2) + 1) * A + 1) * (2:ℝ)^(-(m:ℝ) * polySig P) := by
      have hA1 : (16 * (P.leadingCoeff.toNat + 2) : ℝ) * A
          ≤ (16 * (P.leadingCoeff.toNat + 2) + 1) * A + 1 := by
        nlinarith [hApos]
      calc (16 * (P.leadingCoeff.toNat + 2) : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          = ((16 * (P.leadingCoeff.toNat + 2) : ℝ) * A) * (2:ℝ)^(-(m:ℝ) * polySig P) := by ring
        _ ≤ ((16 * (P.leadingCoeff.toNat + 2) + 1) * A + 1) * (2:ℝ)^(-(m:ℝ) * polySig P) :=
            mul_le_mul_of_nonneg_right hA1 hdec
    linarith [h1, hsum, hfin]
  · have hz : polyModelQBlock P m (2^k) θ = 0 := by
      refine polyModelQBlock_eq_zero_of_lt P ?_ θ
      omega
    rw [hz, norm_zero]
    exact mul_nonneg (by positivity) hdec

end Work.BourgainPlan.Maximal
