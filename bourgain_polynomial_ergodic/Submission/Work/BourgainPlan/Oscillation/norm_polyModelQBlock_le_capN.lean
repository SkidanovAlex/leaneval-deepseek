import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_cap
import Submission.Work.BourgainPlan.Oscillation.polyModelQBlock_eq_zero_of_lt_pow4
import Submission.Work.BourgainPlan.Oscillation.polyActIdxN_card_le_one_pow4

/-!
# The arbitrary-scale block symbol is uniformly `2^{-mσ}`-small

The circle-method (= maximal) development bounds the `m`-th dyadic block `polyModelQBlock P m (2^k)`
of the major-arc model (`Work.BourgainPlan.Maximal.norm_polyModelQBlock_le_cap`).  Bourgain's
oscillation inequality is stated along the *lacunary* scales `N_i = ⌊ρ^i⌋`, which are not dyadic, so
the same bound is needed at an **arbitrary** scale `N`:

`‖polyModelQBlock P m N θ‖ ≤ B · 2^{−mσ}`.

The proof is the arbitrary-scale transcription of the dyadic one:

* the block expands into its arc terms `polyModelTermArcN` (same expansion as
  `star_polyModelQBlock_eq_sum`, only the denominator cutoff `q ≤ ⌊N^{1/4}⌋` is now a genuine
  restriction);
* each arc term is bounded by the modulus-`q·c` complete sum `polyWeight`;
* the weights are `≤ A · 2^{−mσ}` on the block (`polyWeight_cap_Icc`, an `N`-independent statement);
* the number of active indices is `≤ 1` as soon as `m ≥ 3` and `4^m ≤ N` (uniqueness of the
  major-arc representation combined with the separation `2N^{−(d−1/4)} < (q q')^{−1}`), and is
  bounded by `2^{2m+1}(c+2)` in the remaining small-`m` case; for `N < 4^m` the block is empty.

The three number-theoretic/combinatorial inputs are proved in
`polyActIdxN_card_le_one_pow4` and `polyModelQBlock_eq_zero_of_lt_pow4`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Oscillation

open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

/-! ## The arc term at an arbitrary scale -/

open Classical in
/-- A single arc term of the `m`-th block at an **arbitrary** scale `N`: the model term, restricted
to its arc `|c θ − a/q − l| ≤ polyArcRadN P N` (the arbitrary-scale analogue of
`Work.BourgainPlan.Maximal.polyModelTermArc`, which is the case `N = 2^k`). -/
noncomputable def polyModelTermArcN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ) : ℂ :=
  if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
    then polyModelTermPre P N q a l θ else 0

lemma polyModelTermArcN_eq_zero_of_not_act (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ)
    (h : ¬ |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N) :
    polyModelTermArcN P q a l N θ = 0 := by
  unfold polyModelTermArcN
  rw [if_neg h]

/-! ## The monomial-block expansion at an arbitrary scale -/

/-- The `q`-layer of the `m`-th block, with the denominator cutoff kept as a filter. -/
lemma blockQN_eq_filter_le (E m : ℕ) :
    (Finset.Icc 1 E).filter (fun q => Nat.log 2 q = m)
      = (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ E) := by
  rw [filter_log_eq_filter_pow]
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  have h1 : 1 ≤ 2^m := Nat.one_le_two_pow
  constructor
  · rintro ⟨⟨h1', h2'⟩, h3', h4'⟩
    exact ⟨⟨h3', h4'⟩, h2'⟩
  · rintro ⟨⟨h3', h4'⟩, h2'⟩
    exact ⟨⟨by omega, h2'⟩, h3', h4'⟩

/-- The `q`-th major-arc block, expanded into its arc-restricted terms. -/
lemma polyMajorArcBlockPre_eq_sum_arcN (P : Polynomial ℤ) (N q : ℕ) (θ : ℝ) :
    polyMajorArcBlockPre P ((1:ℝ)/4) N θ q
      = ∑ a ∈ Finset.range q, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          (if Nat.gcd a q = 1 then polyModelTermArcN P q a l N θ else 0) := by
  have hmb : polyMajorArcBlockPre P ((1:ℝ)/4) N θ q
      = ∑ a ∈ Finset.range q, (if Nat.gcd a q = 1 then
          (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
              then polyModelTermPre P N q a l θ else 0)) else 0) := rfl
  rw [hmb]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hg : Nat.gcd a q = 1
  · simp only [hg, if_true]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold polyModelTermArcN
    rfl
  · simp only [hg, if_false, Finset.sum_const_zero]

/-- **The partial-block expansion at an arbitrary scale.** -/
theorem star_polyModelQBlock_eq_sum_arcN (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (polyModelQBlock P m N θ)
      = ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArcN P q a l N θ) := by
  unfold polyModelQBlock
  rw [blockQN_eq_filter_le]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [polyMajorArcBlockPre_eq_sum_arcN P N q θ, map_sum]
  have hstep : ∀ a : ℕ,
      starRingEnd ℂ (∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          (if Nat.gcd a q = 1 then polyModelTermArcN P q a l N θ else 0))
        = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            starRingEnd ℂ (polyModelTermArcN P q a l N θ) else 0) := by
    intro a
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l _ => conj_ite_zero _ (polyModelTermArcN P q a l N θ))]
    exact sum_ite_gcd_eq' a q _ (fun l => starRingEnd ℂ (polyModelTermArcN P q a l N θ))
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_filter]

/-! ## The active-index sum -/

/-- The sum over the *active* index triples of the `m`-th block, written with the denominator
cutoff `q ≤ Q` pulled into the summand. -/
lemma sum_active_arcN_eq_blockPair (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) (Q : ℕ)
    (F : (ℕ × ℕ) × ℤ → ℝ) :
    (∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N ∧ q ≤ Q)
              then F ((q,a),l) else 0))
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
                ∧ i.1 ≤ Q)
              then F (i,l) else 0) := by
  -- elements with `q > Q` contribute `0` (the conjunction `q ≤ Q` is inside every summand)
  have hdrop : (∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N ∧ q ≤ Q)
              then F ((q,a),l) else 0))
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N ∧ q ≤ Q)
              then F ((q,a),l) else 0) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hnot => ?_)
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun l _ => ?_))
    exact if_neg (fun hcon => hnot (Finset.mem_filter.mpr ⟨hq, hcon.2⟩))
  rw [hdrop, ← sum_blockPair m (F := fun i : ℕ × ℕ => ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
      (if (|(P.leadingCoeff:ℝ)*θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ polyArcRadN P N ∧ i.1 ≤ Q)
        then F (i,l) else 0))]

/-- **The block symbol is bounded by the weighted active-index sum at an arbitrary scale.** -/
theorem norm_polyModelQBlock_le_sum_actIdxN (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) :
    ‖polyModelQBlock P m N θ‖
      ≤ ∑ p ∈ polyActIdxN P m N θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ := by
  rw [← Complex.norm_conj, star_polyModelQBlock_eq_sum_arcN P m N θ]
  -- each arc term is bounded by the complete sum of modulus `q · c`
  have hterm : ∀ (q a : ℕ) (l : ℤ),
      ‖starRingEnd ℂ (polyModelTermArcN P q a l N θ)‖
        ≤ (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
            then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0) := by
    intro q a l
    rw [Complex.norm_conj]
    unfold polyModelTermArcN
    by_cases h : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
    · rw [if_pos h, if_pos h]
      unfold polyModelTermPre
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_polyProfile_le_one P N _)
    · rw [if_neg h, if_neg h, norm_zero]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun q _ => norm_sum_le _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun a _ => norm_sum_le _ _))) ?_
  refine le_trans (Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun a _ =>
    Finset.sum_le_sum (fun l _ => hterm q a l)))) ?_
  -- rewrite the weighted arc sum into the block-pair form
  have hL2 : (∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
          (fun q => q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4))),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
              then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0))
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
                ∧ i.1 ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4)))
              then ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ else 0) := by
    have hA : (∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
              (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
                then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0))
        = ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
              (if (|(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
                  ∧ q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4)))
                then ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ else 0) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      have hqQ : q ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4)) := (Finset.mem_filter.mp hq).2
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun l _ => ?_))
      by_cases h : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
      · rw [if_pos h, if_pos ⟨h, hqQ⟩]
      · rw [if_neg h, if_neg (fun hh => h hh.1)]
    rw [hA, sum_active_arcN_eq_blockPair P m N θ (Nat.floor ((N : ℝ)^((1:ℝ)/4)))
      (fun p => ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖)]
  -- rewrite the active-index sum into the block-pair form
  have hR2 : (∑ p ∈ (polyActIdxN P m N θ).filter
          (fun p => p.1.1 ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4))),
        ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖)
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            (if (|(P.leadingCoeff:ℝ)*θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
                ∧ i.1 ≤ Nat.floor ((N : ℝ)^((1:ℝ)/4)))
              then ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ else 0) := by
    rw [polyActIdxN, Finset.filter_filter, polyAllIdx, Finset.sum_filter, Finset.sum_product]
  rw [hL2]
  refine le_trans (le_of_eq hR2.symm) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => norm_nonneg _)


/-! ## The crude cardinality bound -/

/-- The number of index triples of the `m`-th block is at most `2^{2m+1}(c+2)`. -/
lemma card_polyActIdxN_le_crude (P : Polynomial ℤ) (hc : 0 ≤ P.leadingCoeff) (m N : ℕ) (θ : ℝ) :
    (polyActIdxN P m N θ).card ≤ 2^(2*m+1) * (P.leadingCoeff.toNat + 2) := by
  have hsubPair : blockPair m ⊆ (Finset.Ico (2^m) (2^(m+1))) ×ˢ (Finset.range (2^(m+1))) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hp
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
    exact ⟨⟨h1, h2⟩, lt_of_lt_of_le h3 (le_of_lt h2)⟩
  have hcardIcc : (Finset.Icc (-1:ℤ) P.leadingCoeff).card ≤ P.leadingCoeff.toNat + 2 := by
    rw [Int.card_Icc]
    have h3 : P.leadingCoeff + 1 - (-1 : ℤ) = P.leadingCoeff + 2 := by ring
    rw [h3]
    have h2 : (P.leadingCoeff + 2).toNat = P.leadingCoeff.toNat + 2 := by
      have h := Int.toNat_add (a := P.leadingCoeff) (b := 2) hc (by norm_num)
      simpa using h
    rw [h2]
  have hcardPair : (blockPair m).card ≤ 2^(2*m+1) := by
    calc (blockPair m).card
        ≤ ((Finset.Ico (2^m) (2^(m+1))) ×ˢ (Finset.range (2^(m+1)))).card :=
          Finset.card_le_card hsubPair
      _ = (2^(m+1) - 2^m) * 2^(m+1) := by
          rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
      _ ≤ 2^m * 2^(m+1) := by
          have h : 2^(m+1) - 2^m = 2^m := by
            rw [pow_succ]
            omega
          rw [h]
      _ = 2^(2*m+1) := by
          rw [← pow_add]
          congr 1
          omega
  calc (polyActIdxN P m N θ).card
      ≤ (polyAllIdx P m).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = (blockPair m ×ˢ Finset.Icc (-1:ℤ) P.leadingCoeff).card := by rw [polyAllIdx]
    _ = (blockPair m).card * (Finset.Icc (-1:ℤ) P.leadingCoeff).card := Finset.card_product _ _
    _ ≤ 2^(2*m+1) * (P.leadingCoeff.toNat + 2) := Nat.mul_le_mul hcardPair hcardIcc

/-! ## The cap -/

/-- **The block symbol is uniformly `2^{-mσ}`-small at an arbitrary scale.** -/
theorem norm_polyModelQBlock_le_capN (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m N : ℕ) (θ : ℝ),
      ‖Work.BourgainPlan.Maximal.polyModelQBlock P m N θ‖
        ≤ B * (2:ℝ)^(-(m:ℝ) * Work.BourgainPlan.Maximal.polySig P) := by
  obtain ⟨A, hApos, hA⟩ := polyWeight_cap_Icc P hc hd
  have hc0 : 0 ≤ P.leadingCoeff := le_of_lt hc
  refine ⟨(32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1, by positivity, fun m N θ => ?_⟩
  have hdec : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ) * polySig P) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hw : ∀ p ∈ polyActIdxN P m N θ,
      ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P) := by
    intro p hp
    rw [polyActIdxN, Finset.mem_filter, mem_polyAllIdx] at hp
    obtain ⟨⟨hpb, hpl⟩, _⟩ := hp
    obtain ⟨hm1, hm2, ha, hgcd⟩ := mem_blockPair.mp hpb
    exact hA m p.1.1 p.1.2 p.2 hm1 hm2 hgcd hpl
  have hsum : (∑ p ∈ polyActIdxN P m N θ,
        ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖)
      ≤ ((polyActIdxN P m N θ).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
    calc (∑ p ∈ polyActIdxN P m N θ,
          ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖)
        ≤ ∑ _p ∈ polyActIdxN P m N θ, (A * (2:ℝ)^(-(m:ℝ) * polySig P)) :=
          Finset.sum_le_sum (fun p hp => hw p hp)
      _ = ((polyActIdxN P m N θ).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rcases lt_or_ge N (4^m) with hNlt | hNge
  · -- the block is empty
    rw [polyModelQBlock_eq_zero_of_lt_pow4 P hNlt θ, norm_zero]
    exact mul_nonneg (by positivity) hdec
  · refine le_trans (norm_polyModelQBlock_le_sum_actIdxN P m N θ) (le_trans hsum ?_)
    rcases le_or_gt m 2 with hm | hm
    · -- small `m`: the crude cardinality bound
      have hcard := card_polyActIdxN_le_crude P hc0 m N θ
      have hc2 : (0:ℝ) ≤ ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) := by positivity
      have hcardR : ((polyActIdxN P m N θ).card : ℝ)
          ≤ (2^(2*m+1) : ℕ) * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have hpow : ((2^(2*m+1) : ℕ) : ℝ) ≤ 32 := by
        have h2 : (2:ℕ)^(2*m+1) ≤ 2^5 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        calc ((2^(2*m+1) : ℕ) : ℝ) ≤ ((2^5 : ℕ) : ℝ) := by exact_mod_cast h2
          _ = 32 := by norm_num
      have step1 : ((polyActIdxN P m N θ).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          ≤ (((2^(2*m+1) : ℕ) : ℝ) * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ))
              * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) :=
        mul_le_mul_of_nonneg_right hcardR (mul_nonneg hApos.le hdec)
      have step2 : (((2^(2*m+1) : ℕ) : ℝ) * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ))
              * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          ≤ (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ))
              * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hc2)
          (mul_nonneg hApos.le hdec)
      have step3 : (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ))
              * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          ≤ ((32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1)
              * (2:ℝ)^(-(m:ℝ) * polySig P) := by
        have h : 32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) * A
            ≤ (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1 := by
          nlinarith [hApos]
        calc (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ)) * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
            = (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) * A)
              * (2:ℝ)^(-(m:ℝ) * polySig P) := by ring
          _ ≤ ((32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1)
              * (2:ℝ)^(-(m:ℝ) * polySig P) := mul_le_mul_of_nonneg_right h hdec
      linarith [step1, step2, step3]
    · -- `m ≥ 3`: at most one active index
      have hm3 : 3 ≤ m := by omega
      have hcard := polyActIdxN_card_le_one_pow4 P hd hm3 hNge θ
      have hcardR : ((polyActIdxN P m N θ).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have step1 : ((polyActIdxN P m N θ).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          ≤ 1 * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) :=
        mul_le_mul_of_nonneg_right hcardR (mul_nonneg hApos.le hdec)
      have step3 : 1 * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
          ≤ ((32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1)
              * (2:ℝ)^(-(m:ℝ) * polySig P) := by
        have h : A ≤ (32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1 := by
          nlinarith [hApos]
        calc 1 * (A * (2:ℝ)^(-(m:ℝ) * polySig P))
            = A * (2:ℝ)^(-(m:ℝ) * polySig P) := by ring
          _ ≤ ((32 * ((P.leadingCoeff.toNat + 2 : ℕ) : ℝ) + 1) * A + 1)
              * (2:ℝ)^(-(m:ℝ) * polySig P) := mul_le_mul_of_nonneg_right h hdec
      linarith [step1, step3]

end

end Work.BourgainPlan.Oscillation
