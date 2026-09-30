import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.bike_count_arc
import Submission.Work.BMF.candSet_le
import Submission.Work.BMF.edges_card_le
import Submission.Work.BMF.bikeSetAll_bridge
import Submission.Work.BMF.walk_closure
import Submission.Work.BMF.arc_count_ge
import Submission.Work.BMF.good_bike_aux
import Submission.Work.BMF.primesIn_half_card_le_all
import Submission.Work.BMF.bikeSet_sum_lower
import Submission.Work.BMF.degen_bikes_sum_le
import Submission.Work.BMF.notVeryGood_bikes_sum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.good_bike_exists`

The counting step of `Work.BMF.adi_cycles` (MRTTZ, Prop. 3.7 and the averaging argument of
MRT, Section 4): for a quadruple graph `D` with `≥ c π₀(P₁)² (X/L)` edges there is a prime
`q ∈ [P₂/2, P₂]` whose `q`-subgraph carries `≫ c^{4ℓ+2} (π₀(P₁)²)^{2ℓ+1}/(X/L)` good
bicycles (an arc of `D`, a non-degenerate closed walk through each of its endpoints, and a
supporting prime set of size `> δ π₀(P₂)`).

The proof decomposes into the three counting lemmas imported above:

* `bikeSet_sum_lower`: the sum over `q` of `#bikeSet D q ℓ` is `≫ c^{4ℓ+2} π₀(P₂)
  (π₀(P₁)²)^{2ℓ+1}/(X/L)` (Blakley–Roy / power mean over the `q`-arcs);
* `degen_bikes_sum_le`: the number of bicycles one of whose cycles is degenerate is
  `≪ c₅ π₀(P₂) (π₀(P₁)²)^{2ℓ+1}/(X/L)`;
* `notVeryGood_bikes_sum_le`: the number of bicycles whose supporting prime set is small is
  `≪ δ π₀(P₂) (π₀(P₁)²)^{2ℓ+1}/(X/L)`;

and a pigeonhole over the primes of `[P₂/2, P₂]`, with `c₅`, `δ` chosen small compared with
`c^{4ℓ+2}` and `P₀` large enough to make `1/log P₁ ≤ c₅`.
-/

namespace Work.BMF

open Finset Real

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000 in
theorem good_bike_exists (k : ℕ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (heven : Even ℓ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ (c : ℝ), 0 < c → ∃ c₅ δ P₀ : ℝ, 0 < c₅ ∧ 0 < δ ∧ 0 < P₀ ∧
      ∀ (f : ℕ → ℂ) (C X L P₁ P₂ : ℝ) (D : Work.BMF.QuadData k f c C X L P₁ P₂),
        P₀ ≤ P₁ → 0 < P₁ → 2 ≤ P₂ → 0 < L → 0 < X →
        8000 * P₁ ^ 2 < X / L → 3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) →
        c * Work.BMF.pi0 P₁ ^ 2 * (X / L) ≤ (D.edges.card : ℝ) →
        ∃ q ∈ Work.BMF.primesIn (P₂ / 2) P₂,
          c₂ * c ^ (4 * ℓ + 2) * (Work.BMF.pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) ≤
            ((Work.BMF.goodBikeSet D q ℓ (X / L) c₅ δ).card : ℝ) := by
  obtain ⟨cA, P₀A, hcA, hP₀A, hA⟩ := bikeSet_sum_lower k ℓ hℓ heven
  obtain ⟨cB, P₀B, hcB, hP₀B, hB⟩ := degen_bikes_sum_le k ℓ hℓ
  obtain ⟨cN, P₀N, hcN, hP₀N, hN⟩ := notVeryGood_bikes_sum_le k ℓ hℓ
  obtain ⟨CQ, hCQ, hQc⟩ := primesIn_half_card_le_all
  refine ⟨cA / (2 * CQ), by positivity, ?_⟩
  intro c hc
  set cx : ℝ := min 1 (c ^ (4 * ℓ + 2)) with hcx
  have hcxpos : 0 < cx := lt_min one_pos (by positivity)
  have hcxle : cx ≤ c ^ (4 * ℓ + 2) := min_le_right _ _
  set e₅ : ℝ := cx * cA / (4 * cB) with he₅
  set δ : ℝ := cx * cA / (4 * cN) with hδ
  have he₅pos : 0 < e₅ := by rw [he₅]; positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set P₀ : ℝ := max 3 (max P₀A (max P₀B (max P₀N (Real.exp (1 / e₅))))) with hP₀def
  refine ⟨e₅, δ, P₀, he₅pos, hδpos, ?_, ?_⟩
  · rw [hP₀def]; positivity
  intro f C X L P₁ P₂ D hP₀ hP₁ hP₂ hL hX hbig hN3 hNle hedges
  -- extraction of the bounds from `P₀ ≤ P₁`
  have h3P₁ : (3:ℝ) ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have hA₁ : max P₀A (max P₀B (max P₀N (Real.exp (1 / e₅)))) ≤ P₁ :=
    le_trans (le_max_right _ _) hP₀
  have hP₀A' : P₀A ≤ P₁ := le_trans (le_max_left _ _) hA₁
  have hA₂ : max P₀B (max P₀N (Real.exp (1 / e₅))) ≤ P₁ := le_trans (le_max_right _ _) hA₁
  have hP₀B' : P₀B ≤ P₁ := le_trans (le_max_left _ _) hA₂
  have hA₃ : max P₀N (Real.exp (1 / e₅)) ≤ P₁ := le_trans (le_max_right _ _) hA₂
  have hP₀N' : P₀N ≤ P₁ := le_trans (le_max_left _ _) hA₃
  have hexp : Real.exp (1 / e₅) ≤ P₁ := le_trans (le_max_right _ _) hA₃
  have hlog : 1 / Real.log P₁ ≤ e₅ := by
    have hlogpos : 0 < Real.log P₁ := Real.log_pos (by linarith)
    have h1 : Real.log (Real.exp (1 / e₅)) ≤ Real.log P₁ := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at h1
    rw [div_le_iff₀ hlogpos]
    have h2 : 1 / e₅ * e₅ ≤ Real.log P₁ * e₅ := mul_le_mul_of_nonneg_right h1 (le_of_lt he₅pos)
    rw [div_mul_cancel₀ 1 (ne_of_gt he₅pos)] at h2
    linarith
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hfintype : (Fintype.card (GVert D) : ℝ) ≤ X / L := by
    rw [fintype_card_GVert]
    exact fam_card_le_NR D hX hL hN3
  -- the three sum bounds
  have hlow := hA f c C X L P₁ P₂ D hP₀A' hP₁ hc hP₂ hL hX hbig hN3 hNle hfintype hedges
  have hdeg := hB f c C X L P₁ P₂ e₅ D hP₀B' hP₁ hP₂ hL hX hbig hN3 hNle hlog
  have hng := hN f c C X L P₁ P₂ δ D hP₀N' hP₁ hP₂ hL hX hbig hN3 hNle hδnn
  -- per-`q` decomposition
  have hsub : ∀ q : ℕ, bikeSet D q ℓ ⊆
      goodBikeSet D q ℓ (X / L) e₅ δ ∪
        (degenBikes D ℓ (X / L) e₅ q ∪ notVeryGoodBikes D ℓ δ q) := by
    intro q t ht
    by_cases hg : t ∈ goodBikeSet D q ℓ (X / L) e₅ δ
    · exact Finset.mem_union.mpr (Or.inl hg)
    · refine Finset.mem_union.mpr (Or.inr ?_)
      have hmem : ¬ goodBikeQ (X / L) e₅ δ D ℓ t := by
        intro hq
        refine hg ?_
        rw [show goodBikeSet D q ℓ (X / L) e₅ δ
            = (bikeSet D q ℓ).filter (fun t => goodBikeQ (X / L) e₅ δ D ℓ t) from rfl,
          Finset.mem_filter]
        exact ⟨ht, hq⟩
      simp only [goodBikeQ, not_and_or, not_not] at hmem
      rcases hmem with h | h | h
      · exact Finset.mem_union.mpr (Or.inl (by
          rw [degenBikes_def, Finset.mem_filter]; exact ⟨ht, Or.inl h⟩))
      · exact Finset.mem_union.mpr (Or.inl (by
          rw [degenBikes_def, Finset.mem_filter]; exact ⟨ht, Or.inr h⟩))
      · exact Finset.mem_union.mpr (Or.inr (by
          rw [notVeryGoodBikes_def, Finset.mem_filter]; exact ⟨ht, h⟩))
  have hperq : ∀ q : ℕ, ((bikeSet D q ℓ).card : ℝ) ≤
      ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) +
      ((degenBikes D ℓ (X / L) e₅ q).card : ℝ) + ((notVeryGoodBikes D ℓ δ q).card : ℝ) := by
    intro q
    have h1 : (bikeSet D q ℓ).card ≤ (goodBikeSet D q ℓ (X / L) e₅ δ ∪
        (degenBikes D ℓ (X / L) e₅ q ∪ notVeryGoodBikes D ℓ δ q)).card :=
      Finset.card_le_card (hsub q)
    have h2 := Finset.card_union_le (goodBikeSet D q ℓ (X / L) e₅ δ)
      (degenBikes D ℓ (X / L) e₅ q ∪ notVeryGoodBikes D ℓ δ q)
    have h3 := Finset.card_union_le (degenBikes D ℓ (X / L) e₅ q) (notVeryGoodBikes D ℓ δ q)
    have h4 : (goodBikeSet D q ℓ (X / L) e₅ δ ∪
        (degenBikes D ℓ (X / L) e₅ q ∪ notVeryGoodBikes D ℓ δ q)).card ≤
        (goodBikeSet D q ℓ (X / L) e₅ δ).card +
          ((degenBikes D ℓ (X / L) e₅ q).card + (notVeryGoodBikes D ℓ δ q).card) :=
      le_trans h2 (Nat.add_le_add_left h3 _)
    calc ((bikeSet D q ℓ).card : ℝ)
        ≤ ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) +
          (((degenBikes D ℓ (X / L) e₅ q).card : ℝ) + ((notVeryGoodBikes D ℓ δ q).card : ℝ)) := by
          exact_mod_cast le_trans h1 h4
      _ = ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) +
          ((degenBikes D ℓ (X / L) e₅ q).card : ℝ) + ((notVeryGoodBikes D ℓ δ q).card : ℝ) := by
          ring
  set F : ℝ := pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) with hF
  have hFnn : 0 ≤ F := by
    rw [hF]
    have h1 : 0 ≤ pi0 P₂ := (pi0_pos hP₂).le
    have h2 : 0 ≤ (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) := by positivity
    have h3 : 0 < X / L := by linarith
    positivity
  have hsum := Finset.sum_le_sum (fun q (_ : q ∈ primesIn (P₂ / 2) P₂) => hperq q)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  -- the arithmetic core
  have hlow' : cA * c ^ (4 * ℓ + 2) * F ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂, ((bikeSet D q ℓ).card : ℝ) := by
    have h': cA * c ^ (4 * ℓ + 2) * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L)
        = cA * c ^ (4 * ℓ + 2) * F := by rw [hF]; ring
    rwa [h'] at hlow
  have hdeg' : ∑ q ∈ primesIn (P₂ / 2) P₂, ((degenBikes D ℓ (X / L) e₅ q).card : ℝ)
      ≤ (cB * e₅) * F := by
    have h': cB * e₅ * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) = (cB * e₅) * F := by
      rw [hF]; ring
    rwa [h'] at hdeg
  have hng' : ∑ q ∈ primesIn (P₂ / 2) P₂, ((notVeryGoodBikes D ℓ δ q).card : ℝ)
      ≤ (cN * δ) * F := by
    have h': cN * δ * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) = (cN * δ) * F := by
      rw [hF]; ring
    rwa [h'] at hng
  have he₅bd : cB * e₅ ≤ cA * c ^ (4 * ℓ + 2) / 4 := by
    have h': cB * e₅ = cx * cA / 4 := by rw [he₅]; field_simp
    rw [h']
    have := mul_le_mul_of_nonneg_right hcxle (le_of_lt hcA)
    linarith
  have hδbd : cN * δ ≤ cA * c ^ (4 * ℓ + 2) / 4 := by
    have h': cN * δ = cx * cA / 4 := by rw [hδ]; field_simp
    rw [h']
    have := mul_le_mul_of_nonneg_right hcxle (le_of_lt hcA)
    linarith
  have hmain : (cA / 2) * c ^ (4 * ℓ + 2) * F ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂, ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) := by
    have hb1 := mul_le_mul_of_nonneg_right he₅bd hFnn
    have hb2 := mul_le_mul_of_nonneg_right hδbd hFnn
    nlinarith [hlow', hdeg', hng', hsum, hb1, hb2]
  -- pigeonhole
  have hpos : (0:ℝ) < (cA / 2) * c ^ (4 * ℓ + 2) * F := by
    have h1 : 0 < cA / 2 := by linarith
    have h2 : 0 < c ^ (4 * ℓ + 2) := by positivity
    have hFpos : 0 < F := by
      have hXL : 0 < X / L := by linarith
      have hpi1 : 0 < pi0 P₁ := pi0_pos (by linarith)
      rw [hF]
      exact div_pos (mul_pos (pi0_pos hP₂) (pow_pos (pow_pos hpi1 2) _)) hXL
    exact mul_pos (mul_pos h1 h2) hFpos
  have hQne : (primesIn (P₂ / 2) P₂).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hz : ∑ q ∈ primesIn (P₂ / 2) P₂, ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) = 0 := by
      rw [hempty]; simp
    rw [hz] at hmain
    linarith
  obtain ⟨q, hqmem, hqmax⟩ := Finset.exists_max_image (primesIn (P₂ / 2) P₂)
    (fun q => ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ)) hQne
  refine ⟨q, hqmem, ?_⟩
  have hQc' : ((primesIn (P₂ / 2) P₂).card : ℝ) ≤ CQ * pi0 P₂ := hQc P₂ hP₂
  have hQcardpos : 0 < ((primesIn (P₂ / 2) P₂).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hQne
  have hsummax : ∑ q' ∈ primesIn (P₂ / 2) P₂, ((goodBikeSet D q' ℓ (X / L) e₅ δ).card : ℝ)
      ≤ ((primesIn (P₂ / 2) P₂).card : ℝ) *
        ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) := by
    have h := Finset.sum_le_sum (fun q' (hq' : q' ∈ primesIn (P₂ / 2) P₂) => hqmax q' hq')
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hpi0P₂pos : 0 < pi0 P₂ := pi0_pos hP₂
  have hmain2 : (cA / 2) * c ^ (4 * ℓ + 2) * F ≤
      ((primesIn (P₂ / 2) P₂).card : ℝ) * ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) :=
    le_trans hmain hsummax
  have hCQpos : 0 < CQ := hCQ
  -- divide
  have hgoal : cA / (2 * CQ) * c ^ (4 * ℓ + 2) * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) ≤
      ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) := by
    rw [hF] at hmain2
    have hstep : cA / (2 * CQ) * c ^ (4 * ℓ + 2) * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L)
        = (cA / 2) * c ^ (4 * ℓ + 2) * F / (CQ * pi0 P₂) := by
      rw [hF]; field_simp
    rw [hstep, div_le_iff₀ (mul_pos hCQpos hpi0P₂pos)]
    calc (cA / 2) * c ^ (4 * ℓ + 2) * F
        ≤ ((primesIn (P₂ / 2) P₂).card : ℝ) * ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) :=
          hmain2
      _ ≤ (CQ * pi0 P₂) * ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) :=
          mul_le_mul_of_nonneg_right hQc' (by positivity)
      _ = ((goodBikeSet D q ℓ (X / L) e₅ δ).card : ℝ) * (CQ * pi0 P₂) := by ring
  exact hgoal

end Work.BMF
