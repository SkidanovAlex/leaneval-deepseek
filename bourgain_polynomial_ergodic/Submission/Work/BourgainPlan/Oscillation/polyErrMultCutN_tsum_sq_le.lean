import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.norm_polyBlockErrN_le_actIdxN
import Submission.Work.BourgainPlan.Oscillation.polyErrValN_le_split
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

/-! ## Elementary helpers -/

lemma sq_sum_eq_sum_sq_of_card_le_one {ι : Type*} (s : Finset ι) (h : s.card ≤ 1) (a : ι → ℝ) :
    (∑ p ∈ s, a p) ^ 2 = ∑ p ∈ s, (a p) ^ 2 := by
  rcases Finset.eq_empty_or_nonempty s with h0 | ⟨p₀, hp₀⟩
  · rw [h0]; simp
  · have hs : s = {p₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hp₀, fun b hb => Finset.card_le_one.mp h b hb p₀ hp₀⟩
    rw [hs]; simp

lemma tsum_ite_mem_finset (s : Finset ℕ) (c : ℝ) :
    (∑' i : ℕ, if i ∈ s then c else 0) = (s.card : ℝ) * c := by
  rw [tsum_eq_sum (s := s) (fun i hi => if_neg hi)]
  rw [Finset.sum_congr rfl (fun i hi => if_pos hi), Finset.sum_const, nsmul_eq_mul]

/-- `polySig P > 0`. -/
lemma polySig_pos (P : Polynomial ℤ) : 0 < polySig P := by
  rw [polySig, powSig]; positivity

/-- The arc radius at an arbitrary scale is antitone in the scale. -/
lemma polyArcRadN_antitone (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {N N' : ℕ}
    (hN : 1 ≤ N) (hNN' : N ≤ N') : polyArcRadN P N' ≤ polyArcRadN P N := by
  unfold polyArcRadN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN'
  have hz : -((P.natDegree : ℝ) - 1 / 4) ≤ 0 := by
    have h1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
    linarith
  exact Real.rpow_le_rpow_of_nonpos hNpos hle hz

/-- The active index set shrinks as the scale grows. -/
lemma polyActIdxN_subset_of_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {m : ℕ} {θ : ℝ}
    {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N ≤ N') :
    polyActIdxN P m N' θ ⊆ polyActIdxN P m N θ := by
  intro p hp
  simp only [polyActIdxN, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, le_trans hp.2 (polyArcRadN_antitone P hd hN hNN')⟩

/-- On `θ ∈ (0,1)` and `N ≥ N₀` the cut error multiplier is the block error. -/
lemma polyErrMultCutN_eq_polyBlockErrN (P : Polynomial ℤ) (m N₀ N : ℕ) {θ : ℝ}
    (hN : N₀ ≤ N) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    polyErrMultCutN P m N₀ N θ = polyBlockErrN P m N N θ := by
  unfold polyErrMultCutN polyErrMultN polyBlockErrN
  rw [if_pos hN, if_pos ⟨hθ0, hθ1⟩, if_pos hN, if_pos le_rfl]

/-- Off `(0,1)` the cut error multiplier vanishes. -/
lemma polyErrMultCutN_eq_zero (P : Polynomial ℤ) (m N₀ N : ℕ) {θ : ℝ}
    (hθ : ¬ (0 < θ ∧ θ < 1)) : polyErrMultCutN P m N₀ N θ = 0 := by
  simp only [polyErrMultCutN, polyErrMultN, hθ, if_false]
  split_ifs <;> rfl

/-! ## The crude (triangle-inequality) bound for the block error -/

lemma norm_polyModelTermArcN_sub_sharpN_le_two (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ)
    (θ : ℝ) :
    ‖BlockErrN.polyModelTermArcN P q a l N θ - polySharpTermN P q a l N θ‖
      ≤ 2 * ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ := by
  set w : ℝ := ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have h1 : ‖BlockErrN.polyModelTermArcN P q a l N θ‖ ≤ w := by
    by_cases h : |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRadN P N
    · rw [BlockErrN.polyModelTermArcN, if_pos h, polyModelTermPre, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_polyProfile_le_one P N _)
    · rw [BlockErrN.polyModelTermArcN, if_neg h, norm_zero]
      exact hw0
  have h2 : ‖polySharpTermN P q a l N θ‖ ≤ w := by
    rw [polySharpTermN, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    split_ifs <;> simp
  calc ‖BlockErrN.polyModelTermArcN P q a l N θ - polySharpTermN P q a l N θ‖
      ≤ ‖BlockErrN.polyModelTermArcN P q a l N θ‖ + ‖polySharpTermN P q a l N θ‖ :=
        norm_sub_le _ _
    _ ≤ w + w := add_le_add h1 h2
    _ = 2 * w := by ring

/-- **Crude bound for the block error**: simply the triangle inequality plus the weight cap. -/
lemma norm_polyBlockErrN_le_crude (P : Polynomial ℤ) {A : ℝ}
    (hcap : ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P))
    {m N : ℕ} (hN : 2^(4*m+4) ≤ N) (θ : ℝ) :
    ‖polyBlockErrN P m N N θ‖
      ≤ 2 * A * (2:ℝ)^(-(m:ℝ) * polySig P) * ((polyAllIdx P m).card : ℝ) := by
  rw [BlockErrN.polyBlockErrN_eq_sum P hN θ]
  calc ‖∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
        starRingEnd ℂ (BlockErrN.polyModelTermArcN P i.1 i.2 l N θ
          - polySharpTermN P i.1 i.2 l N θ)‖
      ≤ ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          2 * ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => ?_))
        rw [Complex.norm_conj]
        exact norm_polyModelTermArcN_sub_sharpN_le_two P i.1 i.2 l N θ
    _ ≤ ∑ _i ∈ blockPair m, ∑ _l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          2 * (A * (2:ℝ)^(-(m:ℝ) * polySig P)) := by
        refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
        obtain ⟨hm1, hm2, _ha, hg⟩ := mem_blockPair.mp hi
        exact mul_le_mul_of_nonneg_left (hcap m i.1 i.2 l hm1 hm2 hg hl) (by norm_num)
    _ = 2 * A * (2:ℝ)^(-(m:ℝ) * polySig P) * ((polyAllIdx P m).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [polyAllIdx, Finset.card_product]
        push_cast
        ring

/-- The number of index triples of the `m`-th block. -/
lemma card_polyAllIdx_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (m : ℕ) :
    (polyAllIdx P m).card ≤ 2^(2*m+1) * (P.leadingCoeff.toNat + 2) := by
  have hbp : (blockPair m).card ≤ 2^(2*m+1) := by
    have hsub : blockPair m ⊆ Finset.Ico (2^m) (2^(m+1)) ×ˢ Finset.range (2^(m+1)) := by
      intro p hp
      obtain ⟨h1, h2, ha, _hg⟩ := mem_blockPair.mp hp
      rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
      exact ⟨⟨h1, h2⟩, lt_trans ha h2⟩
    calc (blockPair m).card
        ≤ (Finset.Ico (2^m) (2^(m+1)) ×ˢ Finset.range (2^(m+1))).card :=
          Finset.card_le_card hsub
      _ = (2^(m+1) - 2^m) * 2^(m+1) := by rw [Finset.card_product, Nat.card_Ico, Finset.card_range]
      _ = 2^m * 2^(m+1) := by
          have h : 2^(m+1) = 2^m + 2^m := by rw [pow_succ]; ring
          rw [h, Nat.add_sub_cancel]
      _ = 2^(2*m+1) := by
          rw [Nat.mul_comm, ← pow_add]
          congr 1
          omega
  have hIcc : (Finset.Icc (-1:ℤ) P.leadingCoeff).card ≤ P.leadingCoeff.toNat + 2 := by
    have hcc : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff :=
      Int.toNat_of_nonneg (le_of_lt hc)
    have hsub : Finset.Icc (-1:ℤ) P.leadingCoeff
        ⊆ Finset.Icc (-1:ℤ) ((P.leadingCoeff.toNat : ℕ) : ℤ) := by
      intro l hl
      rw [Finset.mem_Icc] at hl ⊢
      exact ⟨hl.1, by rw [hcc]; exact hl.2⟩
    calc (Finset.Icc (-1:ℤ) P.leadingCoeff).card
        ≤ (Finset.Icc (-1:ℤ) ((P.leadingCoeff.toNat : ℕ) : ℤ)).card := Finset.card_le_card hsub
      _ = P.leadingCoeff.toNat + 2 := by
          rw [Int.card_Icc]
          have h3 : ((P.leadingCoeff.toNat : ℕ) : ℤ) + 1 - (-1)
              = ((P.leadingCoeff.toNat + 2 : ℕ) : ℤ) := by push_cast; ring
          rw [h3, Int.toNat_natCast]
  rw [polyAllIdx, Finset.card_product]
  exact Nat.mul_le_mul hbp hIcc

/-! ## The squared profile error is summable along the lacunary scales, uniformly in the frequency -/

lemma polyErrValN_lacScale_summable (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ Cer : ℝ, 0 < Cer ∧ ∀ β : ℝ,
      Summable (fun i : ℕ => (polyErrValN P β (lacScale ρ i)) ^ 2) ∧
      (∑' i : ℕ, (polyErrValN P β (lacScale ρ i)) ^ 2) ≤ Cer := by
  obtain ⟨Ksp, hKsppos, hsplit⟩ := polyErrValN_le_split P hd
  obtain ⟨Clac, hClacpos, hlac⟩ := lacScale_error_tsum_le ρ hρ P.natDegree (by omega)
  refine ⟨Ksp ^ 2 * Clac + 1, by positivity, fun β => ?_⟩
  have hscale1 : ∀ i : ℕ, (1:ℝ) ≤ (lacScale ρ i : ℝ) := by
    intro i
    have h := Nat.le_floor (show ((1:ℕ):ℝ) ≤ ρ ^ i from by
      push_cast
      exact one_le_pow₀ hρ.le)
    exact_mod_cast h
  by_cases hβ : β = 0
  · have hzero : ∀ i : ℕ, polyErrValN P β (lacScale ρ i) = 0 := by
      intro i
      rw [hβ]
      unfold polyErrValN
      rw [polyProfile_zero P (lacScale ρ i), if_pos (by simp : |polyDilN P (lacScale ρ i) * 0| ≤ 1)]
      simp
    have hz0 : ∀ i : ℕ, (polyErrValN P β (lacScale ρ i)) ^ 2 = 0 := by
      intro i; rw [hzero i]; ring
    refine ⟨(summable_congr hz0).mpr summable_zero, ?_⟩
    rw [tsum_congr hz0]
    simp
    positivity
  · set z : ℕ → ℝ := fun i => |β| * ((lacScale ρ i : ℕ) : ℝ) ^ P.natDegree with hzdef
    have hsumz : Summable (fun i : ℕ =>
          if z i ≤ 1 then (z i) ^ 2 else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2) ∧
        (∑' i : ℕ, (if z i ≤ 1 then (z i) ^ 2
            else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2)) ≤ Clac := by
      simpa only [hzdef] using hlac β hβ
    have hpt : ∀ i : ℕ, (polyErrValN P β (lacScale ρ i)) ^ 2
        ≤ Ksp ^ 2 * (if z i ≤ 1 then (z i) ^ 2
            else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2) := by
      intro i
      have h2 : polyErrValN P β (lacScale ρ i)
          ≤ Ksp * (if z i ≤ 1 then z i else (z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) := by
        have h := hsplit (lacScale ρ i) (by exact_mod_cast (hscale1 i)) β
        simpa only [hzdef] using h
      have h3 : (0:ℝ) ≤ polyErrValN P β (lacScale ρ i) := by unfold polyErrValN; positivity
      have h4 : (0:ℝ) ≤ Ksp * (if z i ≤ 1 then z i
            else (z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) := by
        refine mul_nonneg hKsppos.le ?_
        split_ifs with h
        · positivity
        · exact Real.rpow_nonneg (by rw [hzdef]; positivity : (0:ℝ) ≤ z i) _
      calc (polyErrValN P β (lacScale ρ i)) ^ 2
          ≤ (Ksp * (if z i ≤ 1 then z i
              else (z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ))))) ^ 2 := pow_le_pow_left₀ h3 h2 2
        _ = Ksp ^ 2 * (if z i ≤ 1 then (z i) ^ 2
              else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2) := by
            split_ifs <;> ring
    have hsumm : Summable (fun i : ℕ => (polyErrValN P β (lacScale ρ i)) ^ 2) :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _) hpt (hsumz.1.mul_left _)
    refine ⟨hsumm, ?_⟩
    calc (∑' i : ℕ, (polyErrValN P β (lacScale ρ i)) ^ 2)
        ≤ ∑' i : ℕ, Ksp ^ 2 * (if z i ≤ 1 then (z i) ^ 2
            else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2) :=
          Summable.tsum_le_tsum hpt hsumm (hsumz.1.mul_left _)
      _ = Ksp ^ 2 * (∑' i : ℕ, if z i ≤ 1 then (z i) ^ 2
            else ((z i) ^ (-((1 : ℝ) / (P.natDegree : ℝ)))) ^ 2) := tsum_mul_left
      _ ≤ Ksp ^ 2 * Clac := mul_le_mul_of_nonneg_left hsumz.2 (sq_nonneg _)
      _ ≤ Ksp ^ 2 * Clac + 1 := by linarith

/-! ## Membership and weight bounds for active indices -/

lemma polyActIdxN_mem_allIdx (P : Polynomial ℤ) {m N : ℕ} {θ : ℝ} {p : (ℕ × ℕ) × ℤ}
    (hp : p ∈ polyActIdxN P m N θ) : p ∈ polyAllIdx P m := by
  rw [polyActIdxN] at hp
  exact (Finset.mem_filter.mp hp).1

lemma weight_le_of_mem_act (P : Polynomial ℤ) {A : ℝ}
    (hcap : ∀ (m q a : ℕ) (l : ℤ), 2^m ≤ q → q < 2^(m+1) → Nat.gcd a q = 1 →
      l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff →
      ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖
        ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P))
    {m N : ℕ} {θ : ℝ} {p : (ℕ × ℕ) × ℤ} (hp : p ∈ polyActIdxN P m N θ) :
    ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖
      ≤ A * (2:ℝ)^(-(m:ℝ) * polySig P) := by
  obtain ⟨hpb, hpl⟩ := Work.BourgainPlan.Maximal.mem_polyAllIdx.mp (polyActIdxN_mem_allIdx P hp)
  obtain ⟨hm1, hm2, _ha, hgcd⟩ := mem_blockPair.mp hpb
  exact hcap m p.1.1 p.1.2 p.2 hm1 hm2 hgcd hpl

/-! ## The main estimate -/

theorem polyErrMultCutN_tsum_sq_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {K : ℕ}
    (hK : ∀ (m N : ℕ), K ≤ N → 2 ^ (4 * m + 4) ≤ N → ∀ θ : ℝ,
      (Work.BourgainPlan.Oscillation.polyActIdxN P m N θ).card ≤ 1)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (N₀ : ℕ), K ≤ N₀ → 2 ^ (4 * m + 4) ≤ N₀ → ∀ θ : ℝ,
      (∑' i : ℕ, ‖Work.BourgainPlan.Oscillation.polyErrMultCutN P m N₀
          (Work.BourgainPlan.Oscillation.lacScale ρ i) θ‖ₑ ^ (2 : ℝ))
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ) * Work.BourgainPlan.Maximal.polySig P)) ^ 2 := by
  obtain ⟨A, hApos, hcap⟩ := polyWeight_cap_Icc P hc hd
  obtain ⟨K₂, hK₂⟩ := norm_polyBlockErrN_le_actIdxN P hc hd
  obtain ⟨Cer, hCerpos, hCer⟩ := polyErrValN_lacScale_summable P hd ρ hρ
  have hA0 : 0 ≤ A := le_of_lt hApos
  -- a scale beyond which `K₂ ≤ lacScale ρ i`
  have hex : ∃ i : ℕ, K₂ ≤ lacScale ρ i := by
    obtain ⟨i, hi⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually
      (Filter.eventually_ge_atTop ((K₂ : ℝ) + 1))).exists
    exact ⟨i, Nat.le_floor (by push_cast; linarith)⟩
  set I : ℕ := Nat.find hex with hIdef
  have hI : ∀ i : ℕ, I ≤ i → K₂ ≤ lacScale ρ i := by
    intro i hi
    exact le_trans (Nat.find_spec hex) (lacScale_mono ρ hρ.le hi)
  set σ : ℝ := polySig P with hσdef
  set Bd : ℝ := 2 * A * (2:ℝ)^(2*K₂+1) * ((P.leadingCoeff.toNat : ℝ) + 2) with hBddef
  refine ⟨max 1 (A^2 * Cer + (I:ℝ) * Bd^2), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro m N₀ hKN h2mN θ
  by_cases hθ : 0 < θ ∧ θ < 1
  · set x : ℝ := (2:ℝ)^(-(m:ℝ) * σ) with hxdef
    have hxpos : 0 < x := by rw [hxdef]; positivity
    have hx0 : 0 ≤ x := le_of_lt hxpos
    set S₀ : Finset ((ℕ × ℕ) × ℤ) := polyActIdxN P m N₀ θ with hS₀def
    have hS₀card : S₀.card ≤ 1 := hK m N₀ hKN h2mN θ
    set E : ℕ → ℝ := fun i => ∑ p ∈ S₀,
      polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ)) / (P.leadingCoeff:ℝ)))
        (lacScale ρ i) with hEdef
    have hE0 : ∀ i, 0 ≤ E i := by
      intro i
      simp only [hEdef]
      exact Finset.sum_nonneg (fun p _ => by unfold polyErrValN; positivity)
    -- the `E`-part is summable with sum `≤ Cer`
    have hEbound : Summable (fun i => (E i)^2) ∧ (∑' i, (E i)^2) ≤ Cer := by
      rcases Finset.eq_empty_or_nonempty S₀ with h0 | ⟨p₀, hp₀⟩
      · have hEE : ∀ i, E i = 0 := by
          intro i
          simp only [hEdef]
          rw [h0, Finset.sum_empty]
        have hz : ∀ i, (E i)^2 = 0 := fun i => by rw [hEE i]; ring
        refine ⟨(summable_congr hz).mpr summable_zero, ?_⟩
        rw [tsum_congr hz]
        simp
        linarith [hCerpos]
      · have hS₀ : S₀ = {p₀} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hp₀, fun b hb => Finset.card_le_one.mp hS₀card b hb p₀ hp₀⟩
        obtain ⟨hsum, hbnd⟩ := hCer (θ - (((p₀.1.2:ℝ)/(p₀.1.1:ℝ) + (p₀.2:ℝ))
          / (P.leadingCoeff:ℝ)))
        have hEeq : ∀ i, E i = polyErrValN P (θ - (((p₀.1.2:ℝ)/(p₀.1.1:ℝ) + (p₀.2:ℝ))
            / (P.leadingCoeff:ℝ))) (lacScale ρ i) := by
          intro i
          simp only [hEdef]
          rw [hS₀, Finset.sum_singleton]
        exact ⟨by simpa [hEeq] using hsum, by simpa [hEeq] using hbnd⟩
    -- the exceptional index set
    set badF : Finset ℕ := (Finset.range I).filter (fun i => lacScale ρ i < K₂) with hbaddef
    have hbadcard : badF.card ≤ I := by
      have h := Finset.card_le_card (Finset.filter_subset (fun i => lacScale ρ i < K₂)
        (Finset.range I))
      simpa [hbaddef] using h
    -- the pointwise bound
    have hpt : ∀ i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2
        ≤ (if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2 := by
      intro i
      by_cases hge : N₀ ≤ lacScale ρ i
      · have hEq : polyErrMultCutN P m N₀ (lacScale ρ i) θ
            = polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ :=
          polyErrMultCutN_eq_polyBlockErrN P m N₀ _ hge hθ.1 hθ.2
        rw [hEq]
        by_cases hK₂le : K₂ ≤ lacScale ρ i
        · have h1 : ‖polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ‖ ≤ A * x * E i := by
            have hbound := hK₂ m (lacScale ρ i) hK₂le (le_trans h2mN hge) θ hθ.1 hθ.2
            have hN₀1 : 1 ≤ N₀ := le_trans (Nat.one_le_two_pow) h2mN
            have hsub : polyActIdxN P m (lacScale ρ i) θ ⊆ S₀ :=
              polyActIdxN_subset_of_le P hd hN₀1 hge
            have hsum1 : ∑ p ∈ polyActIdxN P m (lacScale ρ i) θ,
                  ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat) (p.1.2 + p.2 * p.1.1)‖ *
                    polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ))
                      / (P.leadingCoeff:ℝ))) (lacScale ρ i)
                ≤ ∑ p ∈ polyActIdxN P m (lacScale ρ i) θ,
                    (A * x) * polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ))
                      / (P.leadingCoeff:ℝ))) (lacScale ρ i) := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hw := weight_le_of_mem_act P hcap hp
              have hw' : ‖polyWeight P (p.1.1 * P.leadingCoeff.toNat)
                    (p.1.2 + p.2 * p.1.1)‖ ≤ A * x := by
                rw [hxdef, hσdef]
                exact hw
              exact mul_le_mul_of_nonneg_right hw' (by unfold polyErrValN; positivity)
            have hsum2 : ∑ p ∈ polyActIdxN P m (lacScale ρ i) θ,
                    (A * x) * polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ) + (p.2:ℝ))
                      / (P.leadingCoeff:ℝ))) (lacScale ρ i)
                ≤ ∑ p ∈ S₀, (A * x) * polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ)
                      + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) (lacScale ρ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
                unfold polyErrValN; positivity)
            have hsum3 : ∑ p ∈ S₀, (A * x) * polyErrValN P (θ - (((p.1.2:ℝ)/(p.1.1:ℝ)
                    + (p.2:ℝ)) / (P.leadingCoeff:ℝ))) (lacScale ρ i) = A * x * E i := by
              simp only [hEdef]
              rw [Finset.mul_sum]
            linarith [hbound, hsum1, hsum2, hsum3]
          calc (‖polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ‖)^2
              ≤ (A * x * E i)^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
            _ = (A * x)^2 * (E i)^2 := by ring
            _ ≤ (if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2 := by
                by_cases hib : i ∈ badF <;> simp [hib] <;> positivity
        · have hlt : lacScale ρ i < K₂ := lt_of_not_ge hK₂le
          have hmK₂ : m ≤ K₂ := by
            have h1 : 2^(4*m+4) < K₂ := lt_of_le_of_lt (le_trans h2mN hge) hlt
            have h2 : m < 2^(4*m+4) := lt_of_lt_of_le Nat.lt_two_pow_self
              (Nat.pow_le_pow_right (by norm_num) (by omega))
            omega
          have hcrude : ‖polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ‖ ≤ Bd * x := by
            have h1 := norm_polyBlockErrN_le_crude P hcap (le_trans h2mN hge) θ
            have hcard : ((polyAllIdx P m).card : ℝ)
                ≤ (2:ℝ)^(2*m+1) * ((P.leadingCoeff.toNat : ℝ) + 2) := by
              have h := card_polyAllIdx_le P hc m
              have h' : ((polyAllIdx P m).card : ℝ)
                  ≤ ((2^(2*m+1) * (P.leadingCoeff.toNat + 2) : ℕ) : ℝ) := by exact_mod_cast h
              simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add]
                using h'
            have hpw : (2:ℝ)^(2*m+1) ≤ (2:ℝ)^(2*K₂+1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have hc0 : (0:ℝ) ≤ (P.leadingCoeff.toNat : ℝ) + 2 := by positivity
            calc ‖polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ‖
                ≤ 2 * A * (2:ℝ)^(-(m:ℝ) * polySig P) * ((polyAllIdx P m).card : ℝ) := h1
              _ ≤ 2 * A * (2:ℝ)^(-(m:ℝ) * polySig P)
                    * ((2:ℝ)^(2*m+1) * ((P.leadingCoeff.toNat : ℝ) + 2)) :=
                  mul_le_mul_of_nonneg_left hcard (by positivity)
              _ ≤ Bd * x := by
                  rw [hBddef, hxdef, hσdef]
                  calc 2 * A * (2:ℝ) ^ (-(m:ℝ) * polySig P)
                        * ((2:ℝ) ^ (2 * m + 1) * ((P.leadingCoeff.toNat : ℝ) + 2))
                      ≤ 2 * A * (2:ℝ) ^ (-(m:ℝ) * polySig P)
                        * ((2:ℝ) ^ (2 * K₂ + 1) * ((P.leadingCoeff.toNat : ℝ) + 2)) :=
                        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpw hc0)
                          (by positivity)
                    _ = 2 * A * (2:ℝ) ^ (2 * K₂ + 1) * ((P.leadingCoeff.toNat : ℝ) + 2)
                        * (2:ℝ) ^ (-(m:ℝ) * polySig P) := by ring
          have hiI : i < I := not_le.mp (fun hcon => (not_le.mpr hlt) (hI i hcon))
          have hib : i ∈ badF := by
            rw [hbaddef, Finset.mem_filter, Finset.mem_range]
            exact ⟨hiI, hlt⟩
          calc (‖polyBlockErrN P m (lacScale ρ i) (lacScale ρ i) θ‖)^2
              ≤ (Bd * x)^2 := pow_le_pow_left₀ (norm_nonneg _) hcrude 2
            _ ≤ (if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2 := by
                rw [if_pos hib]
                nlinarith [sq_nonneg (A * x * E i), sq_nonneg (Bd * x)]
      · have hzero : polyErrMultCutN P m N₀ (lacScale ρ i) θ = 0 := by
          unfold polyErrMultCutN
          rw [if_neg (not_le.mpr (not_le.mp hge))]
        rw [hzero]
        have h2 : (0:ℝ) ≤ (if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2 := by
          by_cases hib : i ∈ badF
          · rw [if_pos hib]; positivity
          · rw [if_neg hib]; positivity
        simpa using h2
    -- summability and the bound
    have hsumG : Summable (fun i : ℕ =>
        (if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2) := by
      refine Summable.add ?_ (hEbound.1.mul_left _)
      refine summable_of_ne_finset_zero (s := badF) (fun i hi => ?_)
      rw [if_neg hi]
    have hsumF : Summable (fun i : ℕ => (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2) :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _) hpt hsumG
    have htsumE : (∑' i : ℕ, ((if i ∈ badF then (Bd * x)^2 else 0)
        + (A * x)^2 * (E i)^2))
        = (badF.card : ℝ) * (Bd * x)^2 + (A * x)^2 * (∑' i, (E i)^2) := by
      have hs1 : Summable (fun i : ℕ => if i ∈ badF then (Bd * x)^2 else 0) :=
        summable_of_ne_finset_zero (s := badF) (fun i hi => by rw [if_neg hi])
      have hs2 : Summable (fun i : ℕ => (A * x)^2 * (E i)^2) := hEbound.1.mul_left _
      rw [hs1.tsum_add hs2, tsum_mul_left, tsum_ite_mem_finset]
    have hmain : (∑' i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2)
        ≤ (max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x)^2 := by
      have h1 : (∑' i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2)
          ≤ ∑' i : ℕ, ((if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2) :=
        Summable.tsum_le_tsum hpt hsumF hsumG
      have h6 : (badF.card : ℝ) * (Bd * x)^2 + (A * x)^2 * Cer
          ≤ (max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x)^2 := by
        have h4 : ((badF.card : ℝ)) ≤ (I : ℝ) := by exact_mod_cast hbadcard
        have hcardle : (badF.card : ℝ) * (Bd * x)^2 ≤ (I:ℝ) * (Bd * x)^2 :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
        have hmax : A^2 * Cer + (I:ℝ) * Bd^2 ≤ max 1 (A^2 * Cer + (I:ℝ) * Bd^2) :=
          le_max_right _ _
        have hmax1 : 1 ≤ max 1 (A^2 * Cer + (I:ℝ) * Bd^2) := le_max_left _ _
        have hmax0 : 0 ≤ max 1 (A^2 * Cer + (I:ℝ) * Bd^2) := le_trans zero_le_one hmax1
        have hBd0 : 0 ≤ Bd := by rw [hBddef]; positivity
        have step2 : (I:ℝ) * (Bd * x)^2 + (A * x)^2 * Cer
            = (A^2 * Cer + (I:ℝ) * Bd^2) * x^2 := by ring
        have hM2 : max 1 (A^2 * Cer + (I:ℝ) * Bd^2) ≤ (max 1 (A^2 * Cer + (I:ℝ) * Bd^2))^2 := by
          nlinarith [hmax1, hmax0]
        calc (badF.card : ℝ) * (Bd * x)^2 + (A * x)^2 * Cer
            ≤ (I:ℝ) * (Bd * x)^2 + (A * x)^2 * Cer := by linarith [hcardle]
          _ = (A^2 * Cer + (I:ℝ) * Bd^2) * x^2 := step2
          _ ≤ max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x^2 :=
              mul_le_mul_of_nonneg_right hmax (sq_nonneg x)
          _ ≤ (max 1 (A^2 * Cer + (I:ℝ) * Bd^2))^2 * x^2 :=
              mul_le_mul_of_nonneg_right hM2 (sq_nonneg x)
          _ = (max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x)^2 := by ring
      calc (∑' i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2)
          ≤ ∑' i : ℕ, ((if i ∈ badF then (Bd * x)^2 else 0) + (A * x)^2 * (E i)^2) := h1
        _ = (badF.card : ℝ) * (Bd * x)^2 + (A * x)^2 * (∑' i, (E i)^2) := htsumE
        _ ≤ (badF.card : ℝ) * (Bd * x)^2 + (A * x)^2 * Cer := by
            refine add_le_add le_rfl ?_
            exact mul_le_mul_of_nonneg_left hEbound.2 (by positivity)
        _ ≤ (max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x)^2 := h6
    have hLHS : (∑' i : ℕ, ‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖ₑ ^ (2 : ℝ))
        = ENNReal.ofReal (∑' i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hsumF]
      refine tsum_congr (fun i => ?_)
      have h1 : ‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖ₑ
          = ENNReal.ofReal ‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖ := by simp
      rw [h1, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    calc (∑' i : ℕ, ‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖ₑ ^ (2 : ℝ))
        = ENNReal.ofReal (∑' i : ℕ, (‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖)^2) := hLHS
      _ ≤ ENNReal.ofReal ((max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x)^2) :=
          ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (max 1 (A^2 * Cer + (I:ℝ) * Bd^2) * x) ^ 2 :=
          ENNReal.ofReal_pow (by positivity) 2
      _ = ENNReal.ofReal (max 1 (A^2 * Cer + (I:ℝ) * Bd^2)
            * (2:ℝ)^(-(m:ℝ) * Work.BourgainPlan.Maximal.polySig P)) ^ 2 := by
          rw [hxdef, hσdef]
  · have hterm : ∀ i : ℕ, polyErrMultCutN P m N₀ (lacScale ρ i) θ = 0 :=
      fun i => polyErrMultCutN_eq_zero P m N₀ _ hθ
    rw [show (∑' i : ℕ, ‖polyErrMultCutN P m N₀ (lacScale ρ i) θ‖ₑ ^ (2 : ℝ))
        = ∑' _i : ℕ, (0 : ℝ≥0∞) by
      refine tsum_congr (fun i => ?_)
      rw [hterm i]
      simp]
    simp

end

end Work.BourgainPlan.Oscillation
