import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.pair_counts
import Submission.Work.HP.Sig2.ellXY_pair_le
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.CountXYD3_shell_data
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.CountXYD3_shell_bound
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.CountXYD3_final_arith
import Submission.Work.HP.MDEstimates.Sigma2_44_I_lo_aux.CountXYD3_cover

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

open Work.HP

/-- The dyadic shell of pairs `(x,y)` whose two norms lie in the dyadic boxes `2^q.1`, `2^q.2`
and whose `𝔡₃` is at most `4Δ/2^{q.1+q.2}`.  This is the set whose cardinality is the pair count
`ℓ_{3,4}(2^{q.1},2^{q.2}; 4Δ/2^{q.1+q.2})`. -/
def shellSet (Δ : ℝ) (q : ℕ × ℕ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | LinearIndependent ℤ ![p.1, p.2] ∧
       eNorm p.1 ≤ (2:ℝ) ^ q.1 ∧ eNorm p.2 ≤ (2:ℝ) ^ q.2 ∧
       dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ 4 * Δ / (2:ℝ) ^ (q.1 + q.2)}

/-- The dyadic index of a pair, read off from the ceilings of the logarithms of the norms. -/
def shellIdx (p : (Fin 5 → ℤ) × (Fin 5 → ℤ)) : ℕ × ℕ :=
  (⌈Real.logb 2 (eNorm p.1)⌉₊, ⌈Real.logb 2 (eNorm p.2)⌉₊)

/-- The finite set of admissible dyadic indices `{(k,l) : k + l ≤ M}`. -/
def idxFinset (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter (fun q => q.1 + q.2 ≤ M)

theorem shellSet_finite (Δ : ℝ) (q : ℕ × ℕ) : (shellSet Δ q).Finite := by
  refine Set.Finite.subset
    ((MDBasic.finite_eNorm_le (ι := Fin 5) ((2:ℝ) ^ q.1)).prod
      (MDBasic.finite_eNorm_le (ι := Fin 5) ((2:ℝ) ^ q.2))) ?_
  intro p hp
  exact ⟨hp.2.1, hp.2.2.1⟩

theorem shellSet_ncard (Δ : ℝ) (q : ℕ × ℕ) :
    (shellSet Δ q).ncard
      = ellXY 4 3 ((2:ℝ) ^ q.1) ((2:ℝ) ^ q.2) (4 * Δ / (2:ℝ) ^ (q.1 + q.2)) := rfl

theorem idxFinset_card_le (M : ℕ) : (idxFinset M).card ≤ (M + 1) ^ 2 := by
  calc (idxFinset M).card
      ≤ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).card := Finset.card_filter_le _ _
    _ = (M + 1) * (M + 1) := by rw [Finset.card_product, Finset.card_range]
    _ = (M + 1) ^ 2 := by ring

theorem two_pow_floor_logb_le (Δ : ℝ) (hΔ : 1 ≤ Δ) :
    (2:ℝ) ^ (⌊Real.logb 2 (4 * Δ)⌋₊) ≤ 4 * Δ := by
  have hlog0 : (0:ℝ) ≤ Real.logb 2 (4 * Δ) := Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 (4 * Δ) := Nat.floor_le hlog0
  calc (2:ℝ) ^ (⌊Real.logb 2 (4 * Δ)⌋₊)
      = (2:ℝ) ^ ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    _ ≤ (2:ℝ) ^ (Real.logb 2 (4 * Δ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 4 * Δ := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)

theorem CountXYD3 :
    ∃ K : ℝ, 0 < K ∧ ∀ B Δ : ℝ, 1 ≤ B → 1 ≤ Δ →
      (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
          p ∈ Work.HP.Omega 4 4 B ∧
          Work.HP.eNorm p.1 * Work.HP.eNorm p.2 *
            Work.HP.dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ}.ncard : ℝ)) ≤ K * Δ ^ 4 := by
  obtain ⟨C, hCpos, hC⟩ := CountXYD3_shell_bound
  obtain ⟨K, hKpos, hK⟩ := CountXYD3_final_arith C hCpos
  refine ⟨K, hKpos, ?_⟩
  intro B Δ hB hΔ
  set M : ℕ := ⌊Real.logb 2 (4 * Δ)⌋₊ with hMdef
  set S : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
    {p | p ∈ Work.HP.Omega 4 4 B ∧
      Work.HP.eNorm p.1 * Work.HP.eNorm p.2 *
        Work.HP.dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ} with hSdef
  have hSfin : S.Finite := by
    refine (MDBasic.finite_sets 4 4 0 B (fun _ => True)).2.2.subset ?_
    intro p hp
    rw [hSdef] at hp
    exact hp.1
  have hM2 : (2:ℝ) ^ M ≤ 4 * Δ := by
    rw [hMdef]
    exact two_pow_floor_logb_le Δ hΔ
  have hqle : ∀ q ∈ idxFinset M, q.1 + q.2 ≤ M := by
    intro q hq
    unfold idxFinset at hq
    rw [Finset.mem_filter] at hq
    exact hq.2
  have hmap : ∀ p ∈ S, shellIdx p ∈ idxFinset M := by
    intro p hp
    rw [hSdef] at hp
    obtain ⟨hpOm, hpprod⟩ := hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := CountXYD3_shell_data B Δ hB hΔ p hpOm hpprod
    unfold idxFinset
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) h5)
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (le_trans (Nat.le_add_left _ _) h5)
    · exact h5
  have hsub : ∀ q ∈ idxFinset M, ∀ p ∈ S, shellIdx p = q → p ∈ shellSet Δ q := by
    intro q hq p hp hpq
    rw [hSdef] at hp
    obtain ⟨hpOm, hpprod⟩ := hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := CountXYD3_shell_data B Δ hB hΔ p hpOm hpprod
    have hq1 : q.1 = ⌈Real.logb 2 (eNorm p.1)⌉₊ := by
      have h := congrArg Prod.fst hpq
      simpa [shellIdx] using h.symm
    have hq2 : q.2 = ⌈Real.logb 2 (eNorm p.2)⌉₊ := by
      have h := congrArg Prod.snd hpq
      simpa [shellIdx] using h.symm
    refine ⟨Work.HP.Sig2.li_of_mem_Omega 4 4 B p hpOm, ?_, ?_, ?_⟩
    · rw [hq1]; exact h1
    · rw [hq2]; exact h2
    · rw [hq1, hq2]; exact h3
  have hcover := CountXYD3_cover S (idxFinset M) (shellSet Δ) shellIdx hSfin
    (fun q _ => shellSet_finite Δ q) hmap hsub
  have hterm : ∀ q ∈ idxFinset M,
      ((shellSet Δ q).ncard : ℝ) ≤ C * Δ ^ 3 * Real.log (8 * Δ) ^ 2 := by
    intro q hq
    rw [shellSet_ncard Δ q]
    exact hC Δ hΔ q
      (le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (hqle q hq)) hM2)
  have hsum : (((∑ q ∈ idxFinset M, (shellSet Δ q).ncard) : ℕ) : ℝ)
      ≤ (((idxFinset M).card : ℕ) : ℝ) * (C * Δ ^ 3 * Real.log (8 * Δ) ^ 2) := by
    push_cast
    calc ∑ q ∈ idxFinset M, ((shellSet Δ q).ncard : ℝ)
        ≤ ∑ q ∈ idxFinset M, C * Δ ^ 3 * Real.log (8 * Δ) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (((idxFinset M).card : ℕ) : ℝ) * (C * Δ ^ 3 * Real.log (8 * Δ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((idxFinset M).card : ℕ) : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by
    have h1 : (idxFinset M).card ≤ (M + 1) ^ 2 := idxFinset_card_le M
    calc (((idxFinset M).card : ℕ) : ℝ) ≤ (((M + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
  have hΔ0 : (0:ℝ) < Δ := by linarith
  have hCΔ : 0 ≤ C * Δ ^ 3 * Real.log (8 * Δ) ^ 2 := by
    have h1 : (0:ℝ) ≤ Real.log (8 * Δ) := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg hCpos.le (pow_nonneg hΔ0.le 3)) (sq_nonneg _)
  have hcoverR : (S.ncard : ℝ)
      ≤ (((∑ q ∈ idxFinset M, (shellSet Δ q).ncard) : ℕ) : ℝ) := by
    exact_mod_cast hcover
  calc (S.ncard : ℝ)
      ≤ (((∑ q ∈ idxFinset M, (shellSet Δ q).ncard) : ℕ) : ℝ) := hcoverR
    _ ≤ (((idxFinset M).card : ℕ) : ℝ) * (C * Δ ^ 3 * Real.log (8 * Δ) ^ 2) := hsum
    _ ≤ ((M : ℝ) + 1) ^ 2 * (C * Δ ^ 3 * Real.log (8 * Δ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hCΔ
    _ = C * Δ ^ 3 * Real.log (8 * Δ) ^ 2 * ((⌊Real.logb 2 (4 * Δ)⌋₊ : ℝ) + 1) ^ 2 := by
          rw [hMdef]; ring
    _ ≤ K * Δ ^ 4 := hK Δ hΔ

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
