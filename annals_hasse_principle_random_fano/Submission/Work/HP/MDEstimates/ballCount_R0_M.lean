import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.ball_count_R0

/-!
# `Work.HP.MDEstimates.ballCount_R0_M`

The lattice point count of Browning--Le Boudec--Sawin, *The Hasse principle for random Fano
hypersurfaces* (Annals 2023), Lemma R0, in the form needed for the "M" (short-vector) reduction:
for a lattice `L` of rank `R` with successive minima `λ₁ ≤ … ≤ λ_R`, a parameter `M` with
`2M ≤ λ₁`, and `Y ≥ λ_R ≥ T`,

`#{v ∈ L : ‖v‖ ≤ T} ≪_R T^{R-j} Y^j / det L + (T/M)^{R-1-j}`.

The sharper second term `(T/M)^{R-1-j}` (compare `MDEstimates.ball_count_R0`, where `M = 1`) is
what the reduction step needs.  We split the Schmidt-type sum `∑_k T^k / ∏_{i<k} λ_{i+1}` at
`k = R - j`: the head is dominated by `(T/(2M))^k` because `λ_i ≥ 2M`, and the tail by the
determinant term exactly as in `MDEstimates.sum_le_target`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.MDEstimates

open Work.HP

/-- Arithmetic core of the head estimate: if `0 < M ≤ T` then for `k ≤ m`,
`(T/(2M))^k ≤ (T/M)^m`. -/
lemma pow_div_two_le {M T : ℝ} (hMpos : 0 < M) (hMT : M ≤ T) {k m : ℕ} (hkm : k ≤ m) :
    (T / (2 * M)) ^ k ≤ (T / M) ^ m := by
  have hTpos : 0 < T := lt_of_lt_of_le hMpos hMT
  have hTM1 : 1 ≤ T / M := by rw [le_div_iff₀ hMpos]; linarith
  have h2Mpos : 0 < 2 * M := by linarith
  have htab : T / (2 * M) ≤ T / M := by
    exact div_le_div_of_nonneg_left hTpos.le hMpos (by linarith)
  rcases lt_or_ge (T / (2 * M)) 1 with ha | ha
  · calc (T / (2 * M)) ^ k ≤ 1 := pow_le_one₀ (div_nonneg hTpos.le h2Mpos.le) ha.le
      _ ≤ (T / M) ^ m := one_le_pow₀ hTM1
  · calc (T / (2 * M)) ^ k ≤ (T / (2 * M)) ^ m := pow_le_pow_right₀ ha hkm
      _ ≤ (T / M) ^ m := pow_le_pow_left₀ (le_trans zero_le_one ha) htab m

/-- **Schmidt's sum bound with a short-vector parameter `M`.**  Generalises
`Work.HP.MDEstimates.sum_le_target` (the case `M = 1`): under `2M ≤ λ₁`, the sum
`∑_{k ≤ R} T^k / ∏_{i<k} λ_{i+1}` is bounded by `K (T^{R-j} Y^j / det L + (T/M)^{R-1-j})`. -/
theorem sum_le_target_M {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (R j : ℕ) (M Y T : ℝ),
      rk L = R → 2 ≤ R → j ≤ R - 1 → 1 ≤ T → M ≤ T → T ≤ Y → lam L R ≤ Y →
      0 < detL L → detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1) → 0 < M → 2 * M ≤ lam L 1 →
      (∑ k ∈ Finset.range (R + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
        ≤ K * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j)) := by
  refine ⟨2 * (Fintype.card ι : ℝ) + 1, by positivity, ?_⟩
  intro L R j M Y T hrk hR hj hT hMT hTY hlamR hdet hdetle hMpos h2M
  have hRrk : R ≤ rk L := by rw [hrk]
  have hcard : (R : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have h := rk_le_card L; rw [hrk] at h; exact_mod_cast h
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hYnn : 0 ≤ Y := le_trans hTpos.le hTY
  have hlampos : ∀ i, 1 ≤ i → i ≤ R → 0 < lam L i := fun i hi1 hiR =>
    lt_of_lt_of_le one_pos (one_le_lam L hi1 (by rw [hrk]; exact hiR))
  have hlamle : ∀ i, i ≤ R → lam L i ≤ Y := fun i hi =>
    le_trans (lam_mono L hi hRrk) hlamR
  have hPpos : ∀ k, k ≤ R → 0 < ∏ i ∈ Finset.range k, lam L (i + 1) := by
    intro k hk
    refine Finset.prod_pos fun i hi => ?_
    exact hlampos (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  set f : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) with hf
  have hsplit : ∑ k ∈ Finset.range (R + 1), f k
      = (∑ k ∈ Finset.range (R - j), f k)
        + (∑ k ∈ Finset.range (j + 1), f ((R - j) + k)) := by
    have h : R + 1 = (R - j) + (j + 1) := by omega
    rw [h, Finset.sum_range_add]
  rw [hsplit]
  -- Head: `k ≤ R - 1 - j`, each term at most `(T/M)^{R-1-j}` because `λ_i ≥ 2M`.
  have hfirst : ∑ k ∈ Finset.range (R - j), f k ≤ (R : ℝ) * (T / M) ^ (R - 1 - j) := by
    have h1 : ∀ k ∈ Finset.range (R - j), f k ≤ (T / M) ^ (R - 1 - j) := by
      intro k hk
      have hkR : k ≤ R - 1 - j := by have h1 := Finset.mem_range.mp hk; omega
      have hprod_ge : (2 * M) ^ k ≤ ∏ i ∈ Finset.range k, lam L (i + 1) := by
        have hbase : (∏ _i ∈ Finset.range k, (2 * M)) ≤ ∏ i ∈ Finset.range k, lam L (i + 1) :=
          Finset.prod_le_prod₀ (fun i _ => le_of_lt (by linarith : (0:ℝ) < 2 * M))
            (fun i hi => by
              have hi' : i < k := Finset.mem_range.mp hi
              exact le_trans h2M (lam_mono L (by omega) (by rw [hrk]; omega)))
        simpa [Finset.prod_const, Finset.card_range] using hbase
      have h2Mpow : 0 < (2 * M) ^ k := pow_pos (by linarith) k
      have hfk : f k ≤ (T / (2 * M)) ^ k := by
        rw [hf]; simp only; rw [div_pow]
        exact div_le_div_of_nonneg_left (pow_nonneg hTpos.le k) h2Mpow hprod_ge
      exact le_trans hfk (pow_div_two_le hMpos hMT hkR)
    calc ∑ k ∈ Finset.range (R - j), f k
        ≤ ∑ _k ∈ Finset.range (R - j), (T / M) ^ (R - 1 - j) := Finset.sum_le_sum h1
      _ = ((R - j : ℕ) : ℝ) * (T / M) ^ (R - 1 - j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (R : ℝ) * (T / M) ^ (R - 1 - j) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (div_nonneg hTpos.le hMpos.le) _)
          exact_mod_cast Nat.sub_le R j
  -- Tail: `k ≥ R - j`, each term at most `T^{R-j} Y^j / det L`.
  have hsecond : ∑ k ∈ Finset.range (j + 1), f ((R - j) + k)
      ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
    have h2 : ∀ k ∈ Finset.range (j + 1), f ((R - j) + k) ≤ T ^ (R - j) * Y ^ j / detL L := by
      intro k hk
      have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
      set m : ℕ := (R - j) + k with hm
      have hmge : R - j ≤ m := by omega
      have hmR : m ≤ R := by omega
      have hfac : ∏ i ∈ Finset.range R, lam L (i + 1)
          = (∏ i ∈ Finset.range m, lam L (i + 1))
            * ∏ i ∈ Finset.range (R - m), lam L (i + m + 1) := by
        have h := Finset.prod_range_add (fun i => lam L (i + 1)) m (R - m)
        rw [Nat.add_sub_of_le hmR] at h
        rw [h]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by congr 1; omega
      have htail : ∏ i ∈ Finset.range (R - m), lam L (i + m + 1) ≤ Y ^ (R - m) := by
        have h0 : ∀ i ∈ Finset.range (R - m), (0 : ℝ) ≤ lam L (i + m + 1) := by
          intro i hi
          exact le_of_lt (hlampos (i + m + 1) (by omega) (by have := Finset.mem_range.mp hi; omega))
        have h1 : ∀ i ∈ Finset.range (R - m), lam L (i + m + 1) ≤ Y := by
          intro i hi
          exact hlamle (i + m + 1) (by have := Finset.mem_range.mp hi; omega)
        calc ∏ i ∈ Finset.range (R - m), lam L (i + m + 1)
            ≤ ∏ _i ∈ Finset.range (R - m), Y := Finset.prod_le_prod₀ h0 h1
          _ = Y ^ (R - m) := by rw [Finset.prod_const, Finset.card_range]
      have hdetm : detL L ≤ (∏ i ∈ Finset.range m, lam L (i + 1)) * Y ^ (R - m) := by
        rw [hfac] at hdetle
        exact le_trans hdetle (mul_le_mul_of_nonneg_left htail (le_of_lt (hPpos m hmR)))
      have hstep : f m = T ^ m / (∏ i ∈ Finset.range m, lam L (i + 1)) := by simp only [hf]
      rw [hstep]
      have hle1 : T ^ m / (∏ i ∈ Finset.range m, lam L (i + 1))
          ≤ T ^ m * Y ^ (R - m) / detL L := by
        rw [div_le_div_iff₀ (hPpos m hmR) hdet]
        calc T ^ m * detL L
            ≤ T ^ m * ((∏ i ∈ Finset.range m, lam L (i + 1)) * Y ^ (R - m)) :=
              mul_le_mul_of_nonneg_left hdetm (pow_nonneg hTpos.le m)
          _ = T ^ m * Y ^ (R - m) * ∏ i ∈ Finset.range m, lam L (i + 1) := by ring
      refine le_trans hle1 (div_le_div_of_nonneg_right ?_ hdet.le)
      have hkey : T ^ (m - (R - j)) ≤ Y ^ (m - (R - j)) :=
        pow_le_pow_left₀ (le_of_lt hTpos) hTY _
      have hexp : T ^ m * Y ^ (R - m) ≤ T ^ (R - j) * Y ^ j := by
        have h1 : T ^ (R - j) * T ^ (m - (R - j)) = T ^ m := by
          rw [← pow_add]; congr 1; omega
        have h2 : Y ^ (m - (R - j)) * Y ^ (R - m) = Y ^ j := by
          rw [← pow_add]; congr 1; omega
        calc T ^ m * Y ^ (R - m)
            = T ^ (R - j) * (T ^ (m - (R - j)) * Y ^ (R - m)) := by
              rw [← h1]; ring
          _ ≤ T ^ (R - j) * (Y ^ (m - (R - j)) * Y ^ (R - m)) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hTpos.le _)
              exact mul_le_mul_of_nonneg_right hkey (pow_nonneg hYnn _)
          _ = T ^ (R - j) * Y ^ j := by rw [h2]
      exact hexp
    calc ∑ k ∈ Finset.range (j + 1), f ((R - j) + k)
        ≤ ∑ _k ∈ Finset.range (j + 1), T ^ (R - j) * Y ^ j / detL L := Finset.sum_le_sum h2
      _ = ((j + 1 : ℕ) : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
          refine mul_le_mul_of_nonneg_right ?_
            (div_nonneg (mul_nonneg (pow_nonneg hTpos.le _) (pow_nonneg hYnn _)) hdet.le)
          have : j + 1 ≤ R := by omega
          exact_mod_cast this
  calc (∑ k ∈ Finset.range (R - j), f k) + (∑ k ∈ Finset.range (j + 1), f ((R - j) + k))
      ≤ (R : ℝ) * (T / M) ^ (R - 1 - j) + (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) :=
        add_le_add hfirst hsecond
    _ = (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j)) := by ring
    _ ≤ (2 * (Fintype.card ι : ℝ) + 1) * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j)) := by
        refine mul_le_mul_of_nonneg_right (by linarith [hcard]) ?_
        exact add_nonneg
          (div_nonneg (mul_nonneg (pow_nonneg hTpos.le _) (pow_nonneg hYnn _)) hdet.le)
          (pow_nonneg (div_nonneg hTpos.le hMpos.le) _)

theorem ballCount_R0_M {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (R j : ℕ) (M Y T : ℝ),
      rk L = R → 2 ≤ R → j ≤ R - 1 → 1 ≤ T → M ≤ T → T ≤ Y → lam L R ≤ Y →
      0 < detL L → detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1) →
      0 < M → 2 * M ≤ lam L 1 →
      (ballCount L T : ℝ) ≤ K * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j)) := by
  obtain ⟨K1, hK1pos, hK1⟩ := ballCount_sum_bound (ι := ι) (Fintype.card ι)
  obtain ⟨K2, hK2pos, hK2⟩ := sum_le_target_M (ι := ι)
  refine ⟨K1 * K2, mul_pos hK1pos hK2pos, ?_⟩
  intro L R j M Y T hrk hR hj hT hMT hTY hlamR hdet hdetle hMpos h2M
  have h1 := hK1 L (rk_le_card L) T hT
  rw [hrk] at h1
  have h2 := hK2 L R j M Y T hrk hR hj hT hMT hTY hlamR hdet hdetle hMpos h2M
  calc (ballCount L T : ℝ)
      ≤ K1 * ∑ k ∈ Finset.range (R + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := h1
    _ ≤ K1 * (K2 * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j))) :=
        mul_le_mul_of_nonneg_left h2 hK1pos.le
    _ = K1 * K2 * (T ^ (R - j) * Y ^ j / detL L + (T / M) ^ (R - 1 - j)) := by ring

end Work.HP.MDEstimates
