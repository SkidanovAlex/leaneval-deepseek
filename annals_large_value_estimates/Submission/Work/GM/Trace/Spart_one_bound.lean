import Mathlib
import Submission.Work.GM.Trace.Spart_defs
import Submission.Work.GM.Trace.sep_card_le
import Submission.Work.GM.Trace.Iterm_bound_large
import Submission.Work.GM.Trace.Iterm_bound_small
import Submission.Work.GM.Trace.rho_sum_pow_le
import Submission.Work.GM.Trace.rho_card_le
import Submission.Work.GM.Trace.final_arith

/-!
# GM Proposition 5.1: `S₁` is negligible

Assembles `Work.GM.Trace.Spart_one_bound` from
* `Iterm_bound_large`, `Iterm_bound_small` -- the two pointwise bounds for a single `I_m`
  (`m` with exactly one non-zero coordinate), in the regimes `|rho m| > X` resp. `≤ X`;
* `rho_card_le`, `rho_sum_pow_le` -- the counting bounds for the finite index sets;
* `sep_card_le` -- `|W| ≤ M N + 1`;
* `final_arith` -- the final elementary estimate giving `≤ 1` for `N ≥ N₀`.
-/

namespace Work.GM.Trace

open Submission.GM
open scoped BigOperators

-- ==== the finite sum bound ====

private theorem finite_sum_bound (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (T δ X : ℝ) (j : ℕ)
    (hT1 : 1 ≤ T) (hδ1 : 1 ≤ δ) (hX1 : 1 ≤ X) (hj : 2 ≤ j)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|)
    (Cd Cz : ℝ) (hCd : 0 ≤ Cd) (hCz : 0 ≤ Cz)
    (hdecc : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hhat t ξ‖ ≤ Cd * (1 + |t|) ^ j / |ξ| ^ j)
    (hzeroc : ∀ t : ℝ, 1 ≤ |t| → ‖hhat t 0‖ ≤ Cz / |t| ^ j)
    (hAzc : ∀ t ξ : ℝ, ‖hhat t ξ‖ ≤ Azero)
    (s : Finset (ℤ × ℤ × ℤ)) (hs : ∀ m ∈ s, nzCount m = 1) :
    ∑ m ∈ s, ‖Iterm N W m‖ ≤
      27 * X ^ 3 * ((N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j +
          2 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j) +
        24 * ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cd * (1 + T) ^ j / (N : ℝ) ^ j) /
          X ^ (j - 1) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNj : (0 : ℝ) < (N : ℝ) ^ j := pow_pos hNpos j
  have hdm : (0 : ℝ) < δ ^ j := pow_pos (lt_of_lt_of_le zero_lt_one hδ1) j
  have hXpow : (0 : ℝ) < X ^ (j - 1) := pow_pos (lt_of_lt_of_le zero_lt_one hX1) _
  have hAz0 : (0 : ℝ) ≤ Azero := Azero_nonneg
  have hw0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  rw [← Finset.sum_filter_add_sum_filter_not s (fun m => |(rho m : ℝ)| ≤ X)
      (fun m => ‖Iterm N W m‖)]
  apply add_le_add
  · -- ============ small part ============
    set B : ℝ := (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j +
          2 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j with hB
    have hBnn : 0 ≤ B := by rw [hB]; positivity
    have hpoint : ∀ m ∈ s.filter (fun m => |(rho m : ℝ)| ≤ X), ‖Iterm N W m‖ ≤ B := by
      intro m hm
      obtain ⟨hms, -⟩ := Finset.mem_filter.mp hm
      have hm1 : nzCount m = 1 := hs m hms
      have hb := Iterm_bound_small N hN W δ hδ1 hsep j Cd Cz hCd hCz hdecc hzeroc hAzc m hm1
      have hge1 : (1 : ℝ) ≤ |(rho m : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast one_le_abs_rho m hm1
      have hpow1 : (1 : ℝ) ≤ |(rho m : ℝ)| ^ j := one_le_pow₀ hge1
      have hle : (W.card : ℝ) * Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) ≤
          (W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j := by
        apply div_le_div_of_nonneg_left (by positivity) hNj
        calc (N : ℝ) ^ j = 1 * (N : ℝ) ^ j := (one_mul _).symm
          _ ≤ |(rho m : ℝ)| ^ j * (N : ℝ) ^ j :=
              mul_le_mul_of_nonneg_right hpow1 (le_of_lt hNj)
      rw [hB]
      have hsum2 : (W.card : ℝ) * Azero ^ 2 * Cd / (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) +
            2 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j ≤
          (W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j +
            2 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j := by linarith
      calc ‖Iterm N W m‖
          ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) * Azero ^ 2 * Cd /
              (|(rho m : ℝ)| ^ j * (N : ℝ) ^ j) +
            2 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j) := hb
        _ ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j +
            2 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j) :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
        _ = (N : ℝ) ^ 3 * (W.card : ℝ) * Azero ^ 2 * Cd / (N : ℝ) ^ j +
            2 * (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cz / δ ^ j := by ring
    have hsum_le : ∑ m ∈ s.filter (fun m => |(rho m : ℝ)| ≤ X), ‖Iterm N W m‖ ≤
        B * ((s.filter (fun m => |(rho m : ℝ)| ≤ X)).card : ℝ) := by
      calc ∑ m ∈ s.filter (fun m => |(rho m : ℝ)| ≤ X), ‖Iterm N W m‖
          ≤ ∑ _m ∈ s.filter (fun m => |(rho m : ℝ)| ≤ X), B := Finset.sum_le_sum hpoint
        _ = B * ((s.filter (fun m => |(rho m : ℝ)| ≤ X)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hcard : ((s.filter (fun m => |(rho m : ℝ)| ≤ X)).card : ℝ) ≤ 27 * X ^ 3 := by
      apply rho_card_le X hX1
      · intro m hm; exact hs m (Finset.mem_of_mem_filter m hm)
      · intro m hm; exact (Finset.mem_filter.mp hm).2
    calc ∑ m ∈ s.filter (fun m => |(rho m : ℝ)| ≤ X), ‖Iterm N W m‖
        ≤ B * ((s.filter (fun m => |(rho m : ℝ)| ≤ X)).card : ℝ) := hsum_le
      _ ≤ B * (27 * X ^ 3) := mul_le_mul_of_nonneg_left hcard hBnn
      _ = 27 * X ^ 3 * B := by ring
  · -- ============ large part ============
    set c3 : ℝ := (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cd * (1 + T) ^ j / (N : ℝ) ^ j
      with hc3
    have hc3nn : 0 ≤ c3 := by rw [hc3]; positivity
    have hrho0 : ∀ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)), (rho m : ℝ) ≠ 0 := by
      intro m hm
      have hm1 : nzCount m = 1 := hs m (Finset.mem_of_mem_filter m hm)
      exact_mod_cast rho_ne_zero m hm1
    have hpoint : ∀ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)),
        ‖Iterm N W m‖ ≤ c3 * (1 / |(rho m : ℝ)| ^ j) := by
      intro m hm
      obtain ⟨hms, -⟩ := Finset.mem_filter.mp hm
      have hm1 : nzCount m = 1 := hs m hms
      have hb := Iterm_bound_large N hN W T (le_trans zero_le_one hT1) hW j Cd hCd hdecc hAzc
        m hm1
      have hr : (rho m : ℝ) ≠ 0 := by exact_mod_cast rho_ne_zero m hm1
      have hden : |(rho m : ℝ)| ^ j * (N : ℝ) ^ j ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (abs_ne_zero.mpr hr)) (ne_of_gt hNj)
      rw [hc3]
      refine hb.trans (le_of_eq ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    have hsum_le : ∑ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)), ‖Iterm N W m‖ ≤
        c3 * ∑ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)),
          1 / |(rho m : ℝ)| ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    have hsum2 : ∑ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)),
        (1 : ℝ) / |(rho m : ℝ)| ^ j ≤ 24 / X ^ (j - 1) := by
      apply rho_sum_pow_le j hj X hX1
      · intro m hm; exact hs m (Finset.mem_of_mem_filter m hm)
      · intro m hm
        exact not_le.mp (Finset.mem_filter.mp hm).2
    calc ∑ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)), ‖Iterm N W m‖
        ≤ c3 * ∑ m ∈ s.filter (fun m => ¬ (|(rho m : ℝ)| ≤ X)), 1 / |(rho m : ℝ)| ^ j :=
          hsum_le
      _ ≤ c3 * (24 / X ^ (j - 1)) := mul_le_mul_of_nonneg_left hsum2 hc3nn
      _ = 24 * ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 * Azero ^ 2 * Cd * (1 + T) ^ j / (N : ℝ) ^ j) /
            X ^ (j - 1) := by
          rw [hc3]; ring

-- ==== the main theorem ====

theorem Spart_one_bound (ε : ℝ) (hε : 0 < ε)
    (hdec : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (hzero : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Submission.GM.hhat t 0‖ ≤ C / |t| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ‖Submission.GM.Spart 1 N W‖ ≤ 1 := by
  obtain ⟨j₁, hj₁⟩ := exists_nat_ge (20 / ε)
  obtain ⟨j₂, hj₂⟩ := exists_nat_ge (4 * ε + 10)
  obtain ⟨j, hjε, hjj⟩ : ∃ j : ℕ, 20 ≤ ε * j ∧ 4 * ε + 10 ≤ (j : ℝ) := by
    refine ⟨max j₁ j₂, ?_, ?_⟩
    · have h1 : 20 / ε ≤ ((max j₁ j₂ : ℕ) : ℝ) :=
        le_trans hj₁ (by exact_mod_cast Nat.le_max_left j₁ j₂)
      have h2 : 20 ≤ ((max j₁ j₂ : ℕ) : ℝ) * ε := (div_le_iff₀ hε).mp h1
      simpa [mul_comm] using h2
    · exact le_trans hj₂ (by exact_mod_cast Nat.le_max_right j₁ j₂)
  obtain ⟨Cd, hCd0, hd⟩ := hdec j
  obtain ⟨Cz, hCz0, hz⟩ := hzero j
  obtain ⟨N₁, hN₁⟩ := final_arith ε hε j hjj hjε Azero Cd Cz Azero_nonneg hCd0 hCz0
  refine ⟨max N₁ 1, ?_⟩
  intro N hN W hW hsep
  have hN1 : 1 ≤ N := le_trans (le_max_right N₁ 1) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left N₁ 1) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM1 : 1 ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN1
  have hM0 : (0 : ℝ) ≤ Submission.LargeValues.M N := le_trans zero_le_one hM1
  have hδ1 : 1 ≤ (Submission.LargeValues.M N) ^ ε := Real.one_le_rpow hM1 hε.le
  have hj2 : 2 ≤ j := by
    have : (2 : ℝ) ≤ (j : ℝ) := by linarith
    exact_mod_cast this
  have hX1 : 1 ≤ (Submission.LargeValues.M N) ^ (1 + ε) / (N : ℝ) := by
    have hMN : (Submission.LargeValues.M N) ^ (1 + ε) =
        (N : ℝ) ^ ((6 : ℝ) / 5 * (1 + ε)) := by
      rw [Submission.LargeValues.M]
      rw [Real.rpow_mul (le_of_lt hNpos)]
    have hsplit : (N : ℝ) ^ ((6 : ℝ) / 5 * (1 + ε)) / (N : ℝ) =
        (N : ℝ) ^ ((6 : ℝ) / 5 * (1 + ε) - 1) := by
      rw [Real.rpow_sub hNpos, Real.rpow_one]
    rw [hMN, hsplit]
    apply Real.one_le_rpow (by exact_mod_cast hN1)
    linarith
  have hcard : (W.card : ℝ) ≤ Submission.LargeValues.M N + 1 :=
    sep_card_le W (Submission.LargeValues.M N) ((Submission.LargeValues.M N) ^ ε) hM0 hδ1 hW hsep
  have hfin : ∀ u : Finset {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 1},
      ∑ m ∈ u, ‖Submission.GM.Iterm N W m‖ ≤ 1 := by
    intro u
    have hb := finite_sum_bound N hN1 W (Submission.LargeValues.M N) ((Submission.LargeValues.M N) ^ ε)
      ((Submission.LargeValues.M N) ^ (1 + ε) / (N : ℝ)) j hM1 hδ1 hX1 hj2 hW hsep Cd Cz hCd0 hCz0
      hd hz hAz (u.image Subtype.val) (by
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨a, -, rfl⟩ := hm
        exact a.2)
    have hsum_eq : ∑ m ∈ u.image Subtype.val, ‖Submission.GM.Iterm N W m‖ =
        ∑ m ∈ u, ‖Submission.GM.Iterm N W m‖ :=
      Finset.sum_image (fun a _ b _ h => Subtype.ext h)
    rw [hsum_eq] at hb
    exact hb.trans (hN₁ N hNN₁ (W.card : ℝ) (Nat.cast_nonneg _) hcard)
  have hsumm : Summable (fun m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 1} =>
      ‖Submission.GM.Iterm N W m‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  calc ‖Submission.GM.Spart 1 N W‖
      = ‖∑' m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 1}, Submission.GM.Iterm N W m‖ := rfl
    _ ≤ ∑' m : {m : ℤ × ℤ × ℤ // Submission.GM.nzCount m = 1}, ‖Submission.GM.Iterm N W m‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ 1 := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfin

end Work.GM.Trace
