import Mathlib
import Submission.Work.Peluse.LevelRaise.boxNormPow_succ_ge
import Submission.Work.Peluse.Peel.boxNormPow_diag_ge
import Submission.Work.Peluse.PET.boxNormPow_control_linear_v2_pelGauge
import Submission.Work.Peluse.PET.pow_le_transfer_gain_pelGauge
import Submission.Work.Peluse.PET.regimeB_core

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

/-!
# `boxNormPow_control_linear_v2`

Target: Peluse, *Bounds for sets with no polynomial progressions*, Lemma 4.10 (the base case of the
PET induction), specialised to polynomial shifts with zero constant term, plus the hypothesis
`c 0 = 0`.

## The proof

The hypothesis `γ' ≤ γ/(1000(m+1))` is *weaker* than the paper's gauge `γ' ≪ γ^{O_m(1)}`, so the
conclusion is a genuine strengthening of Peluse's Lemma 4.10.  The proof is a three-régime argument
around the *fine gauge* `γ' ≤ (γ/1000)^(2^m)`:

* `PET.boxNormPow_control_linear_v2_pelGauge` (proved in this directory) is Peluse's chain in that
  fine gauge;
* `TransferUp.boxNormPow_transfer_up` (**the new transference**, `k ≥ 2` only) lets one run the
  chain at the fine scale `⌊(γ/1000)^(2^m) M⌋` and then move *up* to the required coarse scale
  `⌊γ'M⌋` at the cost of a power `γ^{(2^m-1)e}` of `γ`;
* `PET.boxNormPow_control_linear_v2_diag` (the iterated exact diagonal) covers the remaining
  "gap" régime, where even the fine scale is below `1`;
* `Track.boxNormPow_control_linear_v2_of_degenerate_direction` and
  `PET.boxNormPow_control_linear_v2_one` cover degenerate directions and `m = 1`.

The two arithmetic lemmas `PET.pow_le_transfer_gain_pelGauge` (régime B) and
`PET.diagHyp_of_gapHyp` (régime C) convert the gained factors into the final exponent `K`.
Since every constant is data-independent, the three régimes can be made exhaustive by *enlarging*
`K` — see `NOTES_boxNormPow_control_v2.md`.
-/

namespace Work.Peluse.PET

noncomputable section

theorem boxNormPow_control_linear_v2 {m : ℕ} (hm : 0 < m) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (m + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋.toNat)) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨K, hK, hmain⟩ := boxNormPow_control_linear_v2_one
    exact ⟨K, hK, fun c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam =>
      hmain c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy (by simpa using hγ'le) hHge hLam⟩
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨K1, hK11, hpg⟩ := boxNormPow_control_linear_v2_pelGauge (m := m) hm
    obtain ⟨cT, hcT, eT, hTfer⟩ := Work.Peluse.TransferUp.boxNormPow_transfer_up (k := m) hm2
    obtain ⟨Kd, hKd1, hdegen⟩ :=
      Work.Peluse.Track.boxNormPow_control_linear_v2_of_degenerate_direction hm
    set a : ℝ := ((m : ℝ) + 1) / (2 * (1000 : ℝ) ^ (2 ^ m - 1)) with hadef
    have ha0 : 0 < a := by rw [hadef]; positivity
    set AA : ℝ := max 1 (max (1000 ^ K1 * (1 + (1 / a) ^ eT) / cT)
      (4 * (2 * (1000 : ℝ) ^ (2 ^ m)) ^ m / (1000 * ((m : ℝ) + 1)) ^ m)) with hAAdef
    obtain ⟨q, hqA⟩ : ∃ q : ℕ, AA ≤ (1000 : ℝ) ^ q := by
      obtain ⟨n, hn⟩ := exists_nat_ge AA
      refine ⟨n, le_trans hn ?_⟩
      calc (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast le_of_lt Nat.lt_two_pow_self
        _ ≤ (1000 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
            (by norm_num : (2:ℝ) ≤ 1000) n
    set K : ℕ := max (2 ^ (m - 1) + m * (2 ^ m - 1))
      (max (K1 + eT * 2 ^ m) (max Kd (max (2 ^ (m - 1) + q) q))) with hKdef
    have hK1K : K1 ≤ K := by
      rw [hKdef]
      exact le_trans (Nat.le_add_right K1 (eT * 2 ^ m))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hKdK : Kd ≤ K := by
      rw [hKdef]
      exact le_trans (le_max_left Kd (max (2 ^ (m - 1) + q) q))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hKq : q ≤ K := by
      rw [hKdef]
      exact le_trans (le_max_right (2 ^ (m - 1) + q) q)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hKpq : 2 ^ (m - 1) + q ≤ K := by
      rw [hKdef]
      exact le_trans (le_max_left (2 ^ (m - 1) + q) q)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    have hKq2 : q ≤ K - 2 ^ (m - 1) := by omega
    have hKl : 2 ^ (m - 1) + m * (2 ^ m - 1) ≤ K := by
      rw [hKdef]; exact le_max_left _ _
    have hKe : K1 + eT * (2 ^ m - 1) ≤ K := by
      rw [hKdef]
      exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left eT (Nat.sub_le _ _)) _)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    have hAAK : AA ≤ (1000 : ℝ) ^ K :=
      le_trans hqA (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000) (by exact_mod_cast hKq))
    refine ⟨K, Nat.one_le_iff_ne_zero.mpr (by omega), ?_⟩
    intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam
    set H : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hHdef
    set T : ℝ := (γ / 1000) ^ (2 ^ m) with hTdef
    have hTsplit : T = γ ^ (2 ^ m) / (1000 : ℝ) ^ (2 ^ m) := by rw [hTdef, div_pow]
    have hH1 : 1 ≤ H := hHge
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hHle : (H : ℝ) ≤ γ' * (M : ℝ) := by
      rw [hHdef, Int.floor_toNat]; exact Nat.floor_le (by positivity)
    have hden : (0 : ℝ) < (1000 : ℝ) * ((m : ℝ) + 1) := by
      have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hγ'1 : γ' ≤ 1 := by
      have h : γ / ((1000 : ℝ) * ((m : ℝ) + 1)) ≤ 1 :=
        (div_le_one hden).mpr (by
          have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith [hγ1, h0])
      linarith [hγ'le, h]
    have hHM : H ≤ M := by
      have h : (H : ℝ) ≤ (M : ℝ) := by
        calc (H : ℝ) ≤ γ' * (M : ℝ) := hHle
          _ ≤ 1 * (M : ℝ) := mul_le_mul_of_nonneg_right hγ'1 hMpos.le
          _ = (M : ℝ) := one_mul _
      exact_mod_cast h
    have hHγ : (H : ℝ) * ((1000 : ℝ) * ((m : ℝ) + 1)) ≤ γ * (M : ℝ) := by
      have h2 : γ' * ((1000 : ℝ) * ((m : ℝ) + 1)) ≤ γ := (le_div_iff₀ hden).mp hγ'le
      nlinarith [hHle, h2, hMpos]
    have hdH : ∀ i : Fin m,
        |c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc| * (H : ℤ) ≤ 2 * (N : ℤ) := by
      intro i
      have hcM : ∀ j : Fin (m + 1), |c j| * (M : ℤ) ≤ (N : ℤ) := by
        intro j
        have h := hcy M (Finset.mem_Icc.mpr ⟨by omega, le_refl M⟩) j
        rwa [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) by positivity)] at h
      have hHMz : (H : ℤ) ≤ (M : ℤ) := by exact_mod_cast hHM
      have hHN : (0 : ℤ) ≤ (H : ℤ) := by positivity
      have h1 : |c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc|
          ≤ |c ⟨m, Nat.lt_succ_self m⟩| + |c i.castSucc| := abs_sub _ _
      calc |c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc| * (H : ℤ)
          ≤ (|c ⟨m, Nat.lt_succ_self m⟩| + |c i.castSucc|) * (H : ℤ) :=
            mul_le_mul_of_nonneg_right h1 hHN
        _ ≤ (|c ⟨m, Nat.lt_succ_self m⟩| + |c i.castSucc|) * (M : ℤ) :=
            mul_le_mul_of_nonneg_left hHMz (by positivity)
        _ = |c ⟨m, Nat.lt_succ_self m⟩| * (M : ℤ) + |c i.castSucc| * (M : ℤ) := by ring
        _ ≤ (N : ℤ) + (N : ℤ) := add_le_add (hcM _) (hcM _)
        _ = 2 * (N : ℤ) := by ring
    by_cases hdeg : ∃ i₀ : Fin m, c i₀.castSucc = c ⟨m, Nat.lt_succ_self m⟩
    · have h := hdegen c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam hdeg
      exact le_trans (pow_le_pow_of_le_one (by positivity) (by linarith) hKdK) h
    · push_neg at hdeg
      have hdne : ∀ i : Fin m, c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc ≠ 0 :=
        fun i => sub_ne_zero.mpr (Ne.symm (hdeg i))
      have hT0 : 0 < T := by rw [hTdef]; positivity
      by_cases hA : γ' ≤ T
      · have h := hpg c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hA hHge hLam
        exact le_trans (pow_le_pow_of_le_one (by positivity) (by linarith) hK1K) h
      · push_neg at hA
        by_cases hB : 2 ≤ T * (M : ℝ)
        · set H1 : ℕ := ⌊T * (M : ℝ)⌋.toNat with hH1def
          have hH1ge : 1 ≤ H1 := by
            rw [hH1def]
            refine (Int.le_toNat (Int.floor_nonneg.mpr (by positivity))).mpr ?_
            rw [Int.le_floor]; push_cast; linarith [hB]
          have hH1pos : (0 : ℝ) < (H1 : ℝ) := by exact_mod_cast hH1ge
          have hH1H : H1 ≤ H := by
            rw [hH1def, hHdef, Int.toNat_le]
            have h2 : ⌊T * (M : ℝ)⌋ ≤ ⌊γ' * (M : ℝ)⌋ :=
              Int.floor_mono (le_of_lt (mul_lt_mul_of_pos_right hA hMpos))
            rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))]
            exact h2
          have hchain := hpg c hc0 hN hM F hγ hT0 hγ1 hF hFs hcy le_rfl hH1ge hLam
          have htr := hTfer N (F ⟨m, Nat.lt_succ_self m⟩) (fun x => hF _ x) (hFs _)
            (fun i : Fin m => c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) hdne H1 H
            hH1ge hH1H hdH
          have hratio : a * γ ^ (2 ^ m - 1) ≤ (H1 : ℝ) / (H : ℝ) := by
            rw [le_div_iff₀ (by exact_mod_cast hH1 : (0:ℝ) < (H : ℝ))]
            have h2 : T * (M : ℝ) / 2 ≤ (H1 : ℝ) := by
              have h3 : T * (M : ℝ) - 1 < (⌊T * (M : ℝ)⌋ : ℝ) := by
                have := Int.lt_floor_add_one (T * (M : ℝ)); linarith
              have h4 : ((⌊T * (M : ℝ)⌋ : ℤ).toNat : ℝ) = (⌊T * (M : ℝ)⌋ : ℝ) := by
                rw [← Int.cast_natCast, Int.toNat_of_nonneg
                  (Int.floor_nonneg.mpr (by positivity))]
              have h5 : (H1 : ℝ) = (⌊T * (M : ℝ)⌋ : ℝ) := by rw [hH1def, h4]
              linarith [h3, h5, hB]
            have h5 : a * γ ^ (2 ^ m - 1) * (H : ℝ) ≤ T * (M : ℝ) / 2 :=
              regimeB_core (m := m) (H := H) (M := M) hγ hTsplit hadef
                (by exact_mod_cast hH1 : (0:ℝ) < (H:ℝ)) hMpos hHγ
            exact le_trans h5 h2
          have hgain := pow_le_transfer_gain_pelGauge (m := m) hm hK11 (eT := eT)
            (cT := cT) (a := a) (γ := γ) (H1 := (H1 : ℝ)) (H := (H : ℝ))
            hcT ha0 hγ hγ1 (by exact_mod_cast hH1 : (0:ℝ) < (H:ℝ)) hH1pos hKe ?_ hratio
          · refine le_trans (le_trans hgain ?_) htr
            exact mul_le_mul_of_nonneg_left hchain (by positivity)
          · have hq' : 1000 ^ K1 * (1 + (1 / a) ^ eT) / cT ≤ (1000 : ℝ) ^ q :=
              le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hqA
            exact le_trans hq' (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000)
              (by exact_mod_cast hKq))
        · push_neg at hB
          have hgap : γ ^ (2 ^ m) * (M : ℝ) < 2 * ((1000 : ℝ) ^ (2 ^ m)) := by
            have h1 : T * (M : ℝ) < 2 := by linarith [hB]
            rw [hTsplit] at h1
            have h2 : γ ^ (2 ^ m) * (M : ℝ) / (1000 : ℝ) ^ (2 ^ m) < 2 := by
              rwa [div_mul_eq_mul_div] at h1
            rw [div_lt_iff₀ (by positivity)] at h2
            exact h2
          have hihyp := diagHyp_of_gapHyp (m := m) hm2 (Kp := 2 ^ m) (K := K)
            (Nat.one_le_two_pow) (Cp := (1000 : ℝ) ^ (2 ^ m)) (by positivity)
            hγ hγ1 hMpos hgap hKl ?_
          · have hres := boxNormPow_control_linear_v2_diag hm2 (K - 2 ^ (m - 1)) c hc0 hN hM F
              hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam hihyp
            refine le_trans ?_ hres
            refine pow_le_pow_of_le_one (by positivity) (by linarith) ?_
            omega
          · have hq' : 4 * (2 * (1000 : ℝ) ^ (2 ^ m)) ^ m / (1000 * ((m : ℝ) + 1)) ^ m
                ≤ (1000 : ℝ) ^ q :=
              le_trans (le_trans (le_max_right _ _) (le_max_right (1:ℝ) _)) hqA
            refine le_trans hq' (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 1000)
              (by exact_mod_cast hKq2))

end

end Work.Peluse.PET
