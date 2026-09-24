import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.R_l2
import Submission.Work.GM.Energy.EnergyCore.GcdSetup
import Submission.Work.GM.Energy.RMoments.sum_norm_sqPsi_le

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **GM Lemma 11.8** (small GCD terms), given the local constancy of `R` (Lemma 11.7), the
`L²` bound `∫₁²‖R‖² ≪ |W|` and the `L⁴` bound `∫₁²‖R‖⁴ ≪ E(W)` as hypotheses, with the locality
window parameter `K` of Lemma 11.7 exposed:
`Σ_{gcd(n₁,n₂)≤D} ‖R(n₁/n₂)‖³ ⪅ K³ (DT+N²)|W|^{1/2}E^{1/2} + N²|W|³/K^{3m}`.
(Route: Lemma 11.7 (cubed, via Jensen over the window of length `K/T`) replaces each
`‖R(n₁/n₂)‖³` by `K²T∫_{|v'-n₁/n₂|≤K/T}‖R(v')‖³dv'` plus the error `(CR/K^m|W|)³`; the coprime
fractions `n₁'/n₂'` are `d²/N²`-separated (Farey), so a window of length `K/T` contains
`≪ 1 + KN²/(d²T)` of them; summing over `d ≤ D` gives `DT + N²` window-integrals, and Hölder with
the `L²`/`L⁴` bounds gives `|W|^{1/2}E^{1/2}`. The additive error is the term that survives at
`K = 1`, where the locality bound carries no information.) -/
theorem gcd_small (m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (CR : ℝ), 0 < CR →
      (∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
        ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ (K : ℝ), 1 ≤ K →
          ‖Submission.GM.Rfun W v‖ ≤
            CR * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
              + CR / K ^ (m : ℝ) * (W.card : ℝ)) →
      (∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
          Submission.GM.Separated W 1 →
          (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) ≤ CR * (W.card : ℝ)) →
      (∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
          Submission.GM.Separated W 1 →
          (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4)
            ≤ CR * (Submission.GM.energy W : ℝ)) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W 1 →
      ∀ (K : ℝ), 1 ≤ K → ∀ (D : ℝ), 1 ≤ D →
        (∑ n1 ∈ Finset.Icc N (2 * N),
            ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
          ≤ C * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε
              * (D * Submission.LargeValues.M N + (N : ℝ) ^ 2)
              * (W.card : ℝ) ^ ((1 : ℝ) / 2)
              * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)
            + C * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3
                / K ^ (3 * (m : ℝ)) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro CR hCR hloc hL2 hL4 N hN W hW hsep K hK D hD
  have hT1 : (1 : ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
  set T : ℝ := Submission.LargeValues.M N with hTdef
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hW'T : ∀ t ∈ W, t ∈ Set.Icc 0 T := by intro t ht; rw [hTdef]; exact hW t ht
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hKmpos : (0 : ℝ) < K ^ (m : ℝ) := Real.rpow_pos_of_pos hKpos m
  have hKp3 : 0 < K ^ (3 * (m : ℝ)) := Real.rpow_pos_of_pos hKpos _
  have hD1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcW0 : 0 ≤ (W.card : ℝ) := by positivity
  set ce : ℝ := (W.card : ℝ) ^ ((1 : ℝ) / 2)
    * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) with hce
  have hce0 : 0 ≤ ce := by rw [hce]; positivity
  have hL2' : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ CR * (W.card : ℝ) :=
    hL2 W T hW'T hsep
  have hL4' : ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4
      ≤ CR * (Submission.GM.energy W : ℝ) := hL4 W T hW'T hsep
  have hI := integral_bound hCR hL2' hL4'
  rw [← hce] at hI
  have hcube := card_pow_three_le W hT1 hW'T hsep
  rw [← hce] at hcube
  rw [gcd_sum_reindex hN D hD (fun f : ℝ => ‖Submission.GM.Rfun W f‖ ^ 3)]
  -- ## the bound for a single `dd`
  have hper : ∀ dd ∈ Finset.Icc 1 ⌊D⌋₊,
      (∑ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3)
        ≤ 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
              * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3)
            + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (2 * (K / T) * (W.card : ℝ)) ^ 3)
          + 8 * (CR / K ^ (m : ℝ)) ^ 3 * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ) := by
    intro dd hdd
    have hdd1 : 1 ≤ dd := (Finset.mem_Icc.mp hdd).1
    have hp1 : ∀ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3
        ≤ 8 * (CR * T * (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖)) ^ 3
          + 8 * (CR / K ^ (m : ℝ) * (W.card : ℝ)) ^ 3 := by
      intro f hf
      have hb := fracSet_bounds hN hf
      have hl := hloc T hT1 W hW'T f hb K hK
      have hκ0 : 0 ≤ K / T := div_nonneg (le_of_lt hKpos) (le_of_lt hTpos)
      have hP1 : 0 ≤ CR * T * (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) :=
        mul_nonneg (mul_nonneg (le_of_lt hCR) (le_of_lt hTpos))
          (intervalIntegral.integral_nonneg (by linarith) (fun x _ => norm_nonneg _))
      have hP2 : 0 ≤ CR / K ^ (m : ℝ) * (W.card : ℝ) :=
        mul_nonneg (div_nonneg (le_of_lt hCR) (le_of_lt hKmpos)) hcW0
      calc ‖Submission.GM.Rfun W f‖ ^ 3
          ≤ (CR * T * (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖)
              + CR / K ^ (m : ℝ) * (W.card : ℝ)) ^ 3 :=
            pow_le_pow_left₀ (norm_nonneg _) hl 3
        _ ≤ 8 * (CR * T * (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖)) ^ 3
              + 8 * (CR / K ^ (m : ℝ) * (W.card : ℝ)) ^ 3 := add_cube_le hP1 hP2
    calc (∑ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3)
        ≤ ∑ f ∈ fracSet N dd,
            (8 * (CR * T * (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖)) ^ 3
              + 8 * (CR / K ^ (m : ℝ) * (W.card : ℝ)) ^ 3) := Finset.sum_le_sum hp1
      _ = 8 * (CR * T) ^ 3 * (∑ f ∈ fracSet N dd,
              (∫ v in f - K / T..f + K / T, ‖Submission.GM.Rfun W v‖) ^ 3)
            + 8 * (CR / K ^ (m : ℝ)) ^ 3 * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun f hf => ?_
            ring_nf
          · rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
              * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3)
            + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (2 * (K / T) * (W.card : ℝ)) ^ 3)
          + 8 * (CR / K ^ (m : ℝ)) ^ 3 * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ) := by
          have hsw := sum_window_pow3_le (N := N) (dd := dd) hN hdd1 (W := W) (T := T) (K := K) hT1 hK
          have h8 : 0 ≤ 8 * (CR * T) ^ 3 := by positivity
          have h9 := mul_le_mul_of_nonneg_left hsw h8
          linarith [h9]
  -- ## the sums of the coefficients
  have hs1 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
        (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
      ≤ D + 16 * K * (N : ℝ) ^ 2 / T := by
    have hterm : ∀ dd ∈ Finset.Icc 1 ⌊D⌋₊,
        (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
          = 1 + 8 * K * (N : ℝ) ^ 2 / ((dd : ℝ) ^ 2 * T) := by
      intro dd hdd
      have hddne : (dd : ℝ) ≠ 0 := by
        have h1 : 1 ≤ dd := (Finset.mem_Icc.mp hdd).1
        exact_mod_cast (by omega : dd ≠ 0)
      field_simp
      try ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * K * (N : ℝ) ^ 2 / ((dd : ℝ) ^ 2 * T))
        = 8 * K * (N : ℝ) ^ 2 / T
          * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun dd hdd => ?_
      have hddne : (dd : ℝ) ≠ 0 := by
        have h1 : 1 ≤ dd := (Finset.mem_Icc.mp hdd).1
        exact_mod_cast (by omega : dd ≠ 0)
      field_simp
      try ring
    rw [h2]
    have hcard : (((Finset.Icc 1 ⌊D⌋₊).card : ℕ) : ℝ) ≤ D := by
      rw [Nat.card_Icc]
      have h : ⌊D⌋₊ + 1 - 1 = ⌊D⌋₊ := by omega
      rw [h]
      exact Nat.floor_le hD0
    have hsq := Work.GM.Energy.RMoments.sum_Icc_inv_sq_le_two ⌊D⌋₊
    have hsq0 : 0 ≤ ∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hS : 0 ≤ 8 * K * (N : ℝ) ^ 2 / T := by positivity
    have hmul : 8 * K * (N : ℝ) ^ 2 / T
          * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2)
        ≤ 8 * K * (N : ℝ) ^ 2 / T * 2 := mul_le_mul_of_nonneg_left hsq hS
    have h3 : 8 * K * (N : ℝ) ^ 2 / T * 2 = 16 * K * (N : ℝ) ^ 2 / T := by ring
    linarith [hcard, hmul, hsq0, h3]
  have hs2 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
        (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
      ≤ D + 8 * K * (N : ℝ) ^ 2 / T := by
    have hterm : ∀ dd ∈ Finset.Icc 1 ⌊D⌋₊,
        (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
          = 1 + 4 * K * (N : ℝ) ^ 2 / ((dd : ℝ) ^ 2 * T) := by
      intro dd hdd
      have hddne : (dd : ℝ) ≠ 0 := by
        have h1 : 1 ≤ dd := (Finset.mem_Icc.mp hdd).1
        exact_mod_cast (by omega : dd ≠ 0)
      field_simp
      try ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 4 * K * (N : ℝ) ^ 2 / ((dd : ℝ) ^ 2 * T))
        = 4 * K * (N : ℝ) ^ 2 / T
          * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun dd hdd => ?_
      have hddne : (dd : ℝ) ≠ 0 := by
        have h1 : 1 ≤ dd := (Finset.mem_Icc.mp hdd).1
        exact_mod_cast (by omega : dd ≠ 0)
      field_simp
      try ring
    rw [h2]
    have hcard : (((Finset.Icc 1 ⌊D⌋₊).card : ℕ) : ℝ) ≤ D := by
      rw [Nat.card_Icc]
      have h : ⌊D⌋₊ + 1 - 1 = ⌊D⌋₊ := by omega
      rw [h]
      exact Nat.floor_le hD0
    have hsq := Work.GM.Energy.RMoments.sum_Icc_inv_sq_le_two ⌊D⌋₊
    have hsq0 : 0 ≤ ∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hS : 0 ≤ 4 * K * (N : ℝ) ^ 2 / T := by positivity
    have hmul : 4 * K * (N : ℝ) ^ 2 / T
          * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (1 : ℝ) / (dd : ℝ) ^ 2)
        ≤ 4 * K * (N : ℝ) ^ 2 / T * 2 := mul_le_mul_of_nonneg_left hsq hS
    have h3 : 4 * K * (N : ℝ) ^ 2 / T * 2 = 8 * K * (N : ℝ) ^ 2 / T := by ring
    linarith [hcard, hmul, hsq0, h3]
  have hs3 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((fracSet N dd).card : ℝ)) ≤ ((N : ℝ) + 1) ^ 2 := by
    have h := sum_fracSet_card_le (N := N) hN D hD
    have h' : ((∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (fracSet N d).card : ℕ) : ℝ)
        ≤ (((N + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sum] at h'
    rw [show (((N + 1) ^ 2 : ℕ) : ℝ) = ((N : ℝ) + 1) ^ 2 by push_cast; ring] at h'
    exact h'
  -- ## summing over `dd`
  set I3 : ℝ := ∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 3 with hI3
  have hI3nn : 0 ≤ I3 := by
    rw [hI3]; exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)
  have hI3' : I3 ≤ 2 * CR * ce := by rw [hI3, hce]; exact hI
  have hsum : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ∑ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3)
      ≤ 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
        + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
        + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
        + 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
    have hA : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
            * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * I3
          + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
            * (2 * (K / T) * (W.card : ℝ)) ^ 3))
        ≤ 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
          + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
          + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T := by
      have hfac1 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((2 * (K / T)) ^ 2 * I3)
            * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
          = (2 * (K / T)) ^ 2 * I3
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))) := by
        rw [← Finset.mul_sum]
      have hfac2 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
            (2 * (2 * (K / T) * (W.card : ℝ)) ^ 3)
            * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
          = 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))) := by
        rw [← Finset.mul_sum]
      have hshape1 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (2 * (K / T)) ^ 2
            * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * I3)
          = ∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((2 * (K / T)) ^ 2 * I3)
            * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) :=
        Finset.sum_congr rfl fun dd hdd => by ring
      have hshape2 : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 2
            * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
            * (2 * (K / T) * (W.card : ℝ)) ^ 3)
          = ∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (2 * (2 * (K / T) * (W.card : ℝ)) ^ 3)
            * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) :=
        Finset.sum_congr rfl fun dd hdd => by ring
      have hrew : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
              * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * I3
            + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (2 * (K / T) * (W.card : ℝ)) ^ 3))
          = 8 * (CR * T) ^ 3 * ((∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((2 * (K / T)) ^ 2 * I3)
                * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
              + (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (2 * (2 * (K / T) * (W.card : ℝ)) ^ 3)
                * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← hshape1, ← hshape2]
      rw [hrew, hfac1, hfac2]
      have e1 : (2 * (K / T)) ^ 2 * I3
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
          ≤ (2 * (K / T)) ^ 2 * I3 * (D + 16 * K * (N : ℝ) ^ 2 / T) :=
        mul_le_mul_of_nonneg_left hs1 (by positivity)
      have e2 : 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
          ≤ 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3 * (D + 8 * K * (N : ℝ) ^ 2 / T) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      have hmono : 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2 * I3
              * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                  (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))))
            + 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3
              * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊,
                  (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))))
          ≤ 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2 * I3 * (D + 16 * K * (N : ℝ) ^ 2 / T)
            + 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3 * (D + 8 * K * (N : ℝ) ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity)
      have hX : 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2 * I3 * (D + 16 * K * (N : ℝ) ^ 2 / T)
            + 2 * (2 * (K / T) * (W.card : ℝ)) ^ 3 * (D + 8 * K * (N : ℝ) ^ 2 / T))
          = 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
            + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
            + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T := by
        field_simp
        ring
      rw [hX] at hmono
      exact hmono
    have hC : (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * (CR / K ^ (m : ℝ)) ^ 3
          * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ))
        ≤ 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
      rw [← Finset.mul_sum]
      have hpoweq : (CR / K ^ (m : ℝ)) ^ 3 = CR ^ 3 / K ^ (3 * (m : ℝ)) := by
        rw [div_pow, ← Real.rpow_natCast (K ^ (m : ℝ)) 3, ← Real.rpow_mul (le_of_lt hKpos)]
        norm_num
        ring_nf
      have h4 : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith [hN1]
      have h8nn : 0 ≤ 8 * CR ^ 3 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) :=
        div_nonneg (by positivity) (le_of_lt hKp3)
      calc 8 * (CR / K ^ (m : ℝ)) ^ 3 * (W.card : ℝ) ^ 3
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((fracSet N dd).card : ℝ))
          = (8 * CR ^ 3 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)))
            * (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ((fracSet N dd).card : ℝ)) := by
            rw [hpoweq]; ring
        _ ≤ (8 * CR ^ 3 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))) * ((N : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hs3 h8nn
        _ ≤ (8 * CR ^ 3 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))) * (4 * (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left h4 h8nn
        _ = 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by ring
    calc (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ∑ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3)
        ≤ ∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, (8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
              * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * I3
            + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (2 * (K / T) * (W.card : ℝ)) ^ 3)
          + 8 * (CR / K ^ (m : ℝ)) ^ 3 * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ)) :=
          Finset.sum_le_sum hper
      _ = (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * (CR * T) ^ 3 * ((2 * (K / T)) ^ 2
              * (1 + 2 * (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))) * I3
            + 2 * (1 + (K / T) / ((dd : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)))
              * (2 * (K / T) * (W.card : ℝ)) ^ 3))
          + (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, 8 * (CR / K ^ (m : ℝ)) ^ 3
              * (W.card : ℝ) ^ 3 * ((fracSet N dd).card : ℝ)) := Finset.sum_add_distrib
      _ ≤ (32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
          + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
          + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T)
          + 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) :=
          add_le_add hA hC
  -- ## the final arithmetic
  have hCR4 : CR ^ 4 ≤ (CR + 1) ^ 4 := by
    have hp : (0 : ℝ) ≤ CR ^ 4 + 3 * CR ^ 3 + 6 * CR ^ 2 + 4 * CR + 1 := by positivity
    nlinarith [hp]
  have hCR3 : CR ^ 3 ≤ (CR + 1) ^ 4 := by
    have hp : (0 : ℝ) ≤ CR ^ 4 + 3 * CR ^ 3 + 6 * CR ^ 2 + 4 * CR + 1 := by positivity
    nlinarith [hp]
  have hK4 : K ^ 4 ≤ (K + 1) ^ 4 := by
    have hp : (0 : ℝ) ≤ K ^ 4 + 4 * K ^ 3 + 6 * K ^ 2 + 4 * K := by positivity
    nlinarith [hp, hK]
  have hK3 : K ^ 3 ≤ (K + 1) ^ 4 := by
    have hp : (0 : ℝ) ≤ K ^ 4 + 4 * K ^ 3 + 6 * K ^ 2 + 4 * K := by positivity
    nlinarith [hp, hK]
  have hK2 : K ^ 2 ≤ (K + 1) ^ 4 := by
    have hp : (0 : ℝ) ≤ K ^ 4 + 4 * K ^ 3 + 6 * K ^ 2 + 4 * K := by positivity
    nlinarith [hp, hK]
  have hTD : T * D ≤ D * T + (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
  have hN2 : (N : ℝ) ^ 2 ≤ D * T + (N : ℝ) ^ 2 := by
    have : 0 ≤ D * T := mul_nonneg hD0 (le_of_lt hTpos)
    linarith
  have hD2T3 : D * (2 * T + 3) ≤ 5 * (D * T + (N : ℝ) ^ 2) := by
    nlinarith [hD0, hTpos, sq_nonneg (N : ℝ)]
  have h2T3T : (2 * T + 3) / T ≤ 5 := by rw [div_le_iff₀ hTpos]; linarith
  have hfin : 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
        + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
        + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
        + 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))
      ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
    have t1 : 32 * CR ^ 3 * T * D * K ^ 2 * I3
        ≤ 64 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
      calc 32 * CR ^ 3 * T * D * K ^ 2 * I3 ≤ 32 * CR ^ 3 * T * D * K ^ 2 * (2 * CR * ce) := by
            gcongr
        _ = 64 * CR ^ 4 * K ^ 2 * (T * D) * ce := by ring
        _ ≤ 64 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hCR4 | exact hK2 | exact hTD
    have t2 : 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
        ≤ 1024 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
      calc 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
            ≤ 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * (2 * CR * ce) := by gcongr
        _ = 1024 * CR ^ 4 * K ^ 3 * (N : ℝ) ^ 2 * ce := by ring
        _ ≤ 1024 * (CR + 1) ^ 4 * (K + 1) ^ 4 * ((N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hCR4 | exact hK3
        _ ≤ 1024 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hN2
    have t3 : 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
        ≤ 640 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
      calc 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
            ≤ 128 * CR ^ 3 * D * K ^ 3 * ((2 * T + 3) * ce) := by gcongr
        _ = 128 * CR ^ 3 * K ^ 3 * (D * (2 * T + 3)) * ce := by ring
        _ ≤ 128 * CR ^ 3 * K ^ 3 * (5 * (D * T + (N : ℝ) ^ 2)) * ce := by
            gcongr <;> first | positivity | norm_num | exact hD2T3
        _ = 640 * CR ^ 3 * K ^ 3 * (D * T + (N : ℝ) ^ 2) * ce := by ring
        _ ≤ 640 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hCR3 | exact hK3
    have t4 : 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
        ≤ 5120 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
      calc 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
            ≤ 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * ((2 * T + 3) * ce) / T := by gcongr
        _ = 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * ((2 * T + 3) / T) * ce := by ring
        _ ≤ 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * 5 * ce := by
            gcongr <;> first | positivity | norm_num | exact h2T3T
        _ = 5120 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * ce := by ring
        _ ≤ 5120 * (CR + 1) ^ 4 * (K + 1) ^ 4 * ((N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hCR3 | exact hK4
        _ ≤ 5120 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
            gcongr <;> first | positivity | norm_num | exact hN2
    have t5 : 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))
        ≤ 32 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
      gcongr <;> first | positivity | exact hCR3
    have hM : 0 ≤ (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by positivity
    have hM2 : 0 ≤ (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) :=
      div_nonneg (by positivity) (le_of_lt hKp3)
    have hmult1 : (6848 : ℝ) * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
        ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by
      calc (6848 : ℝ) * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          ≤ 100000 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce) := by
            gcongr <;> first | norm_num | positivity
        _ = 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce := by ring
    have hmult2 : (32 : ℝ) * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3
          / K ^ (3 * (m : ℝ)))
        ≤ 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
      calc (32 : ℝ) * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)))
          = (32 * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3)) / K ^ (3 * (m : ℝ)) := by ring
        _ ≤ (100000 * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3))
              / K ^ (3 * (m : ℝ)) := by
            refine div_le_div_of_nonneg_right ?_ (le_of_lt hKp3)
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by ring
    have u1 : 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
          + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
        ≤ 64 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 1024 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 640 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce) := by
      have h12 := t1
      have h34 := t2
      have h56 := t3
      refine le_trans (add_le_add (add_le_add h12 h34) h56) (le_of_eq ?_)
      ring
    have u2 : 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
          + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
          + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
        ≤ 64 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 1024 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 640 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 5120 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce) := by
      have h78 := t4
      refine le_trans (add_le_add u1 h78) (le_of_eq ?_)
      ring
    have u3 : 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
          + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
          + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
          + 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))
        ≤ 64 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 1024 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 640 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 5120 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 32 * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))) := by
      refine le_trans (add_le_add u2 t5) (le_of_eq ?_)
      ring
    refine le_trans u3 ?_
    have hsum68 : 64 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 1024 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 640 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 5120 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 32 * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)))
        = 6848 * ((CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce)
          + 32 * ((CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))) := by
      ring
    rw [hsum68]
    exact add_le_add hmult1 hmult2
  have hfin2 : 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))
      ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2) * ce
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2
            * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by
    have hNeps : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 (le_of_lt hε)
    have hfac1 : (D * T + (N : ℝ) ^ 2) ≤ (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2) := by
      simpa using mul_le_mul_of_nonneg_right hNeps (by positivity : (0 : ℝ) ≤ D * T + (N : ℝ) ^ 2)
    have hfac2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ ε * (N : ℝ) ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hNeps (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
    refine add_le_add ?_ ?_
    · calc 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce
          ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4
              * ((N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2)) * ce := by
            gcongr <;> first | positivity | norm_num | exact hfac1
        _ = 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2) * ce := by
            ring
    · calc 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ))
          ≤ 100000 * (CR + 1) ^ 4 * ((N : ℝ) ^ ε * (N : ℝ) ^ 2) * (W.card : ℝ) ^ 3
              / K ^ (3 * (m : ℝ)) := by
            gcongr <;> first | positivity | norm_num | exact hfac2
        _ = 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2
              * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := by ring
  calc (∑ dd ∈ Finset.Icc 1 ⌊D⌋₊, ∑ f ∈ fracSet N dd, ‖Submission.GM.Rfun W f‖ ^ 3)
      ≤ 32 * CR ^ 3 * T * D * K ^ 2 * I3 + 512 * CR ^ 3 * K ^ 3 * (N : ℝ) ^ 2 * I3
        + 128 * CR ^ 3 * D * K ^ 3 * (W.card : ℝ) ^ 3
        + 1024 * CR ^ 3 * K ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / T
        + 32 * CR ^ 3 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := hsum
    _ ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (D * T + (N : ℝ) ^ 2) * ce
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := hfin
    _ ≤ 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2) * ce
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2
            * (W.card : ℝ) ^ 3 / K ^ (3 * (m : ℝ)) := hfin2
    _ = 100000 * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2)
          * (W.card : ℝ) ^ ((1 : ℝ) / 2) * (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2)
        + 100000 * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 3
            / K ^ (3 * (m : ℝ)) := by
        rw [hce]; ring
