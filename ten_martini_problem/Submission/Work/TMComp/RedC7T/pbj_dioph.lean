import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.BJ
import Submission.Work.TMC7Core.Sound.LDT
import Submission.Work.TMC7Core.Scale.hasLEBound_Icc
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMC7Core.Scale.conv_chain_rational
import Submission.Work.TMC7Core.Scale.base_pairing_bd
import Submission.Work.TMC7Core.Scale.persists_level_pairing
import Submission.Work.TMC7Core.Scale.psi_upper
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz
import Submission.Work.TMC7Core.Solutions.rat_bound
import Submission.Work.TMC7Core.Bridge.P_BJ_transfer
import Submission.Work.TMC7Core.Bridge.Components

/-!
# The Diophantine case of C7 from the finite rational tower (S1)

Component C11 (`P_Reducibility`) consumes C7 only at frequencies satisfying `DiophBelow α b₀`
for some `b₀ > 0` (`RedC7T/mAnalytic_dioph.lean`).  For such a frequency the *dichotomy* of the
lead's C7 design (`TMC7Core/C7_INPUTS_LEAD.md`, `TMC7Core/S6_STATUS.md`) reduces to its Case II:
the continued-fraction chain of `α` (S2 `conv_chain_rational`) supplies the approximants for the
finite rational tower S1 (`rat_tower_lower`), and the only remaining inputs are

* the (proved) large deviation theorem with the level bound on an interval around `E`
  (`RedC7.large_deviation` via `TMC7Core.large_deviation_sound`, `Scale.hasLEBound_Icc`),
* `Scale.base_pairing_bd` (the frozen base scale `N₀`, with level and pairing at `(α,E)`),
* `Scale.persists_level_pairing` (level/pairing at the *same* scale `N₀` for nearby rationals),
* `Scale.psi_upper` (the upper bound on `ψ = L + L_N - 2L_{2N}` at the irrational point),
* `Scale.lyapAvg_lipschitz`/TMC7Core `lyapAvg_lipschitz` (the *crude, fixed-scale* transfer),
* `Solutions.rat_bound` (Krasovsky's rational bound).

The single non-elementary input is `RatTowerLower`, the statement of S1.  Everything here is
written against that statement, so that S1 can be plugged in as soon as it is proved
(`Work.TMComp.C7Aux.rat_tower_lower`, or `Work.TMC7Core.Scale.rat_tower_lower`).

## The argument (contradiction)

Assume `L := L(α,E) > M := max 0 (log ‖λ‖)`, put `ε = (L-M)/2`, `κ = min (L/400) (1/100)`,
`κ' = κ/2`.

1. Choose a large base index `i₀` of the chain (`T ≤ q i₀`, S1's error
   `B e^{-cκ'q i₀/8} < ε/16`);
2. choose `j > i₀` with `4 q i₀ ≤ q j`, `Cd κ^{-2} ≤ q j`, and the `psi_upper` load errors
   `(12C₀+1000)e^{-cκ q j/4} < ε/16`, `m < e^{cκ q j/2}`;
3. `base_pairing_bd` at `(α, q j, κ)` produces the *frozen* scale `N₀` with
   `Cdκ⁻²q j ≤ N₀`, level `100κ < L_{N₀}(α,E)` and pairing; note
   `Cdκ'⁻²q i₀ = 4Cdκ⁻²q i₀ ≤ Cdκ⁻²q j ≤ N₀`;
4. `persists_level_pairing` at `(α,E,N₀)` keeps the level and the pairing at the scale `N₀`
   for `(α',E')` in a neighbourhood;
5. choose `k > j` with `α' := p_k/q_k` in that neighbourhood and, via
   `Scale.spectral_continuity`, an energy `E' ∈ Σ_{p_k/q_k} ∩ K` with `|E'-E| < δ₀` where `δ₀`
   is smaller than `η`, `r` and `ε/(96 Kl)` (`Kl` = the crude Lipschitz constant at the *fixed*
   scale `N₀`);
6. S1 applied to the *shifted chain* `i ↦ (p_{i₀+i}, q_{i₀+i})` at the rational `p_k/q_k` and the
   energy `E'` gives `P(ω,E',N₀) ≤ L(ω,E') + B e^{-cκ'q i₀/8}`, where
   `P(α,E,N) = 2L_N(α,E) - L_{2N}(α,E)`;
7. the fixed-scale transfer together with the level/pairing persistence gives
   `P(α,E,N₀) ≤ P(ω,E',N₀) + ε/16` and `L(ω,E') ≤ M + log 6/q_k`.

Adding up, `L ≤ M + 5ε/16 < M + 2ε = L`, a contradiction.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.TMComp.RedC7T

open Work.TMC7Core

/-- **S1** of the lead's C7 design (the *finite rational tower*), as a single hypothesis, in the
exact shape of `Work.TMC7Core.Scale.rat_tower_lower` /
`Work.TMComp.C7Aux.rat_tower_lower`. -/
def RatTowerLower : Prop :=
  ∀ (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ), HasLDTOn lam K c C → HasLEBound lam K C₀ → c ≤ 1 →
    ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 200 → ∀ (b : ℝ), 0 < b →
      ∃ B T : ℝ, 0 < B ∧ ∀ (k : ℕ) (P : ℕ → ℤ) (Q : ℕ → ℕ),
        (∀ i ≤ k, 1 ≤ Q i) → (∀ i < k, Q i < Q (i + 1)) →
        (∀ i ≤ k, Nat.Coprime (Int.natAbs (P i)) (Q i)) →
        (∀ i < k, |(P k : ℝ) / (Q k) - (P i : ℝ) / (Q i)| < 1 / ((Q i : ℝ) ^ 2)) →
        (∀ i < k, (Q (i + 1) : ℝ) ≤ Real.exp (b * (Q i : ℝ))) →
        T ≤ (Q 0 : ℝ) →
        ∀ E ∈ K, ∀ N₀ : ℕ, C * (κ ^ 2)⁻¹ * (Q 0 : ℝ) ≤ (N₀ : ℝ) →
        200 * κ < lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀ →
        (9 / 10) * lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
            < lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀) →
        2 * lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀)
          - lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
          ≤ lyap ((P k : ℝ) / (Q k)) lam (E : ℂ)
            + B * Real.exp (-(c * κ * (Q 0 : ℝ) / 8))

/-- **The Diophantine case of C7 from S1.** -/
theorem D_BJ_dioph_of_tower (h1 : P_OpBasics) (h4 : P_LEBasics) (h15 : P_Schnol)
    (hS1 : RatTowerLower) :
    ∀ (α lam b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 →
      ∀ E : ℝ, E ∈ amoSpec α lam → lyap α lam (E : ℂ) = max 0 (Real.log |lam|) := by
  intro α lam b₀ hαirr hb₀pos hDio hlam E hE
  refine le_antisymm ?_ (max_log_le_lyap h4 α lam (E : ℂ))
  by_contra hcon
  push Not at hcon
  -- `hcon : max 0 (log |lam|) < lyap α lam ↑E`
  have hLpos : 0 < lyap α lam (E : ℂ) := lt_of_le_of_lt (le_max_left _ _) hcon
  set L : ℝ := lyap α lam (E : ℂ) with hLdef
  have hLpos' : 0 < L := by rw [hLdef]; exact hLpos
  set M : ℝ := max 0 (Real.log |lam|) with hMdef
  have hML : M < L := by rw [hMdef, hLdef]; exact hcon
  set ε : ℝ := (L - M) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hε16 : 0 < ε / 16 := by linarith
  have hε2 : M + 2 * ε = L := by rw [hεdef]; ring
  -- the level `κ`
  set κ : ℝ := min (L / 400) (1 / 100) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact lt_min (by linarith) (by norm_num)
  have hκ100 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  have hκL : 100 * κ < L := by
    have h' : κ ≤ L / 400 := by rw [hκdef]; exact min_le_left _ _
    linarith
  set κ' : ℝ := κ / 2 with hκ'def
  have hκ'pos : 0 < κ' := by rw [hκ'def]; linarith
  have hκ'200 : κ' ≤ 1 / 200 := by rw [hκ'def]; linarith
  have hκ'level : 200 * κ' = 100 * κ := by rw [hκ'def]; ring
  have hκ'inv : (κ' ^ 2)⁻¹ = 4 * (κ ^ 2)⁻¹ := by
    rw [hκ'def]; field_simp; ring
  -- the large deviation theorem and the level bound on `K`
  obtain ⟨c₀, Cd, r, hc₀pos, hCd1, hrpos, hLDT0⟩ := large_deviation_sound lam E
  set cc : ℝ := min c₀ 1 with hccdef
  have hccpos : 0 < cc := by rw [hccdef]; exact lt_min hc₀pos one_pos
  have hcc1 : cc ≤ 1 := by rw [hccdef]; exact min_le_right _ _
  set K : Set ℝ := Set.Icc (E - r) (E + r) with hKdef
  have hEK : E ∈ K := ⟨by linarith, by linarith⟩
  have hLDT : HasLDTOn lam K cc Cd := by
    rw [hccdef]; exact hLDT0.mono_const (lt_min hc₀pos one_pos) (min_le_left _ _)
  set C₀ : ℝ := max 1 (Real.log (Real.sqrt (((|E| + r) + 2 * |lam|) ^ 2 + 2))) with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hLEB : HasLEBound lam K C₀ := by
    rw [hC₀def]
    exact (Scale.hasLEBound_Icc lam (|E| + r) (add_nonneg (abs_nonneg E) hrpos.le)).mono
      (Icc_subset_Icc_abs (E := E) (r := r) hrpos.le)
  -- S1's constants
  obtain ⟨B, T, hBpos, hS1props⟩ :=
    hS1 lam K cc Cd C₀ hLDT hLEB hcc1 κ' hκ'pos hκ'200 b₀ hb₀pos
  -- the continued-fraction chain of `α`
  obtain ⟨A, q, n₀, hq1, hqmono, hqcop, hqapprox, hqcross, hqgrowth⟩ :=
    Scale.conv_chain_rational α hαirr b₀ hb₀pos hDio
  have hqge : ∀ n, q 0 + n ≤ q n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h : q n < q (n + 1) := hqmono (Nat.lt_succ_self n)
      calc q 0 + (n + 1) = (q 0 + n) + 1 := Nat.add_succ (q 0) n
        _ ≤ q n + 1 := Nat.add_le_add_right ih 1
        _ ≤ q (n + 1) := Nat.succ_le_of_lt h
  have hqtop : Tendsto (fun n : ℕ => (q n : ℝ)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨Nat.ceil (max b 0), fun n hn => ?_⟩
    have h1 : (q 0 : ℝ) + n ≤ (q n : ℝ) := by exact_mod_cast hqge n
    have h2 : b ≤ (Nat.ceil (max b 0) : ℝ) := le_trans (le_max_left b 0) (Nat.le_ceil _)
    have h3 : ((Nat.ceil (max b 0) : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- the closed form of the approximant sequence
  have hdist : Tendsto (fun k : ℕ => |α - (A k : ℝ) / (q k : ℝ)|) atTop (nhds 0) := by
    have hbound : ∀ k, |α - (A k : ℝ) / (q k : ℝ)| ≤ 1 / ((q k : ℝ) ^ 2) :=
      fun k => le_of_lt (hqapprox k)
    have hzero : Tendsto (fun k : ℕ => 1 / ((q k : ℝ) ^ 2)) atTop (nhds 0) := by
      have hp : Tendsto (fun k : ℕ => (q k : ℝ) ^ 2) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop] at hqtop ⊢
        intro b
        obtain ⟨n₁, hn₁⟩ := hqtop (max 1 b)
        refine ⟨n₁, fun n hn => ?_⟩
        have h1 : max 1 b ≤ (q n : ℝ) := hn₁ n hn
        have h2 : (0 : ℝ) ≤ (q n : ℝ) :=
          le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left (1 : ℝ) b)) h1
        nlinarith [h1, h2, le_max_left (1 : ℝ) b, le_max_right (1 : ℝ) b]
      have h1' : Tendsto (fun k : ℕ => (((q k : ℝ) ^ 2))⁻¹) atTop (nhds 0) :=
        Tendsto.inv_tendsto_atTop hp
      simpa only [one_div] using h1'
    exact squeeze_zero (fun k => abs_nonneg _) hbound hzero
  -- ## Step 1: the base index `i₀`
  have hccκ' : 0 < cc * κ' / 8 := by positivity
  have hevT : ∀ᶠ i : ℕ in atTop, T ≤ (q i : ℝ) := hqtop.eventually_ge_atTop T
  have hevI0 : ∀ᶠ i : ℕ in atTop, n₀ ≤ i := eventually_atTop.2 ⟨n₀, fun i hi => hi⟩
  have hevExp : ∀ᶠ i : ℕ in atTop,
      B * Real.exp (-(cc * κ' * (q i : ℝ) / 8)) < ε / 16 := by
    have harg : Tendsto (fun i : ℕ => cc * κ' * (q i : ℝ) / 8) atTop atTop := by
      have h1 : Tendsto (fun i : ℕ => (cc * κ' / 8) * (q i : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop hccκ' hqtop
      exact h1.congr (fun i => by ring)
    have h0 : Tendsto (fun i : ℕ => Real.exp (-(cc * κ' * (q i : ℝ) / 8))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
    exact (h0.const_mul B).eventually (eventually_lt_nhds (by simpa using hε16))
  obtain ⟨i₀, hi₀n, hi₀T, hi₀exp⟩ := (hevI0.and (hevT.and hevExp)).exists
  -- ## Step 2: the index `j` and the frozen scale `N₀`
  set m : ℕ := Nat.ceil (32 * C₀ / ε) + 3 with hmdef
  have hm3 : 3 ≤ m := by rw [hmdef]; omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hme : 2 * C₀ / (m : ℝ) < ε / 16 := by
    have h1' : 32 * C₀ / ε + 3 ≤ (m : ℝ) := by
      rw [hmdef]; push_cast
      linarith [Nat.le_ceil (32 * C₀ / ε)]
    have h4' : 32 * C₀ / ε ≤ (m : ℝ) := by linarith
    have h5' : 32 * C₀ ≤ (m : ℝ) * ε := (div_le_iff₀ hεpos).mp h4'
    have h6' : 32 * C₀ + 3 * ε ≤ (m : ℝ) * ε := by
      have hmul := mul_le_mul_of_nonneg_right h1' hεpos.le
      have he : (32 * C₀ / ε + 3) * ε = 32 * C₀ + 3 * ε := by field_simp
      linarith [hmul, he.le, he.ge]
    rw [div_lt_iff₀ hmpos]
    nlinarith [h6', hεpos, hC₀pos]
  have hCdκ : 0 < Cd * (κ ^ 2)⁻¹ := by
    refine mul_pos (lt_of_lt_of_le zero_lt_one hCd1) ?_
    positivity
  have hev4q : ∀ᶠ j : ℕ in atTop, 4 * (q i₀ : ℝ) ≤ (q j : ℝ) := hqtop.eventually_ge_atTop _
  have hevqC : ∀ᶠ j : ℕ in atTop, Cd * (κ ^ 2)⁻¹ ≤ (q j : ℝ) := hqtop.eventually_ge_atTop _
  have hevErr : ∀ᶠ j : ℕ in atTop,
      (12 * C₀ + 1000) * Real.exp (-(cc * κ * (q j : ℝ) / 4)) < ε / 16 := by
    have hccκ : 0 < cc * κ / 4 := by positivity
    have harg : Tendsto (fun j : ℕ => cc * κ * (q j : ℝ) / 4) atTop atTop := by
      have h1 : Tendsto (fun j : ℕ => (cc * κ / 4) * (q j : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop hccκ hqtop
      exact h1.congr (fun j => by ring)
    have h0 : Tendsto (fun j : ℕ => Real.exp (-(cc * κ * (q j : ℝ) / 4))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
    exact ((h0.const_mul (12 * C₀ + 1000))).eventually
      (eventually_lt_nhds (by simpa using hε16))
  have hevMr : ∀ᶠ j : ℕ in atTop, (m : ℝ) < Real.exp (cc * κ * (q j : ℝ) / 2) := by
    have harg : Tendsto (fun j : ℕ => cc * κ * (q j : ℝ) / 2) atTop atTop := by
      have h1 : Tendsto (fun j : ℕ => (cc * κ / 2) * (q j : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hqtop
      exact h1.congr (fun j => by ring)
    exact (Real.tendsto_exp_atTop.comp harg).eventually_gt_atTop ((m : ℝ))
  have hevJ : ∀ᶠ j : ℕ in atTop, i₀ < j := eventually_atTop.2 ⟨i₀ + 1, fun j hj => hj⟩
  obtain ⟨j, hi₀j, h4qj, hqCj, herrj, hmrj⟩ :=
    (hevJ.and (hev4q.and (hevqC.and (hevErr.and hevMr)))).exists
  have hq1j : 1 ≤ q j := hq1 j
  obtain ⟨N₀, hN₀dvd, hN₀1, hN₀ge, hN₀le, hN₀lev, hN₀pair⟩ :=
    Scale.base_pairing_bd (lam := lam) (K := K) (C₀ := C₀) (C := Cd) (κ := κ)
      hLEB hκpos hC₀pos hq1j hqCj hEK hκL
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₀1)
  have hN₀2 : 1 ≤ 2 * N₀ := by omega
  have hNQ : Cd * (κ' ^ 2)⁻¹ * (q i₀ : ℝ) ≤ (N₀ : ℝ) := by
    rw [hκ'inv]
    have h2 : Cd * (κ ^ 2)⁻¹ * (4 * (q i₀ : ℝ)) ≤ Cd * (κ ^ 2)⁻¹ * (q j : ℝ) :=
      mul_le_mul_of_nonneg_left h4qj hCdκ.le
    nlinarith [h2, hN₀ge]
  -- ## Step 3: persistence of the level and pairing at the scale `N₀`
  obtain ⟨η, hηpos, hηprop⟩ :=
    Scale.persists_level_pairing lam κ hκpos α E (A j) (q j) hq1j (hqapprox j) N₀ hN₀1
      hN₀lev hN₀pair
  -- the crude Lipschitz constants at the frozen scales
  set R : ℝ := |α| + |E| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hαR : |α| ≤ R := by rw [hRdef]; linarith [abs_nonneg E]
  have hER : |E| ≤ R := by rw [hRdef]; linarith [abs_nonneg α]
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Scale.lyapAvg_lipschitz lam N₀ hN₀1 R hRpos
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Scale.lyapAvg_lipschitz lam (2 * N₀) hN₀2 R hRpos
  set Kl : ℝ := max K₁ K₂ with hKldef
  have hKlpos : 0 < Kl := lt_of_lt_of_le hK₁pos (by rw [hKldef]; exact le_max_left _ _)
  have hK₁le : K₁ ≤ Kl := by rw [hKldef]; exact le_max_left _ _
  have hK₂le : K₂ ≤ Kl := by rw [hKldef]; exact le_max_right _ _
  set δ₀ : ℝ := min η (min 1 (min r (ε / (96 * Kl)))) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact lt_min hηpos (lt_min one_pos (lt_min hrpos (by positivity)))
  have hδ₀η : δ₀ ≤ η := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀1 : δ₀ ≤ 1 := by
    rw [hδ₀def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀r : δ₀ ≤ r := by
    rw [hδ₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀E : δ₀ ≤ ε / (96 * Kl) := by
    rw [hδ₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨δs, hδspos, hδs⟩ := Scale.spectral_continuity h1 lam α E hE δ₀ hδ₀pos
  -- ## Step 4: the index `k`
  have hδsη : ∀ᶠ k : ℕ in atTop, |α - (A k : ℝ) / (q k : ℝ)| < min δs η :=
    hdist.eventually (eventually_lt_nhds (lt_min hδspos hηpos))
  have hErrs : ∀ᶠ k : ℕ in atTop, |α - (A k : ℝ) / (q k : ℝ)| < ε / (96 * Kl) :=
    hdist.eventually (eventually_lt_nhds (by positivity))
  have hOnes : ∀ᶠ k : ℕ in atTop, |α - (A k : ℝ) / (q k : ℝ)| < 1 :=
    hdist.eventually (eventually_lt_nhds one_pos)
  have hlog6 : ∀ᶠ k : ℕ in atTop, Real.log 6 / (q k : ℝ) < ε / 16 := by
    have hzero : Tendsto (fun k : ℕ => Real.log 6 / (q k : ℝ)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds hqtop
    exact hzero.eventually (eventually_lt_nhds hε16)
  have hevK : ∀ᶠ k : ℕ in atTop, j < k := eventually_atTop.2 ⟨j + 1, fun k hk => hk⟩
  obtain ⟨k, hjk, hkδη, hkErr, hk1, hklog⟩ :=
    (hevK.and (hδsη.and (hErrs.and (hOnes.and hlog6)))).exists
  have hi₀k : i₀ ≤ k := le_of_lt (lt_trans hi₀j hjk)
  have hkδs : |α - (A k : ℝ) / (q k : ℝ)| < δs := lt_of_lt_of_le hkδη (min_le_left _ _)
  have hkη : |α - (A k : ℝ) / (q k : ℝ)| < η := lt_of_lt_of_le hkδη (min_le_right _ _)
  obtain ⟨E', hE'close, hE'mem⟩ :=
    hδs ((A k : ℝ) / (q k : ℝ)) (by rw [abs_sub_comm]; exact hkδs)
  have hE'η : |E' - E| < η := lt_of_lt_of_le hE'close hδ₀η
  have hE'r : |E' - E| < r := lt_of_lt_of_le hE'close hδ₀r
  have hE'1 : |E' - E| < 1 := lt_of_lt_of_le hE'close hδ₀1
  have hE'K : E' ∈ K := by
    rw [hKdef, Set.mem_Icc]
    have h := abs_lt.mp hE'r
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hα'R : |(A k : ℝ) / (q k : ℝ)| ≤ R := by
    have he : ((A k : ℝ) / (q k : ℝ) - α) + α = (A k : ℝ) / (q k : ℝ) := by ring
    have h1 : |(A k : ℝ) / (q k : ℝ)| ≤ |(A k : ℝ) / (q k : ℝ) - α| + |α| := by
      calc |(A k : ℝ) / (q k : ℝ)| = |((A k : ℝ) / (q k : ℝ) - α) + α| := by rw [he]
        _ ≤ |(A k : ℝ) / (q k : ℝ) - α| + |α| := abs_add_le _ _
    have hk1' : |(A k : ℝ) / (q k : ℝ) - α| < 1 := by
      simpa only [abs_sub_comm] using hk1
    rw [hRdef]; linarith [h1, hk1', abs_nonneg E]
  have hE'R : |E'| ≤ R := by
    have h1 : |E'| ≤ |E' - E| + |E| := by
      have he : (E' - E) + E = E' := by ring
      calc |E'| = |(E' - E) + E| := by rw [he]
        _ ≤ |E' - E| + |E| := abs_add_le _ _
    rw [hRdef]; linarith [h1, hE'1, abs_nonneg α]
  -- ## Step 5: the shifted chain and S1
  set P' : ℕ → ℤ := fun i => A (i₀ + i) with hP'def
  set Q' : ℕ → ℕ := fun i => q (i₀ + i) with hQ'def
  set κk : ℕ := k - i₀ with hκkdef
  have htopP : P' κk = A k := by
    rw [hP'def, hκkdef]
    show A (i₀ + (k - i₀)) = A k
    rw [Nat.add_sub_cancel' hi₀k]
  have htopQ : Q' κk = q k := by
    rw [hQ'def, hκkdef]
    show q (i₀ + (k - i₀)) = q k
    rw [Nat.add_sub_cancel' hi₀k]
  have hQ1' : ∀ i ≤ κk, 1 ≤ Q' i := by intro i _; rw [hQ'def]; exact hq1 (i₀ + i)
  have hQmono' : ∀ i < κk, Q' i < Q' (i + 1) := by
    intro i _; rw [hQ'def]; exact hqmono (by omega)
  have hQcop' : ∀ i ≤ κk, Nat.Coprime (Int.natAbs (P' i)) (Q' i) := by
    intro i _; rw [hP'def, hQ'def]; exact hqcop (i₀ + i)
  have hQcross' : ∀ i < κk, |(P' κk : ℝ) / (Q' κk) - (P' i : ℝ) / (Q' i)| < 1 / ((Q' i : ℝ) ^ 2) := by
    intro i hi
    rw [htopP, htopQ, hP'def, hQ'def]
    exact hqcross (i₀ + i) k (by omega)
  have hQgrowth' : ∀ i < κk, (Q' (i + 1) : ℝ) ≤ Real.exp (b₀ * (Q' i : ℝ)) := by
    intro i _; rw [hQ'def]; exact hqgrowth (i₀ + i) (by omega)
  have hTle : T ≤ (Q' 0 : ℝ) := by rw [hQ'def]; simpa using hi₀T
  have hα'η : |(A k : ℝ) / (q k : ℝ) - α| < η := by rw [abs_sub_comm]; exact hkη
  have hlev' : 200 * κ' < lyapAvg ((P' κk : ℝ) / (Q' κk)) lam (E' : ℂ) N₀ := by
    have h := (hηprop ((A k : ℝ) / (q k : ℝ)) E' hE'η hα'η).1
    rw [← htopP, ← htopQ] at h
    rw [hκ'level]; exact h
  have hpair' : (9 / 10) * lyapAvg ((P' κk : ℝ) / (Q' κk)) lam (E' : ℂ) N₀
      < lyapAvg ((P' κk : ℝ) / (Q' κk)) lam (E' : ℂ) (2 * N₀) := by
    have h := (hηprop ((A k : ℝ) / (q k : ℝ)) E' hE'η hα'η).2.1
    rw [← htopP, ← htopQ] at h
    exact h
  have hS1app := hS1props κk P' Q' hQ1' hQmono' hQcop' hQcross' hQgrowth' hTle E' hE'K N₀
    hNQ hlev' hpair'
  have hS1c : 2 * lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀)
      - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀
      ≤ lyap ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ)
        + B * Real.exp (-(cc * κ' * (q i₀ : ℝ) / 8)) := by
    rw [htopP, htopQ] at hS1app
    simpa only [hQ'def, Nat.add_zero] using hS1app
  -- the rational bound
  have hrat := Solutions.rat_bound h1 h15 (A k) (q k) (hq1 k) (hqcop k) lam E' hE'mem
  -- ## Step 6: the transfer at the frozen scale
  have hKlne : Kl ≠ 0 := ne_of_gt hKlpos
  have hE'δ : |E - E'| < ε / (96 * Kl) := by
    rw [abs_sub_comm]; exact lt_of_lt_of_le hE'close hδ₀E
  have hX : |α - (A k : ℝ) / (q k : ℝ)| + |E - E'| < ε / (48 * Kl) := by
    have hsum : ε / (96 * Kl) + ε / (96 * Kl) = ε / (48 * Kl) := by
      field_simp; ring
    linarith [add_lt_add hkErr hE'δ, hsum.le, hsum.ge]
  have hd2 := hK₂ α E ((A k : ℝ) / (q k : ℝ)) E' hαR hER hα'R hE'R
  have hd1 := hK₁ α E ((A k : ℝ) / (q k : ℝ)) E' hαR hER hα'R hE'R
  have htrans : (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
      ≤ (2 * lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀) + ε / 16 := by
    have hdiff : (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        - (2 * lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀)
        = 2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀))
          - (lyapAvg α lam (E : ℂ) N₀
            - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀) := by ring
    have hA : (lyapAvg α lam (E : ℂ) (2 * N₀)
          - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀))
        ≤ K₂ * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|) :=
      le_trans (le_abs_self _) hd2
    have hB : -(lyapAvg α lam (E : ℂ) N₀
          - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀)
        ≤ K₁ * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|) := by
      have h := neg_le_abs (lyapAvg α lam (E : ℂ) N₀
        - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀)
      linarith [h, hd1]
    have hXX : (0 : ℝ) ≤ |α - (A k : ℝ) / (q k : ℝ)| + |E - E'| := by positivity
    have hKle : 2 * (K₂ * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|))
        + K₁ * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|)
        ≤ 3 * Kl * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|) := by
      nlinarith [hK₂le, hK₁le, hXX]
    have hfin : (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        - (2 * lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) N₀)
        ≤ 3 * Kl * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|) := by
      rw [hdiff]
      have h2A : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) (2 * N₀))
          ≤ 2 * (K₂ * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|)) := by linarith [hA]
      linarith [h2A, hB, hKle]
    have hsmall : 3 * Kl * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|) < ε / 16 := by
      have h3 : (0 : ℝ) < 3 * Kl := by linarith
      calc 3 * Kl * (|α - (A k : ℝ) / (q k : ℝ)| + |E - E'|)
          < 3 * Kl * (ε / (48 * Kl)) := by
            exact mul_lt_mul_of_pos_left hX h3
        _ = ε / 16 := by field_simp; ring
    linarith [hfin, hsmall]

  -- ## Step 7: `psi_upper` and the contradiction
  have hψup : L + lyapAvg α lam (E : ℂ) N₀ - 2 * lyapAvg α lam (E : ℂ) (2 * N₀)
      ≤ (12 * C₀ + 1000) * Real.exp (-(cc * κ * (q j : ℝ) / 4)) + 2 * C₀ / (m : ℝ) := by
    have h := Scale.psi_upper lam K cc Cd C₀ hLDT hLEB hcc1 κ hκpos hκ100 E hEK α (A j) (q j)
      hq1j (hqcop j) hqCj (hqapprox j) N₀ hN₀ge hκL hN₀pair m hm3 hmrj
    rw [hLdef]; exact h
  have hmain : L ≤ M + ε / 8 + ε / 16
      + B * Real.exp (-(cc * κ' * (q i₀ : ℝ) / 8)) + Real.log 6 / (q k : ℝ) := by
    have h1' : L ≤ (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        + ((12 * C₀ + 1000) * Real.exp (-(cc * κ * (q j : ℝ) / 4)) + 2 * C₀ / (m : ℝ)) := by
      linarith [hψup]
    have hsum : (12 * C₀ + 1000) * Real.exp (-(cc * κ * (q j : ℝ) / 4)) + 2 * C₀ / (m : ℝ)
        < ε / 8 := by linarith [herrj, hme]
    have h3' : lyap ((A k : ℝ) / (q k : ℝ)) lam (E' : ℂ) ≤ M + Real.log 6 / (q k : ℝ) := by
      rw [hMdef]; exact hrat
    linarith [h1', hsum, htrans, hS1c, h3']
  have hlt : M + 5 * (ε / 16) < L := by
    rw [← hε2]; linarith
  have hfin : L ≤ M + 5 * (ε / 16) := by
    have hb : B * Real.exp (-(cc * κ' * (q i₀ : ℝ) / 8)) < ε / 16 := hi₀exp
    have hlo : Real.log 6 / (q k : ℝ) < ε / 16 := hklog
    linarith [hmain, hb, hlo]
  exact absurd (lt_of_le_of_lt hfin hlt) (lt_irrefl L)

/-- The Diophantine case of C7 in the *frozen* `Work.TMContract` vocabulary. -/
theorem D_BJ_dioph_of_tower' (h1 : P_OpBasics) (h4 : P_LEBasics) (h15 : P_Schnol)
    (hS1 : RatTowerLower) :
    ∀ (α lam b₀ : ℝ), Irrational α → 0 < b₀ → Work.TMContract.DiophBelow α b₀ → lam ≠ 0 →
      ∀ E : ℝ, E ∈ Work.TMContract.amoSpec α lam →
        Work.TMContract.lyap α lam (E : ℂ) = max 0 (Real.log |lam|) := by
  intro α lam b₀ hα hb hD hlam E hE
  have h := D_BJ_dioph_of_tower h1 h4 h15 hS1 α lam b₀ hα hb hD hlam E hE
  simpa only [Work.TMC7Core.Bridge.lyap_eq] using h

end Work.TMComp.RedC7T
