import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.BJ
import Submission.Work.TMC7Core.Sound.LDT
import Submission.Work.TMC7Core.Solutions.rat_bound
import Submission.Work.TMC7Core.Scale.hasLEBound_Icc
import Submission.Work.TMC7Core.Scale.exists_approx_seq
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.psi_upper
import Submission.Work.TMC7Core.Scale.psi_lower_rat
import Submission.Work.TMC7Core.Scale.base_pairing_bd

/-!
# `P_BJ` from two Lipschitz inputs (no Proposition 9, no scale chain)

`p_bj_of_inputs` proves the Bourgain--Jitomirskaya component `P_BJ` — the formula
`lyap α lam (E:ℂ) = max 0 (log |lam|)` for `E ∈ amoSpec α lam`, `α` irrational, `lam ≠ 0` —
from the components `P_OpBasics`, `P_LEBasics`, `P_Schnol` together with **two** quantitative
statements about the finite-scale averages `L_N(α,E) = lyapAvg α lam (E:ℂ) N`, and nothing else.
In particular the exponential-in-`q` conclusion of [BJ] Proposition 9 (which is *false* at
rational frequencies: the doubling defect there is only polynomial) is never used.

The two inputs:

* `hαLip : |L_N(α,E) - L_N(α',E)| ≤ 2π|λ|N|α - α'|`   (`Scale/alpha_lipschitz`);
* `hEuni : ∀ε>0 ∃δ>0 ∀N ≥ 1, |E - E'| < δ → |L_N(α,E) - L_N(α,E')| < ε`   (`Scale/E_uniform`),
  a continuity modulus in the energy that is *uniform* in the scale `N`.

Both are Lipschitz/continuity statements about `(1/N)∫log‖A_N‖`, and the second one is
elementary-looking ("the energy dependence of the finitely many factors"), while the first is
the classical "phase-shift" Lipschitz bound.

## Proof

Assume `L := lyap α lam (E:ℂ) > M := max 0 (log|λ|)`, put `ε := (L-M)/2 > 0` and
`κ := min (L/400) (1/100)`, so that `100κ < L` (via `lyap ≤ L_N`, `Scale.lyap_le_lyapAvg`).

1. `K := [E-r,E+r]` comes from the sound large deviation theorem
   (`TMC7Core.large_deviation_sound`), `C₀` is the level bound on `K` (`hasLEBound_Icc`).
2. By `hEuni` there is `δ_E > 0` with the energy-modulus `ε/16` at every scale `N ≥ 1`; by
   `Scale.spectral_continuity` there is `δ_s > 0` such that every `α'` with `|α'-α| < δ_s`
   carries a spectral point `E'` with `|E'-E| < min δ_E 1 r`.
3. Take a Dirichlet approximant `a/q` of `α` (`Scale.exists_approx_seq`) with `q` so large that
   the seven numerical conditions below hold — all of them eventual in `q` and all with
   *fixed* constants, so `n` can be chosen after `δ_E`, `δ_s` are known.
4. `Scale.base_pairing_bd` produces `N₀ = m₀ q` with `Cd κ⁻² q ≤ N₀ ≤ W q` (`W` explicit), the
   level `100κ < L_{N₀}` and the pairing `(9/10)L_{N₀} < L_{2N₀}`.
5. `Scale.psi_upper` at `(α,E)` bounds `ψ := L + L_{N₀} - 2L_{2N₀}` from above by
   `(12C₀+1000)e^{-cκq/4} + 2C₀/m`, and `Scale.psi_lower_rat` at the *same scale* `m₀q = N₀`
   bounds it from below at the rational point `a/q` by `-(log 2)/N₀` (this is the classical
   doubling estimate `LocCantor.defect_upper`; at a rational frequency the defect really is
   polynomial, not exponential).
6. The energy mismatch `E → E'` costs `3ε/16` by `hEuni`; the frequency mismatch costs
   `6π|λ|W/q < ε/4` by `hαLip` together with `N₀ ≤ W q` and `|α - a/q| < 1/q²`.
7. `Solutions.rat_bound` gives `L(a/q,E') ≤ M + log 6/q`.

Collecting, `L ≤ M + 12ε/16 < M + ε = (L+M)/2 < L`, a contradiction.
-/

set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-- The explicit upper-bound constant of `Scale.base_pairing_bd`. -/
def Wtower (C₀ C κ : ℝ) : ℕ :=
  max 1 (Nat.ceil (C * (κ ^ 2)⁻¹)) * 2 ^ (Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1)

theorem p_bj_of_inputs (h1 : P_OpBasics) (h4 : P_LEBasics) (h15 : P_Schnol)
    (hαLip : ∀ (lam : ℝ) (R : ℝ), 0 < R → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ (α α' E : ℝ), |α| ≤ R → |α'| ≤ R → |E| ≤ R →
      |lyapAvg α lam (E : ℂ) N - lyapAvg α' lam (E : ℂ) N| ≤ C * (N : ℝ) * |α - α'|)
    (hEuni : ∀ (lam : ℝ), lam ≠ 0 → ∀ (R : ℝ), 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (α E E' : ℝ),
        |α| ≤ R → |E| ≤ R → |E'| ≤ R → |E - E'| < δ →
        |lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E' : ℂ) N| < ε) :
    P_BJ := by
  intro α lam hα hlam E hE
  refine le_antisymm ?_ (max_log_le_lyap h4 α lam (E : ℂ))
  by_contra hcon
  push Not at hcon
  set L : ℝ := lyap α lam (E : ℂ) with hLdef
  set M : ℝ := max 0 (Real.log |lam|) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hLpos : 0 < L := lt_of_le_of_lt hMnn hcon
  set ε : ℝ := (L - M) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hε16 : 0 < ε / 16 := by linarith
  have hε4 : 0 < ε / 4 := by linarith
  set κ : ℝ := min (L / 400) (1 / 100) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact lt_min (by linarith) (by norm_num)
  have hκ100 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  have hκL : 100 * κ < L := by
    have h1' : κ ≤ L / 400 := by rw [hκdef]; exact min_le_left _ _
    linarith
  -- the large deviation theorem and the level bound
  obtain ⟨c₀, Cd, r, hc₀pos, hCd1, hrpos, hLDT0⟩ := large_deviation_sound lam E
  set K : Set ℝ := Set.Icc (E - r) (E + r) with hKdef
  have hEK : E ∈ K := ⟨by linarith, by linarith⟩
  have hc1'pos : 0 < min c₀ 1 := lt_min hc₀pos one_pos
  have hLDT : HasLDTOn lam K (min c₀ 1) Cd := hLDT0.mono_const hc1'pos (min_le_left _ _)
  have hLEB : HasLEBound lam K (max 1 (Real.log (Real.sqrt (((|E| + r) + 2 * |lam|) ^ 2 + 2)))) :=
    (Scale.hasLEBound_Icc lam (|E| + r) (add_nonneg (abs_nonneg E) hrpos.le)).mono
      (Icc_subset_Icc_abs (E := E) (r := r) hrpos.le)
  set C₀ : ℝ := max 1 (Real.log (Real.sqrt (((|E| + r) + 2 * |lam|) ^ 2 + 2))) with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  -- the two radii
  set R : ℝ := |α| + |E| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hαR : |α| ≤ R := by rw [hRdef]; linarith [abs_nonneg E]
  have hER : |E| ≤ R := by rw [hRdef]; linarith [abs_nonneg α]
  obtain ⟨δ_E, hδEpos, hδE⟩ := hEuni lam hlam R hRpos (ε / 16) hε16
  obtain ⟨CL, hCLpos, hCL⟩ := hαLip lam R hRpos
  have hδspos' : 0 < min δ_E (min 1 (min 1 r)) :=
    lt_min hδEpos (lt_min one_pos (lt_min one_pos hrpos))
  obtain ⟨δ_s, hδspos, hδs⟩ :=
    Scale.spectral_continuity h1 lam α E hE (min δ_E (min 1 (min 1 r))) hδspos'
  -- the Dirichlet sequence
  obtain ⟨a, q, hq1, hqtend, hqcop, hqapprox⟩ := Scale.exists_approx_seq α hα
  have hqtop : Tendsto (fun n : ℕ => (q n : ℝ)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop] at hqtend ⊢
    intro b
    obtain ⟨n₀, hn₀⟩ := hqtend ⌈max b 0⌉₊
    refine ⟨n₀, fun n hn => ?_⟩
    have h1' : (⌈max b 0⌉₊ : ℝ) ≤ ((q n : ℕ) : ℝ) := by exact_mod_cast hn₀ n hn
    have h2' : b ≤ (⌈max b 0⌉₊ : ℝ) := le_trans (le_max_left b 0) (Nat.le_ceil _)
    linarith
  -- the free multiplier
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
  -- the explicit tower constant
  set W : ℕ := Wtower C₀ Cd κ with hWdef
  -- the eventual conditions
  have ev_qC : ∀ᶠ n : ℕ in atTop, Cd * (κ ^ 2)⁻¹ ≤ (q n : ℝ) :=
    hqtop.eventually_ge_atTop _
  have hκ2inv : (0 : ℝ) < Cd * (κ ^ 2)⁻¹ := by
    have : 0 < (κ ^ 2)⁻¹ := by positivity
    positivity
  have ev_err : ∀ᶠ n : ℕ in atTop,
      (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q n : ℝ) / 4)) < ε / 16 := by
    have harg : Tendsto (fun n : ℕ => (min c₀ 1) * κ * ((q n : ℕ) : ℝ) / 4) atTop atTop := by
      have h1' : Tendsto (fun n : ℕ => ((min c₀ 1) * κ / 4) * ((q n : ℕ) : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hqtop
      exact h1'.congr (fun n => by ring)
    have h0' : Tendsto (fun n : ℕ =>
        Real.exp (-((min c₀ 1) * κ * ((q n : ℕ) : ℝ) / 4))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
    have h0 : Tendsto (fun n : ℕ =>
        (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * ((q n : ℕ) : ℝ) / 4))) atTop (nhds 0) := by
      simpa using h0'.const_mul (12 * C₀ + 1000)
    exact h0.eventually (eventually_lt_nhds hε16)
  have ev_m : ∀ᶠ n : ℕ in atTop, ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q n : ℝ) / 2) := by
    have harg : Tendsto (fun n : ℕ => (min c₀ 1) * κ * ((q n : ℕ) : ℝ) / 2) atTop atTop := by
      have h1' : Tendsto (fun n : ℕ => ((min c₀ 1) * κ / 2) * ((q n : ℕ) : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hqtop
      exact h1'.congr (fun n => by ring)
    exact (Real.tendsto_exp_atTop.comp harg).eventually_gt_atTop ((m : ℕ) : ℝ)
  have ev_log2 : ∀ᶠ n : ℕ in atTop,
      Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q n : ℝ)) < ε / 16 := by
    have h0 : Tendsto (fun n : ℕ => Real.log 2 / (Cd * (κ ^ 2)⁻¹ * ((q n : ℕ) : ℝ))) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop hκ2inv hqtop)
    exact h0.eventually (eventually_lt_nhds hε16)
  have ev_log6 : ∀ᶠ n : ℕ in atTop, Real.log 6 / (q n : ℝ) < ε / 16 :=
    (Tendsto.div_atTop tendsto_const_nhds hqtop).eventually (eventually_lt_nhds hε16)
  have ev_δs : ∀ᶠ n : ℕ in atTop, |α - (a n : ℝ) / (q n : ℝ)| < δ_s := by
    have hbound : ∀ n : ℕ, |α - (a n : ℝ) / (q n : ℝ)| ≤ 1 / ((q n : ℝ) ^ 2) :=
      fun n => le_of_lt (hqapprox n)
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((q n : ℝ) ^ 2)) atTop (nhds 0) := by
      have hp : Tendsto (fun n : ℕ => (q n : ℝ) ^ 2) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop] at hqtop ⊢
        intro b
        obtain ⟨n₀, hn₀⟩ := hqtop (max 1 b)
        refine ⟨n₀, fun n hn => ?_⟩
        have h1' : max 1 b ≤ (q n : ℝ) := hn₀ n hn
        have h2' : (0 : ℝ) ≤ (q n : ℝ) :=
          le_trans (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left (1:ℝ) b)) h1'
        nlinarith [h1', h2', le_max_left (1:ℝ) b, le_max_right (1:ℝ) b]
      have h1' : Tendsto (fun n : ℕ => (((q n : ℝ) ^ 2))⁻¹) atTop (nhds 0) :=
        Tendsto.inv_tendsto_atTop hp
      simpa only [one_div] using h1'
    have h0 : Tendsto (fun n : ℕ => |α - (a n : ℝ) / (q n : ℝ)|) atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hbound hzero
    exact h0.eventually (eventually_lt_nhds hδspos)
  have ev_lip : ∀ᶠ n : ℕ in atTop,
      5 * CL * (W : ℝ) / (q n : ℝ) < ε / 4 :=
    (Tendsto.div_atTop tendsto_const_nhds hqtop).eventually (eventually_lt_nhds hε4)
  -- pick `n`
  have hAll : ∀ᶠ n : ℕ in atTop,
      Cd * (κ ^ 2)⁻¹ ≤ (q n : ℝ) ∧
      (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q n : ℝ) / 4)) < ε / 16 ∧
      ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q n : ℝ) / 2) ∧
      Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q n : ℝ)) < ε / 16 ∧
      Real.log 6 / (q n : ℝ) < ε / 16 ∧
      |α - (a n : ℝ) / (q n : ℝ)| < δ_s ∧
      5 * CL * (W : ℝ) / (q n : ℝ) < ε / 4 := by
    filter_upwards [ev_qC, ev_err, ev_m, ev_log2, ev_log6, ev_δs, ev_lip] with n h1' h2' h3' h4' h5' h6' h7'
    exact ⟨h1', h2', h3', h4', h5', h6', h7'⟩
  obtain ⟨n, hnqC, hnerr, hnexp, hnlog2, hnlog6, hnδs, hnlip⟩ := hAll.exists
  have hqn1 : 1 ≤ q n := hq1 n
  have hqnpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqn1)
  -- the base scale
  obtain ⟨N₀, hN₀dvd, hN₀1, hN₀ge, hN₀le, hN₀lev, hN₀pair⟩ :=
    Scale.base_pairing_bd (lam := lam) (K := K) (C₀ := C₀) (C := Cd) (κ := κ)
      hLEB hκpos hC₀pos (α := α) (q := q n) hqn1 hnqC hEK (by rw [← hLdef]; exact hκL)
  obtain ⟨m₀, hm₀⟩ := hN₀dvd
  have hm₀1 : 1 ≤ m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hm₀; omega
    · exact h0
  have hN₀eq : N₀ = m₀ * q n := by rw [hm₀, Nat.mul_comm]
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₀1)
  -- the energy at the rational point
  obtain ⟨E', hE'close, hE'mem⟩ :=
    hδs ((a n : ℝ) / (q n : ℝ)) (by rw [abs_sub_comm]; exact hnδs)
  have hE'δ' : |E' - E| < δ_E := lt_of_lt_of_le hE'close (min_le_left _ _)
  have hE'δ : |E - E'| < δ_E := by rw [abs_sub_comm]; exact hE'δ'
  have hE'1' : |E' - E| < 1 := lt_of_lt_of_le hE'close (le_trans (min_le_right _ _) (min_le_left _ _))
  have hE'1 : |E - E'| < 1 := by rw [abs_sub_comm]; exact hE'1'
  have hE'r : |E' - E| < r :=
    lt_of_lt_of_le hE'close (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hE'K : E' ∈ K := by
    rw [hKdef, Set.mem_Icc]
    have h := abs_lt.mp hE'r
    constructor <;> linarith [h.1, h.2]
  have hE'R : |E'| ≤ R := by
    have h1' : |E'| ≤ |E' - E| + |E| := by
      calc |E'| = |(E' - E) + E| := by ring_nf
        _ ≤ |E' - E| + |E| := abs_add_le _ _
    rw [hRdef]; linarith [le_of_lt hE'1', abs_nonneg α]
  -- ψ upper at the irrational point
  have hψup : L + lyapAvg α lam (E : ℂ) N₀ - 2 * lyapAvg α lam (E : ℂ) (2 * N₀)
      ≤ (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q n : ℝ) / 4)) + 2 * C₀ / (m : ℝ) := by
    have h := Scale.psi_upper lam K (min c₀ 1) Cd C₀ hLDT hLEB (min_le_right _ _) κ hκpos hκ100
      E hEK α (a n) (q n) hqn1 (hqcop n) hnqC (hqapprox n) N₀ hN₀ge
      (by rw [← hLdef]; exact hκL) hN₀pair m hm3 hnexp
    rw [hLdef]; exact h
  -- ψ lower at the rational point
  have hψlow : -(Real.log 2) / (N₀ : ℝ)
      ≤ lyap ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ)
        + lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀
        - 2 * lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀) := by
    rw [hN₀eq]
    exact Scale.psi_lower_rat (a n) (q n) hqn1 lam E' m₀ hm₀1
  -- the energy cross-term
  have hcross_E : |(2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
      - (2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀)| < ε / 4 := by
    have h2N : 1 ≤ 2 * N₀ := by omega
    have hA : |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀)| < ε / 16 :=
      hδE (2 * N₀) h2N α E E' hαR hER hE'R hE'δ
    have hB : |lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀| < ε / 16 :=
      hδE N₀ hN₀1 α E E' hαR hER hE'R hE'δ
    have h4' : (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        - (2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀)
        = 2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀))
          - (lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀) := by ring
    rw [h4']
    have h5' : |2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀))
        - (lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀)|
        ≤ 2 * |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀)|
          + |lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀| := by
      calc |2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀))
            - (lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀)|
          ≤ |2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀))|
            + |lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀| := by
            have h := abs_sub_le (2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
              - lyapAvg α lam (E' : ℂ) (2 * N₀))) 0
              (lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀)
            simpa only [sub_zero, zero_sub, abs_neg] using h
        _ = 2 * |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) (2 * N₀)|
            + |lyapAvg α lam (E : ℂ) N₀ - lyapAvg α lam (E' : ℂ) N₀| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  -- the frequency cross-term
  have hcross_α : |(2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀)
      - (2 * lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)| < ε / 4 := by
    have h2N : 1 ≤ 2 * N₀ := by omega
    have hα'R : |(a n : ℝ) / (q n : ℝ)| ≤ R := by
      have h1' : |(a n : ℝ) / (q n : ℝ)| ≤ |α - (a n : ℝ) / (q n : ℝ)| + |α| := by
        calc |(a n : ℝ) / (q n : ℝ)| = |((a n : ℝ) / (q n : ℝ) - α) + α| := by ring_nf
          _ ≤ |(a n : ℝ) / (q n : ℝ) - α| + |α| := abs_add_le _ _
          _ = |α - (a n : ℝ) / (q n : ℝ)| + |α| := by rw [abs_sub_comm]
      have h2' : |α - (a n : ℝ) / (q n : ℝ)| < 1 := by
        have h3' : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqn1
        have h4' : 1 / ((q n : ℝ) ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [h3']
        linarith [hqapprox n, h4']
      have h5' : |α| ≤ R - 1 := by rw [hRdef]; linarith [abs_nonneg E]
      linarith [h1', h2', h5']
    have hA : |lyapAvg α lam (E' : ℂ) (2 * N₀)
        - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)|
        ≤ CL * (((2 * N₀ : ℕ)) : ℝ) * |α - (a n : ℝ) / (q n : ℝ)| :=
      hCL (2 * N₀) h2N α ((a n : ℝ) / (q n : ℝ)) E' hαR hα'R hE'R
    have hB : |lyapAvg α lam (E' : ℂ) N₀
        - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀|
        ≤ CL * (N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)| :=
      hCL N₀ hN₀1 α ((a n : ℝ) / (q n : ℝ)) E' hαR hα'R hE'R
    have h2N0cast : (((2 * N₀ : ℕ)) : ℝ) = 2 * (N₀ : ℝ) := by push_cast; ring
    have hsmall : 2 * (CL * (((2 * N₀ : ℕ)) : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|)
        + CL * (N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|
        ≤ 5 * CL * (W : ℝ) / (q n : ℝ) := by
      have hqn2 : (0 : ℝ) < (q n : ℝ) ^ 2 := by positivity
      have hstep : (N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)| ≤ (W : ℝ) / (q n : ℝ) := by
        have h1' : (N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|
            ≤ ((W : ℝ) * (q n : ℝ)) * (1 / ((q n : ℝ) ^ 2)) := by
          apply mul_le_mul hN₀le (le_of_lt (hqapprox n)) (abs_nonneg _) (le_of_lt (by positivity))
        have h2' : ((W : ℝ) * (q n : ℝ)) * (1 / ((q n : ℝ) ^ 2)) = (W : ℝ) / (q n : ℝ) := by
          field_simp
        linarith [h1', h2'.le, h2'.ge]
      have hcast :
          2 * (CL * (((2 * N₀ : ℕ)) : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|)
          + CL * (N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|
          = 5 * CL * ((N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|) := by
        rw [h2N0cast]; ring
      rw [hcast]
      have h0 : (0 : ℝ) ≤ 5 * CL := by linarith [hCLpos]
      calc 5 * CL * ((N₀ : ℝ) * |α - (a n : ℝ) / (q n : ℝ)|)
          ≤ 5 * CL * ((W : ℝ) / (q n : ℝ)) := mul_le_mul_of_nonneg_left hstep h0
        _ = 5 * CL * (W : ℝ) / (q n : ℝ) := by ring
    have h4' : (2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀)
        - (2 * lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)
            - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)
        = 2 * (lyapAvg α lam (E' : ℂ) (2 * N₀)
            - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀))
          - (lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀) := by
      ring
    rw [h4']
    have h5' : |2 * (lyapAvg α lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀))
        - (lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)|
        ≤ 2 * |lyapAvg α lam (E' : ℂ) (2 * N₀)
            - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)|
          + |lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀| := by
      calc |2 * (lyapAvg α lam (E' : ℂ) (2 * N₀)
            - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀))
          - (lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)|
          ≤ |2 * (lyapAvg α lam (E' : ℂ) (2 * N₀)
              - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀))|
            + |lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀| := by
              have h := abs_sub_le (2 * (lyapAvg α lam (E' : ℂ) (2 * N₀)
                - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀))) 0
                (lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)
              simpa only [sub_zero, zero_sub, abs_neg] using h
        _ = 2 * |lyapAvg α lam (E' : ℂ) (2 * N₀)
              - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)|
            + |lyapAvg α lam (E' : ℂ) N₀ - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h5', hA, hB, hsmall, hnlip]
  -- rat_bound
  have hrat := Solutions.rat_bound h1 h15 (a n) (q n) hqn1 (hqcop n) lam E' hE'mem
  -- the chain
  have hlog2 : Real.log 2 / (N₀ : ℝ) < ε / 16 := by
    have h1' : Real.log 2 / (N₀ : ℝ) ≤ Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q n : ℝ)) := by
      rw [div_le_div_iff₀ hN₀pos (by positivity)]
      nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2), hN₀ge, hκ2inv, hqnpos]
    linarith [h1', hnlog2]
  have hmain : L ≤ M + 12 * ε / 16 := by
    have h1' : L ≤ (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        + (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q n : ℝ) / 4)) + 2 * C₀ / (m : ℝ) := by
      linarith [hψup]
    have h2' : (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
        ≤ (2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀) + ε / 4 := by
      have h := (abs_lt.mp hcross_E).2
      linarith [h]
    have h3' : (2 * lyapAvg α lam (E' : ℂ) (2 * N₀) - lyapAvg α lam (E' : ℂ) N₀)
        ≤ (2 * lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)
            - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀) + ε / 4 := by
      have h := (abs_lt.mp hcross_α).2
      linarith [h]
    have h4' : (2 * lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) (2 * N₀)
          - lyapAvg ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) N₀)
        ≤ lyap ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) + Real.log 2 / (N₀ : ℝ) := by
      have h := hψlow
      rw [neg_div] at h
      linarith [h]
    have h5' : lyap ((a n : ℝ) / (q n : ℝ)) lam (E' : ℂ) ≤ M + Real.log 6 / (q n : ℝ) := by
      rw [hMdef]; exact hrat
    have h6' : (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q n : ℝ) / 4)) < ε / 16 := hnerr
    linarith [h1', h2', h3', h4', h5', h6', hme, hlog2, hnlog6]
  have hfin : L < L := by
    have hlt : M + 12 * ε / 16 < L := by
      have : ε = (L - M) / 2 := hεdef
      rw [this]; linarith
    linarith [hmain, hlt]
  exact absurd hfin (lt_irrefl L)

end Work.TMC7Core

end
