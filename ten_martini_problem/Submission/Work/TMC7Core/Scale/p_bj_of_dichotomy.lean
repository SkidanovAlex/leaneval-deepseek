import Mathlib
import Submission.Work.TMC7Core.Scale.pbj_assembly
import Submission.Work.TMC7Core.Scale.psi_upper
import Submission.Work.TMC7Core.Scale.psi_lower_rat
import Submission.Work.TMC7Core.Scale.base_pairing_bd
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz_lipK
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMC7Core.Scale.lipK_le_exp
import Submission.Work.TMC7Core.Scale.conv_chain_rational
import Submission.Work.TMC7Core.Scale.liouville_approx
import Submission.Work.TMC7Core.Scale.qsc
import Submission.Work.TMC7Core.Scale.rat_bound_phase
import Submission.Work.TMC7Core.Scale.rat_tower_lower
import Submission.Work.TMC7Core.Scale.rat_tower_lower_v2
import Submission.Work.TMC7Core.Solutions.rat_bound
import Submission.Work.TMC7Core.Sound.LDT
import Submission.Work.TMC7Core.Scale.persists_level_pairing

/-!
# S6 of the C7 design: the dichotomy assembly

`p_bj_of_dichotomy` proves `P_BJ` from the components `P_OpBasics`, `P_LEBasics`, `P_Schnol`
alone, by the dichotomy of `Submission/Work/TMC7Core/C7_INPUTS_LEAD.md` §2:

* Case I (`LiouvilleAbove α b*`): exponentially good approximants (S3 `liouville_approx`),
  spectral closeness at a free phase (S4 `qsc`), the rational bound at that phase
  (S5 `rat_bound_phase`), and the *crude* Lipschitz transfer at the scale `N₀ ≤ W q`
  supplied by `lyapAvg_lipschitz_lipK` + S0 `lipK_le_exp`.
* Case II (`DiophBelow α b*`): continued fraction convergents (S2 `conv_chain_rational`),
  a frozen base scale `N₀` (`base_pairing_bd`), the persistence of level/pairing at that
  scale (`persists_level_pairing`), and the finite rational tower S1
  (`rat_tower_lower_v2`) closing with `rat_bound`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

set_option maxHeartbeats 10000000

/-- **S6** of the lead's C7 design — the final C7 assembly.

Read `Submission/Work/TMC7Core/S6_STATUS.md` (my plan, with the constants and both error
ledgers), `Submission/Work/TMC7Core/C7_INPUTS_LEAD.md` §2 (the lead's design) and
`Submission/Work/TMC7Core/Scale/pbj_assembly.lean` (the **axiom-clean, compiling template**:
Case I is that proof with its two Lipschitz hypotheses discharged by `lyapAvg_lipschitz` — the
crude constant `lipK` suffices in Case I because `|α − a/q| < e^{−b*q}` and `|E − E'| ≤
(9+16π|λ|)e^{−b*q/2}` while `N₀ ≤ Wq`, and in Case II because `N₀` is fixed before the
approximant — and with the rational side supplied by S4 `qsc` + S5 `rat_bound_phase`).

Case split on `LiouvilleAbove α b*`, `b* = 4ΓW + 2`, `Γ = log (lipM λ R) + 2`,
`κ' = κ/2`, `W = Wtower C₀ Cd κ`; Case I uses `liouville_approx` (S3), Case II uses
`conv_chain_rational` (S2) + `rat_tower_lower` (S1) + `persists_level_pairing`. -/
theorem p_bj_of_dichotomy (h1 : Work.TMC7Core.P_OpBasics) (h4 : Work.TMC7Core.P_LEBasics)
    (h15 : Work.TMC7Core.P_Schnol) : Work.TMC7Core.P_BJ := by
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
  have hε8 : 0 < ε / 8 := by linarith
  have hLMε : M + 2 * ε = L := by rw [hεdef]; ring
  set κ : ℝ := min (L / 400) (1 / 100) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact lt_min (by linarith) (by norm_num)
  have hκ100 : κ ≤ 1 / 100 := by rw [hκdef]; exact min_le_right _ _
  have hκL : 100 * κ < L := by
    have h1' : κ ≤ L / 400 := by rw [hκdef]; exact min_le_left _ _
    linarith
  obtain ⟨c₀, Cd, r, hc₀pos, hCd1, hrpos, hLDT0⟩ := large_deviation_sound lam E
  set K : Set ℝ := Set.Icc (E - r) (E + r) with hKdef
  have hEK : E ∈ K := ⟨by linarith, by linarith⟩
  have hc1'pos : 0 < min c₀ 1 := lt_min hc₀pos one_pos
  have hLDT : HasLDTOn lam K (min c₀ 1) Cd := hLDT0.mono_const hc1'pos (min_le_left _ _)
  have hLEB : HasLEBound lam K (max 1 (Real.log (Real.sqrt (((|E| + r) + 2 * |lam|) ^ 2 + 2)))) :=
    (hasLEBound_Icc lam (|E| + r) (add_nonneg (abs_nonneg E) hrpos.le)).mono
      (Icc_subset_Icc_abs (E := E) (r := r) hrpos.le)
  set C₀ : ℝ := max 1 (Real.log (Real.sqrt (((|E| + r) + 2 * |lam|) ^ 2 + 2))) with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  set R : ℝ := |α| + |E| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hαR : |α| ≤ R := by rw [hRdef]; linarith [abs_nonneg E]
  have hER : |E| ≤ R := by rw [hRdef]; linarith [abs_nonneg α]
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
  set W : ℕ := max 1 (Nat.ceil (Cd * (κ ^ 2)⁻¹))
    * 2 ^ (Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1) with hWdef
  have hW1 : 1 ≤ W := by
    rw [hWdef]
    exact Nat.mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (pow_pos (by norm_num) _)
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 1 ≤ W)
  set Γ : ℝ := Real.log (lipM lam R) + 2 with hΓdef
  have hΓ2 : 2 ≤ Γ := by rw [hΓdef]; linarith [Real.log_nonneg (lipM_ge_one lam R)]
  have hΓpos : 0 < Γ := by linarith
  set bstar : ℝ := 4 * Γ * (W : ℝ) + 2 with hbstar
  have hbstarpos : 0 < bstar := by rw [hbstar]; nlinarith [hΓpos, hWpos]
  have hbstar2 : 2 < bstar := by rw [hbstar]; nlinarith [hΓpos, hWpos]
  set κ' : ℝ := κ / 2 with hκ'def
  have hκ'pos : 0 < κ' := by rw [hκ'def]; linarith
  have hκ'200 : κ' ≤ 1 / 200 := by rw [hκ'def]; linarith
  have hκ'level : 200 * κ' = 100 * κ := by rw [hκ'def]; ring
  have hκ'inv : (κ' ^ 2)⁻¹ = 4 * (κ ^ 2)⁻¹ := by
    rw [hκ'def]
    field_simp
    ring
  have hκ2inv : (0 : ℝ) < Cd * (κ ^ 2)⁻¹ := by
    refine mul_pos (lt_of_lt_of_le zero_lt_one hCd1) ?_
    positivity
  have hnat : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hCdpos : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd1
  have hlipLpos : 0 < lipL lam := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have mk_ev : ∀ (P : ℕ → Prop), (∀ᶠ q : ℕ in atTop, P q) →
      ∀ᶠ q0 : ℕ in atTop, ∀ q : ℕ, q0 ≤ q → P q := by
    intro P hP
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hP
    exact Filter.eventually_atTop.2 ⟨N, fun q0 hq0 q hq => hN q (le_trans hq0 hq)⟩
  have ev1 : ∀ᶠ q : ℕ in atTop, 1 ≤ q := Filter.eventually_ge_atTop 1
  have ev2 : ∀ᶠ q : ℕ in atTop, Cd * (κ ^ 2)⁻¹ ≤ (q : ℝ) := hnat.eventually_ge_atTop _
  have ev3 : ∀ᶠ q : ℕ in atTop, Real.exp (-(bstar * (q : ℝ))) < 1 / ((q : ℝ) ^ 2) := by
    filter_upwards [ev1] with q hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hsq : ((q : ℝ)) ^ 2 ≤ Real.exp (2 * ((q : ℝ) - 1)) := by
      have h1 : ((q : ℝ)) ^ 2 = Real.exp (Real.log (((q : ℝ)) ^ 2)) :=
        (Real.exp_log (by positivity)).symm
      rw [h1]
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow]
      push_cast
      linarith [Real.log_le_sub_one_of_pos hqpos]
    have h2 : 2 * ((q : ℝ) - 1) < bstar * (q : ℝ) := by nlinarith [hbstar2, hqR1]
    have h3 : ((q : ℝ)) ^ 2 < Real.exp (bstar * (q : ℝ)) :=
      lt_of_le_of_lt hsq (Real.exp_lt_exp.mpr h2)
    rw [Real.exp_neg, show (1 : ℝ) / ((q : ℝ) ^ 2) = (((q : ℝ) ^ 2))⁻¹ by rw [one_div]]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr h3
  have ev4 : ∀ᶠ q : ℕ in atTop, 3 ≤ Nat.ceil (Real.exp (bstar * (q : ℝ) / 2)) := by
    filter_upwards [hnat.eventually_ge_atTop (4 / bstar)] with q hq
    have hle : (2 : ℝ) ≤ bstar * (q : ℝ) / 2 := by
      rw [div_le_iff₀ hbstarpos] at hq
      linarith [hq]
    have h2 : (3 : ℝ) ≤ Real.exp (bstar * (q : ℝ) / 2) := by
      have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        rw [h5]
        nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
      exact le_trans (by linarith) (Real.exp_le_exp.mpr hle)
    have h6 : (3 : ℝ) ≤ ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ) :=
      le_trans h2 (Nat.le_ceil _)
    exact_mod_cast h6
  have ev5 : ∀ᶠ q : ℕ in atTop,
      (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4)) < ε / 16 := by
    have harg : Tendsto (fun q : ℕ => (min c₀ 1) * κ * (q : ℝ) / 4) atTop atTop := by
      have h1' : Tendsto (fun q : ℕ => ((min c₀ 1) * κ / 4) * (q : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hnat
      exact h1'.congr (fun q => by ring)
    have h0' : Tendsto (fun q : ℕ => Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
    have h0 : Tendsto (fun q : ℕ =>
        (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4))) atTop (nhds 0) := by
      simpa using h0'.const_mul (12 * C₀ + 1000)
    exact h0.eventually (eventually_lt_nhds hε16)
  have ev6 : ∀ᶠ q : ℕ in atTop,
      ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q : ℝ) / 2) := by
    have harg : Tendsto (fun q : ℕ => (min c₀ 1) * κ * (q : ℝ) / 2) atTop atTop := by
      have h1' : Tendsto (fun q : ℕ => ((min c₀ 1) * κ / 2) * (q : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hnat
      exact h1'.congr (fun q => by ring)
    exact (Real.tendsto_exp_atTop.comp harg).eventually_gt_atTop ((m : ℕ) : ℝ)
  have ev7 : ∀ᶠ q : ℕ in atTop,
      Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q : ℝ)) < ε / 16 := by
    have h0 : Tendsto (fun q : ℕ => Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q : ℝ))) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop hκ2inv hnat)
    exact h0.eventually (eventually_lt_nhds hε16)
  have ev8 : ∀ᶠ q : ℕ in atTop, Real.log 6 / (q : ℝ) < ε / 16 :=
    (Tendsto.div_atTop tendsto_const_nhds hnat).eventually (eventually_lt_nhds hε16)
  have ev9 : ∀ᶠ q : ℕ in atTop,
      6 * lipL lam * (10 + 16 * Real.pi * |lam|) * Real.exp (-(q : ℝ)) < ε / 8 := by
    have h0' : Tendsto (fun q : ℕ => Real.exp (-(q : ℝ))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hnat)
    have h0 : Tendsto (fun q : ℕ =>
        6 * lipL lam * (10 + 16 * Real.pi * |lam|) * Real.exp (-(q : ℝ))) atTop (nhds 0) := by
      simpa using h0'.const_mul (6 * lipL lam * (10 + 16 * Real.pi * |lam|))
    exact h0.eventually (eventually_lt_nhds hε8)
  have ev10 : ∀ᶠ q : ℕ in atTop,
      (9 + 16 * Real.pi * |lam|) * Real.exp (-(bstar * (q : ℝ) / 2)) < 1 := by
    have harg : Tendsto (fun q : ℕ => bstar * (q : ℝ) / 2) atTop atTop := by
      have h1' : Tendsto (fun q : ℕ => (bstar / 2) * (q : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) hnat
      exact h1'.congr (fun q => by ring)
    have h0' : Tendsto (fun q : ℕ => Real.exp (-(bstar * (q : ℝ) / 2))) atTop (nhds 0) := by
      simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
    have h0 : Tendsto (fun q : ℕ =>
        (9 + 16 * Real.pi * |lam|) * Real.exp (-(bstar * (q : ℝ) / 2))) atTop (nhds 0) := by
      simpa using h0'.const_mul (9 + 16 * Real.pi * |lam|)
    exact h0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  rcases Classical.em (LiouvilleAbove α bstar) with hLiou | hNotLiou
  · -- ================= Case I: LiouvilleAbove α b* =================
    have hEv : ∀ᶠ q0 : ℕ in atTop, ∀ (a : ℤ) (q : ℕ), q0 ≤ q →
        Nat.Coprime (Int.natAbs a) q →
        |α - (a : ℝ) / (q : ℝ)| < Real.exp (-(bstar * (q : ℝ))) → False := by
      filter_upwards [mk_ev _ ev1, mk_ev _ ev2, mk_ev _ ev3, mk_ev _ ev4, mk_ev _ ev5,
        mk_ev _ ev6, mk_ev _ ev7, mk_ev _ ev8, mk_ev _ ev9, mk_ev _ ev10]
        with q0 h1e h2e h3e h4e h5e h6e h7e h8e h9e h10e
      intro a q hq hcop happ
      have hq1 : 1 ≤ q := h1e q hq
      have hqC : Cd * (κ ^ 2)⁻¹ ≤ (q : ℝ) := h2e q hq
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hα1 : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2) := lt_trans happ (h3e q hq)
      have hmq : ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q : ℝ) / 2) := h6e q hq
      obtain ⟨N₀, hN₀dvd, hN₀1, hN₀ge, hN₀le, hN₀lev, hN₀pair⟩ :=
        base_pairing_bd (lam := lam) (K := K) (C₀ := C₀) (C := Cd) (κ := κ)
          hLEB hκpos hC₀pos (α := α) (q := q) hq1 hqC hEK (by rw [← hLdef]; exact hκL)
      obtain ⟨m₀, hm₀⟩ := hN₀dvd
      have hm₀1 : 1 ≤ m₀ := by
        rcases Nat.eq_zero_or_pos m₀ with h0 | h0
        · subst h0; rw [Nat.mul_zero] at hm₀; omega
        · exact h0
      have hN₀eq : N₀ = m₀ * q := by rw [hm₀, Nat.mul_comm]
      have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₀1)
      have hψup : L + lyapAvg α lam (E : ℂ) N₀ - 2 * lyapAvg α lam (E : ℂ) (2 * N₀)
          ≤ (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4))
            + 2 * C₀ / (m : ℝ) := by
        have h := psi_upper lam K (min c₀ 1) Cd C₀ hLDT hLEB (min_le_right _ _) κ hκpos
          hκ100 E hEK α a q hq1 hcop hqC hα1 N₀ hN₀ge (by rw [← hLdef]; exact hκL)
          hN₀pair m hm3 hmq
        rw [← hLdef] at h
        exact h
      obtain ⟨H, hH, hspec⟩ := hE
      obtain ⟨θ', E', H', hH', hspec', hclose⟩ :=
        qsc h1 lam α ((a : ℝ) / (q : ℝ)) 0 E H hH hspec
          (Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) (h4e q hq)
      have hLw_ge : Real.exp (bstar * (q : ℝ) / 2) ≤
          ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ) := Nat.le_ceil _
      have hLwpos : (0 : ℝ) < ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ) :=
        lt_of_lt_of_le (Real.exp_pos _) hLw_ge
      have hLw_le : ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ) ≤
          2 * Real.exp (bstar * (q : ℝ) / 2) := by
        have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Real.exp (bstar * (q : ℝ) / 2)
          from (Real.exp_pos _).le)
        have h1 : (1 : ℝ) ≤ Real.exp (bstar * (q : ℝ) / 2) := Real.one_le_exp (by positivity)
        linarith
      have hE'close : |E - E'| ≤ (9 + 16 * Real.pi * |lam|) *
          Real.exp (-(bstar * (q : ℝ) / 2)) := by
        have h9 : 9 / ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ) ≤
            9 * Real.exp (-(bstar * (q : ℝ) / 2)) := by
          have h1 : (((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ))⁻¹ ≤
              Real.exp (-(bstar * (q : ℝ) / 2)) := by
            have h2 := one_div_le_one_div_of_le (Real.exp_pos _) hLw_ge
            rw [one_div, one_div, ← Real.exp_neg] at h2
            exact h2
          exact mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 9)
        have h8 : 8 * Real.pi * |lam| * ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ)
            * |α - (a : ℝ) / (q : ℝ)| ≤ 16 * Real.pi * |lam| *
              Real.exp (-(bstar * (q : ℝ) / 2)) := by
          have habs1 : |α - (a : ℝ) / (q : ℝ)| ≤ Real.exp (-(bstar * (q : ℝ))) := le_of_lt happ
          have hprod : Real.exp (bstar * (q : ℝ) / 2) * Real.exp (-(bstar * (q : ℝ))) =
              Real.exp (-(bstar * (q : ℝ) / 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have hstep : ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ)
              * |α - (a : ℝ) / (q : ℝ)| ≤ 2 * Real.exp (-(bstar * (q : ℝ) / 2)) := by
            calc ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ)
                  * |α - (a : ℝ) / (q : ℝ)|
                ≤ (2 * Real.exp (bstar * (q : ℝ) / 2)) * Real.exp (-(bstar * (q : ℝ))) := by
                  apply mul_le_mul hLw_le habs1 (abs_nonneg _) (by positivity)
              _ = 2 * Real.exp (-(bstar * (q : ℝ) / 2)) := by rw [mul_assoc, hprod]
          calc 8 * Real.pi * |lam| * ((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ)
                * |α - (a : ℝ) / (q : ℝ)|
              = 8 * Real.pi * |lam| * (((Nat.ceil (Real.exp (bstar * (q : ℝ) / 2))) : ℝ)
                  * |α - (a : ℝ) / (q : ℝ)|) := by ring
            _ ≤ 8 * Real.pi * |lam| * (2 * Real.exp (-(bstar * (q : ℝ) / 2))) :=
                mul_le_mul_of_nonneg_left hstep (by positivity)
            _ = 16 * Real.pi * |lam| * Real.exp (-(bstar * (q : ℝ) / 2)) := by ring
        linarith [hclose, h9, h8]
      have hE'1 : |E - E'| < 1 := lt_of_le_of_lt hE'close (h10e q hq)
      have hωR : |(a : ℝ) / (q : ℝ)| ≤ R := by
        have hexp1 : Real.exp (-(bstar * (q : ℝ))) ≤ 1 := by
          have h : -(bstar * (q : ℝ)) ≤ 0 := by nlinarith [hbstarpos, hqpos]
          simpa using Real.exp_le_exp.mpr h
        have h2 : |(a : ℝ) / (q : ℝ) - α| < 1 := by
          rw [abs_sub_comm]
          exact lt_of_lt_of_le happ hexp1
        have h1 : |(a : ℝ) / (q : ℝ)| ≤ |(a : ℝ) / (q : ℝ) - α| + |α| := by
          calc |(a : ℝ) / (q : ℝ)| = |((a : ℝ) / (q : ℝ) - α) + α| := by ring_nf
            _ ≤ |(a : ℝ) / (q : ℝ) - α| + |α| := abs_add_le _ _
        rw [hRdef]; linarith [h1, h2, abs_nonneg E]
      have hE'R : |E'| ≤ R := by
        have h1 : |E'| ≤ |E' - E| + |E| := by
          calc |E'| = |(E' - E) + E| := by ring_nf
            _ ≤ |E' - E| + |E| := abs_add_le _ _
        have h2 : |E' - E| < 1 := by rw [abs_sub_comm]; exact hE'1
        rw [hRdef]; linarith [h1, h2, abs_nonneg α]
      set ω : ℝ := (a : ℝ) / (q : ℝ) with hωdef
      have hdnonneg : 0 ≤ |α - ω| + |E - E'| := by positivity
      have hΔ2 : |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀)|
          ≤ lipK lam (2 * N₀) R * (|α - ω| + |E - E'|) :=
        lyapAvg_lipschitz_lipK lam (2 * N₀) (by omega) R hRpos α E ω E' hαR hER hωR hE'R
      have hΔ1 : |lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀|
          ≤ lipK lam N₀ R * (|α - ω| + |E - E'|) :=
        lyapAvg_lipschitz_lipK lam N₀ hN₀1 R hRpos α E ω E' hαR hER hωR hE'R
      have hS0_2 := lipK_le_exp lam (2 * N₀) R (by omega)
      have hS0_1 := lipK_le_exp lam N₀ R hN₀1
      rw [← hΓdef] at hS0_2 hS0_1
      have hN₀le' : (N₀ : ℝ) ≤ (W : ℝ) * (q : ℝ) := by
        rw [hWdef]; exact hN₀le
      have hexpE2 : Real.exp (Γ * (((2 * N₀ : ℕ)) : ℝ)) ≤
          Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hcast : (((2 * N₀ : ℕ)) : ℝ) = 2 * (N₀ : ℝ) := by push_cast; ring
        rw [hcast]
        have h1 : (N₀ : ℝ) ≤ (W : ℝ) * (q : ℝ) := hN₀le'
        nlinarith [hΓpos, h1]
      have hexpE1 : Real.exp (Γ * (N₀ : ℝ)) ≤ Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h1 : Γ * (N₀ : ℝ) ≤ Γ * ((W : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hN₀le' hΓpos.le
        nlinarith [h1]
      have hK2b : lipK lam (2 * N₀) R ≤ 2 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) :=
        le_trans hS0_2 (mul_le_mul_of_nonneg_left hexpE2 (by positivity))
      have hK1b : lipK lam N₀ R ≤ 2 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) :=
        le_trans hS0_1 (mul_le_mul_of_nonneg_left hexpE1 (by positivity))
      have hd' : |α - ω| + |E - E'| ≤ (10 + 16 * Real.pi * |lam|) *
          Real.exp (-(bstar * (q : ℝ) / 2)) := by
        have h1 : |α - ω| ≤ Real.exp (-(bstar * (q : ℝ) / 2)) := by
          have h2 : Real.exp (-(bstar * (q : ℝ))) ≤ Real.exp (-(bstar * (q : ℝ) / 2)) :=
            Real.exp_le_exp.mpr (by nlinarith [hbstarpos, hqpos])
          exact le_trans (le_of_lt happ) h2
        have h3 : |E - E'| ≤ (9 + 16 * Real.pi * |lam|) *
            Real.exp (-(bstar * (q : ℝ) / 2)) := hE'close
        linarith
      have hexpid : Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) *
          Real.exp (-(bstar * (q : ℝ) / 2)) = Real.exp (-(q : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hbstar]
        ring
      have hbig : 2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀
          - (2 * lyapAvg ω lam (E' : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) N₀) < ε / 8 := by
        have habs : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀))
            - (lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀)
            ≤ 2 * |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀)|
              + |lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀| := by
          have h1 : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀))
              ≤ 2 * |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀)| := by
            have := le_abs_self (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀))
            linarith
          have h2 : -(lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀)
              ≤ |lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀| := neg_le_abs _
          linarith
        have hmid : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀))
            - (lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀)
            = 2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀
              - (2 * lyapAvg ω lam (E' : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) N₀) := by ring
        rw [← hmid]
        refine lt_of_le_of_lt
          (b := 6 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) * (|α - ω| + |E - E'|)) ?_ ?_
        · have h4 : 2 * |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀)|
              + |lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀|
              ≤ 6 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ))
                * (|α - ω| + |E - E'|) := by
            have h5 : |lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) (2 * N₀)|
                ≤ (2 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)))
                  * (|α - ω| + |E - E'|) :=
              le_trans hΔ2 (mul_le_mul_of_nonneg_right hK2b hdnonneg)
            have h6 : |lyapAvg α lam (E : ℂ) N₀ - lyapAvg ω lam (E' : ℂ) N₀|
                ≤ (2 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)))
                  * (|α - ω| + |E - E'|) :=
              le_trans hΔ1 (mul_le_mul_of_nonneg_right hK1b hdnonneg)
            linarith
          linarith [habs, h4]
        · have hprod : Real.exp (2 * Γ * (W : ℝ) * (q : ℝ)) *
              ((10 + 16 * Real.pi * |lam|) * Real.exp (-(bstar * (q : ℝ) / 2)))
              = (10 + 16 * Real.pi * |lam|) * Real.exp (-(q : ℝ)) := by
            rw [← hexpid]; ring
          have h7 : 6 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ))
              * (|α - ω| + |E - E'|)
              ≤ 6 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ))
                * ((10 + 16 * Real.pi * |lam|) * Real.exp (-(bstar * (q : ℝ) / 2))) := by
            apply mul_le_mul_of_nonneg_left hd' (by positivity)
          have h8 : 6 * lipL lam * Real.exp (2 * Γ * (W : ℝ) * (q : ℝ))
              * ((10 + 16 * Real.pi * |lam|) * Real.exp (-(bstar * (q : ℝ) / 2)))
              = 6 * lipL lam * (10 + 16 * Real.pi * |lam|) * Real.exp (-(q : ℝ)) := by
            rw [mul_assoc (6 * lipL lam), hprod]
            ring
          rw [h8] at h7
          exact lt_of_le_of_lt h7 (h9e q hq)
      have hψlow : -(Real.log 2) / (N₀ : ℝ) ≤ lyap ω lam (E' : ℂ)
          + lyapAvg ω lam (E' : ℂ) N₀ - 2 * lyapAvg ω lam (E' : ℂ) (2 * N₀) := by
        rw [hωdef, hN₀eq]
        exact psi_lower_rat a q hq1 lam E' m₀ hm₀1
      have hrat : lyap ω lam (E' : ℂ) ≤ M + Real.log 6 / (q : ℝ) := by
        have h := rat_bound_phase h1 h15 a q hq1 hcop lam θ' E' H' hH' hspec'
        rw [hωdef, hMdef]
        exact h
      have hlog2b : Real.log 2 / (N₀ : ℝ) < ε / 16 := by
        have h1' : Real.log 2 / (N₀ : ℝ) ≤ Real.log 2 / (Cd * (κ ^ 2)⁻¹ * (q : ℝ)) := by
          rw [div_le_div_iff₀ hN₀pos (by positivity)]
          nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), hN₀ge, hκ2inv, hqpos]
        linarith [h1', h7e q hq]
      have herr : (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4))
          + 2 * C₀ / (m : ℝ) < ε / 8 := by
        linarith [h5e q hq, hme]
      have hPω : 2 * lyapAvg ω lam (E' : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) N₀
          ≤ lyap ω lam (E' : ℂ) + Real.log 2 / (N₀ : ℝ) := by
        have h := hψlow
        rw [neg_div] at h
        linarith
      have hsum : L ≤ M + 3 * ε / 8 := by
        have h1' : L ≤ (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
            + ((12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q : ℝ) / 4))
              + 2 * C₀ / (m : ℝ)) := by linarith [hψup]
        have h2' : 2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀
            ≤ (2 * lyapAvg ω lam (E' : ℂ) (2 * N₀) - lyapAvg ω lam (E' : ℂ) N₀) + ε / 8 := by
          linarith [hbig]
        linarith [h1', h2', hPω, hrat, hlog2b, h8e q hq, herr]
      linarith [hsum, hLMε, hεpos]
    obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hEv
    obtain ⟨a, q, hqQ, hcop, happ⟩ := liouville_approx α hα bstar hbstarpos hLiou Q₀
    exact hQ₀ q hqQ a q le_rfl hcop happ
  · -- ================= Case II: DiophBelow α b* =================
    have hDioph : DiophBelow α bstar := by
      show ∀ᶠ k : ℕ in atTop, Real.exp (-(bstar * (k : ℝ))) ≤ fracDist ((k : ℝ) * α)
      exact (Filter.not_frequently.mp hNotLiou).mono (fun k hk => not_lt.mp hk)
    obtain ⟨a, q, n₀, hq1, hqmono, hqcop, hqapprox, hqcross, hqgap⟩ :=
      conv_chain_rational α hα bstar hbstarpos hDioph
    have hqRstrict : StrictMono (fun j : ℕ => (q j : ℝ)) := fun i j hij =>
      Nat.cast_lt.mpr (hqmono hij)
    have hqtop : Tendsto q atTop atTop := hqmono.tendsto_atTop
    have hqj_ge : ∀ j : ℕ, (q 0 : ℝ) + (j : ℝ) ≤ (q j : ℝ) := by
      intro j
      have hstep : ∀ i : ℕ, q i + 1 ≤ q (i + 1) := fun i => hqmono (Nat.lt_succ_self i)
      have h : q 0 + j ≤ q j := by
        induction j with
        | zero => simp
        | succ j ih =>
          calc q 0 + (j + 1) = (q 0 + j) + 1 := by ring
            _ ≤ q j + 1 := by omega
            _ ≤ q (j + 1) := hstep j
      exact_mod_cast h
    have hqtend : Tendsto (fun j : ℕ => (q j : ℝ)) atTop atTop := by
      have h1 : Tendsto (fun j : ℕ => (q 0 : ℝ) + (j : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ (q 0 : ℝ) tendsto_natCast_atTop_atTop
      exact tendsto_atTop_mono (fun j => hqj_ge j) h1
    obtain ⟨B, T, hBpos, htower⟩ := rat_tower_lower_v2 lam K (min c₀ 1) Cd C₀ hLDT hLEB
      (min_le_right _ _) κ' hκ'pos hκ'200 bstar hbstarpos
    set i₀ : ℕ → ℕ := fun j => Nat.findGreatest (fun i => 4 * q i ≤ q j) j with hi₀def
    obtain ⟨N_T, hN_T⟩ : ∃ N : ℕ, T ≤ (q N : ℝ) := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hqtend.eventually_ge_atTop T)
      exact ⟨N, hN N le_rfl⟩
    obtain ⟨N_B, hN_B⟩ : ∃ N : ℕ,
        B * Real.exp (-((min c₀ 1) * κ' * (q N : ℝ) / 8)) < ε / 16 := by
      have harg : Tendsto (fun j : ℕ => (min c₀ 1) * κ' * (q j : ℝ) / 8) atTop atTop := by
        have h1' : Tendsto (fun j : ℕ => ((min c₀ 1) * κ' / 8) * (q j : ℝ)) atTop atTop :=
          Tendsto.const_mul_atTop (by positivity) hqtend
        exact h1'.congr (fun j => by ring)
      have h0' : Tendsto (fun j : ℕ =>
          Real.exp (-((min c₀ 1) * κ' * (q j : ℝ) / 8))) atTop (nhds 0) := by
        simpa only [Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp harg)
      have h0 : Tendsto (fun j : ℕ =>
          B * Real.exp (-((min c₀ 1) * κ' * (q j : ℝ) / 8))) atTop (nhds 0) := by
        simpa using h0'.const_mul B
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h0.eventually (eventually_lt_nhds hε16))
      exact ⟨N, hN N le_rfl⟩
    have ev3q : ∀ᶠ j : ℕ in atTop, Real.exp (-(bstar * (q j : ℝ))) < 1 / ((q j : ℝ) ^ 2) :=
      hqtop.eventually ev3
    have ev5q : ∀ᶠ j : ℕ in atTop,
        (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q j : ℝ) / 4)) < ε / 16 :=
      hqtop.eventually ev5
    have ev6q : ∀ᶠ j : ℕ in atTop,
        ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q j : ℝ) / 2) := hqtop.eventually ev6
    have evJ : ∀ᶠ j : ℕ in atTop, 4 * (q 0 : ℝ) ≤ (q j : ℝ) ∧
        4 * (q N_T : ℝ) ≤ (q j : ℝ) ∧ 4 * (q N_B : ℝ) ≤ (q j : ℝ) ∧
        4 * (q n₀ : ℝ) ≤ (q j : ℝ) ∧ N_T ≤ j ∧ N_B ≤ j ∧ n₀ ≤ j ∧ 1 ≤ q j ∧
        Cd * (κ ^ 2)⁻¹ ≤ (q j : ℝ) ∧
        Real.exp (-(bstar * (q j : ℝ))) < 1 / ((q j : ℝ) ^ 2) ∧
        (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q j : ℝ) / 4)) < ε / 16 ∧
        ((m : ℕ) : ℝ) < Real.exp ((min c₀ 1) * κ * (q j : ℝ) / 2) := by
      filter_upwards [hqtend.eventually_ge_atTop (4 * (q 0 : ℝ)),
        hqtend.eventually_ge_atTop (4 * (q N_T : ℝ)),
        hqtend.eventually_ge_atTop (4 * (q N_B : ℝ)),
        hqtend.eventually_ge_atTop (4 * (q n₀ : ℝ)),
        Filter.eventually_ge_atTop N_T, Filter.eventually_ge_atTop N_B,
        Filter.eventually_ge_atTop n₀, hqtop.eventually (Filter.eventually_ge_atTop 1),
        hqtend.eventually_ge_atTop (Cd * (κ ^ 2)⁻¹), ev3q, ev5q, ev6q]
        with j hA hB hC hD hE hF hG hH hI hJ hK hL
      exact ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI, hJ, hK, hL⟩
    obtain ⟨j, hA, hB, hC, hD, hjNT, hjNB, hjn₀, hq1j, hqCj, hα1j, herrj, hmqj⟩ := evJ.exists
    have hP_i₀ : 4 * q (i₀ j) ≤ q j := by
      have hA' : 4 * q 0 ≤ q j := by exact_mod_cast hA
      have h := Nat.findGreatest_spec (P := fun i => 4 * q i ≤ q j) (m := 0) (n := j)
        (Nat.zero_le j) hA'
      simpa only [hi₀def] using h
    have hi₀_le_j : i₀ j ≤ j := by
      simpa only [hi₀def] using Nat.findGreatest_le (P := fun i => 4 * q i ≤ q j) j
    have hi₀_lt_j : i₀ j < j := by
      rcases Nat.eq_or_lt_of_le hi₀_le_j with h | h
      · exfalso
        have h' : 4 * q j ≤ q j := by
          nth_rewrite 1 [← h]
          exact hP_i₀
        have h2 := hq1 j
        omega
      · exact h
    have hi₀_ge_T : N_T ≤ i₀ j := by
      have hN : 4 * q N_T ≤ q j := by exact_mod_cast hB
      exact Nat.le_findGreatest (P := fun i => 4 * q i ≤ q j) (m := N_T) hjNT hN
    have hi₀_ge_B : N_B ≤ i₀ j := by
      have hN : 4 * q N_B ≤ q j := by exact_mod_cast hC
      exact Nat.le_findGreatest (P := fun i => 4 * q i ≤ q j) (m := N_B) hjNB hN
    have hi₀_ge_n₀ : n₀ ≤ i₀ j := by
      have hN : 4 * q n₀ ≤ q j := by exact_mod_cast hD
      exact Nat.le_findGreatest (P := fun i => 4 * q i ≤ q j) (m := n₀) hjn₀ hN
    have hT_le : T ≤ (q (i₀ j) : ℝ) := le_trans hN_T (hqRstrict.monotone hi₀_ge_T)
    have hB_le : B * Real.exp (-((min c₀ 1) * κ' * (q (i₀ j) : ℝ) / 8)) < ε / 16 := by
      have hmono : (q N_B : ℝ) ≤ (q (i₀ j) : ℝ) := hqRstrict.monotone hi₀_ge_B
      have hpos : (0 : ℝ) < (min c₀ 1) * κ' / 8 := by positivity
      have hexp : Real.exp (-((min c₀ 1) * κ' * (q (i₀ j) : ℝ) / 8)) ≤
          Real.exp (-((min c₀ 1) * κ' * (q N_B : ℝ) / 8)) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hmono hpos.le
        linarith
      linarith [mul_le_mul_of_nonneg_left hexp hBpos.le, hN_B]
    obtain ⟨N₀, hN₀dvd, hN₀1, hN₀ge, hN₀le, hN₀lev, hN₀pair⟩ :=
      base_pairing_bd (lam := lam) (K := K) (C₀ := C₀) (C := Cd) (κ := κ)
        hLEB hκpos hC₀pos (α := α) (q := q j) hq1j hqCj hEK (by rw [← hLdef]; exact hκL)
    have hψup2 : L + lyapAvg α lam (E : ℂ) N₀ - 2 * lyapAvg α lam (E : ℂ) (2 * N₀)
        ≤ (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q j : ℝ) / 4))
          + 2 * C₀ / (m : ℝ) := by
      have h := psi_upper lam K (min c₀ 1) Cd C₀ hLDT hLEB (min_le_right _ _) κ hκpos
        hκ100 E hEK α (a j) (q j) hq1j (hqcop j) hqCj (hqapprox j) N₀ hN₀ge
        (by rw [← hLdef]; exact hκL) hN₀pair m hm3 hmqj
      rw [← hLdef] at h
      exact h
    obtain ⟨η, hηpos, hpers⟩ := persists_level_pairing lam κ hκpos α E (a j) (q j) hq1j
      (hqapprox j) N₀ hN₀1 hN₀lev hN₀pair
    obtain ⟨K₁, hK₁pos, hK₁⟩ := lyapAvg_lipschitz lam N₀ hN₀1 R hRpos
    obtain ⟨K₂, hK₂pos, hK₂⟩ := lyapAvg_lipschitz lam (2 * N₀) (by omega) R hRpos
    set Kf : ℝ := 2 * K₂ + K₁ with hKfdef
    have hKfpos : 0 < Kf := by rw [hKfdef]; linarith
    have hCεpos : 0 < ε / 8 / (2 * Kf) := by positivity
    set ρE : ℝ := min (min η r) (min (ε / 8 / (2 * Kf)) 1) with hρEdef
    have hρEpos : 0 < ρE := by
      rw [hρEdef]
      exact lt_min (lt_min hηpos hrpos) (lt_min hCεpos one_pos)
    have hρE_η : ρE ≤ η := by rw [hρEdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hρE_r : ρE ≤ r := by rw [hρEdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hρE_ε : ρE ≤ ε / 8 / (2 * Kf) := by
      rw [hρEdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hρE_1 : ρE ≤ 1 := by
      rw [hρEdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨δs, hδspos, hδs⟩ := spectral_continuity h1 lam α E hE ρE hρEpos
    have evk : ∀ᶠ k : ℕ in atTop, j < k ∧
        Real.exp (-(bstar * (q k : ℝ))) < 1 / ((q k : ℝ) ^ 2) ∧
        1 / ((q k : ℝ) ^ 2) < η ∧ 1 / ((q k : ℝ) ^ 2) < δs ∧
        1 / ((q k : ℝ) ^ 2) < ε / 8 / (2 * Kf) ∧
        Real.log 6 / (q k : ℝ) < ε / 16 ∧
        (∃ E_k : ℝ, |E_k - E| < ρE ∧ E_k ∈ amoSpec ((a k : ℝ) / (q k)) lam) := by
      have hlogk : ∀ᶠ k : ℕ in atTop, Real.log 6 / (q k : ℝ) < ε / 16 :=
        (Tendsto.div_atTop tendsto_const_nhds hqtend).eventually (eventually_lt_nhds hε16)
      filter_upwards [Filter.eventually_gt_atTop j, ev3q,
        hqtend.eventually (Filter.eventually_gt_atTop (1 / η)),
        hqtend.eventually (Filter.eventually_gt_atTop (1 / δs)),
        hqtend.eventually (Filter.eventually_gt_atTop (1 / (ε / 8 / (2 * Kf)))),
        hlogk] with k hjk h3k hkη hkδ hkε h6k
      have hqk1 : 1 ≤ q k := hq1 k
      have hqkpos : (0 : ℝ) < (q k : ℝ) := by exact_mod_cast (by omega : 0 < q k)
      have hqkR1 : (1 : ℝ) ≤ (q k : ℝ) := by exact_mod_cast hqk1
      have hsq : 1 / ((q k : ℝ) ^ 2) ≤ 1 / (q k : ℝ) := by
        apply one_div_le_one_div_of_le hqkpos
        nlinarith [hqkR1]
      have key : ∀ c : ℝ, 0 < c → 1 / c < (q k : ℝ) → 1 / ((q k : ℝ) ^ 2) < c := by
        intro c hc hlt
        have h1 : 1 / (q k : ℝ) < c := by
          rw [div_lt_iff₀ hqkpos]
          have := (div_lt_iff₀ hc).mp hlt
          linarith
        exact lt_of_le_of_lt hsq h1
      have hαkδs : |(a k : ℝ) / (q k) - α| < δs := by
        rw [abs_sub_comm]
        exact lt_trans (hqapprox k) (key δs hδspos hkδ)
      refine ⟨hjk, h3k, key η hηpos hkη, key δs hδspos hkδ,
        key (ε / 8 / (2 * Kf)) hCεpos hkε, h6k, ?_⟩
      obtain ⟨E_k, hEk, hEmem⟩ := hδs ((a k : ℝ) / (q k)) hαkδs
      exact ⟨E_k, hEk, hEmem⟩
    obtain ⟨k, hjk, h3k, hkη, hkδ, hkε, h6k, E_k, hEk_close, hEk_mem⟩ := evk.exists
    have hαkη : |(a k : ℝ) / (q k : ℝ) - α| < η := by
      rw [abs_sub_comm]; exact lt_trans (hqapprox k) hkη
    have hαkε : |(a k : ℝ) / (q k : ℝ) - α| < ε / 8 / (2 * Kf) := by
      rw [abs_sub_comm]; exact lt_trans (hqapprox k) hkε
    obtain ⟨hlevk, hpairk, -⟩ := hpers ((a k : ℝ) / (q k)) E_k
      (lt_of_lt_of_le hEk_close hρE_η) hαkη
    have hEkK : E_k ∈ K := by
      rw [hKdef, Set.mem_Icc]
      have h := abs_lt.mp (lt_of_lt_of_le hEk_close hρE_r)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hEk1 : |E_k - E| < 1 := lt_of_lt_of_le hEk_close hρE_1
    have hEkR : |E_k| ≤ R := by
      have h1 : |E_k| ≤ |E_k - E| + |E| := by
        calc |E_k| = |(E_k - E) + E| := by ring_nf
          _ ≤ |E_k - E| + |E| := abs_add_le _ _
      rw [hRdef]; linarith [h1, hEk1, abs_nonneg α]
    have hωkR : |(a k : ℝ) / (q k : ℝ)| ≤ R := by
      have hqk1 : 1 ≤ q k := hq1 k
      have hqkpos : (0 : ℝ) < (q k : ℝ) := by exact_mod_cast (by omega : 0 < q k)
      have hsmall : 1 / ((q k : ℝ) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1 : ℝ) ≤ (q k : ℝ) := by exact_mod_cast hqk1
        nlinarith
      have h1 : |(a k : ℝ) / (q k : ℝ) - α| < 1 := by
        rw [abs_sub_comm]
        exact lt_of_lt_of_le (hqapprox k) hsmall
      have h2 : |(a k : ℝ) / (q k : ℝ)| ≤ |(a k : ℝ) / (q k : ℝ) - α| + |α| := by
        calc |(a k : ℝ) / (q k : ℝ)| = |((a k : ℝ) / (q k : ℝ) - α) + α| := by ring_nf
          _ ≤ |(a k : ℝ) / (q k : ℝ) - α| + |α| := abs_add_le _ _
      rw [hRdef]; linarith [h2, h1, abs_nonneg E]
    have hik : i₀ j + (k - i₀ j) = k := by omega
    have hscale_arith : Cd * (κ' ^ 2)⁻¹ * (q (i₀ j) : ℝ) ≤ (N₀ : ℝ) := by
      have h4q : (4 : ℝ) * (q (i₀ j) : ℝ) ≤ (q j : ℝ) := by exact_mod_cast hP_i₀
      have hCn : (0 : ℝ) ≤ Cd * (κ ^ 2)⁻¹ := le_of_lt hκ2inv
      calc Cd * (κ' ^ 2)⁻¹ * (q (i₀ j) : ℝ)
          = Cd * (4 * (κ ^ 2)⁻¹) * (q (i₀ j) : ℝ) := by rw [hκ'inv]
        _ = Cd * (κ ^ 2)⁻¹ * ((4 : ℝ) * (q (i₀ j) : ℝ)) := by ring
        _ ≤ Cd * (κ ^ 2)⁻¹ * (q j : ℝ) := mul_le_mul_of_nonneg_left h4q hCn
        _ ≤ (N₀ : ℝ) := hN₀ge
    have hlev_arith : 200 * κ' < lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀ := by
      linarith [hlevk, hκ'level]
    have hpair_arith : (9 / 10) * lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀
        < lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀) := hpairk
    have htow := htower (k - i₀ j) (fun i => a (i₀ j + i)) (fun i => q (i₀ j + i))
      (fun i _ => hq1 (i₀ j + i))
      (fun i _ => hqmono (Nat.lt_succ_self (i₀ j + i)))
      (fun i _ => hqcop (i₀ j + i))
      (fun i hi => by
        simp only [hik]
        exact hqcross (i₀ j + i) k (by omega))
      (fun i hi => hqgap (i₀ j + i) (by omega))
      (by simpa only [hik, Nat.add_zero] using hT_le)
      E_k hEkK N₀
      (by simpa only [hik, Nat.add_zero] using hscale_arith)
      (by simpa only [hik] using hlev_arith)
      (by simpa only [hik] using hpair_arith)
    have hratk := Solutions.rat_bound h1 h15 (a k) (q k) (hq1 k) (hqcop k) lam E_k hEk_mem
    have hcrossk : 2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀
        ≤ (2 * lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀) + ε / 8 := by
      set d : ℝ := |α - (a k : ℝ) / (q k : ℝ)| + |E - E_k| with hddef
      have hdnn : 0 ≤ d := by rw [hddef]; positivity
      have hA2 : |lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)| ≤ K₂ * d :=
        hK₂ α E ((a k : ℝ) / (q k : ℝ)) E_k hαR hER hωkR hEkR
      have hA1 : |lyapAvg α lam (E : ℂ) N₀
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀| ≤ K₁ * d :=
        hK₁ α E ((a k : ℝ) / (q k : ℝ)) E_k hαR hER hωkR hEkR
      have hKd : Kf * d < ε / 8 := by
        obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = |α - (a k : ℝ) / (q k : ℝ)| := ⟨_, rfl⟩
        obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = |E - E_k| := ⟨_, rfl⟩
        have hx : x < ε / 8 / (2 * Kf) := by
          rw [hxdef]; exact lt_trans (hqapprox k) hkε
        have hy : y < ε / 8 / (2 * Kf) := by
          rw [hydef, abs_sub_comm]; exact lt_of_lt_of_le hEk_close hρE_ε
        have h4 : Kf * (ε / 8 / (2 * Kf)) = ε / 16 := by
          field_simp
          ring
        have hx' : Kf * x < ε / 16 := by
          have h := mul_lt_mul_of_pos_left hx hKfpos
          rwa [h4] at h
        have hy' : Kf * y < ε / 16 := by
          have h := mul_lt_mul_of_pos_left hy hKfpos
          rwa [h4] at h
        have hdxy : d = x + y := by rw [hddef, ← hxdef, ← hydef]
        rw [hdxy]
        have h6 : Kf * (x + y) = Kf * x + Kf * y := by ring
        linarith [hx', hy', h6]
      have hKd' : (2 * K₂ + K₁) * d < ε / 8 := by
        rwa [hKfdef] at hKd
      have habs : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀))
          - (lyapAvg α lam (E : ℂ) N₀
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀)
          ≤ 2 * |lyapAvg α lam (E : ℂ) (2 * N₀)
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)|
            + |lyapAvg α lam (E : ℂ) N₀
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀| := by
        have h1 : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀))
            ≤ 2 * |lyapAvg α lam (E : ℂ) (2 * N₀)
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)| := by
          have := le_abs_self (lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀))
          linarith
        have h2 : -(lyapAvg α lam (E : ℂ) N₀
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀)
            ≤ |lyapAvg α lam (E : ℂ) N₀
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀| := neg_le_abs _
        linarith
      have hmid : 2 * (lyapAvg α lam (E : ℂ) (2 * N₀)
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀))
          - (lyapAvg α lam (E : ℂ) N₀
            - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀)
          = 2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀
            - (2 * lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)
              - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀) := by ring
      rw [hmid] at habs
      linarith [habs, hA2, hA1, hKd']
    have hsum2 : L ≤ M + 3 * ε / 8 := by
      have h1' : L ≤ (2 * lyapAvg α lam (E : ℂ) (2 * N₀) - lyapAvg α lam (E : ℂ) N₀)
          + ((12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q j : ℝ) / 4))
            + 2 * C₀ / (m : ℝ)) := by linarith [hψup2]
      have herr2 : (12 * C₀ + 1000) * Real.exp (-((min c₀ 1) * κ * (q j : ℝ) / 4))
          + 2 * C₀ / (m : ℝ) < ε / 8 := by linarith [herrj, hme]
      have htow' : 2 * lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) (2 * N₀)
          - lyapAvg ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ) N₀
          ≤ lyap ((a k : ℝ) / (q k : ℝ)) lam (E_k : ℂ)
            + B * Real.exp (-((min c₀ 1) * κ' * (q (i₀ j) : ℝ) / 8)) := by
        simpa only [hik, Nat.add_zero] using htow
      linarith [h1', hcrossk, htow', hratk, h6k, herr2, hB_le]
    linarith [hsum2, hLMε, hεpos]

end Work.TMC7Core.Scale

end
