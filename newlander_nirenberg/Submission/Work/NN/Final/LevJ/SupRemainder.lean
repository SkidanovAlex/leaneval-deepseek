import Mathlib
import Submission.Work.NN.Core.Lev.supRemainderSchauder
import Submission.Work.NN.Final.LevJ.LevelZero

/-!
# The sup-remainder Schauder estimate, level `0`

`Work.NN.Core.Lev.supRemainderSchauder` with the componentwise `C^{0,α}`-smallness hypothesis on the
perturbation instead of the `C^{1,α}`-smallness.  The proof is a copy of the original: the
`C^{1,α}`-smallness is used there only to produce a level-`0` coordinate bound and to feed the
lossless estimate at level `0`, which is provided here by
`Work.NN.Final.LevJ.perturbed_lossless_zero`.
-/

set_option maxHeartbeats 16000000

namespace Work.NN.Final.LevJ

open scoped NNReal ENNReal ContDiff Topology
open Set Filter
open Work.NN.Core Work.NN.Core.Lev

noncomputable section

variable {n : ℕ}

theorem supRemainderSchauder_v {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ'0 : ∀ j, 0 < ρ' j) (hρ' : ∀ j, ρ' j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ u : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
          Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ')
            ≤ ENNReal.ofReal C * ((∑ j : Fin n,
                  Work.CR.Flat.holderNorm 0 α
                    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
                    (Work.CR.Flat.polydisc 0 ρ))
                + ⨆ z ∈ Work.CR.Flat.polydisc 0 ρ, ENNReal.ofReal ‖u z‖) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- ## The geometry
  set s : Fin n → ℝ := fun j => ρ j - ρ' j with hsdef
  have hs : ∀ j, 0 < s j := fun j => by simp only [hsdef]; linarith [hρ' j]
  set smin : ℝ := Finset.univ.inf' Finset.univ_nonempty s with hsmindef
  have hsmin0 : 0 < smin := by
    rw [hsmindef]; exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hs j)
  have hsminle : ∀ j, smin ≤ s j := fun j => by
    rw [hsmindef]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set ρ'' : Fin n → ℝ := fun j => ρ' j + s j / 2 with hρ''def
  have hρ''0 : ∀ j, 0 < ρ'' j := fun j => by simp only [hρ''def]; linarith [hs j, hρ'0 j]
  have hρ''ρ : ∀ j, ρ'' j < ρ j := fun j => by
    simp only [hρ''def, hsdef]; linarith [hs j]
  -- ## the lossless estimate
  obtain ⟨εL, hεLpos, CL, hCLpos, hloss⟩ :=
    Work.NN.Final.LevJ.perturbed_lossless_zero (n := n) hn hα0 hα1 hρ0 hρ''0 hρ''ρ
  -- ## cutoff constants
  set Rmin : ℝ := Finset.univ.inf' Finset.univ_nonempty ρ' with hRmindef
  have hRmin0 : 0 < Rmin := by
    rw [hRmindef]; exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hρ'0 j)
  have hRminle : ∀ j, Rmin ≤ ρ' j := fun j => by
    rw [hRmindef]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty ρ'' with hRmaxdef
  have hRmax0 : 0 < Rmax := by
    rw [hRmaxdef]
    exact lt_of_lt_of_le (hρ''0 ⟨0, hn⟩) (Finset.le_sup' _ (Finset.mem_univ _))
  have hρ''leRmax : ∀ j, ρ'' j ≤ Rmax := fun j => by
    rw [hRmaxdef]; exact Finset.le_sup' _ (Finset.mem_univ j)
  obtain ⟨K, hKpos, p, hppos, hcut⟩ :=
    exists_polydisc_cutoff_lipschitz (n := n) hn hα0 hα1 hRmin0 hRmax0
  -- ## the datum constant
  obtain ⟨Cd, hCdpos, hdatac⟩ :=
    dbarCn_data_le (n := n) hα0 (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
      (Work.CR.Flat.isOpen_polydisc 0 ρ'')
  -- ## the exponent for the interpolation splits
  have h1a : 0 < 1 - α := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 < (m:ℝ) * (1 - α) := by
    obtain ⟨m, hm⟩ := exists_nat_ge ((p + 1) / (1 - α) + 1)
    refine ⟨m, ?_⟩
    have h2 := mul_le_mul_of_nonneg_right hm h1a.le
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h1a), one_mul] at h2
    linarith
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0] at hm
      simp only [Nat.cast_zero, zero_mul] at hm
      linarith [hppos]
    · exact hpos
  -- ## the smallness and thickness constants
  set eps0 : ℝ := min εL 1 with heps0def
  have heps0pos : 0 < eps0 := lt_min hεLpos one_pos
  set Kd : ℝ := Cd * (1 + eps0) with hKddef
  have hKdpos : 0 < Kd := mul_pos hCdpos (by linarith)
  set e0 : ℝ := smin / 100 with he0def
  have he0pos : 0 < e0 := by rw [he0def]; linarith
  have he0le : e0 ≤ smin / 100 := by rw [he0def]
  have he0rpow : (0:ℝ) < Real.rpow e0 (-p) := Real.rpow_pos_of_pos he0pos (-p)
  set CA : ℝ := (3 + K) * (1 + Real.rpow e0 (-p)) with hCAdef
  have hCAnn : 0 ≤ CA := by rw [hCAdef]; exact mul_nonneg (by linarith) (by linarith)
  have hCApos : 0 < CA := by rw [hCAdef]; exact mul_pos (by linarith) (by linarith)
  set CB : ℝ := (3 + 4 * K) * (1 + Real.rpow e0 (-p)) with hCBdef
  have hCBnn : 0 ≤ CB := by rw [hCBdef]; exact mul_nonneg (by linarith) (by linarith)
  have hCBpos : 0 < CB := by rw [hCBdef]; exact mul_pos (by linarith) (by linarith)
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set Cst0 : ℝ := CL * Kd * (n : ℝ) * CB with hCst0def
  have hCst0pos : 0 < Cst0 := by
    rw [hCst0def]
    exact mul_pos (mul_pos (mul_pos hCLpos hKdpos) hnR) hCBpos
  set d0 : ℝ := min (smin / 100) (Real.rpow (1 / Cst0) (1 / (1 - α))) with hd0def
  have hd0pos : 0 < d0 := by
    rw [hd0def]
    exact lt_min (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
  have hd0le : d0 ≤ smin / 100 := min_le_left _ _
  have hd0rpow : Real.rpow d0 (1 - α) ≤ 1 / Cst0 := by
    have hCpos : (0:ℝ) < 1 / Cst0 := by positivity
    have h1 : d0 ≤ Real.rpow (1 / Cst0) (1 / (1 - α)) := min_le_right _ _
    have h2 : Real.rpow d0 (1 - α) ≤ Real.rpow (Real.rpow (1 / Cst0) (1 / (1 - α))) (1 - α) :=
      Real.rpow_le_rpow hd0pos.le h1 (by linarith)
    have h3 : Real.rpow (Real.rpow (1 / Cst0) (1 / (1 - α))) (1 - α)
        = Real.rpow (1 / Cst0) ((1 / (1 - α)) * (1 - α)) :=
      (Real.rpow_mul (le_of_lt hCpos) (1 / (1 - α)) (1 - α)).symm
    have h4 : Real.rpow (1 / Cst0) ((1 / (1 - α)) * (1 - α)) = 1 / Cst0 := by
      rw [show (1 / (1 - α)) * (1 - α) = 1 from by field_simp]
      exact Real.rpow_one _
    linarith [h2, h3, h4]
  -- ## the bases of the growth
  set Bp : ℝ := Real.rpow 2 p with hBpdef
  have hBp1 : 1 ≤ Bp := by rw [hBpdef]; exact one_le_rpow_two hppos.le
  set Bal : ℝ := Real.rpow 2 α with hBaldef
  have hBal1 : 1 ≤ Bal := by rw [hBaldef]; exact one_le_rpow_two hα0.le
  have hBalnn : (0:ℝ) ≤ Bal := by rw [hBaldef]; exact Real.rpow_nonneg (by norm_num) α
  set Bq : ℝ := Real.rpow 2 (p + (m:ℝ) * α) with hBqdef
  have hBq1 : 1 ≤ Bq := by rw [hBqdef]; exact one_le_rpow_two (by positivity)
  set B1 : ℝ := Real.rpow 2 (-(1 - α)) with hB1def
  have hB1nn : (0:ℝ) ≤ B1 := by rw [hB1def]; exact Real.rpow_nonneg (by norm_num) (-(1 - α))
  have hB1eq : B1 = Real.rpow (1/2) (1 - α) := by
    rw [hB1def]; exact (rpow_half_eq (1 - α)).symm
  set beta : ℝ := (m:ℝ) * (1 - α) - p with hbetadef
  have hbeta1 : 1 < beta := by rw [hbetadef]; linarith
  have hB1m : Bp * B1 ^ m = Real.rpow 2 (-beta) := by
    have hstep : B1 ^ m = Real.rpow 2 ((m:ℝ) * (-(1 - α))) := by
      rw [hB1def]
      change ((2:ℝ)^(-(1-α)))^m = ((2:ℝ)^((m:ℝ)*(-(1-α))))
      rw [← Real.rpow_natCast ((2:ℝ)^(-(1-α))) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(1-α)) (m:ℝ)]
      congr 1
      ring
    have hstep2 : Bp * Real.rpow 2 ((m:ℝ) * (-(1 - α))) = Real.rpow 2 (-beta) := by
      rw [hBpdef]
      change ((2:ℝ)^p) * ((2:ℝ)^((m:ℝ)*(-(1-α)))) = ((2:ℝ)^(-beta))
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), hbetadef]
      congr 1
      ring
    rw [hstep, hstep2]
  have hB1le : Real.rpow 2 (-beta) ≤ 1/2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show -beta ≤ -1 from by linarith)
    have h2 : Real.rpow 2 (-1) = (1/2:ℝ) := by
      change ((2:ℝ)^((-1:ℝ))) = (1/2:ℝ)
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) 1]
      norm_num
    rw [← h2]
    exact h
  set CstL : ℝ := CL * Kd * (n : ℝ) * CB * Real.rpow d0 (1 - α) with hCstLdef
  have hCstLle : CstL ≤ 1 := by
    rw [hCstLdef]
    have hbase : (0:ℝ) ≤ CL * Kd * (n:ℝ) * CB :=
      mul_nonneg (mul_nonneg (mul_nonneg hCLpos.le hKdpos.le) hnR.le) hCBnn
    calc CL * Kd * (n:ℝ) * CB * Real.rpow d0 (1 - α)
        ≤ CL * Kd * (n:ℝ) * CB * (1/Cst0) := mul_le_mul_of_nonneg_left hd0rpow hbase
      _ = 1 := by
          rw [hCst0def]
          field_simp
  set A2 : ℝ := CL * CA with hA2def
  have hA2nn : 0 ≤ A2 := by rw [hA2def]; positivity
  set B2 : ℝ := CL * Kd * (n : ℝ) * CB * (1 + 2 * Real.rpow d0 (-α)) with hB2def
  have hB2nn : 0 ≤ B2 := by
    rw [hB2def]
    have hr : (0:ℝ) ≤ Real.rpow d0 (-α) := (Real.rpow_pos_of_pos hd0pos (-α)).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCLpos.le hKdpos.le) hnR.le) hCBnn)
      (by linarith)
  obtain ⟨I0A, hI0A⟩ : ∃ I0A : ℕ, 2 * p + 3 ≤ (I0A:ℝ) := exists_nat_ge (2*p+3)
  obtain ⟨I0B, hI0B⟩ : ∃ I0B : ℕ, 2 * (p + (m:ℝ)*α) + 3 ≤ (I0B:ℝ) :=
    exists_nat_ge (2*(p + (m:ℝ)*α) + 3)
  set DA : ℝ := A2 * Bp ^ I0A * (2:ℝ) ^ I0A with hDAdef
  set DB : ℝ := B2 * Bq ^ I0B * (2:ℝ) ^ I0B with hDBdef
  set Cfin : ℝ := 1 + 2 * DA + 2 * DB with hCfindef
  have hBp0 : (0:ℝ) < Bp := lt_of_lt_of_le one_pos hBp1
  have hBq0 : (0:ℝ) < Bq := lt_of_lt_of_le one_pos hBq1
  have hDA0 : 0 ≤ DA := by
    rw [hDAdef]
    exact mul_nonneg (mul_nonneg hA2nn (pow_nonneg hBp0.le _)) (pow_nonneg (by norm_num) _)
  have hDB0 : 0 ≤ DB := by
    rw [hDBdef]
    exact mul_nonneg (mul_nonneg hB2nn (pow_nonneg hBq0.le _)) (pow_nonneg (by norm_num) _)
  have hCfinpos : 0 < Cfin := by rw [hCfindef]; linarith
  refine ⟨eps0, heps0pos, Cfin, hCfinpos, ?_⟩
  intro A hAsm ε hε hsmall hJ u hu
  -- ## the datum and the norm quantities
  set X : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (Work.CR.Flat.polydisc 0 ρ) with hXdef
  set Z : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ, ENNReal.ofReal ‖u z‖ with hZdef
  set Me : ℝ≥0∞ := ⨆ z ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'', ENNReal.ofReal ‖fderiv ℝ u z‖
    with hMedef
  have hMelt : Me < ⊤ := by
    rw [hMedef]
    exact iSup_ofReal_norm_fderiv_lt_top hn hρ0 hρ''ρ hu
  by_cases hXtop : X = ⊤
  · rw [hXtop, top_add, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCfinpos)]
    exact le_top
  by_cases hZtop : Z = ⊤
  · rw [hZtop, add_top, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCfinpos)]
    exact le_top
  -- ## the sequences of radii
  set Efun : ℕ → ℝ := fun i => e0 * ((1/2:ℝ))^i with hEfundef
  set Dfun : ℕ → ℝ := fun i => d0 * ((1/2:ℝ))^(m*i) with hDfundef
  have hEv : ∀ i, Efun i = e0 * ((1/2:ℝ))^i := fun i => by simp only [hEfundef]
  have hDv : ∀ i, Dfun i = d0 * ((1/2:ℝ))^(m*i) := fun i => by simp only [hDfundef]
  set Rfun : ℕ → Fin n → ℝ :=
    fun i j => ρ' j + ∑ k ∈ Finset.range i, (Efun k + Dfun k) with hRfundef
  have hEpos : ∀ i, 0 < Efun i := fun i => by rw [hEfundef]; positivity
  have hDpos : ∀ i, 0 < Dfun i := fun i => by rw [hDfundef]; positivity
  have hEsum : ∀ i, (∑ k ∈ Finset.range i, Efun k) ≤ 2 * e0 := by
    intro i
    have h : ∀ k, Efun k = e0 * ((1/2:ℝ))^k := fun k => by rw [hEfundef]
    simp only [h, ← Finset.mul_sum]
    have h2 := sum_range_half_pow_le i
    nlinarith [he0pos.le]
  have hDsum : ∀ i, (∑ k ∈ Finset.range i, Dfun k) ≤ 2 * d0 := by
    intro i
    have h : ∀ k, Dfun k = d0 * ((1/2:ℝ))^(m*k) := fun k => by rw [hDfundef]
    simp only [h, ← Finset.mul_sum]
    have hle : (∑ k ∈ Finset.range i, ((1/2:ℝ))^(m*k)) ≤ ∑ k ∈ Finset.range i, ((1/2:ℝ))^k :=
      Finset.sum_le_sum fun k _ => half_pow_mul_le hm1
    have h2 := sum_range_half_pow_le i
    nlinarith [hd0pos.le]
  have hRd : ∀ i j, Rfun i j + (Efun i + Dfun i) ≤ ρ'' j := by
    intro i j
    have hsum1 : (∑ k ∈ Finset.range i, (Efun k + Dfun k)) ≤ 2*e0 + 2*d0 := by
      rw [Finset.sum_add_distrib]; linarith [hEsum i, hDsum i]
    have hED : Efun i + Dfun i ≤ e0 + d0 := by
      rw [hEfundef, hDfundef]
      have h1 : ((1/2:ℝ))^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : ((1/2:ℝ))^(m*i) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [he0pos.le, hd0pos.le]
    have hkey : 3*e0 + 3*d0 ≤ s j / 2 := by
      have h1 : e0 = smin/100 := he0def
      have h3 : smin ≤ s j := hsminle j
      linarith [hd0le]
    simp only [hRfundef, hρ''def]
    linarith
  have hRe : ∀ i j, Rfun i j + Efun i ≤ ρ'' j := by
    intro i j
    have hsum1 : (∑ k ∈ Finset.range i, (Efun k + Dfun k)) ≤ 2*e0 + 2*d0 := by
      rw [Finset.sum_add_distrib]; linarith [hEsum i, hDsum i]
    have h2 : Efun i ≤ e0 := by
      rw [hEfundef]
      have h1 : ((1/2:ℝ))^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [he0pos.le]
    have hkey : 2*e0 + 2*d0 + e0 ≤ s j / 2 := by
      have h1 : e0 = smin/100 := he0def
      have h3 : smin ≤ s j := hsminle j
      linarith [hd0le]
    simp only [hRfundef, hρ''def]
    linarith
  have hRsub : ∀ i j, Rfun i j ≤ ρ'' j := fun i j => by
    have h1 := hRe i j; linarith [hEpos i]
  have hRltρ : ∀ i j, Rfun i j < ρ j := fun i j => lt_of_le_of_lt (hRsub i j) (hρ''ρ j)
  have hRmin : ∀ i j, Rmin ≤ Rfun i j := by
    intro i j
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.range i, (Efun k + Dfun k) :=
      Finset.sum_nonneg fun k _ => by linarith [hEpos k, hDpos k]
    simp only [hRfundef]
    linarith [hRminle j]
  have hRmax : ∀ i j, Rfun i j ≤ Rmax := fun i j =>
    le_trans (hRsub i j) (hρ''leRmax j)
  have hRsucc : ∀ i, (fun j => Rfun i j + (Efun i + Dfun i)) = Rfun (i+1) := by
    intro i
    funext j
    simp only [hRfundef, Finset.sum_range_succ]
    ring
  -- ## the cutoffs
  choose χf hχf using fun i =>
    hcut (Rfun i) (Efun i) (fun j => hRmin i j) (fun j => hRmax i j) (hEpos i)
  have hχsm : ∀ i (m' : ℕ), ContDiff ℝ (m' : WithTop ℕ∞) (χf i) := fun i => (hχf i).1
  have hχnn : ∀ i z, 0 ≤ χf i z := fun i z => ((hχf i).2.1 z).1
  have hχle1 : ∀ i z, χf i z ≤ 1 := fun i z => ((hχf i).2.1 z).2
  have hχ1 : ∀ i z, (∀ j, ‖z j‖ ≤ Rfun i j) → χf i z = 1 := fun i => (hχf i).2.2.1
  have hχ0 : ∀ i z, (∃ j, Rfun i j + Efun i ≤ ‖z j‖) → χf i z = 0 := fun i => (hχf i).2.2.2.1
  have hχg : ∀ i x, ‖fderiv ℝ (fun z => (χf i z : ℂ)) x‖
      ≤ K * (1 + Real.rpow (Efun i) (-p)) := fun i => (hχf i).2.2.2.2.1
  have hχL : ∀ i x y, ‖fderiv ℝ (fun z => (χf i z : ℂ)) x
        - fderiv ℝ (fun z => (χf i z : ℂ)) y‖
      ≤ K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖ := fun i => (hχf i).2.2.2.2.2
  -- ## the level-`1` bounds for the cutoff
  set L1f : ℕ → ℝ := fun i => 3 + K * (1 + Real.rpow (Efun i) (-p)) with hL1fdef
  set L2f : ℕ → ℝ := fun i => 3 + 4 * (K * (1 + Real.rpow (Efun i) (-p))) with hL2fdef
  have hL1fv : ∀ i, L1f i = 3 + K * (1 + Real.rpow (Efun i) (-p)) := fun i => by simp only [hL1fdef]
  have hL2fv : ∀ i, L2f i = 3 + 4 * (K * (1 + Real.rpow (Efun i) (-p))) :=
    fun i => by simp only [hL2fdef]
  have hrpowE : ∀ i, (0:ℝ) < Real.rpow (Efun i) (-p) :=
    fun i => Real.rpow_pos_of_pos (hEpos i) (-p)
  have hL1fpos : ∀ i, 0 < L1f i := fun i => by
    simp only [hL1fdef]; have := hrpowE i; nlinarith [hKpos]
  have hL2fpos : ∀ i, 0 < L2f i := fun i => by
    simp only [hL2fdef]; have := hrpowE i; nlinarith [hKpos]
  have hL1fnn : ∀ i, 0 ≤ L1f i := fun i => by
    simp only [hL1fdef]; have := hrpowE i; nlinarith [hKpos.le]
  have hL2fnn : ∀ i, 0 ≤ L2f i := fun i => by
    simp only [hL2fdef]; have := hrpowE i; nlinarith [hKpos.le]
  have hL1 : ∀ i, Work.CR.Flat.Holder.iDN 0 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      + Work.CR.Flat.Holder.hSN 0 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal (L1f i) := by
    intro i
    have hMnn : 0 ≤ K * (1 + Real.rpow (Efun i) (-p)) := by
      have := hrpowE i; nlinarith [hKpos.le]
    have hχdiff : ∀ z, DifferentiableAt ℝ (fun z : Cn n => (χf i z : ℂ)) z := fun z => by
      have hd : Differentiable ℝ (fun z : Cn n => (χf i z : ℂ)) :=
        ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm i 1)).differentiable
          (by norm_num)
      exact hd.differentiableAt
    have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal 1 := by
      rw [Work.CR.Flat.Holder.iDN_zero_deriv]
      refine iSup₂_le fun z _ => ?_
      rw [show ‖(χf i z : ℂ)‖ = χf i z from by
        rw [show ‖(χf i z : ℂ)‖ = |χf i z| from RCLike.norm_ofReal (χf i z),
          abs_of_nonneg (hχnn i z)]]
      exact ENNReal.ofReal_le_ofReal (hχle1 i z)
    have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (max 2 (K * (1 + Real.rpow (Efun i) (-p)))) := by
      have h2' := hSN_zero_le_of_deriv_bound (Ω := Work.CR.Flat.polydisc (0 : Cn n) ρ'')
        (χ := fun z : Cn n => (χf i z : ℂ))
        (M := K * (1 + Real.rpow (Efun i) (-p))) (Z := 1)
        hα0 hα1.le hMnn (by norm_num)
        hχdiff (fun x => hχg i x) (fun x => by
          rw [show ‖(χf i x : ℂ)‖ = χf i x from by
            rw [show ‖(χf i x : ℂ)‖ = |χf i x| from RCLike.norm_ofReal (χf i x),
              abs_of_nonneg (hχnn i x)]]
          exact hχle1 i x)
      refine h2'.trans_eq ?_
      congr 1
      rw [mul_one]
    have h3 : ENNReal.ofReal 1 + ENNReal.ofReal (max 2 (K * (1 + Real.rpow (Efun i) (-p))))
        ≤ ENNReal.ofReal (L1f i) := by
      rw [hL1fv i, ← ENNReal.ofReal_add (by norm_num)
        (le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_left _ _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hle : max (2:ℝ) (K * (1 + Real.rpow (Efun i) (-p)))
          ≤ 2 + K * (1 + Real.rpow (Efun i) (-p)) :=
        max_le (by linarith) (by linarith)
      linarith
    exact (add_le_add h1 h2).trans h3
  have hL2 : ∀ i, Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal (L2f i) := by
    intro i
    have hMnn : 0 ≤ K * (1 + Real.rpow (Efun i) (-p)) := by
      have := hrpowE i; nlinarith [hKpos.le]
    have hΩ'' : IsOpen (Work.CR.Flat.polydisc (0 : Cn n) ρ'') := Work.CR.Flat.isOpen_polydisc 0 ρ''
    have h3 : Work.CR.Flat.iterDerivNorm 1 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (K * (1 + Real.rpow (Efun i) (-p))) := by
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun z hz => ?_
      rw [norm_iteratedFDerivWithin_one_eq hΩ'' (fun z : Cn n => (χf i z : ℂ)) hz]
      exact ENNReal.ofReal_le_ofReal (hχg i z)
    have h4 : Work.CR.Flat.holderSeminorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'')
        ≤ ENNReal.ofReal (2 * (K * (1 + Real.rpow (Efun i) (-p)))) := by
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      have hx' : x ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'' := hx
      have hy' : y ∈ Work.CR.Flat.polydisc (0 : Cn n) ρ'' := hy
      rw [norm_iteratedFDerivWithin_one_sub_eq hΩ'' (fun z : Cn n => (χf i z : ℂ)) hx' hy']
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hxyα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hxy0 α
      by_cases hle : ‖x - y‖ ≤ 1
      · have hpow : ‖x - y‖ ^ (1 - α) ≤ 1 := Real.rpow_le_one hxy0.le hle (by linarith)
        have hsub : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
          rw [Real.rpow_sub hxy0 (1:ℝ) α, Real.rpow_one]
        calc ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
              - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖ / ‖x - y‖ ^ α
            ≤ (K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right (hχL i x y) hxyα.le
          _ = K * (1 + Real.rpow (Efun i) (-p)) * (‖x - y‖ / ‖x - y‖ ^ α) := by ring
          _ = K * (1 + Real.rpow (Efun i) (-p)) * ‖x - y‖ ^ (1 - α) := by rw [hsub]
          _ ≤ K * (1 + Real.rpow (Efun i) (-p)) * 1 := mul_le_mul_of_nonneg_left hpow hMnn
          _ ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) := by linarith
      · have h2b : ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
            - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖
            ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) := by
          have hxa := hχg i x
          have hya := hχg i y
          have := norm_sub_le (fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x)
            (fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y)
          linarith
        have hα1' : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (not_le.mp hle).le hα0.le
        calc ‖fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) x
              - fderiv ℝ (fun z : Cn n => (χf i z : ℂ)) y‖ / ‖x - y‖ ^ α
            ≤ (2 * (K * (1 + Real.rpow (Efun i) (-p)))) / ‖x - y‖ ^ α :=
              div_le_div_of_nonneg_right h2b hxyα.le
          _ ≤ 2 * (K * (1 + Real.rpow (Efun i) (-p))) :=
              div_le_self (by have := hrpowE i; nlinarith [hKpos.le]) hα1'
    have h5 := hL1 i
    rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_one]
    have hsum : ENNReal.ofReal (L1f i) + (ENNReal.ofReal (K * (1 + Real.rpow (Efun i) (-p)))
        + ENNReal.ofReal (2 * (K * (1 + Real.rpow (Efun i) (-p))))) = ENNReal.ofReal (L2f i) := by
      rw [hL1fv i, hL2fv i,
        ← ENNReal.ofReal_add (p := K * (1 + Real.rpow (Efun i) (-p)))
          (q := 2 * (K * (1 + Real.rpow (Efun i) (-p)))) hMnn (by linarith),
        ← ENNReal.ofReal_add (p := 3 + K * (1 + Real.rpow (Efun i) (-p)))
          (q := K * (1 + Real.rpow (Efun i) (-p)) + 2 * (K * (1 + Real.rpow (Efun i) (-p))))
          (by linarith) (by linarith)]
      congr 1
      ring
    exact (add_le_add h5 (add_le_add h3 h4)).trans (le_of_eq hsum)
  -- ## the datum bound for the cutoff
  have hdatai : ∀ (i : ℕ) (j : Fin n), Work.CR.Flat.holderNorm 0 α
      (fun z => dbarCn (JstdCn n + A) (fun z => (χf i z : ℂ)) z (Pi.single j 1))
      (Work.CR.Flat.polydisc 0 ρ'')
      ≤ ENNReal.ofReal Kd * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ))
          (Work.CR.Flat.polydisc 0 ρ'') := by
    intro i j
    have hε' : 0 ≤ max ε 0 := le_max_right _ _
    have hε'le : max ε 0 ≤ eps0 := max_le hε (le_of_lt heps0pos)
    have hBsm : ∀ i' l : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i' 1) l)
        (Work.CR.Flat.polydisc 0 ρ'') ≤ ENNReal.ofReal (max ε 0) := by
      intro i' l
      refine (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ)
        (Work.CR.Flat.isOpen_polydisc 0 ρ'') ?_ 0 α (fun z => A z (Pi.single i' 1) l)).trans ?_
      · exact fun z hz j => lt_trans (hz j) (hρ''ρ j)
      · exact (hsmall i' l).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hBc : ∀ i' l : Fin n, ContDiffOn ℝ 0 (fun z => A z (Pi.single i' 1) l)
        (Work.CR.Flat.polydisc 0 ρ'') := by
      intro i' l
      rw [contDiffOn_zero]
      have hAcont : Continuous A := contDiff_zero.mp (hAsm 0)
      have h1 : Continuous (fun z : Cn n => A z (Pi.single i' 1)) :=
        hAcont.clm_apply continuous_const
      exact ((continuous_apply l).comp h1).continuousOn
    have hχi : ContDiffOn ℝ 1 (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'') :=
      ((ContinuousLinearMap.contDiff Complex.ofRealCLM).comp (hχsm i 1)).contDiffOn
    have hres := hdatac hχi hε' hBsm hBc j
    refine hres.trans ?_
    have hCdnn : (0:ℝ) ≤ Cd := hCdpos.le
    have h1m : 1 + max ε 0 ≤ 1 + eps0 := by linarith
    have hcoef : ENNReal.ofReal Cd * ENNReal.ofReal (1 + max ε 0) ≤ ENNReal.ofReal Kd := by
      rw [hKddef, ← ENNReal.ofReal_mul hCdnn]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1m hCdpos.le)
    calc ENNReal.ofReal Cd * (ENNReal.ofReal (1 + max ε 0)
          * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ''))
        = (ENNReal.ofReal Cd * ENNReal.ofReal (1 + max ε 0))
          * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ)) (Work.CR.Flat.polydisc 0 ρ'') :=
          by rw [mul_assoc]
      _ ≤ ENNReal.ofReal Kd * Work.CR.Flat.holderNorm 1 α (fun z => (χf i z : ℂ))
            (Work.CR.Flat.polydisc 0 ρ'') := mul_le_mul hcoef le_rfl bot_le bot_le
  -- ## the coefficient sequences
  set ar : ℕ → ℝ := fun i => CL * L1f i with hardef
  set br : ℕ → ℝ := fun i => CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * Real.rpow (Dfun i) (-α))
    with hbrdef
  set lr : ℕ → ℝ := fun i => CL * (Kd * (n:ℝ) * L2f i) * Real.rpow (Dfun i) (1 - α) with hlrdef
  set P : ℕ → ℝ := fun i => ∏ k ∈ Finset.range i, lr k with hPdef
  have harv : ∀ i, ar i = CL * L1f i := fun i => by simp only [hardef]
  have hbrv : ∀ i, br i = CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * Real.rpow (Dfun i) (-α)) :=
    fun i => by simp only [hbrdef]
  have hlrv : ∀ i, lr i = CL * (Kd * (n:ℝ) * L2f i) * Real.rpow (Dfun i) (1-α) :=
    fun i => by simp only [hlrdef]
  have hPv : ∀ i, P i = ∏ k ∈ Finset.range i, lr k := fun i => by simp only [hPdef]
  have hP0 : P 0 = 1 := by simp [hPdef]
  have hPsucc : ∀ i, P (i+1) = P i * lr i := fun i => by
    simp only [hPdef, Finset.prod_range_succ]
  -- ## the growth of `Real.rpow (Efun i) (-p)` etc.
  have hEpow : ∀ i, Real.rpow (Efun i) (-p) = Real.rpow e0 (-p) * Bp ^ i := by
    intro i
    rw [hEv i]
    have key : Real.rpow (e0 * ((1/2:ℝ))^i) (-p)
        = Real.rpow e0 (-p) * Real.rpow ((1/2:ℝ)^i) (-p) :=
      Real.mul_rpow (x := e0) (y := ((1/2:ℝ))^i) (z := -p) he0pos.le (by positivity)
    rw [key, hBpdef, rpow_half_pow_neg i p]
  have hDpow1 : ∀ i, Real.rpow (Dfun i) (1-α) = Real.rpow d0 (1-α) * B1 ^ (m*i) := by
    intro i
    rw [hDv i]
    have key : Real.rpow (d0 * ((1/2:ℝ))^(m*i)) (1-α)
        = Real.rpow d0 (1-α) * Real.rpow ((1/2:ℝ)^(m*i)) (1-α) :=
      Real.mul_rpow (x := d0) (y := ((1/2:ℝ))^(m*i)) (z := 1-α) hd0pos.le (by positivity)
    rw [key, rpow_half_pow (m*i) (1-α), ← hB1eq]
  have hDpowα : ∀ i, Real.rpow (Dfun i) (-α) = Real.rpow d0 (-α) * Bal ^ (m*i) := by
    intro i
    rw [hDv i]
    have key : Real.rpow (d0 * ((1/2:ℝ))^(m*i)) (-α)
        = Real.rpow d0 (-α) * Real.rpow ((1/2:ℝ)^(m*i)) (-α) :=
      Real.mul_rpow (x := d0) (y := ((1/2:ℝ))^(m*i)) (z := -α) hd0pos.le (by positivity)
    rw [key, hBaldef, rpow_half_pow_neg (m*i) α]
  -- ## the bounds on the coefficients
  have hL1b : ∀ i, L1f i ≤ CA * Bp ^ i := by
    intro i
    rw [hL1fv i, hEpow i, hCAdef]
    have h1 : (1:ℝ) ≤ Bp ^ i := one_le_pow₀ hBp1
    have h2 := Real.rpow_pos_of_pos he0pos (-p)
    nlinarith [h1, h2, hKpos.le, hBp1]
  have hL2b : ∀ i, L2f i ≤ CB * Bp ^ i := by
    intro i
    rw [hL2fv i, hEpow i, hCBdef]
    have h1 : (1:ℝ) ≤ Bp ^ i := one_le_pow₀ hBp1
    have h2 := Real.rpow_pos_of_pos he0pos (-p)
    nlinarith [h1, h2, hKpos.le, hBp1]
  have harb : ∀ i, ar i ≤ A2 * Bp ^ i := by
    intro i
    rw [harv i, hA2def]
    calc CL * L1f i ≤ CL * (CA * Bp ^ i) := mul_le_mul_of_nonneg_left (hL1b i) hCLpos.le
      _ = CL * CA * Bp ^ i := by ring
  have hlrb : ∀ i, lr i ≤ ((1/2:ℝ))^i := by
    intro i
    have hkey : lr i ≤ CstL * (Bp * B1 ^ m) ^ i := by
      rw [hlrv i, hCstLdef, hDpow1 i]
      have h1 : CL * (Kd * (n:ℝ) * L2f i) ≤ CL * Kd * (n:ℝ) * CB * Bp ^ i := by
        have h2 : Kd * (n:ℝ) * L2f i ≤ Kd * (n:ℝ) * (CB * Bp ^ i) :=
          mul_le_mul_of_nonneg_left (hL2b i) (by positivity)
        calc CL * (Kd * (n:ℝ) * L2f i) ≤ CL * (Kd * (n:ℝ) * (CB * Bp ^ i)) :=
              mul_le_mul_of_nonneg_left h2 hCLpos.le
          _ = CL * Kd * (n:ℝ) * CB * Bp ^ i := by ring
      calc CL * (Kd * (n:ℝ) * L2f i) * (Real.rpow d0 (1-α) * B1^(m*i))
          ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * (Real.rpow d0 (1-α) * B1^(m*i)) :=
            mul_le_mul_of_nonneg_right h1
              (mul_nonneg (Real.rpow_nonneg hd0pos.le (1-α)) (pow_nonneg hB1nn _))
        _ = CstL * (Bp ^ i * B1^(m*i)) := by rw [hCstLdef]; ring
        _ = CstL * (Bp * B1 ^ m) ^ i := by rw [pow_mul B1 m i, ← mul_pow Bp (B1^m) i]
    calc lr i ≤ CstL * (Bp * B1 ^ m) ^ i := hkey
      _ ≤ 1 * (Real.rpow 2 (-beta))^i := by
          rw [hB1m]
          exact mul_le_mul_of_nonneg_right hCstLle
            (pow_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) i)
      _ ≤ 1 * ((1/2:ℝ))^i := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-beta))
            (le_trans hB1le (by norm_num)) i
      _ = ((1/2:ℝ))^i := one_mul _
  have hbrb : ∀ i, br i ≤ B2 * Bq ^ i := by
    intro i
    have hkey : br i ≤ B2 * ((Bp * Bal ^ m) ^ i) := by
      rw [hbrv i, hB2def, hDpowα i]
      have h1 : CL * (Kd * (n:ℝ) * L2f i)
          ≤ CL * Kd * (n:ℝ) * CB * Bp ^ i := by
        have h2 : Kd * (n:ℝ) * L2f i ≤ Kd * (n:ℝ) * (CB * Bp ^ i) :=
          mul_le_mul_of_nonneg_left (hL2b i) (by positivity)
        calc CL * (Kd * (n:ℝ) * L2f i) ≤ CL * (Kd * (n:ℝ) * (CB * Bp ^ i)) :=
              mul_le_mul_of_nonneg_left h2 hCLpos.le
          _ = CL * Kd * (n:ℝ) * CB * Bp ^ i := by ring
      have h2 : (1:ℝ) + 2 * (Real.rpow d0 (-α) * Bal^(m*i))
          ≤ (1 + 2 * Real.rpow d0 (-α)) * Bal^(m*i) := by
        have hb1 : (1:ℝ) ≤ Bal^(m*i) := one_le_pow₀ hBal1
        have hb2 : (0:ℝ) ≤ Real.rpow d0 (-α) :=
          (Real.rpow_pos_of_pos hd0pos (-α)).le
        nlinarith
      calc CL * (Kd * (n:ℝ) * L2f i) * (1 + 2 * (Real.rpow d0 (-α) * Bal^(m*i)))
          ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * (1 + 2 * (Real.rpow d0 (-α) * Bal^(m*i))) :=
            mul_le_mul_of_nonneg_right h1 (by
              have hb2 : (0:ℝ) ≤ Real.rpow d0 (-α) :=
                (Real.rpow_pos_of_pos hd0pos (-α)).le
              have hb1 : (1:ℝ) ≤ Bal ^ (m*i) := one_le_pow₀ hBal1
              nlinarith)
        _ ≤ (CL * Kd * (n:ℝ) * CB * Bp ^ i) * ((1 + 2 * Real.rpow d0 (-α)) * Bal^(m*i)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = B2 * (Bp ^ i * Bal^(m*i)) := by rw [hB2def]; ring
        _ = B2 * (Bp * Bal ^ m) ^ i := by rw [pow_mul Bal m i, ← mul_pow Bp (Bal^m) i]
    calc br i ≤ B2 * ((Bp * Bal ^ m) ^ i) := hkey
      _ = B2 * Bq ^ i := by
          congr 1
          rw [hBqdef]
          congr 1
          rw [hBpdef, hBaldef]
          change ((2:ℝ)^p) * (((2:ℝ)^α)^m) = ((2:ℝ)^(p + (m:ℝ)*α))
          rw [← Real.rpow_natCast ((2:ℝ)^α) m,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) α (m:ℝ),
            ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
  -- ## the bounds on the products
  have harnn : ∀ i, 0 ≤ ar i := fun i => by rw [harv i]; exact mul_nonneg hCLpos.le (hL1fnn i)
  have hDpowαnn : ∀ i, (0:ℝ) ≤ Real.rpow (Dfun i) (-α) :=
    fun i => (Real.rpow_pos_of_pos (hDpos i) (-α)).le
  have hDpow1nn : ∀ i, (0:ℝ) ≤ Real.rpow (Dfun i) (1-α) :=
    fun i => (Real.rpow_pos_of_pos (hDpos i) (1-α)).le
  have hbrnn : ∀ i, 0 ≤ br i := fun i => by
    rw [hbrv i]
    have h1 : (0:ℝ) ≤ CL := hCLpos.le
    have h2 : (0:ℝ) ≤ Kd := hKdpos.le
    have h3 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h4 : (0:ℝ) ≤ L2f i := hL2fnn i
    have h5 : (0:ℝ) ≤ Real.rpow (Dfun i) (-α) := hDpowαnn i
    positivity
  have hlrnn : ∀ i, 0 ≤ lr i := fun i => by
    rw [hlrv i]
    have h1 : (0:ℝ) ≤ CL := hCLpos.le
    have h2 : (0:ℝ) ≤ Kd := hKdpos.le
    have h3 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h4 : (0:ℝ) ≤ L2f i := hL2fnn i
    have h5 : (0:ℝ) ≤ Real.rpow (Dfun i) (1-α) := hDpow1nn i
    positivity
  have hPnn' : ∀ i, 0 ≤ P i := fun i => by
    rw [hPv i]; exact Finset.prod_nonneg fun k _ => hlrnn k
  have hPbound : ∀ i, P i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) := by
    intro i
    have h1 : P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := by
      rw [hPv i]
      exact prod_range_le_of_nonneg (fun k => hlrnn k) (fun k => pow_nonneg (by norm_num) k)
        (fun k => hlrb k) i
    have h2 : (∏ k ∈ Finset.range i, ((1/2:ℝ))^k)
        = ((1/2:ℝ))^(∑ k ∈ Finset.range i, k) := Finset.prod_pow_eq_pow_sum _ _ _
    have h3 : ((1/2:ℝ))^(∑ k ∈ Finset.range i, k)
        = Real.rpow 2 (-((∑ k ∈ Finset.range i, k : ℕ):ℝ)) :=
      (rpow_two_neg_nat _).symm
    have h4 : ((∑ k ∈ Finset.range i, k : ℕ):ℝ) = (i:ℝ)*((i:ℝ)-1)/2 := cast_range_sum_id i
    calc P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := h1
      _ = ((1/2:ℝ))^(∑ k ∈ Finset.range i, k) := h2
      _ = Real.rpow 2 (-((∑ k ∈ Finset.range i, k : ℕ):ℝ)) := h3
      _ = Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) := by rw [h4]
  have hP1 : ∀ i, P i ≤ 1 := by
    intro i
    calc P i ≤ ∏ k ∈ Finset.range i, ((1/2:ℝ))^k := by
          rw [hPv i]
          exact prod_range_le_of_nonneg (fun k => hlrnn k) (fun k => pow_nonneg (by norm_num) k)
            (fun k => hlrb k) i
      _ ≤ 1 := prod_range_half_le_one i
  have hPar : ∀ i, P i * ar i ≤ DA * ((1/2:ℝ))^i := by
    intro i
    by_cases hi : i ≤ I0A
    · have h3 : Bp ^ i ≤ Bp ^ I0A := pow_le_pow_right₀ hBp1 hi
      have h4 : (1:ℝ) ≤ (2:ℝ)^I0A * ((1/2:ℝ))^i := by
        have h5 : ((1/2:ℝ))^I0A ≤ ((1/2:ℝ))^i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
        have h6 : ((1/2:ℝ))^I0A * (2:ℝ)^I0A = 1 := by rw [← mul_pow]; norm_num
        have h7 : (0:ℝ) < (2:ℝ)^I0A := by positivity
        nlinarith [h5, h6, h7]
      calc P i * ar i ≤ 1 * (A2 * Bp ^ i) :=
            mul_le_mul (hP1 i) (harb i) (harnn i) (by norm_num)
        _ = A2 * Bp ^ i := one_mul _
        _ ≤ A2 * Bp ^ I0A := mul_le_mul_of_nonneg_left h3 hA2nn
        _ ≤ A2 * Bp ^ I0A * ((2:ℝ)^I0A * ((1/2:ℝ))^i) :=
            le_mul_of_one_le_right (mul_nonneg hA2nn (pow_nonneg (le_of_lt hBp0) I0A)) h4
        _ = DA * ((1/2:ℝ))^i := by rw [hDAdef]; ring
    · have hiI : (I0A:ℝ) < (i:ℝ) := by exact_mod_cast (not_le.mp hi)
      have h5 : p * (i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2 ≤ -(i:ℝ) := by
        have hi2 : (2*p+3 : ℝ) ≤ (i:ℝ) := le_trans hI0A hiI.le
        have hpos : (0:ℝ) < (i:ℝ) := by linarith
        nlinarith
      have h6 : Bp ^ i = Real.rpow 2 (p * (i:ℝ)) := by rw [hBpdef]; exact rpow_two_mul_nat i p
      have h7 : Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 (p * (i:ℝ))
          = Real.rpow 2 (p*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by
        rw [show Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 (p * (i:ℝ))
            = ((2:ℝ) ^ (-((i:ℝ)*((i:ℝ)-1)/2))) * ((2:ℝ) ^ (p * (i:ℝ))) from rfl,
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc P i * ar i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * (A2 * Bp ^ i) :=
            mul_le_mul (hPbound i) (harb i) (harnn i) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        _ = A2 * (Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Bp ^ i) := by ring
        _ = A2 * Real.rpow 2 (p*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by rw [h6, h7]
        _ ≤ A2 * Real.rpow 2 (-(i:ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA2nn
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        _ = A2 * ((1/2:ℝ))^i := by rw [rpow_two_neg_nat i]
        _ ≤ DA * ((1/2:ℝ))^i := by
            rw [hDAdef]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h8 : (1:ℝ) ≤ Bp ^ I0A := one_le_pow₀ hBp1
            have h9 : (1:ℝ) ≤ (2:ℝ)^I0A := one_le_pow₀ (by norm_num)
            calc A2 ≤ A2 * Bp ^ I0A := le_mul_of_one_le_right hA2nn h8
              _ ≤ A2 * Bp ^ I0A * (2:ℝ)^I0A :=
                  le_mul_of_one_le_right (mul_nonneg hA2nn (pow_nonneg hBp0.le I0A)) h9
  have hPbr : ∀ i, P i * br i ≤ DB * ((1/2:ℝ))^i := by
    intro i
    by_cases hi : i ≤ I0B
    · have h3 : Bq ^ i ≤ Bq ^ I0B := pow_le_pow_right₀ hBq1 hi
      have h4 : (1:ℝ) ≤ (2:ℝ)^I0B * ((1/2:ℝ))^i := by
        have h5 : ((1/2:ℝ))^I0B ≤ ((1/2:ℝ))^i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
        have h6 : ((1/2:ℝ))^I0B * (2:ℝ)^I0B = 1 := by rw [← mul_pow]; norm_num
        have h7 : (0:ℝ) < (2:ℝ)^I0B := by positivity
        nlinarith [h5, h6, h7]
      calc P i * br i ≤ 1 * (B2 * Bq ^ i) :=
            mul_le_mul (hP1 i) (hbrb i) (hbrnn i) (by norm_num)
        _ = B2 * Bq ^ i := one_mul _
        _ ≤ B2 * Bq ^ I0B := mul_le_mul_of_nonneg_left h3 hB2nn
        _ ≤ B2 * Bq ^ I0B * ((2:ℝ)^I0B * ((1/2:ℝ))^i) :=
            le_mul_of_one_le_right (mul_nonneg hB2nn (pow_nonneg (le_of_lt hBq0) I0B)) h4
        _ = DB * ((1/2:ℝ))^i := by rw [hDBdef]; ring
    · have hiI : (I0B:ℝ) < (i:ℝ) := by exact_mod_cast (not_le.mp hi)
      have h5 : (p + (m:ℝ)*α) * (i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2 ≤ -(i:ℝ) := by
        have hi2 : (2*(p + (m:ℝ)*α)+3 : ℝ) ≤ (i:ℝ) := le_trans hI0B hiI.le
        have hpos : (0:ℝ) < (i:ℝ) := by linarith
        nlinarith
      have h6 : Bq ^ i = Real.rpow 2 ((p + (m:ℝ)*α) * (i:ℝ)) := by
        rw [hBqdef]; exact rpow_two_mul_nat i _
      have h7 : Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 ((p+(m:ℝ)*α) * (i:ℝ))
          = Real.rpow 2 ((p+(m:ℝ)*α)*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by
        rw [show Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Real.rpow 2 ((p+(m:ℝ)*α) * (i:ℝ))
            = ((2:ℝ) ^ (-((i:ℝ)*((i:ℝ)-1)/2))) * ((2:ℝ) ^ ((p+(m:ℝ)*α) * (i:ℝ))) from rfl,
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc P i * br i ≤ Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * (B2 * Bq ^ i) :=
            mul_le_mul (hPbound i) (hbrb i) (hbrnn i) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
        _ = B2 * (Real.rpow 2 (-((i:ℝ)*((i:ℝ)-1)/2)) * Bq ^ i) := by ring
        _ = B2 * Real.rpow 2 ((p+(m:ℝ)*α)*(i:ℝ) - (i:ℝ)*((i:ℝ)-1)/2) := by rw [h6, h7]
        _ ≤ B2 * Real.rpow 2 (-(i:ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hB2nn
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        _ = B2 * ((1/2:ℝ))^i := by rw [rpow_two_neg_nat i]
        _ ≤ DB * ((1/2:ℝ))^i := by
            rw [hDBdef]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have h8 : (1:ℝ) ≤ Bq ^ I0B := one_le_pow₀ hBq1
            have h9 : (1:ℝ) ≤ (2:ℝ)^I0B := one_le_pow₀ (by norm_num)
            calc B2 ≤ B2 * Bq ^ I0B := le_mul_of_one_le_right hB2nn h8
              _ ≤ B2 * Bq ^ I0B * (2:ℝ)^I0B :=
                  le_mul_of_one_le_right (mul_nonneg hB2nn (pow_nonneg hBq0.le I0B)) h9
  -- ## the chain
  set V : ℕ → ℝ≥0∞ := fun i => Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 (Rfun i))
    with hVdef
  set Mes : ℕ → ℝ≥0∞ := fun i =>
    ⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (Rfun i), ENNReal.ofReal ‖fderiv ℝ u z‖ with hMesdef
  have hMesV : ∀ i, Mes i ≤ V i := by
    intro i
    have hΩr : IsOpen (Work.CR.Flat.polydisc (0:Cn n) (Rfun i)) := Work.CR.Flat.isOpen_polydisc 0 _
    rw [hMesdef]
    refine le_trans ?_ (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α u
      (Work.CR.Flat.polydisc 0 (Rfun i)) (le_refl 1))
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun z hz => ?_
    refine le_iSup₂_of_le z hz ?_
    rw [norm_iteratedFDerivWithin_one_eq hΩr u hz]
  have hMesM : ∀ i, Mes i ≤ Me := by
    intro i
    rw [hMesdef, hMedef]
    refine iSup₂_le fun z hz => ?_
    exact le_iSup₂_of_le z (fun j => lt_of_lt_of_le (hz j) (hRsub i j)) le_rfl
  have hstep : ∀ i, V i ≤ ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z
      + ENNReal.ofReal (lr i) * V (i+1) := by
    intro i
    have h := onestepSup (A := A) hn hα0 hα1 hρ''0 hρ''ρ hCLpos hKdpos (hL1fpos i)
      (hL2fpos i) (hDpos i) (fun v hv hvc => hloss hAsm (le_trans hε (min_le_left εL 1)) hsmall hJ v hv hvc)
      (hEpos i) (fun j : Fin n => hRe i j) (hχsm i) (hχ1 i) (hχ0 i) (hL1 i) (hL2 i) (hdatai i) hu
    refine h.trans ?_
    have hm : (⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (fun j => Rfun i j + (Efun i + Dfun i)),
        ENNReal.ofReal ‖fderiv ℝ u z‖) ≤ V (i+1) := by
      rw [hRsucc i]
      exact hMesV (i+1)
    exact add_le_add (add_le_add (by rw [hardef, hXdef]) (by rw [hbrdef, hZdef]))
      (by rw [hlrdef]; exact mul_le_mul le_rfl hm bot_le bot_le)
  have hteles := chain_telescope (V := V) (X := X) (Z := Z) (ar := ar) (br := br) (lr := lr)
    P hP0 hPsucc harnn hbrnn hlrnn hstep
  -- ## the infinite sum
  set Ssum : ℝ≥0∞ := (∑' i, ENNReal.ofReal (P i * ar i)) * X
    + (∑' i, ENNReal.ofReal (P i * br i)) * Z with hSsumdef
  have hgeom1 : (∑' i : ℕ, ENNReal.ofReal (DA * ((1/2:ℝ))^i)) = ENNReal.ofReal (2 * DA) := by
    have hsumm : Summable (fun i : ℕ => DA * ((1/2:ℝ))^i) :=
      Summable.mul_left DA (summable_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsumm, tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1)]
    congr 1
    ring
  have hgeom2 : (∑' i : ℕ, ENNReal.ofReal (DB * ((1/2:ℝ))^i)) = ENNReal.ofReal (2 * DB) := by
    have hsumm : Summable (fun i : ℕ => DB * ((1/2:ℝ))^i) :=
      Summable.mul_left DB (summable_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsumm, tsum_mul_left,
      tsum_geometric_of_norm_lt_one (by norm_num : ‖((1/2:ℝ))‖ < 1)]
    congr 1
    ring
  have hSA : (∑' i, ENNReal.ofReal (P i * ar i)) ≤ ENNReal.ofReal (2 * DA) := by
    refine (ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hPar i)).trans (le_of_eq hgeom1)
  have hSB : (∑' i, ENNReal.ofReal (P i * br i)) ≤ ENNReal.ofReal (2 * DB) := by
    refine (ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hPbr i)).trans (le_of_eq hgeom2)
  have hSsumle : Ssum ≤ ENNReal.ofReal (2 * DA) * X + ENNReal.ofReal (2 * DB) * Z := by
    rw [hSsumdef]
    exact add_le_add (mul_le_mul hSA le_rfl bot_le bot_le) (mul_le_mul hSB le_rfl bot_le bot_le)
  -- ## the limit
  have hV0 : V 0 ≤ Ssum := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδpos : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
    set xv : ℝ := X.toReal with hxv
    set zv : ℝ := Z.toReal with hzv
    set mv : ℝ := Me.toReal with hmv
    have hxcoe : ENNReal.ofReal xv = X := ENNReal.ofReal_toReal hXtop
    have hzcoe : ENNReal.ofReal zv = Z := ENNReal.ofReal_toReal hZtop
    have hmcoe : ENNReal.ofReal mv = Me := ENNReal.ofReal_toReal (ne_of_lt hMelt)
    have hxv0 : 0 ≤ xv := ENNReal.toReal_nonneg
    have hzv0 : 0 ≤ zv := ENNReal.toReal_nonneg
    have hmv0 : 0 ≤ mv := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N ≤ (δ:ℝ) := by
      have ht : Filter.Tendsto (fun N : ℕ => (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N)
          Filter.atTop (𝓝 0) := by
        have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (1/2:ℝ) < 1)).const_mul (2*DA*xv + 2*DB*zv + mv)
        simpa using h0
      have hlt := (tendsto_order.1 ht).2 (δ:ℝ) hδpos
      rw [Filter.eventually_atTop] at hlt
      obtain ⟨N, hN⟩ := hlt
      exact ⟨N, le_of_lt (hN N le_rfl)⟩
    have hPNV : ENNReal.ofReal (P N) * V N ≤ ENNReal.ofReal (δ:ℝ) := by
      have hlast : V N ≤ ENNReal.ofReal (ar N) * X + ENNReal.ofReal (br N) * Z
          + ENNReal.ofReal (lr N) * Me := by
        have h := onestepSup (A := A) hn hα0 hα1 hρ''0 hρ''ρ hCLpos hKdpos (hL1fpos N)
          (hL2fpos N) (hDpos N) (fun v hv hvc => hloss hAsm (le_trans hε (min_le_left εL 1)) hsmall hJ v hv hvc)
          (hEpos N) (fun j : Fin n => hRe N j) (hχsm N) (hχ1 N) (hχ0 N) (hL1 N) (hL2 N) (hdatai N) hu
        refine h.trans ?_
        have hm : (⨆ z ∈ Work.CR.Flat.polydisc (0:Cn n) (fun j => Rfun N j + (Efun N + Dfun N)),
            ENNReal.ofReal ‖fderiv ℝ u z‖) ≤ Me := by
          rw [hRsucc N]
          exact hMesM (N+1)
        exact add_le_add (add_le_add (by rw [hardef, hXdef]) (by rw [hbrdef, hZdef]))
          (by rw [hlrdef]; exact mul_le_mul le_rfl hm bot_le bot_le)
      have hPnn' : 0 ≤ P N := by
        have h : P N ≤ 1 := hP1 N
        have h0 : (0:ℝ) ≤ P N := by
          rw [hPdef]
          exact Finset.prod_nonneg fun k _ => hlrnn k
        exact h0
      refine (mul_le_mul le_rfl hlast bot_le bot_le).trans ?_
      rw [mul_add, mul_add]
      have e1 : ENNReal.ofReal (P N) * ENNReal.ofReal (ar N) = ENNReal.ofReal (P N * ar N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have e2 : ENNReal.ofReal (P N) * ENNReal.ofReal (br N) = ENNReal.ofReal (P N * br N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have e3 : ENNReal.ofReal (P N) * ENNReal.ofReal (lr N) = ENNReal.ofReal (P N * lr N) :=
        (ENNReal.ofReal_mul hPnn').symm
      have hassoc : ENNReal.ofReal (P N) * (ENNReal.ofReal (ar N) * X)
            + ENNReal.ofReal (P N) * (ENNReal.ofReal (br N) * Z)
            + ENNReal.ofReal (P N) * (ENNReal.ofReal (lr N) * Me)
          = (ENNReal.ofReal (P N) * ENNReal.ofReal (ar N)) * X
            + (ENNReal.ofReal (P N) * ENNReal.ofReal (br N)) * Z
            + (ENNReal.ofReal (P N) * ENNReal.ofReal (lr N)) * Me := by ring
      rw [hassoc, e1, e2, e3]
      have hxr : ENNReal.ofReal (P N * ar N) * X ≤ ENNReal.ofReal (DA * ((1/2:ℝ))^N) * X :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hPar N)) bot_le
      have hzr : ENNReal.ofReal (P N * br N) * Z ≤ ENNReal.ofReal (DB * ((1/2:ℝ))^N) * Z :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hPbr N)) bot_le
      have hmr : ENNReal.ofReal (P N * lr N) * Me ≤ ENNReal.ofReal (((1/2:ℝ))^N) * Me := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        calc P N * lr N ≤ 1 * ((1/2:ℝ))^N :=
              mul_le_mul (hP1 N) (hlrb N) (hlrnn N) (by norm_num)
          _ = ((1/2:ℝ))^N := one_mul _
      refine (add_le_add (add_le_add hxr hzr) hmr).trans ?_
      -- rewrite in terms of xv, zv, mv
      rw [← hxcoe, ← hzcoe, ← hmcoe]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ DA * ((1/2:ℝ))^N),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ DB * ((1/2:ℝ))^N),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((1/2:ℝ))^N),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h8 : DA * ((1/2:ℝ))^N * xv + DB * ((1/2:ℝ))^N * zv + ((1/2:ℝ))^N * mv
          ≤ (2*DA*xv + 2*DB*zv + mv) * ((1/2:ℝ))^N := by
        have hNn : (0:ℝ) ≤ ((1/2:ℝ))^N := by positivity
        have h1 : DA * ((1/2:ℝ))^N * xv ≤ (2*DA*xv) * ((1/2:ℝ))^N := by
          have h0 : (0:ℝ) ≤ DA * xv * ((1/2:ℝ))^N := mul_nonneg (mul_nonneg hDA0 hxv0) hNn
          have e1 : DA * ((1/2:ℝ))^N * xv = DA * xv * ((1/2:ℝ))^N := by ring
          have e2 : (2*DA*xv) * ((1/2:ℝ))^N = 2 * (DA * xv * ((1/2:ℝ))^N) := by ring
          linarith
        have h2 : DB * ((1/2:ℝ))^N * zv ≤ (2*DB*zv) * ((1/2:ℝ))^N := by
          have h0 : (0:ℝ) ≤ DB * zv * ((1/2:ℝ))^N := mul_nonneg (mul_nonneg hDB0 hzv0) hNn
          have e1 : DB * ((1/2:ℝ))^N * zv = DB * zv * ((1/2:ℝ))^N := by ring
          have e2 : (2*DB*zv) * ((1/2:ℝ))^N = 2 * (DB * zv * ((1/2:ℝ))^N) := by ring
          linarith
        have h3 : ((1/2:ℝ))^N * mv ≤ mv * ((1/2:ℝ))^N := le_of_eq (mul_comm _ _)
        linarith [h1, h2, h3]
      linarith [hN, h8]
    have hpart : (∑ i ∈ Finset.range N, ENNReal.ofReal (P i) *
        (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z)) ≤ Ssum := by
      rw [hSsumdef]
      have hsplit : (∑ i ∈ Finset.range N, ENNReal.ofReal (P i) *
          (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z))
          = (∑ i ∈ Finset.range N, ENNReal.ofReal (P i * ar i)) * X
            + (∑ i ∈ Finset.range N, ENNReal.ofReal (P i * br i)) * Z := by
        have h1 : ∀ i, ENNReal.ofReal (P i) *
            (ENNReal.ofReal (ar i) * X + ENNReal.ofReal (br i) * Z)
            = ENNReal.ofReal (P i * ar i) * X + ENNReal.ofReal (P i * br i) * Z := by
          intro i
          rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (hPnn' i),
            ← ENNReal.ofReal_mul (hPnn' i)]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      rw [hsplit]
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact (ENNReal.sum_le_tsum _).trans le_rfl
      · refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact (ENNReal.sum_le_tsum _).trans le_rfl
    refine (hteles N).trans (add_le_add hpart ?_)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hPNV
  -- ## conclusion
  have hV0eq : V 0 = Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc 0 ρ') := by
    have hR0 : Rfun 0 = ρ' := by
      funext j
      simp only [hRfundef, Finset.range_zero, Finset.sum_empty, add_zero]
    simp only [hVdef]
    rw [hR0]
  have hfin : ENNReal.ofReal (2*DA) * X + ENNReal.ofReal (2*DB) * Z
      ≤ ENNReal.ofReal Cfin * (X + Z) := by
    have h1 : ENNReal.ofReal (2*DA) ≤ ENNReal.ofReal Cfin := by
      rw [hCfindef]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have h2 : ENNReal.ofReal (2*DB) ≤ ENNReal.ofReal Cfin := by
      rw [hCfindef]; exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal (2*DA) * X + ENNReal.ofReal (2*DB) * Z
        ≤ ENNReal.ofReal Cfin * X + ENNReal.ofReal Cfin * Z :=
          add_le_add (mul_le_mul h1 le_rfl bot_le bot_le) (mul_le_mul h2 le_rfl bot_le bot_le)
      _ = ENNReal.ofReal Cfin * (X + Z) := by rw [mul_add]
  exact hV0eq ▸ (hV0.trans (hSsumle.trans hfin))

end

end Work.NN.Final.LevJ
