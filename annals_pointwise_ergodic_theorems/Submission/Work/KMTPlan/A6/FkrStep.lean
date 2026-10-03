/-
# The main step of the `fkr` interchange lemma
-/
import Mathlib
import Submission.Work.KMTPlan.A6.FkrAux
import Submission.Work.KMTPlan.A6.accVr_exists
import Submission.Work.KMTPlan.A6.fkr_cell_bound
import Submission.Work.Analysis.Variation.dyadicVariationLeGrid
import Submission.Work.Analysis.Probability.lepingle_vector
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- The main estimate: for a fixed truncation `K` the clamped variation is bounded by a constant
times the `V^R(ℕ; L^r)` norm of the sequence. -/
theorem fkr_step (μ : Measure X) {R : ℝ} (hR : 1 ≤ R)
    {r : NNReal} (hr : 1 ≤ r) (hrR : R < (r : ℝ)) (g : ℕ → X → ℂ) (hg : ∀ k, Measurable (g k))
    {w : ℝ} (hw : 0 < w) (hW : fkrW μ R r g = ENNReal.ofReal w) (K : ℕ) :
    eLpNorm (fun x => varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ
      ≤ ENNReal.ofReal (20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R))) * ENNReal.ofReal w := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hrE : (1 : ENNReal) ≤ (r : ENNReal) := by exact_mod_cast hr
  have hq00 : (0 : ℝ) < 1 / R := by positivity
  have hq0 : 1 / (r : ℝ) - 1 / R < 0 := by
    have h : 1 / (r : ℝ) < 1 / R := one_div_lt_one_div_of_lt hR0 hrR
    linarith
  -- Step 1: the accumulated V^R energy
  obtain ⟨a, ha_mono, ha_root, ha_ho⟩ := accVr_exists μ R hR0 r g K
  have ha_root' : ∀ j ≤ K, (a j) ^ (1 / R) ≤ ENNReal.ofReal w := by
    intro j hj
    rw [← hW]
    exact ha_root j hj
  have ha_ne_top : ∀ j ≤ K, a j ≠ ⊤ := by
    intro j hj htop
    have h := ha_root' j hj
    rw [htop, ENNReal.top_rpow_of_pos hq00] at h
    exact absurd h (not_le.mpr ENNReal.ofReal_lt_top)
  -- Step 2: the perturbed, strictly increasing "value" function
  set A : ℕ → ℝ := fun k => (a (min k K)).toReal with hA
  have hA_mono : Monotone A := by
    intro m n hmn
    rw [hA]
    exact ENNReal.toReal_mono (ha_ne_top _ (min_le_right n K))
      (ha_mono (min_le_min_right K hmn))
  have hA_le : ∀ k ≤ K, A k ≤ w ^ R := by
    intro k hk
    have h1 := ha_root' k hk
    have h2 : a k ≤ ENNReal.ofReal (w ^ R) := by
      calc a k = ((a k) ^ (1 / R)) ^ R := by
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hR0.ne', ENNReal.rpow_one]
        _ ≤ (ENNReal.ofReal w) ^ R := ENNReal.rpow_le_rpow h1 hR0.le
        _ = ENNReal.ofReal (w ^ R) := ENNReal.ofReal_rpow_of_nonneg (le_of_lt hw) hR0.le
    change (a (min k K)).toReal ≤ w ^ R
    rw [min_eq_left hk]
    calc (a k).toReal ≤ (ENNReal.ofReal (w ^ R)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
      _ = w ^ R := ENNReal.toReal_ofReal (Real.rpow_nonneg (le_of_lt hw) R)
  set η : ℝ := w ^ R / (K + 1) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  set b : ℕ → ℝ := fun k => A k + (k + 1) * η with hb
  have hb_mono : Monotone b := by
    intro m n hmn
    rw [hb]
    have h1 : A m ≤ A n := hA_mono hmn
    have h2 : ((m : ℝ) + 1) * η ≤ ((n : ℝ) + 1) * η := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      nlinarith [hη]
    linarith
  have hb_strict : ∀ k, 1 ≤ k → k ≤ K → b (k - 1) < b k := by
    intro k hk1 hk
    rw [hb]
    have h1 : A (k - 1) ≤ A k := hA_mono (by omega)
    have h2 : (((k - 1 : ℕ) : ℝ) + 1) < ((k : ℝ) + 1) := by
      have h3 : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by
        have : k - 1 < k := by omega
        exact_mod_cast this
      linarith
    nlinarith [hη]
  have hbK_le : b K ≤ 2 * w ^ R := by
    rw [hb]
    have h2 : ((K : ℝ) + 1) * η = w ^ R := by
      rw [hηdef]; field_simp
    have h3 := hA_le K le_rfl
    linarith
  have hbK_pos : 0 < b K := by
    rw [hb]
    have h1 : (0 : ℝ) < ((K : ℝ) + 1) * η := by positivity
    have h2 : (0 : ℝ) ≤ A K := by rw [hA]; positivity
    linarith
  set β : ℕ → ℝ := fun k => b k / b K with hβ
  have hβ0 : 0 ≤ β 0 := by
    rw [hβ]
    exact div_nonneg (by rw [hb]; positivity) (le_of_lt hbK_pos)
  have hβmono : Monotone β := by
    intro m n hmn
    rw [hβ]
    exact div_le_div_of_nonneg_right (hb_mono hmn) (le_of_lt hbK_pos)
  have hβK : β K = 1 := by
    show b K / b K = 1
    exact div_self hbK_pos.ne'
  have hβ1 : ∀ k ≤ K, β k ≤ 1 := by
    intro k hk
    rw [hβ, div_le_one hbK_pos]
    exact hb_mono hk
  have hβstrict : ∀ k ∈ Finset.Icc (1 : ℕ) K, β (k - 1) < β k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [hβ]
    exact div_lt_div_of_pos_right (hb_strict k hk.1 hk.2) hbK_pos
  -- Step 3: the density and the interpolant
  set Wk : ℕ → X → ℂ := fun k x => (g k x - g (k - 1) x) / ((β k - β (k - 1) : ℝ) : ℂ) with hWk
  have hdens : ∀ k ∈ Finset.Icc (1 : ℕ) K, ∀ x,
      Wk k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x := by
    intro k hk x
    rw [hWk]
    have hne : ((β k - β (k - 1) : ℝ) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]
      linarith [hβstrict k hk]
    exact div_mul_cancel₀ _ hne
  have hWk_meas : ∀ k, Measurable (Wk k) := by
    intro k
    rw [hWk]
    exact ((hg k).sub (hg (k - 1))).div_const _
  have hWk_aesm : ∀ k, AEStronglyMeasurable (Wk k) μ := fun k => (hWk_meas k).aestronglyMeasurable
  have hho : ∀ p q, p ≤ q → q ≤ K →
      eLpNorm (fun x => g q x - g p x) (ENNReal.ofReal (r : ℝ)) μ
        ≤ ENNReal.ofReal ((b K * (β q - β p)) ^ (1 / R)) := by
    intro p q hpq hqK
    have h1 := ha_ho p q hpq hqK
    rw [show (r : ENNReal) = ENNReal.ofReal (r : ℝ) from ENNReal.ofReal_coe_nnreal.symm] at h1
    set ε := eLpNorm (fun x => g q x - g p x) (ENNReal.ofReal (r : ℝ)) μ with hε
    have haq : a q ≠ ⊤ := ha_ne_top q hqK
    have hap : a p ≠ ⊤ := ha_ne_top p (le_trans hpq hqK)
    have hεR_top : ε ^ R ≠ ⊤ := by
      refine ne_top_of_le_ne_top haq (le_trans ?_ h1)
      exact le_add_left le_rfl
    have hεtop : ε ≠ ⊤ := by
      intro h
      exact hεR_top (by rw [h, ENNReal.top_rpow_of_pos hR0])
    have h2 : A p + (ε.toReal) ^ R ≤ A q := by
      have h3 := ENNReal.toReal_mono haq h1
      rw [ENNReal.toReal_add hap hεR_top, ← ENNReal.toReal_rpow] at h3
      have hpK : p ≤ K := le_trans hpq hqK
      calc A p + (ε.toReal) ^ R = (a p).toReal + (ε.toReal) ^ R := by
            simp only [hA, min_eq_left hpK]
        _ ≤ (a q).toReal := h3
        _ = A q := by simp only [hA, min_eq_left hqK]
    have h4 : ε.toReal ≤ (b K * (β q - β p)) ^ (1 / R) := by
      have h5 : (ε.toReal) ^ R ≤ b K * (β q - β p) := by
        have h6 : b q - b p = b K * (β q - β p) := by
          simp only [hβ]
          rw [mul_sub, mul_div_cancel₀ _ hbK_pos.ne', mul_div_cancel₀ _ hbK_pos.ne']
        have h7 : A q - A p ≤ b q - b p := by
          simp only [hb]
          have h8 : (0 : ℝ) ≤ ((q : ℝ) + 1) * η - ((p : ℝ) + 1) * η := by
            have h9 : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
            nlinarith [hη]
          linarith
        linarith
      have h8 : ((ε.toReal) ^ R) ^ (1 / R) ≤ (b K * (β q - β p)) ^ (1 / R) :=
        Real.rpow_le_rpow (x := (ε.toReal) ^ R) (y := b K * (β q - β p)) (z := 1 / R)
          (Real.rpow_nonneg (x := ε.toReal) ENNReal.toReal_nonneg R) h5
          (div_nonneg zero_le_one hR0.le)
      rwa [← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div_cancel hR0.ne',
        Real.rpow_one] at h8
    calc ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hεtop).symm
      _ ≤ ENNReal.ofReal ((b K * (β q - β p)) ^ (1 / R)) := ENNReal.ofReal_le_ofReal h4
  have hcell : ∀ {t0 t1 : ℝ}, 0 ≤ t0 → t0 ≤ t1 → t1 ≤ 1 →
      eLpNorm (fun x => fkrH K β Wk x t1 - fkrH K β Wk x t0) (ENNReal.ofReal (r : ℝ)) μ
        ≤ ENNReal.ofReal (10 * (b K) ^ (1 / R) * (t1 - t0) ^ (1 / R)) := by
    intro t0 t1 h0 h1 h2
    exact fkr_cell_bound μ (show (1 : ℝ) ≤ (r : ℝ) from by exact_mod_cast hr) hR (β := β) (bK := b K) hbK_pos Wk g hβ0 hβmono hβK
      hβstrict hdens hho hWk_aesm (fun k => (hg k).aestronglyMeasurable) h0 h1 h2

  -- Step 4: the dyadic decomposition
  classical
  set TT : ℕ → X → ℕ → ENNReal := fun l x j =>
      ‖fkrH K β Wk x ((j : ℝ) / 2 ^ l) - fkrH K β Wk x (((j : ℝ) - 1) / 2 ^ l)‖ₑ with hTT
  set G : ℕ → X → ENNReal := fun l x =>
      (∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ l), TT l x j ^ (r : ℝ)) ^ (1 / (r : ℝ)) with hG
  set Hh : ℕ → X → ENNReal := fun l x =>
      (∑ j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
        ‖(2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
          - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) with hHh
  have hsubTT : ∀ l x, (∑ j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
        ‖(fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
          - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ ^ (r : ℝ))
      = (∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ l), TT l x j ^ (r : ℝ)) := by
    intro l x
    rw [← Finset.sum_attach (Finset.Icc (1 : ℕ) (2 ^ l)) (fun j => TT l x j ^ (r : ℝ))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hTT]

  have hH2G : ∀ l x, Hh l x = 2 * G l x := by
    intro l x
    simp only [hHh, hG]
    rw [fkr_two_mul_rpow (ι := {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)})
      (v := fun j (y : X) => fkrH K β Wk y (((j : ℕ) : ℝ) / 2 ^ l)
        - fkrH K β Wk y ((((j : ℕ) : ℝ) - 1) / 2 ^ l)) hr0]
    exact congrArg (fun z => 2 * z ^ (1 / (r : ℝ))) (hsubTT l x)
  have hfHmeas : ∀ t : ℝ, Measurable (fun x : X => fkrH K β Wk x t) := by
    intro t
    unfold fkrH
    exact Finset.measurable_sum _ fun k _ => (hWk_meas k).mul_const _
  have hTTmeas : ∀ l j, Measurable (fun x : X => TT l x j) := by
    intro l j
    rw [hTT]
    exact ((hfHmeas _).sub (hfHmeas _)).enorm
  have hmeasH : ∀ l, AEMeasurable (Hh l) μ := by
    intro l
    refine Measurable.aemeasurable ?_
    rw [hHh]
    refine ENNReal.continuous_rpow_const.measurable.comp ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    refine ENNReal.continuous_rpow_const.measurable.comp ?_
    exact (((hfHmeas _).sub (hfHmeas _)).const_smul (2 : ℂ)).enorm
  -- the pointwise estimate
  have hpoint : ∀ x, varKc (r : ℝ) K (fun k => g k x) ≤ ∑' l, Hh l x := by
    intro x
    have hsum2 : (∑' l, Hh l x) = 2 * ∑' l, G l x := by
      rw [show (∑' l, Hh l x) = ∑' l, (2 * G l x) from tsum_congr fun l => hH2G l x]
      exact ENNReal.tsum_mul_left
    rw [hsum2]
    refine iSup_le fun p => ?_
    have hcost : (∑ i : Fin p.1.1,
          ‖(fun k => g k x) ((p.2.1 i.succ : Fin (K + 1)) : ℕ)
            - (fun k => g k x) ((p.2.1 i.castSucc : Fin (K + 1)) : ℕ)‖ₑ ^ (r : ℝ))
        = (∑ i : Fin p.1.1,
          ‖fkrH K β Wk x (β ((p.2.1 i.succ : Fin (K + 1)) : ℕ))
            - fkrH K β Wk x (β ((p.2.1 i.castSucc : Fin (K + 1)) : ℕ))‖ₑ ^ (r : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← fkrH_chain K β Wk g x hβ0 hβmono hβ1 (fun k hk => hdens k hk x)
        (p.2.2 (Fin.castSucc_le_succ i)) (Nat.lt_succ_iff.mp (p.2.1 i.succ).2)]
    rw [hcost]
    exact Work.Analysis.Variation.dyadicVariationLeGrid (r : ℝ)
      (show (1 : ℝ) ≤ (r : ℝ) from by exact_mod_cast hr) (fun t => fkrH K β Wk x t)
      (continuous_fkrH K β Wk x) (fun i => β ((p.2.1 i : Fin (K + 1)) : ℕ))
      (fun i j hij => hβmono (p.2.2 hij))
      (fun i => le_trans hβ0 (hβmono (Nat.zero_le _)))
      (fun i => hβ1 _ (Nat.lt_succ_iff.mp (p.2.1 i).2))
  -- the cell bound
  have hcell2 : ∀ (l j : ℕ), j ∈ Finset.Icc (1 : ℕ) (2 ^ l) →
      eLpNorm (fun x : X => fkrH K β Wk x ((j : ℝ) / 2 ^ l)
          - fkrH K β Wk x (((j : ℝ) - 1) / 2 ^ l)) (ENNReal.ofReal (r : ℝ)) μ
        ≤ ENNReal.ofReal (10 * (b K) ^ (1 / R)
            * ((j : ℝ) / 2 ^ l - ((j : ℝ) - 1) / 2 ^ l) ^ (1 / R)) := by
    intro l j hj
    have hj1 : (1 : ℕ) ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ 2 ^ l := (Finset.mem_Icc.mp hj).2
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have h1 : 0 ≤ ((j : ℝ) - 1) / 2 ^ l := div_nonneg (by linarith) (by positivity)
    have h2 : ((j : ℝ) - 1) / 2 ^ l ≤ (j : ℝ) / 2 ^ l := by
      have h3 : (0 : ℝ) < 2 ^ l := by positivity
      gcongr; linarith
    have h4 : (j : ℝ) / 2 ^ l ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hj2
    exact hcell h1 h2 h4
  -- the level bound
  have hsum_card : ∀ l : ℕ, (∑ _j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
        (ENNReal.ofReal (20 * (b K) ^ (1 / R) * ((1 : ℝ) / 2 ^ l) ^ (1 / R))) ^ (r : ℝ))
      = (2 ^ l) • (ENNReal.ofReal (20 * (b K) ^ (1 / R)
        * ((1 : ℝ) / 2 ^ l) ^ (1 / R))) ^ (r : ℝ) := by
    intro l
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel]
  have hlevel : ∀ l, eLpNorm (Hh l) (r : ENNReal) μ
      ≤ ENNReal.ofReal (20 * (b K) ^ (1 / R))
        * (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l := by
    intro l
    rw [show (r : ENNReal) = ENNReal.ofReal (r : ℝ) from ENNReal.ofReal_coe_nnreal.symm]
    show eLpNorm (fun x : X => (∑ j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
        ‖(2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
          - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)))
        (ENNReal.ofReal (r : ℝ)) μ
      ≤ ENNReal.ofReal (20 * (b K) ^ (1 / R))
        * (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l
    rw [Work.Analysis.Probability.eLpNorm_sum_rpow_eq (s := (r : ℝ)) hr0
      (ι := {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)})
      (W := fun j (x : X) => ‖(2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
        - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ)
      (fun j => ((((hfHmeas _).sub (hfHmeas _)).const_smul (2 : ℂ))).aemeasurable.enorm)]
    set cmax : ENNReal := ENNReal.ofReal (20 * (b K) ^ (1 / R) * ((1 : ℝ) / 2 ^ l) ^ (1 / R))
      with hcmax
    have hbd : ∀ j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
        (eLpNorm (fun x : X => ‖(2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
            - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ)
          (ENNReal.ofReal (r : ℝ)) μ) ^ (r : ℝ) ≤ cmax ^ (r : ℝ) := by
      intro j
      refine ENNReal.rpow_le_rpow ?_ hr0.le
      rw [eLpNorm_enorm (hf := by pw_aesm),
        show (fun x : X => (2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
            - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l)))
          = (2 : ℂ) • (fun x : X => fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
            - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l)) from rfl,
        eLpNorm_const_smul (2 : ℂ) (fun x : X => fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
          - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l)) (ENNReal.ofReal (r : ℝ)) μ]
      have h2c : ‖(2 : ℂ)‖ₑ = (2 : ENNReal) := by rw [← ofReal_norm]; norm_num
      rw [h2c]
      calc (2 : ENNReal) * eLpNorm (fun x : X => fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
              - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l)) (ENNReal.ofReal (r : ℝ)) μ
          ≤ 2 * ENNReal.ofReal (10 * (b K) ^ (1 / R)
              * (((j : ℕ) : ℝ) / 2 ^ l - (((j : ℕ) : ℝ) - 1) / 2 ^ l) ^ (1 / R)) :=
            mul_le_mul' le_rfl (hcell2 l (j : ℕ) j.2)
        _ = cmax := by
            rw [hcmax,
              show (((j : ℕ) : ℝ) / 2 ^ l - (((j : ℕ) : ℝ) - 1) / 2 ^ l) = (1 : ℝ) / 2 ^ l from by
                field_simp; ring]
            rw [show (20 : ℝ) * (b K) ^ (1 / R) * ((1 : ℝ) / 2 ^ l) ^ (1 / R)
                = 2 * (10 * (b K) ^ (1 / R) * ((1 : ℝ) / 2 ^ l) ^ (1 / R)) from by ring]
            rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from ENNReal.ofReal_natCast 2 ▸ rfl,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc (∑ j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)},
            (eLpNorm (fun x : X => ‖(2 : ℂ) • (fkrH K β Wk x (((j : ℕ) : ℝ) / 2 ^ l)
              - fkrH K β Wk x ((((j : ℕ) : ℝ) - 1) / 2 ^ l))‖ₑ)
            (ENNReal.ofReal (r : ℝ)) μ) ^ (r : ℝ)) ^ (1 / (r : ℝ))
        ≤ (∑ _j : {j : ℕ // j ∈ Finset.Icc (1 : ℕ) (2 ^ l)}, cmax ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
          ENNReal.rpow_le_rpow (Finset.sum_le_sum fun j _ => hbd j) (by positivity)
      _ = ((2 ^ l) • cmax ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by rw [hsum_card l]
      _ = ENNReal.ofReal (20 * (b K) ^ (1 / R))
            * (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l := by
          rw [ENNReal_nsmul_rpow (c := cmax) hr0, hcmax]
          exact fkr_level_arith hr0 hR0 hrR l (B := 20 * (b K) ^ (1 / R)) (by positivity)
  have hc2 : (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num)]
    exact Or.inl ⟨by norm_num, hq0⟩
  have htsum_rho : (∑' l : ℕ, (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l)
      = ENNReal.ofReal ((1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹) := by
    have hlt : (0 : ℝ) < 1 - 2 ^ (1 / (r : ℝ) - 1 / R) := by linarith
    rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / (r : ℝ) - 1 / R)),
      ← ENNReal.ofReal_inv_of_pos hlt]
  have hbKR : (b K) ^ (1 / R) ≤ 2 ^ (1 / R) * w := by
    have h1 : b K ≤ 2 * w ^ R := hbK_le
    have h2 : (b K) ^ (1 / R) ≤ (2 * w ^ R) ^ (1 / R) :=
      Real.rpow_le_rpow (le_of_lt hbK_pos) h1 (one_div_nonneg.mpr hR0.le)
    have h3 : (2 * w ^ R) ^ (1 / R) = 2 ^ (1 / R) * w := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg (le_of_lt hw) R),
        ← Real.rpow_mul (le_of_lt hw), mul_one_div_cancel hR0.ne', Real.rpow_one]
    linarith [h2, h3]
  have hfinal : ∑' l, eLpNorm (Hh l) (r : ENNReal) μ
      ≤ ENNReal.ofReal (20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)))
        * ENNReal.ofReal w := by
    calc ∑' l, eLpNorm (Hh l) (r : ENNReal) μ
        ≤ ∑' l, ENNReal.ofReal (20 * (b K) ^ (1 / R))
            * (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l :=
          ENNReal.tsum_le_tsum fun l => hlevel l
      _ = ENNReal.ofReal (20 * (b K) ^ (1 / R))
            * ∑' l, (ENNReal.ofReal (2 ^ (1 / (r : ℝ) - 1 / R))) ^ l :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (20 * (b K) ^ (1 / R))
            * ENNReal.ofReal ((1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹) := by rw [htsum_rho]
      _ ≤ ENNReal.ofReal (20 * (2 ^ (1 / R) * w))
            * ENNReal.ofReal ((1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹) := by
          refine mul_le_mul' ?_ le_rfl
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbKR (by norm_num))
      _ = ENNReal.ofReal (20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)))
            * ENNReal.ofReal w := by
          have hA : ENNReal.ofReal (20 * (2 ^ (1 / R) * w))
                * ENNReal.ofReal ((1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹)
              = ENNReal.ofReal (20 * (2 ^ (1 / R) * w)
                * (1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹) :=
            (ENNReal.ofReal_mul (p := 20 * (2 ^ (1 / R) * w))
              (by positivity : (0 : ℝ) ≤ 20 * (2 ^ (1 / R) * w))).symm
          rw [hA]
          have hB : ENNReal.ofReal (20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)))
                * ENNReal.ofReal w
              = ENNReal.ofReal (20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)) * w) :=
            (ENNReal.ofReal_mul (p := 20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)))
              (by positivity : (0 : ℝ) ≤ 20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)))).symm
          rw [hB]
          congr 1
          rw [show (20 : ℝ) * (2 ^ (1 / R) * w) * (1 - 2 ^ (1 / (r : ℝ) - 1 / R))⁻¹
              = 20 * 2 ^ (1 / R) / (1 - 2 ^ (1 / (r : ℝ) - 1 / R)) * w from by
            rw [div_eq_mul_inv]; ring]
  exact le_trans (eLpNorm_mono_ennreal ENNReal.coe_ne_top hpoint μ
      (measurable_varKc hg (r : ℝ) K).aestronglyMeasurable)
    (le_trans (Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm hrE hmeasH) hfinal)

end Work.KMTPlan.A6
