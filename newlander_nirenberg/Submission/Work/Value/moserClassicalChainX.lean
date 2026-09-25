import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert

import Submission.Work.Value.moserClassicalBoostX
import Submission.Work.NN.Core.Fleet.chainMeanValueFamily

/-!
# The classical chain mean-value family

This is the twin of `Work.NN.Core.Fleet.chainMeanValueFamily` with the *classical* level-`k`
weighted Caccioppoli hypothesis (fixed constant `C₀`) in place of the `u^k`-energy form; the
proved `Work.Value.classicalMoserBoostX` replaces `nnMoserBoost`, and the extra factor
`(1 + k³ C₀)` in the boost constant is absorbed into the geometric bookkeeping.
-/

namespace Work.Value

open MeasureTheory Set Filter
open Work.NN.Core.Fleet
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

set_option maxHeartbeats 2000000

/-- The Moser level sequence is bounded by `(2n-1)·θ^m`. -/
lemma lvl_le_powX {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (Work.NN.Core.Fleet.lvl n m : ℝ)
      ≤ ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Work.NN.Core.Fleet.lvl_succ]
    have hθnn : (0:ℝ) ≤ Work.NN.Core.Lev.moserTheta n :=
      le_of_lt (lt_trans zero_lt_one (Work.NN.Core.Lev.one_lt_moserTheta hn))
    have h1 : ((⌊(Work.NN.Core.Fleet.lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊ : ℕ) : ℝ)
        ≤ (Work.NN.Core.Fleet.lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n :=
      Nat.floor_le (by positivity)
    calc ((⌊(Work.NN.Core.Fleet.lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊ : ℕ) : ℝ)
        ≤ (Work.NN.Core.Fleet.lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n := h1
      _ ≤ (((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n)^m) *
            Work.NN.Core.Lev.moserTheta n := mul_le_mul_of_nonneg_right ih hθnn
      _ = ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n)^(m+1) := by
          rw [pow_succ]; ring

/-- **The classical chain mean-value family** (same statement as the delegated
`Work.Value.classicalChainMeanValueFamily`, kept here under a distinct name to avoid a clash). -/
theorem classicalChainFamilyX {n : ℕ} (hn : 0 < n) {σ ρstar : Fin n → ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hσρ : ∀ j, σ j < ρstar j) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A B : ℝ, 0 < A ∧ 1 ≤ B ∧
      ∀ (u : Work.NN.Core.Cn n → ℂ),
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρstar) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρstar → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρstar, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
              (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρstar, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k)) →
        ∀ j : ℕ, ∀ z ∈ Work.CR.Flat.polydisc 0 (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^j)),
          ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal (A * B^j) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n:ℝ) - 1)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0
                (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^(j+1))))) := by
  have hσρle : ∀ i, σ i ≤ ρstar i := fun i => (hσρ i).le
  have hθ1 : 1 < Work.NN.Core.Lev.moserTheta n := Work.NN.Core.Lev.one_lt_moserTheta hn
  have hθ0 : 0 < Work.NN.Core.Lev.moserTheta n := lt_trans zero_lt_one hθ1
  have hk1 : 1 ≤ 2 * n - 1 := by omega
  have hKθ : ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n - 1) = 1 :=
    kbase_mul_moserTheta_sub_one hn
  obtain ⟨c, ρ, hcpos, hρ1, hgrowth, hkpos⟩ :=
    cmvfLevelGrowth (θ := Work.NN.Core.Lev.moserTheta n) (K := 2 * n - 1) hθ1 hk1 hKθ
      (k := lvl n) rfl (fun m => rfl)
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ1
  obtain ⟨Kc, Lc, hKcpos, hLc1, Hcut⟩ := exists_cutoff_Rrad hn hσ0 hσρ
  obtain ⟨Cb, hCbpos, Hboost⟩ := Work.Value.classicalMoserBoostX hn hC₀
  have hC0 : 0 ≤ Cb := hCbpos.le
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hLc0 : 0 ≤ Lc := le_trans zero_le_one hLc1
  have hrm1 : 0 < ρ - 1 := by linarith
  have h1mrho : 0 < 1 - 1 / ρ := by
    rw [sub_pos, div_lt_one hρ0]; exact hρ1
  set sB : ℝ := 1 / (c * (1 - 1 / ρ)) with hsBdef
  set sL : ℝ := ρ / (c * (ρ - 1) ^ 2) with hsLdef
  have hsB0 : 0 ≤ sB := by
    rw [hsBdef]; exact (one_div_pos.mpr (mul_pos hcpos h1mrho)).le
  have hsL0 : 0 ≤ sL := by
    rw [hsLdef]; exact (div_pos hρ0 (mul_pos hcpos (pow_pos hrm1 2))).le
  set V : ℝ := VolB ρstar with hVdef
  have hV1 : 1 ≤ V := le_max_left _ _
  have hV0 : 0 ≤ V := le_trans zero_le_one hV1
  set B₁ : ℝ := Cb * (1 + Kc) * (1 + ((2 * n - 1 : ℕ) : ℝ)^3 * C₀) + 1 with hB₁def
  have hB₁1 : 1 ≤ B₁ := by
    rw [hB₁def]
    have : (0:ℝ) ≤ Cb * (1 + Kc) * (1 + ((2 * n - 1 : ℕ) : ℝ)^3 * C₀) := by positivity
    linarith
  set Ł : ℝ := max 1 (Work.NN.Core.Lev.moserTheta n ^ 3 * Lc) with hŁdef
  have hŁ1 : 1 ≤ Ł := le_max_left _ _
  have hB₁0 : 0 < B₁ := lt_of_lt_of_le zero_lt_one hB₁1
  set σδ : ℝ := 1 / (2 * c * (ρ - 1)) with hσδdef
  refine ⟨B₁ ^ sB * (max 1 Ł) ^ sL * V ^ σδ, Lc ^ sB, ?_, ?_, ?_⟩
  · have h1 : 0 < B₁ ^ sB := Real.rpow_pos_of_pos hB₁0 _
    have h2 : 0 < (max 1 Ł) ^ sL := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < V ^ σδ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hV1) _
    positivity
  · exact Real.one_le_rpow hLc1 hsB0
  intro u hu hH j z hz
  have hlvl_nn : ∀ m, (0:ℝ) ≤ (lvl n m : ℝ) := fun m => Nat.cast_nonneg _
  have hlvl_pos : ∀ m, (0:ℝ) < (lvl n m : ℝ) := fun m => by exact_mod_cast hkpos m
  have hθc : ∀ m, 0 ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n :=
    fun m => mul_nonneg (hlvl_nn m) hθ0.le
  -- the base norm
  set N : ENNReal := MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n : ℝ) - 1)))
      (MeasureTheory.volume.restrict
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)))) with hNdef
  have hNcast : (2 * (2 * (n : ℝ) - 1)) = 2 * (((2 * n - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  set bfun : ℕ → ℝ := fun m => Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀) + 1 with hbfundef
  have hbfun_nonneg : ∀ m, 0 ≤ bfun m := by
    intro m; rw [hbfundef]
    have : (0:ℝ) ≤ Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀) := by positivity
    linarith
  have hbfun1 : ∀ m, 1 ≤ bfun m := by
    intro m; rw [hbfundef]
    have : (0:ℝ) ≤ Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀) := by positivity
    have := hbfun_nonneg m
    linarith
  set δfun : ℕ → ℝ := fun m => 1 / (2 * (lvl n (m+1) : ℝ))
      - 1 / (2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n)) with hδfundef
  set Pj : ℕ → ENNReal := fun M =>
      (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ)))) *
      (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m))) with hPjdef
  -- ## the chain
  have hchain : ∀ M, MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
        (MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M)))
      ≤ (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m))) * N := by
    intro M
    induction M with
    | zero =>
      rw [hNdef]
      simp only [Finset.range_zero, Finset.prod_empty, one_mul]
      rw [lvl_zero, ← hNcast, Rrad_zero]
    | succ M ih =>
      obtain ⟨χ, hχcd, hχcs, hχsupp, hχrng, hχone, hχgrad⟩ := Hcut j M
      have hχnn : ∀ z, 0 ≤ χ z := fun z => (hχrng z).1
      have hχle1 : ∀ z, χ z ≤ 1 := fun z => (hχrng z).2
      have hρpos : ∀ i, 0 < ρstar i := fun i => (hσ0 i).trans (hσρ i)
      have hrs : ∀ i, Rrad σ ρstar j (M+1) i < Rrad σ ρstar j M i := by
        intro i
        have h2 := Rrad_gap σ ρstar j M i
        have h3 : 0 < (ρstar i - σ i) * (1 / 2 : ℝ) ^ (j + M + 2) :=
          mul_pos (sub_pos.mpr (hσρ i)) (by positivity)
        linarith
      have hsρ : ∀ i, Rrad σ ρstar j M i < ρstar i := fun i => Rrad_lt_ρstar hσρ j M i
      have hsρ' : ∀ i, Rrad σ ρstar j (M+1) i < ρstar i := fun i => Rrad_lt_ρstar hσρ j (M+1) i
      have hL0 : 0 ≤ Kc * Lc ^ (j + M) := by positivity
      have hboost := Hboost (ρ := ρstar) hρpos hu hH (r := Rrad σ ρstar j (M+1))
        (s := Rrad σ ρstar j M) hrs hsρ hχcd hχcs hχsupp hχnn hχle1 hχone
        (L := Kc * Lc ^ (j + M)) hL0 hχgrad (lvl n M) (hkpos M)
      have hboost' : MeasureTheory.eLpNorm u
            (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)))
            (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1))))
          ≤ ENNReal.ofReal (bfun M) ^ (1 / (2 * (lvl n M : ℝ))) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
              (MeasureTheory.volume.restrict
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M))) := by
        refine hboost.trans (mul_le_mul' ?_ le_rfl)
        have hb : Cb * (1 + Kc * Lc ^ (j + M)) * (1 + ((lvl n M : ℝ))^3 * C₀) ≤ bfun M := by
          rw [hbfundef]; linarith
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hb) (by positivity)
      have hvolfac : MeasureTheory.volume
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))
          ≤ ENNReal.ofReal V := by
        rw [hVdef]; exact volume_polydisc_le_VolB (fun i => (hsρ' i).le)
      have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))) :=
        ((hu.mono (Work.CR.Flat.polydisc_mono (fun i => (hsρ' i).le))).continuousOn).aestronglyMeasurable
          (Work.CR.Flat.isOpen_polydisc _ _).measurableSet
      have hpq : ENNReal.ofReal (2 * (lvl n (M+1) : ℝ))
          ≤ ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (lvl n (M+1) : ℝ) ≤ (lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n := by
          rw [lvl_succ]; exact Nat.floor_le (hθc M)
        linarith
      have hdesc := eLpNorm_le_volume_rpow (S := Rrad σ ρstar j (M+1)) (u := u) (V := V)
        hV0 hvolfac hpq (ne_of_gt (ENNReal.ofReal_pos.mpr (by
          have h := hlvl_pos (M+1); positivity)))
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hmeas
      have hp' : (ENNReal.ofReal (2 * (lvl n (M+1) : ℝ))).toReal = 2 * (lvl n (M+1) : ℝ) :=
        ENNReal.toReal_ofReal (by positivity)
      have hq' : (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n))).toReal
          = 2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n) :=
        ENNReal.toReal_ofReal (by positivity)
      rw [hp', hq'] at hdesc
      have hdesc' : MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n (M+1) : ℝ)))
            (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1))))
          ≤ ENNReal.ofReal (V ^ δfun M) *
            MeasureTheory.eLpNorm u
              (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)))
              (MeasureTheory.volume.restrict
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))) := by
        rw [hδfundef]; exact hdesc
      have hgoal : (∏ m ∈ Finset.range (M+1), ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
            * (∏ m ∈ Finset.range (M+1), ENNReal.ofReal (V ^ (δfun m))) * N
          = ENNReal.ofReal (V ^ δfun M) *
              (ENNReal.ofReal (bfun M) ^ (1 / (2 * (lvl n M : ℝ)))
                * (((∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
                    * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))) * N)) := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        ac_rfl
      rw [hgoal]
      exact hdesc'.trans (mul_le_mul' le_rfl (hboost'.trans (mul_le_mul' le_rfl ih)))
  -- ## the uniform bound on the product
  have hprodBound : ∀ M, (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ))))
      ≤ B₁ ^ sB * (Lc ^ sB) ^ j * (max 1 Ł) ^ sL := by
    intro M
    have hbnd : ∀ m, bfun m ≤ (B₁ * Lc^j) * Ł^m := by
      intro m
      have hLcj1 : (1:ℝ) ≤ Lc^j := one_le_pow₀ hLc1
      have hLcm1 : (1:ℝ) ≤ Lc^m := one_le_pow₀ hLc1
      have hθ1' : (1:ℝ) ≤ Work.NN.Core.Lev.moserTheta n := le_of_lt hθ1
      have hθ3m1 : (1:ℝ) ≤ ((Work.NN.Core.Lev.moserTheta n)^3)^m :=
        one_le_pow₀ (one_le_pow₀ hθ1')
      have hlvl : (lvl n m : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n)^m :=
        lvl_le_powX hn m
      have hlvl3 : ((lvl n m : ℝ))^3
          ≤ (((2 * n - 1 : ℕ) : ℝ))^3 * ((Work.NN.Core.Lev.moserTheta n)^3)^m := by
        calc ((lvl n m : ℝ))^3
            ≤ ((((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n)^m))^3 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hlvl 3
          _ = (((2 * n - 1 : ℕ) : ℝ))^3 * (((Work.NN.Core.Lev.moserTheta n)^m))^3 := by ring
          _ = (((2 * n - 1 : ℕ) : ℝ))^3 * ((Work.NN.Core.Lev.moserTheta n)^3)^m := by
              rw [← pow_mul, ← pow_mul]; congr 1; ring
      have hstep1 : 1 + Kc * Lc ^ (j + m) ≤ (1 + Kc) * (Lc^j * Lc^m) := by
        rw [pow_add]
        have hX1 : (1:ℝ) ≤ Lc^j * Lc^m := by nlinarith
        nlinarith [hX1, hKc0, mul_nonneg hKc0 (by positivity : (0:ℝ) ≤ Lc^j * Lc^m)]
      have hstep2 : 1 + ((lvl n m : ℝ))^3 * C₀
          ≤ (1 + (((2 * n - 1 : ℕ) : ℝ))^3 * C₀) * ((Work.NN.Core.Lev.moserTheta n)^3)^m := by
        have hC0nn : 0 ≤ C₀ := hC₀.le
        have hx : 0 ≤ (((2 * n - 1 : ℕ) : ℝ))^3 * C₀ := by positivity
        nlinarith [hlvl3, hθ3m1, mul_le_mul_of_nonneg_right hlvl3 hC0nn]
      have hkey1 : Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀)
          ≤ Cb * (1 + Kc) * (1 + (((2 * n - 1 : ℕ) : ℝ))^3 * C₀) *
              ((Lc^j * Lc^m) * ((Work.NN.Core.Lev.moserTheta n)^3)^m) := by
        have h1 := mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
        have hCbnn : 0 ≤ Cb := hC0
        calc Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀)
            = Cb * ((1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀)) := by ring
          _ ≤ Cb * (((1 + Kc) * (Lc^j * Lc^m)) *
                ((1 + (((2 * n - 1 : ℕ) : ℝ))^3 * C₀) *
                  ((Work.NN.Core.Lev.moserTheta n)^3)^m)) := mul_le_mul_of_nonneg_left h1 hCbnn
          _ = Cb * (1 + Kc) * (1 + (((2 * n - 1 : ℕ) : ℝ))^3 * C₀) *
                ((Lc^j * Lc^m) * ((Work.NN.Core.Lev.moserTheta n)^3)^m) := by ring
      have hkey2 : (Lc^j * Lc^m) * ((Work.NN.Core.Lev.moserTheta n)^3)^m ≤ Lc^j * Ł^m := by
        have h1 : Lc^m * ((Work.NN.Core.Lev.moserTheta n)^3)^m
            = (Lc * (Work.NN.Core.Lev.moserTheta n)^3)^m := by rw [mul_pow]
        have h2 : (Lc * (Work.NN.Core.Lev.moserTheta n)^3)^m ≤ Ł^m := by
          refine pow_le_pow_left₀ (by positivity) ?_ m
          rw [hŁdef, mul_comm]
          exact le_max_right _ _
        calc (Lc^j * Lc^m) * ((Work.NN.Core.Lev.moserTheta n)^3)^m
            = Lc^j * (Lc^m * ((Work.NN.Core.Lev.moserTheta n)^3)^m) := by ring
          _ = Lc^j * (Lc * (Work.NN.Core.Lev.moserTheta n)^3)^m := by rw [h1]
          _ ≤ Lc^j * Ł^m := mul_le_mul_of_nonneg_left h2 (by positivity)
      have hY1 : (1:ℝ) ≤ Lc^j * Ł^m := by
        have h1 : (1:ℝ) ≤ Ł^m := one_le_pow₀ hŁ1
        nlinarith
      rw [hbfundef, hB₁def]
      have hA : Cb * (1 + Kc * Lc ^ (j + m)) * (1 + ((lvl n m : ℝ))^3 * C₀)
          ≤ Cb * (1 + Kc) * (1 + (((2 * n - 1 : ℕ) : ℝ))^3 * C₀) * (Lc^j * Ł^m) :=
        hkey1.trans (mul_le_mul_of_nonneg_left hkey2 (by positivity))
      nlinarith [hA, hY1]

    have hb := cmvfProdBound (p := ρ) (c := c) (B := B₁ * Lc^j) (L := Ł) hρ1 hcpos
      (by have h1 : (0:ℝ) < B₁ := hB₁0
          have h2 : (0:ℝ) < Ł := lt_of_lt_of_le zero_lt_one hŁ1
          positivity) hŁ1
      (m := fun m => 2 * lvl n m)
      (fun m => by have h := hgrowth m; push_cast; linarith)
      (fun m => by have h := hkpos m; omega)
      (b := bfun) (fun m => hbfun_nonneg m) hbnd M
    have hX1 : (1:ℝ) ≤ B₁ * Lc^j := by
      have h1 : (1:ℝ) ≤ Lc^j := one_le_pow₀ hLc1
      nlinarith [hB₁1, h1]
    have h1 : (max 1 (B₁ * Lc^j)) ^ sB ≤ (B₁ * Lc^j) ^ sB :=
      Real.rpow_le_rpow (by positivity) (max_le hX1 le_rfl) hsB0
    have h2 : (B₁ * Lc^j)^sB = B₁^sB * (Lc^sB)^j := by
      rw [Real.mul_rpow (le_of_lt hB₁0) (by positivity : (0:ℝ) ≤ Lc^j)]
      congr 1
      rw [show Lc ^ j = Lc ^ ((j:ℝ)) from (Real.rpow_natCast Lc j).symm,
        ← Real.rpow_mul hLc0, show ((j:ℝ) * sB) = sB * (j:ℝ) by ring,
        Real.rpow_mul hLc0, Real.rpow_natCast]
    have e1 : (max 1 (B₁ * Lc^j)) ^ (1 / (c * (1 - 1 / ρ)))
        = (max 1 (B₁ * Lc^j)) ^ sB := by rw [hsBdef]
    have e2 : (max 1 Ł) ^ (ρ / (c * (ρ - 1) ^ 2)) = (max 1 Ł) ^ sL := by rw [hsLdef]
    have heq : (∏ j ∈ Finset.range M, bfun j ^ (1 / (2 * (lvl n j : ℝ))))
        = ∏ j ∈ Finset.range M, bfun j ^ (1 / ((2 * lvl n j : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [show ((2 * lvl n j : ℕ) : ℝ) = 2 * (lvl n j : ℝ) by push_cast; ring]
    rw [← heq, e1, e2] at hb
    refine hb.trans ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hPbound : ∀ M, (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))
      ≤ ENNReal.ofReal ((B₁ ^ sB * (max 1 Ł) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j) := by
    intro M
    have h1 : (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        = ENNReal.ofReal (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ)))) := by
      have hstep : (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
          = ∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m ^ (1 / (2 * (lvl n m : ℝ)))) :=
        Finset.prod_congr rfl (fun m _ => ENNReal.ofReal_rpow_of_nonneg
          (hbfun_nonneg m) (by positivity))
      rw [hstep, ← ENNReal.ofReal_prod_of_nonneg (fun m _ => Real.rpow_nonneg (hbfun_nonneg m) _)]
    have hδ0 : ∀ m, 0 ≤ δfun m := by
      intro m
      have h2 : (lvl n (m+1) : ℝ) ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n := by
        rw [lvl_succ]; exact Nat.floor_le (hθc m)
      have ha : (0:ℝ) < 2 * (lvl n (m+1) : ℝ) := by
        have h := hlvl_pos (m+1); linarith
      have hb : 2 * (lvl n (m+1) : ℝ) ≤ 2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n) :=
        by linarith [h2]
      have h6 := one_div_le_one_div_of_le ha hb
      rw [hδfundef]
      simp only [one_div] at h6 ⊢
      linarith
    have h2 : (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))
        = ENNReal.ofReal (V ^ (∑ m ∈ Finset.range M, δfun m)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun m _ => Real.rpow_nonneg hV0 _),
        ← Real.rpow_sum_of_nonneg hV0 (fun m _ => hδ0 m)]
    have hδle : ∀ m, δfun m ≤ (1 / (2 * c * ρ)) * (ρ⁻¹)^m := by
      intro m
      have hsub : (0:ℝ) ≤ 1 / (2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n)) :=
        (one_div_pos.mpr (mul_pos (by norm_num) (mul_pos (hlvl_pos m) hθ0))).le
      have h1 : δfun m ≤ 1 / (2 * (lvl n (m+1) : ℝ)) := by rw [hδfundef]; linarith
      have hg := hgrowth (m+1)
      have h2 : (1:ℝ) / (2 * (lvl n (m+1) : ℝ)) ≤ 1 / (2 * (c * ρ^(m+1))) := by
        exact one_div_le_one_div_of_le (by
            have h1 : (0:ℝ) < c := hcpos
            have h2 : (0:ℝ) < ρ^(m+1) := pow_pos hρ0 _
            positivity) (by linarith [hg])
      have h3 : (1:ℝ) / (2 * (c * ρ^(m+1))) = (1 / (2 * c * ρ)) * (ρ⁻¹)^m := by
        rw [pow_succ, inv_pow]
        have hcρ : c * ρ ≠ 0 := ne_of_gt (mul_pos hcpos hρ0)
        field_simp
        try ring
      linarith
    have hsum : ∑ m ∈ Finset.range M, δfun m ≤ σδ := by
      have hρinv : ‖(ρ⁻¹ : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0), ← one_div, div_lt_one hρ0]
        exact hρ1
      have hsumm : Summable (fun m : ℕ => (1 / (2 * c * ρ)) * (ρ⁻¹)^m) :=
        (summable_geometric_of_norm_lt_one hρinv).mul_left _
      have h4 : ∑ m ∈ Finset.range M, (1 / (2 * c * ρ)) * (ρ⁻¹)^m ≤ σδ := by
        have h5 : ∑ m ∈ Finset.range M, (1 / (2 * c * ρ)) * (ρ⁻¹)^m
            ≤ ∑' m : ℕ, (1 / (2 * c * ρ)) * (ρ⁻¹)^m :=
          Summable.sum_le_tsum _ (fun m _ => by positivity) hsumm
        have h6 : ∑' m : ℕ, (1 / (2 * c * ρ)) * (ρ⁻¹)^m = σδ := by
          rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hρinv, hσδdef]
          have hcρ : c * (ρ - 1) ≠ 0 := ne_of_gt (mul_pos hcpos hrm1)
          have hcρρ : 2 * c * ρ ≠ 0 := by positivity
          field_simp
          try ring
        linarith
      exact (Finset.sum_le_sum (fun m _ => hδle m)).trans h4
    have hVp : V ^ (∑ m ∈ Finset.range M, δfun m) ≤ V ^ σδ :=
      Real.rpow_le_rpow_of_exponent_le hV1 hsum
    have hVnn : (0:ℝ) ≤ V ^ (∑ m ∈ Finset.range M, δfun m) := Real.rpow_nonneg hV0 _
    rw [h1, h2, ← ENNReal.ofReal_mul
      (Finset.prod_nonneg (fun m _ => Real.rpow_nonneg (hbfun_nonneg m) _))]
    apply ENNReal.ofReal_le_ofReal
    calc (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ))))
          * V ^ (∑ m ∈ Finset.range M, δfun m)
        ≤ (B₁ ^ sB * (Lc ^ sB) ^ j * (max 1 Ł) ^ sL) * V ^ σδ :=
          mul_le_mul (hprodBound M) hVp hVnn (by positivity)
      _ = (B₁ ^ sB * (max 1 Ł) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j := by ring
  -- ## the pointwise bound
  have hz' : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)) :=
    Work.CR.Flat.polydisc_mono (fun i => Lam_le_of_le hσρle (Nat.le_succ j) i) hz
  have hρ'pos : ∀ i, 0 < Lam σ ρstar (j+1) i := fun i => Lam_pos hσ0 hσρ (j+1) i
  have hu' : ContinuousOn u (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1))) :=
    (hu.mono (Work.CR.Flat.polydisc_mono (fun i => (Lam_lt_ρstar hσρ (j+1) i).le))).continuousOn
  obtain ⟨r, hrpos, hballj⟩ := Metric.mem_nhds_iff.mp
    ((Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar j)).mem_nhds hz)
  have hball : Metric.ball z r ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)) :=
    hballj.trans (Work.CR.Flat.polydisc_mono (fun i => Lam_le_of_le hσρle (Nat.le_succ j) i))
  have hballR : ∀ M, Metric.ball z r ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M) :=
    fun M => hballj.trans (Work.CR.Flat.polydisc_mono (fun i => Lam_le_Rrad hσρle j M i))
  have hE1 : ∀ M : ℕ, (1:ℝ) ≤ 2 * (lvl n M : ℝ) := by
    intro M
    have h1 : (1:ℝ) ≤ (lvl n M : ℝ) := by exact_mod_cast hkpos M
    linarith
  have hEtop : Filter.Tendsto (fun M : ℕ => 2 * (lvl n M : ℝ)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun M : ℕ => c * ρ ^ M) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hρ1).const_mul_atTop hcpos
    refine Filter.tendsto_atTop_mono (fun M => ?_) h1
    have h2 := hgrowth M
    linarith
  have hlim := Work.NN.Core.Lev.ofReal_norm_le_liminf_eLpNorm_on hn (u := u)
    (ρ := Lam σ ρstar (j+1)) hρ'pos hu' hz' hrpos hball
    (E := fun M : ℕ => 2 * (lvl n M : ℝ)) hE1 hEtop
  refine hlim.trans ?_
  have hbound : ∀ M : ℕ, MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
        (MeasureTheory.volume.restrict (Metric.ball z r))
      ≤ ENNReal.ofReal ((B₁ ^ sB * (max 1 Ł) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j) * N := by
    intro M
    have hνμ : MeasureTheory.volume.restrict (Metric.ball z r)
        ≤ MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M)) :=
      MeasureTheory.Measure.restrict_mono (hballR M) le_rfl
    have h1 := MeasureTheory.eLpNorm_mono_measure u hνμ
      (p := ENNReal.ofReal (2 * (lvl n M : ℝ)))
    exact h1.trans ((hchain M).trans (mul_le_mul' (hPbound M) le_rfl))
  refine le_trans (Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)) ?_
  rw [Filter.liminf_const, hNdef]
  rfl

end

end Work.Value
