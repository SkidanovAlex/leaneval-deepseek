import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Lev.moserTheta
import Submission.Work.NN.Core.Fleet.chainMeanValueFamily
import Submission.Work.NN.Core.Fleet.cmvfProdBound
import Submission.Work.NN.Core.Fleet.cmvfLevelGrowth
import Submission.Work.NN.Core.Lev.ofReal_norm_le_liminf_eLpNorm_on

set_option maxHeartbeats 1200000

namespace Work.NN.Core.Lev2

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology
open Work.NN.Core.Fleet

/-- The integer Moser level `lvl n m` grows at most like `(2n-1) θ^m`. -/
private lemma lvl_le_geom {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (lvl n m : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n) ^ m := by
  have hθ0 : 0 ≤ Work.NN.Core.Lev.moserTheta n := Work.NN.Core.Lev.moserTheta_nonneg hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [lvl_succ]
    have hfl : ((⌊(lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊ : ℕ) : ℝ)
        ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hθ0)
    calc ((⌊(lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊ : ℕ) : ℝ)
        ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n := hfl
      _ ≤ (((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n) ^ m)
            * Work.NN.Core.Lev.moserTheta n := mul_le_mul_of_nonneg_right ih hθ0
      _ = ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n) ^ (m + 1) := by
          rw [pow_succ]; ring

/-- `1 + lvl n m ≤ 2n · θ^m`. -/
private lemma one_add_lvl_le {n : ℕ} (hn : 0 < n) (m : ℕ) :
    1 + (lvl n m : ℝ) ≤ 2 * (n : ℝ) * (Work.NN.Core.Lev.moserTheta n) ^ m := by
  have hθ1 : 1 ≤ Work.NN.Core.Lev.moserTheta n := (Work.NN.Core.Lev.one_lt_moserTheta hn).le
  have hθp1 : (1 : ℝ) ≤ (Work.NN.Core.Lev.moserTheta n) ^ m := one_le_pow₀ hθ1
  have hcast : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  have h := lvl_le_geom hn m
  rw [hcast] at h
  nlinarith [h, hθp1]

/-- **Moser chain family from a boost hypothesis (Lipschitz `u`).**  This is exactly
`Work.NN.Core.Lev.chainMeanValueFamilyLip` (`Submission/Work/NN/Core/Lev/lipChain.lean`) with the
per-level boost taken as a *hypothesis* instead of being produced by `lipMoserBoostC`.  The boost
hypothesis is the conclusion of `Work.NN.Core.Lev2.srcMoserBoost`.  PROOF: copy the proof body of
`chainMeanValueFamilyLip` (or of `Fleet.chainMeanValueFamily`), drop `Hboost := lipMoserBoostC _ _`
and use the given hypothesis, and note that the boost constant now carries an extra factor
`(1+k)`; accordingly replace
`bfun m := C * (1 + Kc * Lc^(j+m)) + 1` by `C * (1 + Kc * Lc^(j+m)) * (1 + (lvl n m : ℝ)) + 1`
and run `cmvfProdBound` at ratio `L' := max 1 ((1 + Lc) * 2 * n * moserTheta n)` (using
`lvl n m ≤ (2*n-1) * θ^m`, `1 + Lc^(j+m) ≤ (1+Lc)^(j+m)`, `L' ≥ 1+Lc ≥ Lc`), so that
`bfun m ≤ ((C*(1+Kc)+1) * L'^j) * L'^m`; the rest of the proof is unchanged. -/
theorem srcChainMeanValueFamily {n : ℕ} (hn : 0 < n) {σ ρstar : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j)
    (hσρ : ∀ j, σ j < ρstar j) {C : ℝ} (hC : 0 < C) :
    ∃ A B : ℝ, 0 < A ∧ 1 ≤ B ∧
      ∀ {K : NNReal} (u : Work.NN.Core.Cn n → ℂ),
        LipschitzOnWith K u (Work.CR.Flat.polydisc 0 ρstar) →
        (∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρstar j) →
          ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
            (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
          ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) →
          ∀ (k : ℕ), 1 ≤ k →
            MeasureTheory.eLpNorm u
                (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
                (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
              ≤ (ENNReal.ofReal (C * (1 + L) * (1 + (k : ℝ)))) ^ (1 / (2 * (k : ℝ))) *
                MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ)))
                  (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))) →
        ∀ (j : ℕ) (z : Work.NN.Core.Cn n),
          z ∈ Work.CR.Flat.polydisc 0 (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^j)) →
          ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal (A * B^j) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n:ℝ) - 1)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0
                (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^(j+1))))) := by
  have hσρle : ∀ i, σ i ≤ ρstar i := fun i => (hσρ i).le
  have hθ1 : 1 < Work.NN.Core.Lev.moserTheta n := Work.NN.Core.Lev.one_lt_moserTheta hn
  have hθ0 : 0 < Work.NN.Core.Lev.moserTheta n := lt_trans zero_lt_one hθ1
  have hθge1 : 1 ≤ Work.NN.Core.Lev.moserTheta n := hθ1.le
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk1 : 1 ≤ 2 * n - 1 := by omega
  have hKθ : ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n - 1) = 1 :=
    kbase_mul_moserTheta_sub_one hn
  obtain ⟨c, ρ, hcpos, hρ1, hgrowth, hkpos⟩ :=
    cmvfLevelGrowth (θ := Work.NN.Core.Lev.moserTheta n) (K := 2 * n - 1) hθ1 hk1 hKθ
      (k := lvl n) rfl (fun m => rfl)
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ1
  obtain ⟨Kc, Lc, hKcpos, hLc1, Hcut⟩ := exists_cutoff_Rrad hn hσ0 hσρ
  have hC0 : 0 ≤ C := hC.le
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
  -- the ratio carrying the geometric growth of the boost constants
  set L0 : ℝ := (1 + Lc) * 2 * (n : ℝ) * Work.NN.Core.Lev.moserTheta n with hL0def
  set L' : ℝ := max 1 L0 with hL'def
  have hL'1 : 1 ≤ L' := by rw [hL'def]; exact le_max_left 1 L0
  have hL'0 : 0 < L' := lt_of_lt_of_le zero_lt_one hL'1
  have hLcL' : Lc ≤ L' := by
    have hL0ge : Lc ≤ L0 := by
      rw [hL0def]
      have h2 : (1 : ℝ) ≤ 2 * (n : ℝ) * Work.NN.Core.Lev.moserTheta n := by
        nlinarith [hnR, hθge1]
      have h3 : Lc * 1 ≤ Lc * (2 * (n : ℝ) * Work.NN.Core.Lev.moserTheta n) :=
        mul_le_mul_of_nonneg_left h2 hLc0
      nlinarith [h3, hLc0, h2]
    rw [hL'def]
    exact le_trans hL0ge (le_max_right 1 L0)
  set β : ℝ := C * (1 + Kc) * (2 * (n : ℝ)) + 1 with hβdef
  have hβ1 : 1 ≤ β := by
    rw [hβdef]
    have h : (0 : ℝ) ≤ C * (1 + Kc) * (2 * (n : ℝ)) := by positivity
    linarith
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  set σδ : ℝ := 1 / (2 * c * (ρ - 1)) with hσδdef
  refine ⟨β ^ sB * (max 1 L') ^ sL * V ^ σδ, L' ^ sB, ?_, ?_, ?_⟩
  · have h1 : 0 < β ^ sB := Real.rpow_pos_of_pos hβ0 _
    have h2 : 0 < (max 1 L') ^ sL := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < V ^ σδ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hV1) _
    positivity
  · exact Real.one_le_rpow hL'1 hsB0
  intro K u hLip Hboost j z hz
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
  set bfun : ℕ → ℝ := fun m => C * (1 + Kc * Lc ^ (j + m)) * (1 + (lvl n m : ℝ)) + 1
    with hbfundef
  have hbfun_nonneg : ∀ m, 0 ≤ bfun m := by
    intro m; rw [hbfundef]
    have : (0:ℝ) ≤ C * (1 + Kc * Lc ^ (j + m)) * (1 + (lvl n m : ℝ)) := by positivity
    linarith
  set δfun : ℕ → ℝ := fun m => 1 / (2 * (lvl n (m+1) : ℝ))
      - 1 / (2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n)) with hδfundef
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
      have hboost := Hboost (r := Rrad σ ρstar j (M+1)) (s := Rrad σ ρstar j M)
        hrs hsρ hχcd hχcs hχsupp hχnn hχle1 hχone
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
        have hb : C * (1 + Kc * Lc ^ (j + M)) * (1 + (lvl n M : ℝ)) ≤ bfun M := by
          rw [hbfundef]; linarith
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hb) (by positivity)
      have hvolfac : MeasureTheory.volume
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))
          ≤ ENNReal.ofReal V := by
        rw [hVdef]; exact volume_polydisc_le_VolB (fun i => (hsρ' i).le)
      have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))) :=
        ((hLip.mono (Work.CR.Flat.polydisc_mono (fun i => (hsρ' i).le))).continuousOn).aestronglyMeasurable
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
      ≤ β ^ sB * (L' ^ sB) ^ j * (max 1 L') ^ sL := by
    intro M
    have hbnd : ∀ m, bfun m ≤ (β * L'^j) * L'^m := by
      intro m
      have h1m : 1 + Kc * Lc ^ (j + m) ≤ (1 + Kc) * Lc ^ (j + m) := by
        have h : (1:ℝ) ≤ Lc ^ (j + m) := one_le_pow₀ hLc1
        have h2 : Kc * 1 ≤ Kc * Lc ^ (j + m) := mul_le_mul_of_nonneg_left h hKc0
        nlinarith [h, h2]
      have h2m : 1 + (lvl n m : ℝ) ≤ 2 * (n:ℝ) * Work.NN.Core.Lev.moserTheta n ^ m :=
        one_add_lvl_le hn m
      have hpowed : Lc ^ (j + m) = Lc ^ j * Lc ^ m := by rw [pow_add]
      have hpowj : Lc ^ j ≤ L' ^ j := pow_le_pow_left₀ hLc0 hLcL' j
      have hpowm : Lc ^ m * Work.NN.Core.Lev.moserTheta n ^ m ≤ L' ^ m := by
        have hmul : Lc ^ m * Work.NN.Core.Lev.moserTheta n ^ m
            = (Lc * Work.NN.Core.Lev.moserTheta n) ^ m := by rw [mul_pow]
        rw [hmul, hL'def]
        have h0 : (0:ℝ) ≤ Lc * Work.NN.Core.Lev.moserTheta n := mul_nonneg hLc0 hθ0.le
        have h1 : Lc * Work.NN.Core.Lev.moserTheta n ≤ L0 := by
          rw [hL0def]; nlinarith [hLc0, hθ0.le, hnR]
        exact le_trans (pow_le_pow_left₀ h0 h1 m)
          (pow_le_pow_left₀ (le_trans h0 h1) (le_max_right 1 L0) m)
      have hcoef : 0 ≤ C * (1 + Kc) * (2 * (n:ℝ)) := by positivity
      have hprod := mul_le_mul h1m h2m (by positivity) (by positivity)
      calc bfun m = C * (1 + Kc * Lc ^ (j + m)) * (1 + (lvl n m : ℝ)) + 1 := by rw [hbfundef]
        _ ≤ C * ((1 + Kc) * Lc ^ (j + m))
              * (2 * (n:ℝ) * Work.NN.Core.Lev.moserTheta n ^ m) + 1 := by
              have h := mul_le_mul_of_nonneg_left hprod hC0
              linarith
        _ = C * (1 + Kc) * (2 * (n:ℝ))
              * (Lc^j * Lc^m * Work.NN.Core.Lev.moserTheta n ^ m) + 1 := by
              rw [hpowed]; ring
        _ ≤ C * (1 + Kc) * (2 * (n:ℝ)) * (L'^j * L'^m) + 1 := by
              have hstep : Lc^j * Lc^m * Work.NN.Core.Lev.moserTheta n ^ m ≤ L'^j * L'^m := by
                rw [mul_assoc]
                exact mul_le_mul hpowj hpowm (by positivity) (by positivity)
              have h := mul_le_mul_of_nonneg_left hstep hcoef
              linarith
        _ ≤ (β * L'^j) * L'^m := by
              rw [hβdef]
              have hX : (1:ℝ) ≤ L'^j * L'^m := by
                have h1 : (1:ℝ) ≤ L'^j := one_le_pow₀ hL'1
                have h2 : (1:ℝ) ≤ L'^m := one_le_pow₀ hL'1
                nlinarith
              have hA : (0:ℝ) ≤ C * (1 + Kc) * (2 * (n:ℝ)) := hcoef
              have h2 := mul_le_mul_of_nonneg_left hX hA
              nlinarith [h2]
    have hb := cmvfProdBound (p := ρ) (c := c) (B := β * L'^j) (L := L') hρ1 hcpos
      (by have h1 : (0:ℝ) < β := hβ0
          have h2 : (0:ℝ) < L' := hL'0
          positivity) hL'1
      (m := fun m => 2 * lvl n m)
      (fun m => by have h := hgrowth m; push_cast; linarith)
      (fun m => by have h := hkpos m; omega)
      (b := bfun) (fun m => hbfun_nonneg m) hbnd M
    have hX1 : (1:ℝ) ≤ β * L'^j := by
      have h1 : (1:ℝ) ≤ L'^j := one_le_pow₀ hL'1
      nlinarith [hβ1, h1]
    have h1 : (max 1 (β * L'^j)) ^ sB ≤ (β * L'^j) ^ sB :=
      Real.rpow_le_rpow (by positivity) (max_le hX1 le_rfl) hsB0
    have h2 : (β * L'^j)^sB = β^sB * (L'^sB)^j := by
      rw [Real.mul_rpow (le_of_lt hβ0) (by positivity : (0:ℝ) ≤ L'^j)]
      congr 1
      rw [show L' ^ j = L' ^ ((j:ℝ)) from (Real.rpow_natCast L' j).symm,
        ← Real.rpow_mul hL'0.le, show ((j:ℝ) * sB) = sB * (j:ℝ) by ring,
        Real.rpow_mul hL'0.le, Real.rpow_natCast]
    have e1 : (max 1 (β * L'^j)) ^ (1 / (c * (1 - 1 / ρ)))
        = (max 1 (β * L'^j)) ^ sB := by rw [hsBdef]
    have e2 : (max 1 L') ^ (ρ / (c * (ρ - 1) ^ 2)) = (max 1 L') ^ sL := by rw [hsLdef]
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
      ≤ ENNReal.ofReal ((β ^ sB * (max 1 L') ^ sL * V ^ σδ) * (L' ^ sB) ^ j) := by
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
        ≤ (β ^ sB * (L' ^ sB) ^ j * (max 1 L') ^ sL) * V ^ σδ :=
          mul_le_mul (hprodBound M) hVp hVnn (by positivity)
      _ = (β ^ sB * (max 1 L') ^ sL * V ^ σδ) * (L' ^ sB) ^ j := by ring
  -- ## the pointwise bound
  have hz' : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)) :=
    Work.CR.Flat.polydisc_mono (fun i => Lam_le_of_le hσρle (Nat.le_succ j) i) hz
  have hρ'pos : ∀ i, 0 < Lam σ ρstar (j+1) i := fun i => Lam_pos hσ0 hσρ (j+1) i
  have hu' : ContinuousOn u (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1))) :=
    (hLip.mono (Work.CR.Flat.polydisc_mono (fun i => (Lam_lt_ρstar hσρ (j+1) i).le))).continuousOn
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
      ≤ ENNReal.ofReal ((β ^ sB * (max 1 L') ^ sL * V ^ σδ) * (L' ^ sB) ^ j) * N := by
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

end Work.NN.Core.Lev2
