import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.CorrectionDefs
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum
import Submission.Work.NumberTheory.Chen.BTermCount.BLodConductorDecomp
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCharReduction
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.BLodMobiusReduction2
import Submission.Work.NumberTheory.Chen.BTermCount.BLodUnweightedDefs
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSmallRSum
import Submission.Work.NumberTheory.Chen.BTermCount.BLodLargeRSumUnweightedDyadic
import Submission.Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound
import Submission.Work.NumberTheory.Chen.BTermCount.primeCharSumBound
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Work.NumberTheory.Chen.BTermCount.bRemUNwCharMobius
import Submission.Work.NumberTheory.Chen.BTermCount.bRemUNwSmallRParam
import Submission.Work.NumberTheory.Chen.BTermCount.bRemUNwArithConsume

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The **unweighted** bilinear level of distribution for the corrected `B`-term remainder

Final assembly of the unweighted level of distribution

  `Σ_{d ≤ ⌊√x/(log x)^B⌋, d odd} |bRemCorr x (chenSiftLimit x) (chenWindowTop x) d| ≤ x/(log x)^A`,

the unweighted analogue of `bRemCorrLevelOfDistribution` (the `3^{ω d}`-weighted version, which
requires the well-factorable Bombieri–Vinogradov mean value and is out of reach in this
workspace; see `notes/SESSION5_WEIGHT_WALL.md`).

The chain is
* character expansion + Möbius reduction (`bRemUNwCharMobius`),
* the `1/φ`-weighted reindexing `reindex_bound` (`BLodMobiusReduction2`),
* the split of the resulting modulus sum `blodAllUnw = blodSmallUnw + blodLargeUnw` at a
  conductor threshold `R₀ = ⌊(log x)^{C'}⌋`,
* small conductors: Siegel–Walfisz (`bRemUNwSmallRParam`, from `BLodSmallRSum`),
* large conductors: the dyadic bilinear large sieve (`BLodLargeRSumUnweightedDyadic`, from
  `bRemUNwLSBlock` and `BLodGeomSum`) followed by its arithmetic evaluation
  (`bRemUNwArithConsume`).
-/

/-! ## Comparisons between the Chen parameters -/

/-- `chenSiftLimit x ≤ chenWindowTop x`: the sift limit `⌊x^{599/8000}⌋+1` is below the
window top `⌊x^{1/3}⌋+2`. -/
theorem bRemUNwSiftLimit_le_windowTop (x : ℕ) :
    Submission.chenSiftLimit x ≤ Submission.chenWindowTop x := by
  rcases eq_or_lt_of_le (Nat.zero_le x) with hx0 | hx0
  · subst hx0
    rw [Submission.chenSiftLimit, Submission.chenWindowTop]
    have h1 : Real.rpow ((0 : ℕ) : ℝ) ((1 : ℝ) / 8) = 0 := by
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
      exact Real.zero_rpow (x := (1 : ℝ) / 8) (by norm_num)
    have h2 : cut 0 1 = 0 := by
      unfold cut
      rw [Real.zero_rpow (x := sieveAlpha ^ 1)
        (show sieveAlpha ^ 1 ≠ 0 by rw [pow_one, sieveAlpha]; norm_num)]
    have h3 : Real.rpow ((0 : ℕ) : ℝ) ((1 : ℝ) / 3) = 0 := by
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
      exact Real.zero_rpow (x := (1 : ℝ) / 3) (by norm_num)
    rw [h1, h2, h3]
    norm_num
  · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hx0' : (0 : ℝ) < (x : ℝ) := by linarith
    have hcut : cut (Real.rpow (x : ℝ) ((1 : ℝ) / 8)) 1 = (x : ℝ) ^ (sieveAlpha / 8) := by
      unfold cut
      rw [pow_one, show Real.rpow (x : ℝ) ((1 : ℝ) / 8) = (x : ℝ) ^ ((1 : ℝ) / 8) from rfl,
        ← Real.rpow_mul (le_of_lt hx0')]
      congr 1
      ring
    have hle : cut (Real.rpow (x : ℝ) ((1 : ℝ) / 8)) 1 ≤ Real.rpow (x : ℝ) ((1 : ℝ) / 3) := by
      rw [hcut]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      rw [sieveAlpha]; norm_num
    have h2 := Nat.floor_mono hle
    rw [Submission.chenSiftLimit, Submission.chenWindowTop]
    exact le_trans (Nat.add_le_add_right h2 1) (Nat.add_le_add_left (by norm_num : 1 ≤ 2) _)

/-- The sift limit stays below `x + 2` (the range of the ternary sequence `B̄`). -/
lemma bRemUNwSiftLimit_le_add_two (x : ℕ) : (Submission.chenSiftLimit x : ℝ) ≤ (x : ℝ) + 2 := by
  rcases eq_or_lt_of_le (Nat.zero_le x) with hx0 | hx0
  · subst hx0
    rw [Submission.chenSiftLimit]
    have h1 : Real.rpow ((0 : ℕ) : ℝ) ((1 : ℝ) / 8) = 0 := by
      rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
      exact Real.zero_rpow (x := (1 : ℝ) / 8) (by norm_num)
    rw [h1]
    have h2 : cut 0 1 = 0 := by
      unfold cut
      rw [Real.zero_rpow (x := sieveAlpha ^ 1)
        (show sieveAlpha ^ 1 ≠ 0 by rw [pow_one, sieveAlpha]; norm_num)]
    rw [h2]
    norm_num
  · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hx0' : (0 : ℝ) < (x : ℝ) := by linarith
    have hcut : cut (Real.rpow (x : ℝ) ((1 : ℝ) / 8)) 1 = (x : ℝ) ^ (sieveAlpha / 8) := by
      unfold cut
      rw [pow_one, show Real.rpow (x : ℝ) ((1 : ℝ) / 8) = (x : ℝ) ^ ((1 : ℝ) / 8) from rfl,
        ← Real.rpow_mul (le_of_lt hx0')]
      congr 1
      ring
    have hle : cut (Real.rpow (x : ℝ) ((1 : ℝ) / 8)) 1 ≤ (x : ℝ) := by
      rw [hcut]
      calc (x : ℝ) ^ (sieveAlpha / 8) ≤ (x : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by rw [sieveAlpha]; norm_num)
        _ = (x : ℝ) := Real.rpow_one _
    have hnn : 0 ≤ cut (Real.rpow (x : ℝ) ((1 : ℝ) / 8)) 1 := by
      rw [hcut]
      exact Real.rpow_nonneg (le_of_lt hx0') _
    rw [Submission.chenSiftLimit]
    push_cast
    have hfloor := Nat.floor_le hnn
    linarith

/-! ## The elementary reduction to the two `1/φ`-weighted modulus sums -/

/-- **The unweighted character expansion plus reindexing.**  For `2 ≤ D`, the sum of the
absolute values of the corrected remainders over the odd moduli `d ≤ D` is at most a constant
times `(log D + 1)` and the `1/φ`-weighted double sum `blodAllUnw`. -/
theorem bRemUNwAbsSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M Y D : ℕ), 2 ≤ D →
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1), |bRemCorr x M Y d|)
        ≤ C * (Real.log (D : ℝ) + 1) * blodAllUnw x M Y D := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := sumInvTotientLogBound
  refine ⟨C₀, hC₀pos, fun x M Y D hD => ?_⟩
  have hchar := bRemUNwCharMobius x M Y D hD
  have hre : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        (Nat.totient d : ℝ)⁻¹ *
          (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c),
            ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c))
      ≤ (∑ m ∈ Finset.Icc 1 D, (Nat.totient m : ℝ)⁻¹) *
        (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
          (Nat.totient t : ℝ)⁻¹ * ((Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)) :=
    reindex_bound D (fun n => (Nat.totient n : ℝ)⁻¹)
      (fun t r => bProdCharSumDivSum x M Y t r)
      (fun n => by positivity)
      (fun t r => bProdCharSumDivSum_nonneg x M Y t r)
      (fun c t m hc ht hm => by
        have h1 : (Nat.totient c : ℝ) * (Nat.totient t : ℝ) ≤ (Nat.totient (c * t) : ℝ) := by
          exact_mod_cast Nat.totient_super_multiplicative c t
        have h2 : (Nat.totient (c * t) : ℝ) * (Nat.totient m : ℝ)
            ≤ (Nat.totient (c * t * m) : ℝ) := by
          exact_mod_cast Nat.totient_super_multiplicative (c * t) m
        have h3 : (Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ)
            ≤ (Nat.totient (c * t * m) : ℝ) := by
          calc (Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ)
              ≤ (Nat.totient (c * t) : ℝ) * (Nat.totient m : ℝ) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ _ := h2
        have h4 : (Nat.totient (c * t * m) : ℝ)⁻¹
            ≤ ((Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ))⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).mpr h3
        have h5 : ((Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ))⁻¹
            = (Nat.totient c : ℝ)⁻¹ * ((Nat.totient t : ℝ)⁻¹ * (Nat.totient m : ℝ)⁻¹) := by
          rw [mul_inv, mul_inv]
          ring
        rw [h5] at h4
        simpa only [mul_assoc] using h4)
  have hconv : (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
        (Nat.totient t : ℝ)⁻¹ * ((Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r))
      = blodAllUnw x M Y D := by
    unfold blodAllUnw
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  have hsum : (∑ m ∈ Finset.Icc 1 D, (Nat.totient m : ℝ)⁻¹)
      ≤ C₀ * (Real.log (D : ℝ) + 1) := by
    have h := hC₀ D hD
    have hlog : 0 ≤ Real.log (D : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))
    have hcongr : (∑ m ∈ Finset.Icc 1 D, (Nat.totient m : ℝ)⁻¹)
        = ∑ m ∈ Finset.Icc 1 D, 1 / (Nat.totient m : ℝ) :=
      Finset.sum_congr rfl (fun m _ => by rw [one_div])
    rw [hcongr]
    nlinarith [h, hC₀pos, hlog]
  have hnn : 0 ≤ blodAllUnw x M Y D := by
    unfold blodAllUnw
    refine Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity) ?_)
    refine Finset.sum_nonneg (fun r _ => mul_nonneg (by positivity) ?_)
    exact bProdCharSumDivSum_nonneg x M Y t r
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1), |bRemCorr x M Y d|)
      ≤ _ := hchar
    _ ≤ _ := hre
    _ = (∑ m ∈ Finset.Icc 1 D, (Nat.totient m : ℝ)⁻¹) * blodAllUnw x M Y D := by
        rw [hconv]
    _ ≤ C₀ * (Real.log (D : ℝ) + 1) * blodAllUnw x M Y D :=
        mul_le_mul_of_nonneg_right hsum hnn

/-- The split of the `1/φ`-weighted modulus sum at the conductor threshold `R₀`. -/
theorem bRemUNwAllUnw_split (x M Y D R₀ : ℕ) :
    blodAllUnw x M Y D = blodSmallUnw x M Y D R₀ + blodLargeUnw x M Y D R₀ := by
  classical
  have key : ∀ t : ℕ,
      (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
          (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
        = (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)
          + (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ R₀ < r),
            (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r) := by
    intro t
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 D).filter (fun r => 2 ≤ r))
      (fun r => r ≤ R₀) (fun r => (Nat.totient r : ℝ)⁻¹ * bProdCharSumDivSum x M Y t r)]
    congr 1
    · refine Finset.sum_congr ?_ (fun r _ => rfl)
      ext r
      simp only [Finset.mem_filter]
      tauto
    · refine Finset.sum_congr ?_ (fun r _ => rfl)
      ext r
      simp only [Finset.mem_filter, not_le]
      tauto
  unfold blodAllUnw blodSmallUnw blodLargeUnw
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← mul_add]
  congr 1
  exact key t

/-! ## The final assembly -/

theorem bRemCorrLodUnweighted :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
      Filter.Eventually (fun x : ℕ =>
        Finset.sum
          ((Finset.Icc 1 (Nat.floor (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B))).filter
            (fun d : ℕ => d % 2 = 1))
          (fun d => abs (Work.NumberTheory.Chen.BTermCount.bRemCorr x (Submission.chenSiftLimit x)
              (Submission.chenWindowTop x) d))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) Filter.atTop := by
  intro A hA
  obtain ⟨C₀, hC₀pos, hred⟩ := bRemUNwAbsSum_le
  obtain ⟨B, hBpos, C', hC'pos, harith⟩ := bRemUNwArithConsume (A + 2) (by linarith)
  obtain ⟨Cs, hCspos, hsmall⟩ := bRemUNwSmallRParam (A + 2) C' (by linarith) hC'pos
  obtain ⟨cD, hcDpos, hdyad⟩ := BLodLargeRSumUnweightedDyadic
  refine ⟨B, hBpos, ?_⟩
  have hlog1 : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  have hlogK : ∀ᶠ x : ℕ in Filter.atTop, 2 * C₀ * (Cs + cD) ≤ Real.log (x : ℝ) :=
    eventually_const_le_nat_log (2 * C₀ * (Cs + cD))
  have hR2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ ⌊(Real.log (x : ℝ)) ^ C'⌋₊ := by
    have h : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ C' :=
      tendsto_natCast_atTop_atTop.eventually
        (((tendsto_rpow_atTop hC'pos).comp Real.tendsto_log_atTop).eventually_ge_atTop 2)
    filter_upwards [h] with x hx
    exact Nat.le_floor hx
  have hD2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ := by
    have h : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
      have hb := eventually_nat_log_pow_mul_le_rpow B (1 / 2) hBpos (by norm_num) 2
      filter_upwards [hb, hlog1] with x hx hx1
      have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hx1
      have hpos : 0 < (Real.log (x : ℝ)) ^ B := Real.rpow_pos_of_pos hlogpos B
      have hxw : 2 * (Real.log (x : ℝ)) ^ B ≤ Real.sqrt (x : ℝ) := by
        rw [Real.sqrt_eq_rpow]; exact hx
      rw [le_div_iff₀ hpos]
      linarith
    filter_upwards [h] with x hx
    exact Nat.le_floor hx
  have hx8 : ∀ᶠ x : ℕ in Filter.atTop, 8 ≤ x := Filter.eventually_ge_atTop 8
  filter_upwards [harith, hsmall, hlog1, hlogK, hR2, hD2, hx8] with x
    hAr hSm hlog1x hlogKx hR2x hD2x hx8x
  set M : ℕ := Submission.chenSiftLimit x with hMdef
  set Y : ℕ := Submission.chenWindowTop x with hYdef
  set D : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hDdef
  set R₀ : ℕ := ⌊(Real.log (x : ℝ)) ^ C'⌋₊ with hRdef
  have hD2' : 2 ≤ D := by rw [hDdef]; exact hD2x
  have hR2' : 2 ≤ R₀ := by rw [hRdef]; exact hR2x
  have hM1 : 1 ≤ M := by
    rw [hMdef, Submission.chenSiftLimit]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hMge : (x : ℝ) ^ ((1 : ℝ) / 14) ≤ (M : ℝ) := by
    rw [hMdef]; exact chenSiftLimit_ge_rpow x
  have hMY : M ≤ Y := by rw [hMdef, hYdef]; exact bRemUNwSiftLimit_le_windowTop x
  have hMx2 : (M : ℝ) ≤ (x : ℝ) + 2 := by rw [hMdef]; exact bRemUNwSiftLimit_le_add_two x
  have hYle : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [hYdef]; exact chenWindowTop_le_two_rpow x hx8x
  have hDle : D ≤ ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ := le_of_eq hDdef
  have hRle : ⌊(Real.log (x : ℝ)) ^ C'⌋₊ ≤ R₀ := le_of_eq hRdef.symm
  have hRle' : R₀ ≤ ⌊(Real.log (x : ℝ)) ^ C'⌋₊ := le_of_eq hRdef
  have hredx := hred x M Y D hD2'
  have hdyadx := hdyad x M Y D R₀ hM1 hD2' hR2'
  have harithx := hAr M Y D R₀ hMge hMY hMx2 hYle hD2' hDle hRle
  have hsmallx := hSm M Y D R₀ hMge hD2' hRle'
  have hlogposx : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hlog1x
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  -- the large-conductor piece
  have hlarge : blodLargeUnw x M Y D R₀ ≤ cD * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) := by
    calc blodLargeUnw x M Y D R₀ ≤ cD * blodW1 D * blodLSBlockSum x M Y D R₀ := hdyadx
      _ = cD * (blodW1 D * blodLSBlockSum x M Y D R₀) := by ring
      _ ≤ cD * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) :=
          mul_le_mul_of_nonneg_left harithx hcDpos.le
  -- the split
  have hsplit : blodAllUnw x M Y D = blodSmallUnw x M Y D R₀ + blodLargeUnw x M Y D R₀ :=
    bRemUNwAllUnw_split x M Y D R₀
  have hXnn : 0 ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2) := by positivity
  -- `log D ≤ log x`
  have hlogD : Real.log (D : ℝ) ≤ Real.log (x : ℝ) := by
    have hD2r : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2'
    have hDx : (D : ℝ) ≤ (x : ℝ) := by
      rw [hDdef]
      have hfloor := Nat.floor_le (show (0 : ℝ) ≤ Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B
        by positivity)
      push_cast at hfloor
      refine le_trans hfloor ?_
      have hpow1 : (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ B := Real.one_le_rpow hlog1x hBpos.le
      have hden : 0 < (Real.log (x : ℝ)) ^ B := lt_of_lt_of_le one_pos hpow1
      rw [div_le_iff₀ hden]
      have hsqrtx : Real.sqrt (x : ℝ) ≤ (x : ℝ) :=
        Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [hx1]⟩
      calc Real.sqrt (x : ℝ) ≤ Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ B :=
            le_mul_of_one_le_right (Real.sqrt_nonneg _) hpow1
        _ ≤ (x : ℝ) * (Real.log (x : ℝ)) ^ B :=
            mul_le_mul_of_nonneg_right hsqrtx hden.le
    exact Real.log_le_log (by linarith) hDx
  -- the final absorption
  have hfinal : C₀ * (Real.log (D : ℝ) + 1) * (Cs + cD) ≤ (Real.log (x : ℝ)) ^ (2 : ℕ) := by
    have h2 : Real.log (D : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by linarith [hlogD, hlog1x]
    have hCs : 0 ≤ Cs + cD := by linarith [hCspos.le, hcDpos.le]
    have hlogxnn : 0 ≤ Real.log (x : ℝ) := hlogposx.le
    have step1 : C₀ * (Real.log (D : ℝ) + 1) * (Cs + cD)
        ≤ C₀ * (2 * Real.log (x : ℝ)) * (Cs + cD) := by
      apply mul_le_mul_of_nonneg_right _ hCs
      exact mul_le_mul_of_nonneg_left h2 hC₀pos.le
    have step2 : C₀ * (2 * Real.log (x : ℝ)) * (Cs + cD)
        ≤ (Real.log (x : ℝ)) * (Real.log (x : ℝ)) := by
      have hK : 2 * C₀ * (Cs + cD) ≤ Real.log (x : ℝ) := hlogKx
      have e : C₀ * (2 * Real.log (x : ℝ)) * (Cs + cD)
          = (2 * C₀ * (Cs + cD)) * Real.log (x : ℝ) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hK hlogxnn
    calc C₀ * (Real.log (D : ℝ) + 1) * (Cs + cD) ≤ C₀ * (2 * Real.log (x : ℝ)) * (Cs + cD) :=
          step1
      _ ≤ (Real.log (x : ℝ)) * (Real.log (x : ℝ)) := step2
      _ = (Real.log (x : ℝ)) ^ (2 : ℕ) := by ring
  have hsmallx' : blodSmallUnw x M Y D R₀ ≤ Cs * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) := by
    simpa only [mul_div_assoc] using hsmallx
  have hmain : C₀ * (Real.log (D : ℝ) + 1) * blodAllUnw x M Y D
      ≤ C₀ * (Real.log (D : ℝ) + 1) *
          (Cs * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2))
            + cD * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2))) := by
    have hfac : 0 ≤ C₀ * (Real.log (D : ℝ) + 1) := by
      have : 0 ≤ Real.log (D : ℝ) + 1 := by linarith [Real.log_nonneg (show (1:ℝ) ≤ (D:ℝ) by
        exact_mod_cast (by omega : 1 ≤ D))]
      positivity
    have h := add_le_add hsmallx' hlarge
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h hfac
  have hratio : (Real.log (x : ℝ)) ^ (2 : ℕ) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2))
      = (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
    have hA2 : (Real.log (x : ℝ)) ^ (A + 2)
        = (Real.log (x : ℝ)) ^ A * (Real.log (x : ℝ)) ^ (2 : ℕ) := by
      rw [Real.rpow_add hlogposx]; congr 1; exact Real.rpow_natCast _ 2
    rw [hA2]
    have hAne : (Real.log (x : ℝ)) ^ A ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlogposx A)
    have h2ne : (Real.log (x : ℝ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ (ne_of_gt hlogposx)
    field_simp
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1), |bRemCorr x M Y d|)
      ≤ C₀ * (Real.log (D : ℝ) + 1) * blodAllUnw x M Y D := hredx
    _ ≤ C₀ * (Real.log (D : ℝ) + 1) *
          (Cs * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2))
            + cD * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2))) := hmain
    _ = (C₀ * (Real.log (D : ℝ) + 1) * (Cs + cD))
          * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) := by ring
    _ ≤ (Real.log (x : ℝ)) ^ (2 : ℕ) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2)) :=
        mul_le_mul_of_nonneg_right hfinal hXnn
    _ = (x : ℝ) / (Real.log (x : ℝ)) ^ A := hratio

end Work.NumberTheory.Chen.BTermCount
