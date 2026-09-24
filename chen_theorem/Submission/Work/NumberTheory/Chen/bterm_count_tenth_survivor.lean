import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.NumberTheory.Chen.BTermCount.SharpReduction
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Work.NumberTheory.Chen.BTermCount.Main
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrLodUnweighted
import Submission.Work.NumberTheory.Chen.ri_layer_beta2
import Submission.Work.NumberTheory.Sieve.RosserLinear.Defs

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen

open Work.NumberTheory.Chen.BTermCount

/-!
# The `B`-term survivor bound at the sift limit `x^{1/10}`

Target (the `h3` input of Chen's switch assembly at the optimal sift limit
`M = ⌊x^{1/10}⌋₊ + 1`, see `Submission/Chen/NOTES.md`):

`survivorCount x (chenSiftLimitTenth x) (chenWindowTop x) · (log x)² ≤ (27/10)·x` eventually.

The proof has four inputs:

* **(β)** the unweighted level of distribution for the shifted ternary sequence `B̄` at the tenth
  sift limit (an exact port of the proved `bRemCorrLodUnweighted`), proved in this file;
* **(γ)** the sharp triple count `#B̄ ≤ (1/2)·x/log x` at the tenth sift limit;
* **(α)** the `β = 2` cube-sieve excess bound `MpSum2 D Y ≤ (6/5)·Vsieve Y` for `Y³ ≤ D ≤ Y⁴`;
* **(δ)** the Mertens bound `VsieveOdd z · log z ≤ 149/200`.

With `X = #B̄`, `Z = ⌊D^{1/3}⌋` (`D` the level of distribution) and `s = log D / log Z ≈ 3`:

`survivorCount ≤ X · MpSum2 D Z + Σ_{d ≤ D} |bRemCorr d| + (shared mass)`

`≤ (1/2)·(x/log x)·(6/5)·Vsieve Z + o(x/log²x) ≤ (1/2)·1.2·(149/200)·3·x/(log x·log D) ≈ 2.68·x/log²x`.

The margin over `27/10` is ≈0.7 %, so every one of the four inputs has to be close to its sharp
constant (the sharp value of the whole classical route is `2.593`); see
`Submission/Work/NumberTheory/Chen/BTermCount/notes/NOGO_ANALYSIS.md`.
-/

/-! ## 1. Elementary comparisons for the tenth sift limit -/

/-- `chenSiftLimitTenth x = ⌊x^{1/10}⌋₊ + 1 ≥ 1`. -/
theorem one_le_chenSiftLimitTenth (x : ℕ) : 1 ≤ Submission.chenSiftLimitTenth x := by
  rw [Submission.chenSiftLimitTenth]
  have : (0:ℕ) ≤ ⌊Real.rpow (x : ℝ) ((1:ℝ)/10)⌋₊ := Nat.zero_le _
  omega

/-- `x^{1/14} ≤ chenSiftLimitTenth x` (the hypothesis under which all the level-of-distribution
components of `bRemCorrLodUnweighted` are generic). -/
theorem chenSiftLimitTenth_ge_rpow (x : ℕ) :
    (x : ℝ) ^ ((1:ℝ)/14) ≤ (Submission.chenSiftLimitTenth x : ℝ) := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num : ((1:ℝ)/14) ≠ 0)]
    exact_mod_cast Nat.zero_le (Submission.chenSiftLimitTenth 0)
  · have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx0
    have hx0' : (0:ℝ) ≤ (x:ℝ) := by linarith
    have hle : Real.rpow (x:ℝ) ((1:ℝ)/14) ≤ Real.rpow (x:ℝ) ((1:ℝ)/10) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hfl : Real.rpow (x:ℝ) ((1:ℝ)/10) < ((⌊Real.rpow (x : ℝ) ((1:ℝ)/10)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    calc (x : ℝ) ^ ((1:ℝ)/14) = Real.rpow (x:ℝ) ((1:ℝ)/14) := rfl
      _ ≤ Real.rpow (x:ℝ) ((1:ℝ)/10) := hle
      _ ≤ (Submission.chenSiftLimitTenth x : ℝ) := by
          rw [Submission.chenSiftLimitTenth]
          push_cast
          linarith

/-- `chenSiftLimitTenth x ≤ x + 2` — the sift limit stays inside the range of `B̄`. -/
theorem chenSiftLimitTenth_le_add_two (x : ℕ) :
    (Submission.chenSiftLimitTenth x : ℝ) ≤ (x : ℝ) + 2 := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    have h1 : Submission.chenSiftLimitTenth 0 = 1 := by
      rw [Submission.chenSiftLimitTenth]
      simp [Real.zero_rpow (by norm_num : ((1:ℝ)/10) ≠ 0)]
    rw [h1]; norm_num
  · have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx0
    have hx0' : (0:ℝ) ≤ (x:ℝ) := by linarith
    have hpow : Real.rpow (x : ℝ) ((1:ℝ)/10) ≤ (x:ℝ) := by
      calc Real.rpow (x:ℝ) ((1:ℝ)/10) ≤ Real.rpow (x:ℝ) (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x:ℝ) := Real.rpow_one _
    have hfl : ((⌊Real.rpow (x : ℝ) ((1:ℝ)/10)⌋₊ : ℕ) : ℝ) ≤ Real.rpow (x : ℝ) ((1:ℝ)/10) :=
      Nat.floor_le (Real.rpow_nonneg hx0' _)
    rw [Submission.chenSiftLimitTenth]
    push_cast
    linarith

/-- `chenSiftLimitTenth x ≤ chenWindowTop x`: the tenth sift limit lies below the window top. -/
theorem chenSiftLimitTenth_le_windowTop (x : ℕ) :
    Submission.chenSiftLimitTenth x ≤ Submission.chenWindowTop x := by
  rw [Submission.chenSiftLimitTenth, Submission.chenWindowTop]
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hkey : Real.rpow (x:ℝ) ((1:ℝ)/10) ≤ Real.rpow (x:ℝ) ((1:ℝ)/3) + 1 := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h
      rw [Nat.cast_zero,
        show Real.rpow (0:ℝ) ((1:ℝ)/10) = 0 from Real.zero_rpow (by norm_num),
        show Real.rpow (0:ℝ) ((1:ℝ)/3) = 0 from Real.zero_rpow (by norm_num)]
      norm_num
    · have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast h
      have hmono : Real.rpow (x:ℝ) ((1:ℝ)/10) ≤ Real.rpow (x:ℝ) ((1:ℝ)/3) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      linarith
  have h1 : ⌊Real.rpow (x:ℝ) ((1:ℝ)/10)⌋₊ ≤ ⌊Real.rpow (x:ℝ) ((1:ℝ)/3) + 1⌋₊ :=
    Nat.floor_mono hkey
  have h2 : ⌊Real.rpow (x:ℝ) ((1:ℝ)/3) + 1⌋₊ = ⌊Real.rpow (x:ℝ) ((1:ℝ)/3)⌋₊ + 1 :=
    Nat.floor_add_one (Real.rpow_nonneg hx0 _)
  omega

/-! ## 2. The level of distribution at the tenth sift limit

This is the exact port of `bRemCorrLodUnweighted`: all of its components
(`bRemUNwAbsSum_le`, `bRemUNwArithConsume`, `bRemUNwSmallRParam`,
`BLodLargeRSumUnweightedDyadic`) are generic in `M` under the single hypothesis
`x^{1/14} ≤ M`, which `chenSiftLimitTenth_ge_rpow` supplies. -/

/-- **The unweighted level of distribution for the shifted ternary sequence at the sift limit
`chenSiftLimitTenth x = ⌊x^{1/10}⌋₊ + 1`.** -/
theorem bRemCorrLodUnweighted_tenth :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
      Filter.Eventually (fun x : ℕ =>
        Finset.sum
          ((Finset.Icc 1 (Nat.floor (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B))).filter
            (fun d : ℕ => d % 2 = 1))
          (fun d => abs (BTermCount.bRemCorr x (Submission.chenSiftLimitTenth x)
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
  set M : ℕ := Submission.chenSiftLimitTenth x with hMdef
  set Y : ℕ := Submission.chenWindowTop x with hYdef
  set D : ℕ := ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊ with hDdef
  set R₀ : ℕ := ⌊(Real.log (x : ℝ)) ^ C'⌋₊ with hRdef
  have hD2' : 2 ≤ D := by rw [hDdef]; exact hD2x
  have hR2' : 2 ≤ R₀ := by rw [hRdef]; exact hR2x
  have hM1 : 1 ≤ M := by rw [hMdef]; exact one_le_chenSiftLimitTenth x
  have hMge : (x : ℝ) ^ ((1 : ℝ) / 14) ≤ (M : ℝ) := by
    rw [hMdef]; exact chenSiftLimitTenth_ge_rpow x
  have hMY : M ≤ Y := by rw [hMdef, hYdef]; exact chenSiftLimitTenth_le_windowTop x
  have hMx2 : (M : ℝ) ≤ (x : ℝ) + 2 := by rw [hMdef]; exact chenSiftLimitTenth_le_add_two x
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

end Work.NumberTheory.Chen
