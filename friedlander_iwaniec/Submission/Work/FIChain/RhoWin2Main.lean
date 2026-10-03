/-
# `Submission.Work.FIChain.RhoWin2Main`

The `n₁ ≤ Δ` half of the companion paper's §10 `Π`-removal, in the integrated form needed by
`Work.FIChain.RhoWindowIntegrated2`.

**Statement.**  Given the two pointwise inputs on the `Π`-restricted window sums
`Xpg x Pz c σ u`,

* `Σ_{c ≤ x} |Xpg c σ u| ≤ KA·Ã(x)(log x)^{-2^26}`  (the `Π`-restricted Proposition 4.1,
  `RhoWin2Box`),
* `Σ_{c ≤ x} τ(c)⁶|Xpg c σ u| ≤ C₆·Ã(x)(log x)^{262144}`  (the `τ⁶`-moment, `RhoWin2Moment`),

for `σ ∈ [1,C]`, `u ∈ [lo/Δ, hi]`, the integrated `n₁ ≤ Δ` part of the split is

`∫_lo^hi (∫_1^C Wmain(s,t)/s)/t ≪ KA^{1/3} C₆^{2/3} Ã(x) (log x)^{-5}`.

**Proof.**  Write `Wmain = Σ_c τ(c)² Σ_{n₁|Π, n₁≤Δ} Σ_{d₁|n₁} |Xpg (c n₁)(s/d₁)(t/n₁)|` (a finite
sum, so integral and sums commute: `rhoMainLinear3`).  For a single triple the changes of variable
`σ = s/d₁`, `u = t/n₁` and the range extensions (`σ ≥ 1` kills the part below `1`, and
`n₁ ≤ Δ` gives `lo/Δ ≤ lo/n₁`) yield `RhoWin2PerTriple`.  Merging the sums again and grouping
`Σ_{n₁} Σ_{d₁|n₁}` by the product `m = c n₁` gives at each `(σ,u)`

`Σ_{n₁|Π,n₁≤Δ} τ(n₁) Σ_c τ(c)²|Xpg (c n₁) σ u| ≤ Σ_{m≤x} τ(m)⁴ |Xpg m σ u|`

(`RhoWin2TauGrouping4`), and Hölder between the two pointwise inputs (`RhoWin2Holder34`) bounds
the last sum by `(KA·Ã·L^{-2^26})^{1/3}(C₆·Ã·L^{262144})^{2/3}`.  The remaining
`∫∫ dσ/σ du/u` is `log C · log(hi/(lo/Δ)) ≤ 4(log x)²`, absorbed by `RhoWin2Numeric`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FIChain.RhoWin2TauGrouping4
import Submission.Work.FIChain.RhoWin2Holder34
import Submission.Work.FIChain.RhoWin2ShiftRange

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Interval integrability with the `1/s` inside the parametrised integral -/

/-- The parametrised integral `t ↦ (∫_1^C Φ(s,t)/s)/t` is interval integrable on `(lo,hi]` when
`Φ` is jointly measurable and uniformly bounded. -/
lemma rhoMainParamIntDiv {Φ : ℝ → ℝ → ℝ} (C lo hi K : ℝ) (hC1 : 1 ≤ C) (hlo : 0 < lo)
    (hle : lo ≤ hi) (hΦ : Measurable (fun p : ℝ × ℝ => Φ p.1 p.2))
    (hK : ∀ s t : ℝ, |Φ s t| ≤ K) :
    IntervalIntegrable (fun t : ℝ => (∫ s in (1 : ℝ)..C, Φ s t / s) / t) volume lo hi := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 0)
  have hmeas : Measurable (fun t : ℝ => ∫ s in (1 : ℝ)..C, Φ s t / s) := by
    have hjoint : StronglyMeasurable (fun p : ℝ × ℝ => Φ p.2 p.1 / p.2) :=
      ((hΦ.comp measurable_swap).div measurable_snd).stronglyMeasurable
    have h := StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure ℝ).restrict (Set.Ioc (1 : ℝ) C))
      (f := fun t s : ℝ => Φ s t / s) hjoint
    simpa only [intervalIntegral.integral_of_le hC1] using h.measurable
  have hint : ∀ t : ℝ, |∫ s in (1 : ℝ)..C, Φ s t / s| ≤ K * (C - 1) := by
    intro t
    have hb : |C - 1| = C - 1 := abs_of_nonneg (by linarith)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := C) (C := K) (f := fun s : ℝ => Φ s t / s)
      (fun s hs => by
        rw [Set.uIoc_of_le hC1] at hs
        have hs1 : (1 : ℝ) ≤ s := le_of_lt hs.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hs1)]
        have h1 : |Φ s t| / s ≤ |Φ s t| := by
          rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs1)]
          nlinarith [abs_nonneg (Φ s t)]
        exact le_trans h1 (hK s t))
    rwa [Real.norm_eq_abs, hb] at h
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  refine Measure.integrableOn_of_bounded
    (s_finite := (measure_Ioc_lt_top (a := lo) (b := hi)).ne)
    (f_mble := (hmeas.div measurable_id).aestronglyMeasurable)
    (M := K * (C - 1) / lo) ?_
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le hlo (le_of_lt ht.1)
  have hMnn : 0 ≤ K * (C - 1) := mul_nonneg hKnn (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  calc |∫ s in (1 : ℝ)..C, Φ s t / s| / t ≤ K * (C - 1) / t :=
        div_le_div_of_nonneg_right (hint t) (le_of_lt ht0)
    _ ≤ K * (C - 1) / lo := div_le_div_of_nonneg_left hMnn hlo (le_of_lt ht.1)

/-! ## 1. The numerical exponent bookkeeping -/

lemma rhoMainNumeric (KA C6 A L : ℝ) (hKA : 0 ≤ KA) (hC6 : 0 ≤ C6) (hA : 0 ≤ A)
    (hL1 : 1 ≤ L) :
    L ^ (2 : ℝ) * (KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
        * (C6 * A * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
      ≤ KA ^ ((1 : ℝ) / 3) * C6 ^ ((2 : ℝ) / 3) * A * L ^ (-(5 : ℤ)) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hX : (KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
      = KA ^ ((1 : ℝ) / 3) * A ^ ((1 : ℝ) / 3)
        * L ^ (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3)) := by
    rw [Real.mul_rpow (mul_nonneg hKA hA) (Real.rpow_nonneg hLpos.le _),
      Real.mul_rpow hKA hA, ← Real.rpow_mul hLpos.le]
  have hY : (C6 * A * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
      = C6 ^ ((2 : ℝ) / 3) * A ^ ((2 : ℝ) / 3)
        * L ^ ((262144 : ℝ) * ((2 : ℝ) / 3)) := by
    rw [← Real.rpow_natCast L 262144,
      Real.mul_rpow (mul_nonneg hC6 hA) (Real.rpow_nonneg hLpos.le _),
      Real.mul_rpow hC6 hA, ← Real.rpow_mul hLpos.le]
    norm_num
  have hAcomb : A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3) = A := by
    rw [← Real.rpow_add' hA (by norm_num : ((1 : ℝ) / 3 + (2 : ℝ) / 3) ≠ 0)]
    norm_num
  have hLcomb : L ^ (2 : ℝ) * L ^ (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
        * L ^ ((262144 : ℝ) * ((2 : ℝ) / 3))
      = L ^ ((2 : ℝ) + (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
          + ((262144 : ℝ) * ((2 : ℝ) / 3))) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
  have hexp : (2 : ℝ) + (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
        + ((262144 : ℝ) * ((2 : ℝ) / 3)) ≤ ((-(5 : ℤ)) : ℝ) := by norm_num
  have hLfin : L ^ ((2 : ℝ) + (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
        + ((262144 : ℝ) * ((2 : ℝ) / 3))) ≤ L ^ (-(5 : ℤ)) := by
    rw [show L ^ (-(5 : ℤ)) = L ^ ((↑(-5 : ℤ)) : ℝ) from (Real.rpow_intCast L (-5)).symm]
    rw [show ((↑(-5 : ℤ)) : ℝ) = -(↑(5 : ℤ) : ℝ) from by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hexp
  have hKnn : 0 ≤ KA ^ ((1 : ℝ) / 3) * C6 ^ ((2 : ℝ) / 3) * A :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hKA _) (Real.rpow_nonneg hC6 _)) hA
  calc L ^ (2 : ℝ) * (KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
        * (C6 * A * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)
      = KA ^ ((1 : ℝ) / 3) * C6 ^ ((2 : ℝ) / 3)
          * (A ^ ((1 : ℝ) / 3) * A ^ ((2 : ℝ) / 3))
          * (L ^ (2 : ℝ) * L ^ (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
            * L ^ ((262144 : ℝ) * ((2 : ℝ) / 3))) := by
        rw [hX, hY]; ring
    _ = KA ^ ((1 : ℝ) / 3) * C6 ^ ((2 : ℝ) / 3) * A
          * L ^ ((2 : ℝ) + (-((2 : ℝ) ^ (26 : ℕ)) * ((1 : ℝ) / 3))
            + ((262144 : ℝ) * ((2 : ℝ) / 3))) := by
        rw [hAcomb, hLcomb]
    _ ≤ KA ^ ((1 : ℝ) / 3) * C6 ^ ((2 : ℝ) / 3) * A * L ^ (-(5 : ℤ)) :=
        mul_le_mul_of_nonneg_left hLfin hKnn

lemma rhoMainPerTriple (G : ℝ → ℝ → ℝ) (n d : ℕ) (Δ lo hi C K : ℝ) (hn : 1 ≤ n)
    (hd : 1 ≤ d) (hnΔ : (n : ℝ) ≤ Δ) (hC1 : 1 ≤ C) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hmeas : Measurable (fun p : ℝ × ℝ => G p.1 p.2)) (hbd : ∀ σ u : ℝ, |G σ u| ≤ K)
    (hnn : ∀ σ u : ℝ, 0 ≤ G σ u) (h0 : ∀ σ u : ℝ, σ < 1 → G σ u = 0) :
    (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, G (s / d) (t / n) / s) / t)
      ≤ ∫ u in lo / Δ..hi, (∫ σ in (1 : ℝ)..C, G σ u / σ) / u := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hΔpos : (0 : ℝ) < Δ := lt_of_lt_of_le hnR hnΔ
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans hn1 hnΔ
  have hloK : 0 < lo / Δ := div_pos hlo hΔpos
  have hloDhi : lo / Δ ≤ hi := by
    have h1 : lo / Δ ≤ lo := div_le_self hlo.le hΔ1
    linarith
  have hstep1 : ∀ t : ℝ, (∫ s in (1 : ℝ)..C, G (s / (d : ℝ)) (t / (n : ℝ)) / s)
      = ∫ σ in (1 / (d : ℝ))..(C / (d : ℝ)), G σ (t / (n : ℝ)) / σ := by
    intro t
    exact integral_div_comp_div' (fun σ : ℝ => G σ (t / (n : ℝ))) (ne_of_gt hdR)
  have hstep2 : ∀ t : ℝ, (∫ σ in (1 / (d : ℝ))..(C / (d : ℝ)), G σ (t / (n : ℝ)) / σ)
      ≤ ∫ σ in (1 : ℝ)..C, G σ (t / (n : ℝ)) / σ := by
    intro t
    exact RhoWin2ShiftRange (fun σ : ℝ => G σ (t / (n : ℝ))) (d : ℝ) C K
      (hmeas.comp (measurable_id.prodMk measurable_const))
      (fun σ => hbd σ (t / (n : ℝ))) (fun σ => hnn σ (t / (n : ℝ)))
      (fun σ hσ => h0 σ (t / (n : ℝ)) hσ) (by exact_mod_cast hd) hC1
  have hmono : (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, G (s / (d : ℝ)) (t / (n : ℝ)) / s) / t)
      ≤ ∫ t in lo..hi, (∫ σ in (1 : ℝ)..C, G σ (t / (n : ℝ)) / σ) / t := by
    refine intervalIntegral.integral_mono_on hlohi ?_ ?_ ?_
    · refine rhoMainParamIntDiv (Φ := fun s t => G (s / (d : ℝ)) (t / (n : ℝ)))
        C lo hi K hC1 hlo hlohi ?_ ?_
      · exact hmeas.comp ((measurable_fst.div_const (d : ℝ)).prodMk
          (measurable_snd.div_const (n : ℝ)))
      · intro s t
        exact hbd (s / (d : ℝ)) (t / (n : ℝ))
    · refine rhoMainParamIntDiv (Φ := fun s t => G s (t / (n : ℝ))) C lo hi K hC1 hlo hlohi ?_ ?_
      · exact hmeas.comp (measurable_fst.prodMk (measurable_snd.div_const (n : ℝ)))
      · intro s t
        exact hbd s (t / (n : ℝ))
    · intro t ht
      refine div_le_div_of_nonneg_right ?_ (le_trans hlo.le ht.1)
      exact (hstep1 t).trans_le (hstep2 t)
  have hstep4 : (∫ t in lo..hi, (∫ σ in (1 : ℝ)..C, G σ (t / (n : ℝ)) / σ) / t)
      = ∫ u in lo / (n : ℝ)..hi / (n : ℝ), (∫ σ in (1 : ℝ)..C, G σ u / σ) / u :=
    integral_div_comp_div' (fun u : ℝ => ∫ σ in (1 : ℝ)..C, G σ u / σ) (ne_of_gt hnR)
  refine hmono.trans ?_
  rw [hstep4]
  refine integral_mono_range' ?_ ?_ ?_ ?_ ?_
  · rw [div_le_div_iff₀ hΔpos hnR]
    exact mul_le_mul_of_nonneg_left hnΔ hlo.le
  · exact div_le_div_of_nonneg_right hlohi hnR.le
  · rw [div_le_iff₀ hnR]
    nlinarith [hlo.le, hlohi]
  · intro u hu
    refine div_nonneg ?_ (le_trans hloK.le hu.1)
    exact intervalIntegral.integral_nonneg hC1
      (fun σ hσ => div_nonneg (hnn σ u) (by linarith [hσ.1]))
  · exact rhoMainParamIntDiv (Φ := fun σ u => G σ u) C (lo / Δ) hi K hC1 hloK hloDhi hmeas hbd

/-! ## 2. Abbreviations of the target statement -/

/-- The `n₁ ≤ Δ` range of the target statement. -/
abbrev rhoMainD (Pz : ℕ) (Delta : ℝ) : Finset ℕ :=
  (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Delta)

/-- The pointwise envelope of the merged `Π`-split sum. -/
abbrev rhoMainVenv (KA C6 A L : ℝ) : ℝ :=
  (KA * A * L ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
    * (C6 * A * L ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)

/-- A crude uniform bound for the merged `Π`-split sum (used only for integrability). -/
abbrev rhoMainMassSum (x Pz : ℕ) (Df : Finset ℕ) : ℝ :=
  ∑ n₁ ∈ Df, ((n₁.divisors.card : ℝ)) * ∑ c ∈ Finset.Icc 1 x,
    ((c.divisors.card : ℝ)) ^ 2 * (∑ n ∈ Finset.Icc 1 x,
      ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)

/-! ## 3. Elementary facts about `Xpg` -/

/-- `Xpg` vanishes for moduli beyond `x` (the window condition `c·n ≤ x` is then empty). -/
lemma Xpg_eq_zero_of_lt (x Pz c : ℕ) (σ u : ℝ) (h : x < c) : Xpg x Pz c σ u = 0 := by
  rw [Xpg]
  refine Finset.sum_eq_zero (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnI, hcn, -⟩ := hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
  have hle : c ≤ c * n := by
    calc c = c * 1 := (Nat.mul_one c).symm
      _ ≤ c * n := Nat.mul_le_mul_left c hn1
  omega

/-- A uniform bound for `Xpg` by the full unsigned mass `Σ_{n ≤ x} τ(n)|ã(cn)|`. -/
lemma abs_Xpg_le_massAll (x Pz c : ℕ) (σ u : ℝ) :
    |Xpg x Pz c σ u| ≤ ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc (c * n)| := by
  have ht : ∀ n ∈ (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
      ((n.divisors.card : ℝ)) * atilc (c * n) = ((n.divisors.card : ℝ)) * |atilc (c * n)| :=
    fun n _ => by rw [abs_of_nonneg (Work.FITop.atilFIa_nonneg (c * n))]
  calc |Xpg x Pz c σ u|
      ≤ ∑ n ∈ (Finset.Icc 1 x).filter
          (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
          ((n.divisors.card : ℝ)) * atilc (c * n) := abs_Xpg_le_mass x Pz c σ u
    _ = ∑ n ∈ (Finset.Icc 1 x).filter
          (fun n => c * n ≤ x ∧ u < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ 2 * u),
          ((n.divisors.card : ℝ)) * |atilc (c * n)| := Finset.sum_congr rfl ht
    _ ≤ ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc (c * n)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

/-! ## 4. `Wmain` as a three-fold sum -/

/-- `Wmain` reindexed with the `c`-sum innermost. -/
lemma Wmain_eq_three (x Pz : ℕ) (Delta s t : ℝ) :
    Wmain x Pz Delta s t
      = ∑ n₁ ∈ rhoMainD Pz Delta,
          ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
            ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))| := by
  rw [Wmain, rhoMainD]
  have h1 : ∀ c : ℕ, ((c.divisors.card : ℝ)) ^ 2 *
        (∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Delta),
          ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))|)
      = ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Delta),
          ∑ d₁ ∈ n₁.divisors,
            ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))| := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n₁ _ => ?_)
  rw [Finset.sum_comm]

/-! ## 5. Linearity: integrals of finite sums over the triple index -/

/-- Splitting the iterated integral of a three-fold finite sum, with a weight `w` depending only
on the innermost index. -/
lemma rhoMainLinear3 (T : Finset ℕ) (U : ℕ → Finset ℕ) (V : ℕ → ℕ → Finset ℕ)
    (w : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ) (C lo hi : ℝ) (hC1 : 1 ≤ C)
    (hlo : 0 < lo) (hle : lo ≤ hi)
    (hsint : ∀ n₁ ∈ T, ∀ d₁ ∈ U n₁, ∀ c ∈ V n₁ d₁, ∀ t : ℝ,
        IntervalIntegrable (fun s : ℝ => g c n₁ d₁ s t / s) volume (1 : ℝ) C)
    (hint : ∀ n₁ ∈ T, ∀ d₁ ∈ U n₁, ∀ c ∈ V n₁ d₁,
        IntervalIntegrable (fun t : ℝ => (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)
          volume lo hi) :
    (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
        (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * g c n₁ d₁ s t) / s) / t)
      = ∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t) := by
  have hinner : ∀ t : ℝ,
      (∫ s in (1 : ℝ)..C, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * g c n₁ d₁ s t) / s)
        = ∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
            w c * (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) := by
    intro t
    have hpt : ∀ s : ℝ, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * g c n₁ d₁ s t) / s
        = ∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * (g c n₁ d₁ s t / s) := by
      intro s
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun n₁ _ => ?_)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun d₁ _ => ?_)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
    have h1 : (∫ x in (1 : ℝ)..C, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * (g c n₁ d₁ x t / x)))
        = ∑ n₁ ∈ T, ∫ x in (1 : ℝ)..C, (∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
            w c * (g c n₁ d₁ x t / x)) := by
      refine intervalIntegral.integral_finsetSum (h := fun n₁ hn₁ => ?_)
      refine (IntervalIntegrable.sum (U n₁) (fun d₁ hd₁ =>
        IntervalIntegrable.sum (V n₁ d₁) (fun c hc =>
          (hsint n₁ hn₁ d₁ hd₁ c hc t).const_mul (w c)))).congr_ae
        (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
    rw [h1]
    refine Finset.sum_congr rfl (fun n₁ hn₁ => ?_)
    have h2 : (∫ x in (1 : ℝ)..C, (∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * (g c n₁ d₁ x t / x)))
        = ∑ d₁ ∈ U n₁, ∫ x in (1 : ℝ)..C,
            (∑ c ∈ V n₁ d₁, w c * (g c n₁ d₁ x t / x)) := by
      refine intervalIntegral.integral_finsetSum (h := fun d₁ hd₁ => ?_)
      refine (IntervalIntegrable.sum (V n₁ d₁) (fun c hc =>
        (hsint n₁ hn₁ d₁ hd₁ c hc t).const_mul (w c))).congr_ae
        (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
    rw [h2]
    refine Finset.sum_congr rfl (fun d₁ hd₁ => ?_)
    have h3 : (∫ x in (1 : ℝ)..C, (∑ c ∈ V n₁ d₁, w c * (g c n₁ d₁ x t / x)))
        = ∑ c ∈ V n₁ d₁, ∫ x in (1 : ℝ)..C, w c * (g c n₁ d₁ x t / x) := by
      exact intervalIntegral.integral_finsetSum (h := fun c hc =>
        (hsint n₁ hn₁ d₁ hd₁ c hc t).const_mul (w c))
    rw [h3]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [intervalIntegral.integral_const_mul]
  have hpt2 : ∀ t : ℝ, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
        w c * (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s)) / t
      = ∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t) := by
    intro t
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d₁ _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  have houter : (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
        (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁, w c * g c n₁ d₁ s t) / s) / t)
      = ∫ t in lo..hi, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s)) / t :=
    intervalIntegral.integral_congr (fun t _ => by rw [hinner t])
  rw [houter]
  have h4 : (∫ t in lo..hi, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
        w c * (∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s)) / t)
      = ∫ t in lo..hi, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)) :=
    intervalIntegral.integral_congr (fun t _ => hpt2 t)
  rw [h4]
  have h5 : (∫ t in lo..hi, (∑ n₁ ∈ T, ∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
        w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)))
      = ∑ n₁ ∈ T, ∫ t in lo..hi, (∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
          w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)) := by
    refine intervalIntegral.integral_finsetSum (h := fun n₁ hn₁ => ?_)
    refine (IntervalIntegrable.sum (U n₁) (fun d₁ hd₁ =>
      IntervalIntegrable.sum (V n₁ d₁) (fun c hc =>
        (hint n₁ hn₁ d₁ hd₁ c hc).const_mul (w c)))).congr_ae
      (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
  rw [h5]
  refine Finset.sum_congr rfl (fun n₁ hn₁ => ?_)
  have h6 : (∫ t in lo..hi, (∑ d₁ ∈ U n₁, ∑ c ∈ V n₁ d₁,
        w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)))
      = ∑ d₁ ∈ U n₁, ∫ t in lo..hi, (∑ c ∈ V n₁ d₁,
          w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)) := by
    refine intervalIntegral.integral_finsetSum (h := fun d₁ hd₁ => ?_)
    refine (IntervalIntegrable.sum (V n₁ d₁) (fun c hc =>
      (hint n₁ hn₁ d₁ hd₁ c hc).const_mul (w c))).congr_ae
      (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
  rw [h6]
  refine Finset.sum_congr rfl (fun d₁ hd₁ => ?_)
  have h7 : (∫ t in lo..hi, (∑ c ∈ V n₁ d₁,
        w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t)))
      = ∑ c ∈ V n₁ d₁, ∫ t in lo..hi,
          w c * ((∫ s in (1 : ℝ)..C, g c n₁ d₁ s t / s) / t) := by
    exact intervalIntegral.integral_finsetSum (h := fun c hc =>
      (hint n₁ hn₁ d₁ hd₁ c hc).const_mul (w c))
  rw [h7]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [intervalIntegral.integral_const_mul]

/-! ## 6. The pointwise envelope of the merged sum -/

/-- The grouping + Hölder bound for the merged `Π`-split sum, at a point `(σ,u)` of the window. -/
lemma rhoMainVenvBound (x Pz : ℕ) (Delta lo hi C KA C6 : ℝ)
    (hC1 : 1 ≤ C)
    (hA : ∀ u : ℝ, lo / Delta ≤ u → u ≤ hi → ∀ σ : ℝ, 1 ≤ σ → σ ≤ C →
      (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
        ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))))
    (hB : ∀ σ u : ℝ, (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|)
        ≤ C6 * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ))
    (hKA : 0 ≤ KA) (hC6 : 0 ≤ C6) (hL1 : 1 ≤ Real.log (x : ℝ))
    (σ u : ℝ) (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ C) (hu1 : lo / Delta ≤ u) (hu2 : u ≤ hi) :
    (∑ n₁ ∈ rhoMainD Pz Delta, ((n₁.divisors.card : ℝ)) * ∑ c ∈ Finset.Icc 1 x,
        ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|)
      ≤ rhoMainVenv KA C6 (AcountAtilC x) (Real.log (x : ℝ)) := by
  have hgrp := RhoWin2TauGrouping4 (rhoMainD Pz Delta)
    (fun b hb => Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1)
    (fun m : ℕ => Xpg x Pz m σ u) x (fun c hc => by
      rw [Xpg_eq_zero_of_lt x Pz c σ u hc])
  have hhold := RhoWin2Holder34 x (fun m : ℕ => Xpg x Pz m σ u)
  have hA1 := hA u hu1 hu2 σ hσ1 hσ2
  have hB1 := hB σ u
  refine hgrp.trans (hhold.trans ?_)
  rw [rhoMainVenv]
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg' x
  exact mul_le_mul
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun c _ => abs_nonneg _)) hA1 (by norm_num))
    (Real.rpow_le_rpow (Finset.sum_nonneg (fun c _ => by positivity)) hB1 (by norm_num))
    (Real.rpow_nonneg (Finset.sum_nonneg (fun c _ => by positivity)) _)
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg hKA hAnn) (Real.rpow_nonneg hLpos.le _)) _)

/-! ## 7. The main theorem -/

theorem RhoWin2Main :
    ∃ K : ℝ, 0 < K ∧ ∀ (x Pz : ℕ) (Delta lo hi C KA C₆ : ℝ),
      0 < lo → lo ≤ hi → 1 ≤ C → 1 ≤ Delta → 0 ≤ KA → 0 ≤ C₆ → 1 ≤ Real.log (x : ℝ) →
      Real.log (hi / (lo / Delta)) ≤ 2 * Real.log (x : ℝ) →
      Real.log C ≤ 2 * Real.log (x : ℝ) →
      (∀ u : ℝ, lo / Delta ≤ u → u ≤ hi → ∀ σ : ℝ, 1 ≤ σ → σ ≤ C →
        (∑ c ∈ Finset.Icc 1 x, |Xpg x Pz c σ u|)
          ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ)))) →
      (∀ σ u : ℝ, (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 6 * |Xpg x Pz c σ u|)
        ≤ C₆ * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ)) →
      (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
        (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
          (∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Delta),
            ∑ d₁ ∈ n₁.divisors,
              |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|)) / s) / t)
      ≤ K * KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(5 : ℤ)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro x Pz Delta lo hi C KA C₆ hlo hlohi hC1 hD1 hKA hC6 hL1 hlogR hlogC hA hB
  show (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, Wmain x Pz Delta s t / s) / t)
      ≤ 4 * KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
          * (Real.log (x : ℝ)) ^ (-(5 : ℤ))
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg' x
  by_cases hDempty : rhoMainD Pz Delta = ∅
  · rw [rhoMainD] at hDempty
    have hW : ∀ s t : ℝ, Wmain x Pz Delta s t = 0 := by
      intro s t
      rw [Wmain, hDempty]
      simp
    have hzero : (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, Wmain x Pz Delta s t / s) / t) = 0 := by
      simp only [hW, zero_div, intervalIntegral.integral_zero]
    rw [hzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg hKA _)) (Real.rpow_nonneg hC6 _)) hAnn) (zpow_nonneg hLpos.le _)
  · obtain ⟨n0, hn0mem⟩ := Finset.nonempty_iff_ne_empty.mpr hDempty
    obtain ⟨hn0dvd, hn0le⟩ := Finset.mem_filter.mp hn0mem
    have hn0pos : 0 < n0 := Nat.pos_of_mem_divisors hn0dvd
    have hDge1 : (1 : ℝ) ≤ Delta := le_trans (by exact_mod_cast hn0pos) hn0le
    have hDpos : 0 < Delta := lt_of_lt_of_le zero_lt_one hDge1
    have hloDpos : 0 < lo / Delta := div_pos hlo hDpos
    have hloDle : lo / Delta ≤ lo := by
      rw [div_le_iff₀ hDpos]
      simpa using mul_le_mul_of_nonneg_left hDge1 hlo.le
    have hloDhi : lo / Delta ≤ hi := le_trans hloDle hlohi
    have hhi_pos : 0 < hi := lt_of_lt_of_le hloDpos hloDhi
    -- (1) the split
    have hsplit := rhoMainLinear3 (rhoMainD Pz Delta) (fun n₁ => n₁.divisors)
      (fun _ _ => Finset.Icc 1 x) (fun c => ((c.divisors.card : ℝ)) ^ 2)
      (fun c n₁ d₁ s t => |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))|)
      C lo hi hC1 hlo hlohi
      (fun n₁ _ d₁ _ c _ t => by
        refine intervalIntegrable_div_of_bounded'
          (C := ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)
          one_pos hC1 ?_ ?_
        · exact (((measurable_Xpg_pair x Pz (c * n₁)).comp
            ((measurable_id.div_const (d₁ : ℝ)).prodMk measurable_const))).abs
        · intro s
          rw [abs_abs]
          exact abs_Xpg_le_massAll x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ)))
      (fun n₁ _ d₁ _ c _ => by
        refine rhoMainParamIntDiv
          (Φ := fun s t => |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))|)
          C lo hi (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)
          hC1 hlo hlohi ?_ ?_
        · exact (((measurable_Xpg_pair x Pz (c * n₁)).comp
            ((measurable_fst.div_const (d₁ : ℝ)).prodMk
              (measurable_snd.div_const (n₁ : ℝ))))).abs
        · intro s t
          rw [abs_abs]
          exact abs_Xpg_le_massAll x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ)))
    -- (2) the merge
    have hmerge := rhoMainLinear3 (rhoMainD Pz Delta) (fun n₁ => n₁.divisors)
      (fun _ _ => Finset.Icc 1 x) (fun c => ((c.divisors.card : ℝ)) ^ 2)
      (fun c n₁ _ s t => |Xpg x Pz (c * n₁) s t|)
      C (lo / Delta) hi hC1 hloDpos hloDhi
      (fun n₁ _ d₁ _ c _ t => by
        refine intervalIntegrable_div_of_bounded'
          (C := ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)
          one_pos hC1 ?_ ?_
        · exact (((measurable_Xpg_pair x Pz (c * n₁)).comp
            (measurable_id.prodMk measurable_const))).abs
        · intro s
          rw [abs_abs]
          exact abs_Xpg_le_massAll x Pz (c * n₁) s t)
      (fun n₁ _ d₁ _ c _ => by
        refine rhoMainParamIntDiv (Φ := fun s t => |Xpg x Pz (c * n₁) s t|)
          C (lo / Delta) hi
          (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)
          hC1 hloDpos hloDhi ?_ ?_
        · exact ((measurable_Xpg_pair x Pz (c * n₁))).abs
        · intro s t
          rw [abs_abs]
          exact abs_Xpg_le_massAll x Pz (c * n₁) s t)
    -- (3) the weight collapse `Σ_{d₁ | n₁} 1 = τ(n₁)`
    have hcollapse : ∀ u σ : ℝ,
        (∑ n₁ ∈ rhoMainD Pz Delta, ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
            ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|)
          = ∑ n₁ ∈ rhoMainD Pz Delta, ((n₁.divisors.card : ℝ)) *
              ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u| := by
      intro u σ
      refine Finset.sum_congr rfl (fun n₁ _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    -- (4) the value of the constant integral
    have hVenvnn : 0 ≤ rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) := by
      rw [rhoMainVenv]
      exact mul_nonneg
        (Real.rpow_nonneg (mul_nonneg (mul_nonneg hKA hAnn) (Real.rpow_nonneg hLpos.le _)) _)
        (Real.rpow_nonneg (mul_nonneg (mul_nonneg hC6 hAnn) (pow_nonneg hLpos.le 262144)) _)
    have hCnn : 0 ≤ Real.log C := Real.log_nonneg hC1
    have hIntVenv : (∫ σ in (1 : ℝ)..C,
          rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) / σ)
        = rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C := by
      rw [show (fun σ : ℝ => rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) / σ)
          = fun σ : ℝ => rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * σ⁻¹ from by
        funext σ; rw [div_eq_mul_inv]]
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hC1)]
      rw [div_one]
    have hVal : (∫ u in lo / Delta..hi,
          (∫ σ in (1 : ℝ)..C, rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) / σ) / u)
        = rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C
            * Real.log (hi / (lo / Delta)) := by
      rw [hIntVenv]
      rw [show (fun u : ℝ =>
            (rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C) / u)
          = fun u : ℝ =>
            (rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C) * u⁻¹ from by
        funext u; rw [div_eq_mul_inv]]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hloDpos hhi_pos]
    -- (5) the final numerical bookkeeping
    have hfin : rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C
          * Real.log (hi / (lo / Delta))
        ≤ 4 * KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
            * (Real.log (x : ℝ)) ^ (-(5 : ℤ)) := by
      have hnum := rhoMainNumeric KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) hKA hC6 hAnn hL1
      have hL2 : (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))
          = 4 * Real.log (x : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]; ring
      have hkey : Real.log (x : ℝ) ^ (2 : ℝ)
            * rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))
          = Real.log (x : ℝ) ^ (2 : ℝ)
              * (KA * AcountAtilC x * Real.log (x : ℝ) ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
              * (C₆ * AcountAtilC x * Real.log (x : ℝ) ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3) := by
        rw [rhoMainVenv]; ring
      have hRnn : 0 ≤ Real.log (hi / (lo / Delta)) :=
        Real.log_nonneg (by rw [le_div_iff₀ hloDpos]; simpa using hloDhi)
      calc rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C
            * Real.log (hi / (lo / Delta))
          ≤ rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))
              * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlogC hVenvnn) hlogR hRnn
              (mul_nonneg hVenvnn (by linarith))
        _ = 4 * (Real.log (x : ℝ) ^ (2 : ℝ)
              * rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))) := by
            rw [show rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))
                  * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))
                = rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))
                  * ((2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))) from by ring]
            rw [hL2]; ring
        _ = 4 * (Real.log (x : ℝ) ^ (2 : ℝ)
              * (KA * AcountAtilC x * Real.log (x : ℝ) ^ (-((2 : ℝ) ^ (26 : ℕ)))) ^ ((1 : ℝ) / 3)
              * (C₆ * AcountAtilC x * Real.log (x : ℝ) ^ (262144 : ℕ)) ^ ((2 : ℝ) / 3)) := by
            rw [hkey]
        _ ≤ 4 * (KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
              * (Real.log (x : ℝ)) ^ (-(5 : ℤ))) :=
            mul_le_mul_of_nonneg_left hnum (by norm_num)
        _ = 4 * KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
              * (Real.log (x : ℝ)) ^ (-(5 : ℤ)) := by ring
    -- (6) the monotonicity in `u` and then in `σ`
    have hmono : (∫ u in lo / Delta..hi,
          (∫ σ in (1 : ℝ)..C, (∑ n₁ ∈ rhoMainD Pz Delta,
              ((n₁.divisors.card : ℝ)) * ∑ c ∈ Finset.Icc 1 x,
                ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|) / σ) / u)
        ≤ ∫ u in lo / Delta..hi,
            (∫ σ in (1 : ℝ)..C, rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) / σ) / u := by
      refine intervalIntegral.integral_mono_on hloDhi ?_ ?_ ?_
      · refine rhoMainParamIntDiv
          (Φ := fun σ u => ∑ n₁ ∈ rhoMainD Pz Delta, ((n₁.divisors.card : ℝ)) *
            ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|)
          C (lo / Delta) hi (rhoMainMassSum x Pz (rhoMainD Pz Delta))
          hC1 hloDpos hloDhi ?_ ?_
        · refine Finset.measurable_sum _ (fun n₁ _ => ?_)
          refine Measurable.mul measurable_const ?_
          refine Finset.measurable_sum _ (fun c _ => ?_)
          exact ((measurable_Xpg_pair x Pz (c * n₁)).abs.const_mul _)
        · intro s t
          rw [abs_of_nonneg (Finset.sum_nonneg (fun n₁ _ =>
            mul_nonneg (by positivity) (Finset.sum_nonneg (fun c _ => by positivity))))]
          rw [rhoMainMassSum]
          exact Finset.sum_le_sum (fun n₁ _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun c _ =>
              mul_le_mul_of_nonneg_left (abs_Xpg_le_massAll x Pz (c * n₁) s t) (by positivity)))
            (by positivity))
      · rw [hIntVenv]
        exact integrable_const_div _ (mul_nonneg hVenvnn hCnn) hloDpos hloDhi
      · intro u hu
        refine div_le_div_of_nonneg_right ?_ (le_trans hloDpos.le hu.1)
        refine intervalIntegral.integral_mono_on hC1 ?_ ?_ ?_
        · refine intervalIntegrable_div_of_bounded'
            (C := rhoMainMassSum x Pz (rhoMainD Pz Delta)) one_pos hC1 ?_ ?_
          · refine Finset.measurable_sum _ (fun n₁ _ => ?_)
            refine Measurable.mul measurable_const ?_
            refine Finset.measurable_sum _ (fun c _ => ?_)
            exact (((measurable_Xpg_pair x Pz (c * n₁)).comp
              (measurable_id.prodMk measurable_const))).abs.const_mul _
          · intro σ
            rw [abs_of_nonneg (Finset.sum_nonneg (fun n₁ _ =>
              mul_nonneg (by positivity) (Finset.sum_nonneg (fun c _ => by positivity))))]
            rw [rhoMainMassSum]
            exact Finset.sum_le_sum (fun n₁ _ => mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun c _ =>
                mul_le_mul_of_nonneg_left (abs_Xpg_le_massAll x Pz (c * n₁) σ u) (by positivity)))
              (by positivity))
        · exact intervalIntegrable_div_of_bounded'
            (C := rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ))) one_pos hC1
            measurable_const (fun σ => le_of_eq (abs_of_nonneg hVenvnn))
        · intro σ hσ
          exact div_le_div_of_nonneg_right
            (rhoMainVenvBound x Pz Delta lo hi C KA C₆ hC1 hA hB hKA hC6 hL1 σ u
              hσ.1 hσ.2 hu.1 hu.2)
            (le_trans zero_le_one hσ.1)
    -- (7) the final chain
    calc (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, Wmain x Pz Delta s t / s) / t)
        = ∑ n₁ ∈ rhoMainD Pz Delta, ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
            ((c.divisors.card : ℝ)) ^ 2 *
              (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
                |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))| / s) / t) := by
          rw [show (fun t : ℝ => (∫ s in (1 : ℝ)..C, Wmain x Pz Delta s t / s) / t)
              = fun t : ℝ => (∫ s in (1 : ℝ)..C,
                  (∑ n₁ ∈ rhoMainD Pz Delta, ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
                    ((c.divisors.card : ℝ)) ^ 2 *
                      |Xpg x Pz (c * n₁) (s / (d₁ : ℝ)) (t / (n₁ : ℝ))|) / s) / t from by
            funext t
            congr 1
            congr 1
            funext s
            rw [Wmain_eq_three]]
          exact hsplit
      _ ≤ ∑ n₁ ∈ rhoMainD Pz Delta, ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
            ((c.divisors.card : ℝ)) ^ 2 *
              (∫ u in lo / Delta..hi, (∫ σ in (1 : ℝ)..C,
                |Xpg x Pz (c * n₁) σ u| / σ) / u) := by
          refine Finset.sum_le_sum (fun n₁ hn₁ => Finset.sum_le_sum (fun d₁ hd₁ =>
            Finset.sum_le_sum (fun c _ => ?_)))
          obtain ⟨hn₁dvd, hn₁le⟩ := Finset.mem_filter.mp hn₁
          have hn₁pos : 0 < n₁ := Nat.pos_of_mem_divisors hn₁dvd
          have hd₁pos : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
          exact mul_le_mul_of_nonneg_left
            (rhoMainPerTriple (fun σ u => |Xpg x Pz (c * n₁) σ u|) n₁ d₁ Delta lo hi C
              (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) * |atilc ((c * n₁) * n)|)
              (by exact_mod_cast hn₁pos) (by exact_mod_cast hd₁pos) hn₁le hC1 hlo hlohi
              (measurable_Xpg_pair x Pz (c * n₁)).abs
              (fun σ u => by rw [abs_abs]; exact abs_Xpg_le_massAll x Pz (c * n₁) σ u)
              (fun σ u => abs_nonneg _)
              (fun σ u hσ => by rw [Xpg_eq_zero_of_lt_one x Pz (c * n₁) σ u hσ, abs_zero]))
            (by positivity)
      _ = ∫ u in lo / Delta..hi, (∫ σ in (1 : ℝ)..C,
            (∑ n₁ ∈ rhoMainD Pz Delta, ∑ d₁ ∈ n₁.divisors, ∑ c ∈ Finset.Icc 1 x,
              ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|) / σ) / u :=
            hmerge.symm
      _ = ∫ u in lo / Delta..hi, (∫ σ in (1 : ℝ)..C,
            (∑ n₁ ∈ rhoMainD Pz Delta, ((n₁.divisors.card : ℝ)) *
              ∑ c ∈ Finset.Icc 1 x,
                ((c.divisors.card : ℝ)) ^ 2 * |Xpg x Pz (c * n₁) σ u|) / σ) / u := by
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          congr 1
          congr 1
          funext σ
          rw [hcollapse u σ]
      _ ≤ ∫ u in lo / Delta..hi,
            (∫ σ in (1 : ℝ)..C, rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) / σ) / u :=
            hmono
      _ = rhoMainVenv KA C₆ (AcountAtilC x) (Real.log (x : ℝ)) * Real.log C
            * Real.log (hi / (lo / Delta)) := hVal
      _ ≤ 4 * KA ^ ((1 : ℝ) / 3) * C₆ ^ ((2 : ℝ) / 3) * AcountAtilC x
            * (Real.log (x : ℝ)) ^ (-(5 : ℤ)) := hfin

end

end Work.FIChain
