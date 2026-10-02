import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzInSumAuxDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.KapDivEqProd

/-!
# Region II inner `t`-sum estimate (`czInSum`)

`czInSum w y N q r = Σ_{t ≤ czTmax} [t ⟂ r]·(μ(t)·t/κ(t))·⌊w/t⌋·czFII w y r t` and the claim is
`|czInSum + w·ζ(2)·κ(r)/r| ≤ C·w·σ_{-1/2}(r)·(Dc c (czTmax) + (czTmax/w)²)`.

With `A_t = ⌊w/t⌋`, `σ_t = czSv w t = log(A_t t/w)`, `L_t = czLv w y r t = log(czYv/t)`,
`czYv = w r/y`, one has `czFII w y r t = (σ_t−1)(σ_t+L_t−1)+1`, `t·A_t = w·e^{σ_t}` and hence
`A_t·czFII w y r t = w·((2−L_t) + czPhiv σ_t L_t)`.  This file proves the estimate from scratch
(no external inputs other than `KappaMertensInput` and Mathlib).
-/

set_option maxHeartbeats 4000000

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-! ## Elementary facts -/

private lemma kap_one_cz : Work.ZeroDensity.Jutila.kap 1 = 1 := by
  simp [Work.ZeroDensity.Jutila.kap]

private lemma Dc_zero_cz (c : ℝ) : Work.ZeroDensity.Jutila.Dc c 0 = 1 := by
  unfold Work.ZeroDensity.Jutila.Dc; simp

private lemma Dc_one_cz (c : ℝ) : Work.ZeroDensity.Jutila.Dc c 1 = 1 := by
  unfold Work.ZeroDensity.Jutila.Dc; simp

private lemma log_four_le_two_cz : Real.log 4 ≤ 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith only [this]
  linarith only [h, h2]

/-! ## The floor-correction factor `czPhiv` -/

/-- **`czPhiv` vanishes to second order.** For `|σ| ≤ 1`, `|czPhiv σ L| ≤ 7·σ²·(1+|L|)`. -/
theorem czPhiv_bound {σ L : ℝ} (hσ : |σ| ≤ 1) :
    |czPhiv σ L| ≤ 7 * σ ^ 2 * (1 + |L|) := by
  have hσ1 : σ ≤ 1 := (abs_le.mp hσ).2
  have hσm : -1 ≤ σ := (abs_le.mp hσ).1
  have hσabs : |σ| ≤ 1 := hσ
  have hsplit : czPhiv σ L
      = σ ^ 2 * (σ + L - 1) + (Real.exp σ - 1 - σ) * ((σ - 1) * (σ + L - 1) + 1) := by
    unfold czPhiv; ring
  rw [hsplit]
  have hsigL : |σ + L - 1| ≤ 2 + |L| := by
    have h1 : |σ + L - 1| ≤ |σ| + |L - 1| := by
      have e : σ + L - 1 = σ + (L - 1) := by ring
      rw [e]; exact abs_add_le σ (L-1)
    have h2 : |L - 1| ≤ |L| + 1 := by
      have h := abs_sub_le L 0 1
      simp only [sub_zero, zero_sub, abs_neg, abs_one] at h; linarith only [h]
    linarith only [hσabs, hσ, h1, h2]
  have hFb : |(σ - 1) * (σ + L - 1) + 1| ≤ 5 + 2 * |L| := by
    have h1 : |(σ-1)*(σ+L-1) + 1| ≤ |(σ-1)*(σ+L-1)| + 1 := by
      have := abs_add_le ((σ-1)*(σ+L-1)) 1; simpa using this
    have h2 : |(σ-1)*(σ+L-1)| = |σ-1| * |σ+L-1| := abs_mul _ _
    have h3 : |σ-1| ≤ 2 := by
      have h := abs_sub_le σ 0 1
      simp only [sub_zero, zero_sub, abs_neg, abs_one] at h; linarith only [hσabs, hσ, h]
    have h4 : |σ+L-1| ≤ 2 + |L| := hsigL
    have h5 : |σ-1| * |σ+L-1| ≤ 2 * (2 + |L|) :=
      mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    rw [h2] at h1; linarith only [h1, h5]
  have hA : |σ ^ 2 * (σ + L - 1)| ≤ σ ^ 2 * (2 + |L|) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg σ)]
    exact mul_le_mul_of_nonneg_left hsigL (sq_nonneg σ)
  have hB : |(Real.exp σ - 1 - σ) * ((σ - 1) * (σ + L - 1) + 1)| ≤ σ ^ 2 * (5 + 2 * |L|) := by
    rw [abs_mul]
    have he : |Real.exp σ - 1 - σ| ≤ σ ^ 2 := Real.abs_exp_sub_one_sub_id_le hσabs
    exact mul_le_mul he hFb (abs_nonneg _) (by positivity)
  calc |σ ^ 2 * (σ + L - 1) + (Real.exp σ - 1 - σ) * ((σ - 1) * (σ + L - 1) + 1)|
      ≤ |σ ^ 2 * (σ + L - 1)| + |(Real.exp σ - 1 - σ) * ((σ - 1) * (σ + L - 1) + 1)| :=
        abs_add_le _ _
    _ ≤ σ ^ 2 * (2 + |L|) + σ ^ 2 * (5 + 2 * |L|) := add_le_add hA hB
    _ = σ ^ 2 * (7 + 3 * |L|) := by ring
    _ ≤ 7 * σ ^ 2 * (1 + |L|) := by
        have hnn : 0 ≤ σ ^ 2 := sq_nonneg σ
        have : (7 : ℝ) + 3 * |L| ≤ 7 * (1 + |L|) := by linarith only [abs_nonneg L]
        nlinarith only [hnn, abs_nonneg L, this]

/-! ## Bounds on `kap` -/

/-- For squarefree `n`, `n ≤ kap n`. -/
lemma cz_kap_ge_self {n : ℕ} (hn : Squarefree n) : (n:ℝ) ≤ Work.ZeroDensity.Jutila.kap n := by
  have hprod : (∏ p ∈ n.primeFactors, (p:ℝ)) = (n:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  rw [Work.ZeroDensity.Jutila.kap, ← hprod]
  apply Finset.prod_le_prod₀
  · intro p hp; positivity
  · intro p hp; push_cast; linarith only []

/-- For squarefree `r`, `kap r / r ≤ σ_{-1/2}(r) = Σ_{d ∣ r} 1/√d`. -/
lemma cz_kap_div_le_sigma {r : ℕ} (hr : Squarefree r) :
    Work.ZeroDensity.Jutila.kap r / (r:ℝ) ≤ ∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ) := by
  have hr0 : r ≠ 0 := hr.ne_zero
  rw [KapDivEqProd r hr]
  have hstep1 : (∏ p ∈ r.primeFactors, ((p:ℝ)+1)/(p:ℝ))
      ≤ ∏ p ∈ r.primeFactors, (1 + 1/Real.sqrt (p:ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by
        have := Nat.prime_of_mem_primeFactors hp
        exact_mod_cast this.two_le
      positivity
    · intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith only [hp2]
      have hs0 : (0:ℝ) < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp0
      have hsle : Real.sqrt (p:ℝ) ≤ (p:ℝ) := by
        rw [Real.sqrt_le_left hp0.le]; nlinarith only [hp2]
      have hinv : 1/(p:ℝ) ≤ 1/Real.sqrt (p:ℝ) :=
        one_div_le_one_div_of_le hs0 hsle
      have hthis : ((p:ℝ)+1)/(p:ℝ) = 1 + 1/(p:ℝ) := by field_simp
      linarith only [hinv, hthis]
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) ↑r.primeFactors.powerset := by
    intro S hS T hT heq
    simp only at heq
    have hS' : S ⊆ r.primeFactors := Finset.mem_powerset.mp (Finset.mem_coe.mp hS)
    have hT' : T ⊆ r.primeFactors := Finset.mem_powerset.mp (Finset.mem_coe.mp hT)
    apply Finset.Subset.antisymm
    · intro a haS
      have hap : Nat.Prime a := Nat.prime_of_mem_primeFactors (hS' haS)
      have hdvd : a ∣ ∏ p ∈ T, p := by
        rw [← heq]
        exact Finset.dvd_prod_of_mem (fun p => p) haS
      obtain ⟨q, hqT, haq⟩ := (Prime.dvd_finsetProd_iff hap.prime (fun p => p)).mp hdvd
      have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors (hT' hqT)
      have haq' : a = q := ((Nat.Prime.dvd_iff_eq hqp hap.ne_one).mp haq).symm
      rw [haq']; exact hqT
    · intro a haT
      have hap : Nat.Prime a := Nat.prime_of_mem_primeFactors (hT' haT)
      have hdvd : a ∣ ∏ p ∈ S, p := by
        rw [heq]
        exact Finset.dvd_prod_of_mem (fun p => p) haT
      obtain ⟨q, hqS, haq⟩ := (Prime.dvd_finsetProd_iff hap.prime (fun p => p)).mp hdvd
      have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactors (hS' hqS)
      have haq' : a = q := ((Nat.Prime.dvd_iff_eq hqp hap.ne_one).mp haq).symm
      rw [haq']; exact hqS
  have hkey : (∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, 1/Real.sqrt (p:ℝ))
      = ∑ d ∈ r.primeFactors.powerset.image (fun S : Finset ℕ => ∏ p ∈ S, p),
          1/Real.sqrt (d:ℝ) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro S hS
    have hS' : S ⊆ r.primeFactors := Finset.mem_powerset.mp hS
    have hnn : ∀ p ∈ S, (0:ℝ) ≤ (p:ℝ) := by
      intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by
        have := Nat.prime_of_mem_primeFactors (hS' hp)
        exact_mod_cast this.two_le
      linarith only [hp2]
    rw [show (∏ p ∈ S, 1/Real.sqrt (p:ℝ)) = ∏ p ∈ S, (Real.sqrt (p:ℝ))⁻¹ by
          apply Finset.prod_congr rfl; intro p _; rw [one_div]]
    rw [Finset.prod_inv_distrib, ← Real.sqrt_prod S hnn, ← Nat.cast_prod, one_div]
  calc (∏ p ∈ r.primeFactors, ((p:ℝ)+1)/(p:ℝ))
      ≤ ∏ p ∈ r.primeFactors, (1 + 1/Real.sqrt (p:ℝ)) := hstep1
    _ = ∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, 1/Real.sqrt (p:ℝ) := by
        rw [Finset.prod_one_add]
    _ = ∑ d ∈ r.primeFactors.powerset.image (fun S : Finset ℕ => ∏ p ∈ S, p),
          1/Real.sqrt (d:ℝ) := hkey
    _ ≤ ∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_image] at hd
          obtain ⟨S, hS, rfl⟩ := hd
          rw [Nat.mem_divisors]
          refine ⟨?_, hr0⟩
          have hdvd : (∏ p ∈ S, p) ∣ ∏ p ∈ r.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset S r.primeFactors (fun p => p)
              (Finset.mem_powerset.mp hS)
          rwa [Nat.prod_primeFactors_of_squarefree hr] at hdvd
        · intro d hd _
          positivity


/-! ## The floor-defect `σ_t = czSv w t` -/

/-- **The floor defect is at most `2t/w`.**  For `0 < w`, `1 ≤ t`, `t ≤ w/2`,
`|czSv w t| ≤ 2t/w`. -/
theorem czSv_bound {w : ℝ} {t : ℕ} (hw : 0 < w) (ht1 : 1 ≤ t) (htw : (t:ℝ) ≤ w/2) :
    |czSv w t| ≤ 2 * (t:ℝ) / w := by
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hAle : ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) * (t:ℝ) ≤ w := by
    have h : ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) ≤ w/(t:ℝ) := Nat.floor_le (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h htpos.le
    rwa [div_mul_cancel₀ w (ne_of_gt htpos)] at h2
  have hAlt : w < ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) * (t:ℝ) + (t:ℝ) := by
    have h : w/(t:ℝ) < ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 := (div_lt_iff₀ htpos).mp h
    nlinarith only [h2]
  set ρ : ℝ := w - ((⌊w/(t:ℝ)⌋₊ : ℕ) : ℝ) * (t:ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith only [hAle]
  have hρt : ρ < (t:ℝ) := by rw [hρ]; linarith only [hAlt]
  have hratio : ((⌊w/(t:ℝ)⌋₊ : ℝ) * (t:ℝ))/w = 1 - ρ/w := by
    rw [hρ]; field_simp; ring
  unfold czSv
  rw [hratio]
  have hx0 : (0:ℝ) ≤ ρ/w := div_nonneg hρ0 hw.le
  have hx1 : ρ/w ≤ 1/2 := by rw [div_le_iff₀ hw]; linarith only [hρt, htw, hAlt]
  have h1x : (0:ℝ) < 1 - ρ/w := by linarith only [hx1]
  have hlog : Real.log (1 - ρ/w) ≤ 0 := Real.log_nonpos h1x.le (by linarith only [hx0])
  rw [abs_of_nonpos hlog, ← Real.log_inv]
  have hbound : Real.log (1 - ρ/w)⁻¹ ≤ (ρ/w)/(1 - ρ/w) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 - ρ/w)⁻¹ by positivity)
    have he : (1 - ρ/w)⁻¹ - 1 = (ρ/w)/(1 - ρ/w) := by
      rw [eq_div_iff (ne_of_gt h1x), sub_mul, inv_mul_cancel₀ (ne_of_gt h1x), one_mul]
      ring
    rwa [he] at h
  have h2 : (ρ/w)/(1 - ρ/w) ≤ 2*(ρ/w) := by
    rw [div_le_iff₀ h1x]; nlinarith only [hx0, hx1]
  have h4 : Real.log (1 - ρ/w)⁻¹ ≤ 2*(ρ/w) := le_trans hbound h2
  have h5 : 2*(ρ/w) ≤ 2*(t:ℝ)/w := by
    rw [show (2:ℝ)*(ρ/w) = 2*ρ/w by ring]
    exact div_le_div_of_nonneg_right (by linarith only [hρt, hAlt]) hw.le
  exact le_trans h4 h5

/-! ## The logarithmic sum -/

/-- For `1 ≤ T ≤ Y ≤ 2T+2`, `Σ_{t ≤ T} t·(1+|log(Y/t)|) ≤ 5·T²`. -/
theorem czLogSum : ∀ (T : ℕ) (Y : ℝ), 1 ≤ T → (T:ℝ) ≤ Y → Y ≤ 2*(T:ℝ)+2 →
    (∑ t ∈ Finset.Icc 1 T, (t:ℝ) * (1 + |Real.log (Y/(t:ℝ))|)) ≤ 5 * (T:ℝ)^2 := by
  intro T Y hT hTY hY2
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hYpos : 0 < Y := lt_of_lt_of_le hTpos hTY
  have hlog4 : Real.log (Y/(T:ℝ)) ≤ Real.log 4 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hTpos]
    nlinarith only [hY2, hTpos, (by exact_mod_cast hT : (1:ℝ) ≤ (T:ℝ)), hT]
  have hlog0 : 0 ≤ Real.log (Y/(T:ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hTpos, one_mul]; exact hTY)
  have hsumt : (∑ t ∈ Finset.Icc 1 T, (t:ℝ)) ≤ (T:ℝ)^2 := by
    calc (∑ t ∈ Finset.Icc 1 T, (t:ℝ))
        ≤ ∑ _t ∈ Finset.Icc 1 T, (T:ℝ) := Finset.sum_le_sum (fun t ht => by
              rw [Finset.mem_Icc] at ht; exact_mod_cast ht.2)
      _ = ((Finset.Icc 1 T).card : ℝ) * (T:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (T:ℝ) * (T:ℝ) := by rw [Nat.card_Icc]; simp
      _ = (T:ℝ)^2 := by ring
  have hpt : ∀ t ∈ Finset.Icc 1 T,
      (t:ℝ) * (1 + |Real.log (Y/(t:ℝ))|)
        ≤ (t:ℝ) * (1 + Real.log (Y/(T:ℝ))) + (t:ℝ) * (2 * Real.sqrt ((T:ℝ)/(t:ℝ))) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hlogabs : |Real.log (Y/(t:ℝ))| = Real.log (Y/(t:ℝ)) := by
      rw [abs_of_nonneg]
      apply Real.log_nonneg
      rw [le_div_iff₀ htpos, one_mul]
      exact le_trans (by exact_mod_cast ht.2) hTY
    rw [hlogabs]
    have hsplit : Real.log (Y/(t:ℝ)) = Real.log (Y/(T:ℝ)) + Real.log ((T:ℝ)/(t:ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    rw [hsplit]
    have hlogTt : Real.log ((T:ℝ)/(t:ℝ)) ≤ 2 * Real.sqrt ((T:ℝ)/(t:ℝ)) := by
      have h := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (T:ℝ)/(t:ℝ)) (by norm_num : (0:ℝ) < 1/2)
      have e : ((T:ℝ)/(t:ℝ))^(1/2:ℝ) / (1/2:ℝ) = 2 * Real.sqrt ((T:ℝ)/(t:ℝ)) := by
        rw [Real.sqrt_eq_rpow]; ring
      rwa [e] at h
    nlinarith only [htpos.le, mul_le_mul_of_nonneg_left hlogTt htpos.le, hlogTt, htpos]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib]
  have hA : (∑ t ∈ Finset.Icc 1 T, (t:ℝ) * (1 + Real.log (Y/(T:ℝ)))) ≤ 3*(T:ℝ)^2 := by
    have hc : (1 + Real.log (Y/(T:ℝ))) ≤ 3 := by linarith only [hlog4, log_four_le_two_cz]
    calc (∑ t ∈ Finset.Icc 1 T, (t:ℝ) * (1 + Real.log (Y/(T:ℝ))))
        ≤ ∑ t ∈ Finset.Icc 1 T, (t:ℝ) * 3 := Finset.sum_le_sum (fun t ht => by
              rw [Finset.mem_Icc] at ht
              exact mul_le_mul_of_nonneg_left hc (by positivity))
      _ = (∑ t ∈ Finset.Icc 1 T, (t:ℝ)) * 3 := by rw [Finset.sum_mul]
      _ ≤ (T:ℝ)^2 * 3 := mul_le_mul_of_nonneg_right hsumt (by norm_num)
      _ = 3*(T:ℝ)^2 := by ring
  have hB : (∑ t ∈ Finset.Icc 1 T, (t:ℝ) * (2 * Real.sqrt ((T:ℝ)/(t:ℝ)))) ≤ 2*(T:ℝ)^2 := by
    have hpt2 : ∀ t ∈ Finset.Icc 1 T,
        (t:ℝ) * (2 * Real.sqrt ((T:ℝ)/(t:ℝ))) ≤ 2 * Real.sqrt (T:ℝ) * Real.sqrt (t:ℝ) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
      have hs : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.mpr htpos
      have hsq : Real.sqrt (t:ℝ) * Real.sqrt (t:ℝ) = (t:ℝ) := by rw [← pow_two, Real.sq_sqrt htpos.le]
      rw [Real.sqrt_div (by positivity) (t:ℝ)]
      rw [show (t:ℝ) * (2 * (Real.sqrt (T:ℝ) / Real.sqrt (t:ℝ)))
            = (2 * Real.sqrt (T:ℝ) * (t:ℝ)) / Real.sqrt (t:ℝ) by ring]
      rw [div_le_iff₀ hs]
      nlinarith only [hsq, hs, Real.sqrt_pos.mpr hTpos, hTpos]
    refine le_trans (Finset.sum_le_sum hpt2) ?_
    rw [← Finset.mul_sum]
    have hsqrtle : (∑ t ∈ Finset.Icc 1 T, Real.sqrt (t:ℝ)) ≤ (T:ℝ) * Real.sqrt (T:ℝ) := by
      have hpt3 : ∀ t ∈ Finset.Icc 1 T, Real.sqrt (t:ℝ) ≤ Real.sqrt (T:ℝ) := by
        intro t ht; rw [Finset.mem_Icc] at ht
        exact Real.sqrt_le_sqrt (by exact_mod_cast ht.2)
      calc (∑ t ∈ Finset.Icc 1 T, Real.sqrt (t:ℝ))
          ≤ ∑ _t ∈ Finset.Icc 1 T, Real.sqrt (T:ℝ) := Finset.sum_le_sum hpt3
        _ = ((Finset.Icc 1 T).card : ℝ) * Real.sqrt (T:ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (T:ℝ) * Real.sqrt (T:ℝ) := by rw [Nat.card_Icc]; simp
    have hsqT : Real.sqrt (T:ℝ) * Real.sqrt (T:ℝ) = (T:ℝ) := by rw [← pow_two, Real.sq_sqrt hTpos.le]
    have hnn : (0:ℝ) ≤ 2 * Real.sqrt (T:ℝ) := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hsqrtle hnn, hsqT, hsqrtle, hnn]
  linarith only [hA, hB]

/-! ## The pointwise rewrite of a single `czInSum` summand -/

/-- **The summand of `czInSum` in the `(2−L)+Φ` form.**  With `A_t = ⌊w/t⌋`, `σ_t = czSv w t`,
`L_t = czLv w y r t` and `t·A_t = w·e^{σ_t}`, `A_t·czFII w y r t = w·((2−L_t) + czPhiv σ_t L_t)`. -/
theorem czTermRewrite {w y : ℝ} {r t : ℕ} (hw : 0 < w) (hy : 0 < y) (hr : 0 < (r:ℝ))
    (ht1 : 1 ≤ t) (htw : (t:ℝ) ≤ w/2) :
    (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) * (t:ℝ) / kap t else 0)
        * ((⌊w/(t:ℝ)⌋₊ : ℝ) * czFII w y r t)
      = (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ) / kap t else 0)
        * (w * ((2 - czLv w y r t) + czPhiv (czSv w t) (czLv w y r t))) := by
  have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hA0 : (0:ℝ) < (⌊w/(t:ℝ)⌋₊ : ℝ) := by
    have h : 1 ≤ ⌊w/(t:ℝ)⌋₊ := by
      rw [Nat.one_le_floor_iff]; rw [le_div_iff₀ htpos]; nlinarith only [htw, hw, htpos]
    exact_mod_cast (by omega : 0 < ⌊w/(t:ℝ)⌋₊)
  have hexp : Real.exp (czSv w t) = (⌊w/(t:ℝ)⌋₊ : ℝ) * (t:ℝ) / w := by
    rw [czSv, Real.exp_log]; positivity
  have hF : czFII w y r t
      = (czSv w t - 1) * (czSv w t + czLv w y r t - 1) + 1 := by
    unfold czFII
    have hlog : Real.log ((⌊w/(t:ℝ)⌋₊:ℝ) * (r:ℝ) / y)
        = czSv w t + czLv w y r t := by
      rw [czSv, czLv, czYv]
      rw [show (⌊w/(t:ℝ)⌋₊:ℝ) * (r:ℝ) / y
            = ((⌊w/(t:ℝ)⌋₊:ℝ) * (t:ℝ) / w) * (w * (r:ℝ) / y / (t:ℝ)) by
              field_simp]
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [hlog]; unfold czSv; ring
  have hR : w * ((2 - czLv w y r t) + czPhiv (czSv w t) (czLv w y r t))
      = w * Real.exp (czSv w t)
          * ((czSv w t - 1) * (czSv w t + czLv w y r t - 1) + 1) := by
    unfold czPhiv; ring
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc, if_pos hc, hR, hF, hexp]
    field_simp
  · rw [if_neg hc, if_neg hc]; ring


/-! ## Range facts for `czTmax` -/

/-- Elementary range facts controlling the `t`-sum of `czInSum`. -/
theorem czRangeFacts {w y : ℝ} {N q r : ℕ}
    (hw : 1 ≤ w) (hwy : w ≤ y) (hN : (N:ℝ) < w*y) (hr1 : 1 ≤ r) (hr : r ≤ czR w N q) :
    1 ≤ q ∧ (0:ℝ) < w ∧ (0:ℝ) < y ∧ (r:ℝ) < y ∧ 1 ≤ ⌊y/(r:ℝ)⌋₊ ∧
    ((czTmax w y N q r : ℕ) : ℝ) ≤ w / (((⌊y/(r:ℝ)⌋₊:ℕ):ℝ) + 1) ∧
    ((czTmax w y N q r : ℕ) : ℝ) ≤ czYv w y r ∧
    (1 ≤ czTmax w y N q r → czYv w y r ≤ 2*((czTmax w y N q r : ℕ):ℝ) + 2) ∧
    (∀ t ∈ Finset.Icc 1 (czTmax w y N q r), (t:ℝ) ≤ w/2 ∧ (1:ℕ) ≤ ⌊w/(t:ℝ)⌋₊) := by
  have hw0 : (0:ℝ) < w := by linarith only [hw]
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le hw0 hwy
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exfalso
      subst hq
      have hz : czR w N 0 = 0 := by unfold czR; simp
      omega
    · exact hq
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hry : (r:ℝ) < y := by
    have hrR : (r:ℝ) ≤ (czR w N q : ℝ) := by exact_mod_cast hr
    have hczR : (czR w N q : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
      rw [czR]; exact Nat.floor_le (by positivity)
    have h1 : (N:ℝ)/((q:ℝ)*w) < y/(q:ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hN, hqR, hw0]
    have h2 : y/(q:ℝ) ≤ y := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ))]
      nlinarith only [hqR, hy0, hw, hwy]
    linarith only [hrR, hczR, h1, h2]
  set m : ℕ := ⌊y/(r:ℝ)⌋₊ with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_floor_iff, le_div_iff₀ hrpos]
    linarith only [hry.le, hry]
  have hTle1 : ((czTmax w y N q r : ℕ) : ℝ) ≤ w / (((m:ℕ):ℝ) + 1) := by
    have hmin : ((czTmax w y N q r : ℕ) : ℝ)
        ≤ (⌊w / (((m:ℕ):ℝ) + 1)⌋₊ : ℝ) := by
      unfold czTmax
      rw [← hm]
      exact_mod_cast Nat.min_le_right _ _
    exact le_trans hmin (Nat.floor_le (by positivity))
  have hTleY : ((czTmax w y N q r : ℕ) : ℝ) ≤ czYv w y r := by
    refine le_trans hTle1 ?_
    unfold czYv
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1) hy0]
    have hlt : y/(r:ℝ) < (m:ℝ) + 1 := by rw [hm]; exact Nat.lt_floor_add_one _
    have hyr : y < (r:ℝ) * ((m:ℝ)+1) := by
      have hh := (div_lt_iff₀ hrpos).mp hlt
      linarith only [hh]
    nlinarith only [hyr, hw0, hw]
  have hrqw : (r:ℝ)*(q:ℝ)*w ≤ (N:ℝ) := by
    have hrR : (r:ℝ) ≤ (czR w N q : ℝ) := by exact_mod_cast hr
    have hczR : (czR w N q : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
      rw [czR]; exact Nat.floor_le (by positivity)
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*w)).mp (le_trans hrR hczR)
    nlinarith only [hh]
  have hhalf : ((czTmax w y N q r : ℕ) : ℝ) ≤ w/2 := by
    refine le_trans hTle1 ?_
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1) (by norm_num : (0:ℝ) < 2)]
    nlinarith only [hw0, (by exact_mod_cast hm1 : (1:ℝ) ≤ (m:ℝ)), hm1, hw]
  have hYle2T : (1 ≤ czTmax w y N q r) → czYv w y r ≤ 2*((czTmax w y N q r : ℕ):ℝ) + 2 := by
    intro _
    by_cases hcase : czT y N q ≤ ⌊w / (((m:ℕ):ℝ) + 1)⌋₊
    · have hTm : ((czTmax w y N q r : ℕ):ℝ) = (czT y N q : ℝ) := by
        unfold czTmax; rw [← hm, min_eq_left hcase]
      rw [hTm]
      have hczT : czYv w y r - 1 ≤ (czT y N q : ℝ) := by
        have hfl : (N:ℝ)/((q:ℝ)*y) < (czT y N q : ℝ) + 1 := by
          rw [czT]; exact Nat.lt_floor_add_one _
        have hge : czYv w y r ≤ (N:ℝ)/((q:ℝ)*y) := by
          unfold czYv
          rw [div_le_div_iff₀ hy0 (by positivity : (0:ℝ) < (q:ℝ)*y)]
          nlinarith only [hrqw, hy0, hw, hwy]
        linarith only [hfl, hge]
      linarith only [hTm, hczT]
    · push_neg at hcase
      have hTm : ((czTmax w y N q r : ℕ):ℝ) = (⌊w / (((m:ℕ):ℝ) + 1)⌋₊ : ℝ) := by
        unfold czTmax; rw [← hm, min_eq_right hcase.le]
      rw [hTm]
      have hm1le : (r:ℝ) * ((m:ℝ)+1) ≤ 2*y := by
        have hle : (m:ℝ) ≤ y/(r:ℝ) := by rw [hm]; exact Nat.floor_le (by positivity)
        have hrm : (r:ℝ) * (m:ℝ) ≤ y := by
          have hh := (le_div_iff₀ hrpos).mp hle
          linarith only [hh]
        nlinarith only [hrm, hry.le, hry]
      have hY_half : czYv w y r / 2 ≤ w / (((m:ℕ):ℝ) + 1) := by
        unfold czYv
        rw [show w * (r:ℝ) / y / 2 = w * (r:ℝ) / (2*y) by ring]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*y), div_mul_eq_mul_div,
            le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ)+1)]
        nlinarith only [hm1le, hw0, hw]
      have hfloor2 : w / (((m:ℕ):ℝ)+1)
          < (⌊w / (((m:ℕ):ℝ) + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      linarith only [hY_half, hfloor2]
  refine ⟨hq1, hw0, hy0, hry, hm1, ?_, hTleY, hYle2T, ?_⟩
  · simpa using hTle1
  · intro t ht
    rw [Finset.mem_Icc] at ht
    have htT : (t:ℝ) ≤ (czTmax w y N q r : ℝ) := by exact_mod_cast ht.2
    have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
    have ht2 : (t:ℝ) ≤ w/2 := le_trans htT hhalf
    refine ⟨ht2, ?_⟩
    rw [Nat.one_le_floor_iff, le_div_iff₀ htpos]
    linarith only [ht2, hw0, htpos, hw, hhalf, htT]


/-- **Region II inner `t`-sum estimate.** -/
theorem CzInSumBound2Here (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (w y : ℝ) (N q r : ℕ), 1 ≤ w → w ≤ y → (N:ℝ) < w*y →
    Squarefree r → 1 ≤ r → r ≤ Work.ZeroDensity.Jutila.czR w N q →
    |Work.ZeroDensity.Jutila.BzCross.czInSum w y N q r
        + w * (Real.pi^2/6) * (Work.ZeroDensity.Jutila.kap r / r)|
      ≤ C * w * (∑ d ∈ r.divisors, 1/Real.sqrt d) *
          (Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r)
            + ((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ)/w)^2) := by
  obtain ⟨C0, c0, hC0, hc0, hcl1, hcl2⟩ := h
  refine ⟨max (2*C0) 140 + (7*(1+Real.log 4) + Real.pi^2/6 + 3), c0, ?_, hc0, ?_⟩
  · have hp2 : (0:ℝ) < Real.pi^2/6 := by have := Real.pi_pos; positivity
    have hl := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    have h1 : (0:ℝ) < max (2*C0) 140 := lt_max_of_lt_left (by linarith only [hC0])
    linarith only [hp2, hl, h1]
  · intro w y N q r hw hwy hNwy hsf hr1 hrR
    set K : ℝ := max (2*C0) 140 + (7*(1+Real.log 4) + Real.pi^2/6 + 3) with hKdef
    have hCnum : (0:ℝ) ≤ 7*(1+Real.log 4) + Real.pi^2/6 + 3 := by
      have hl := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
      have hp2 : (0:ℝ) < Real.pi^2/6 := by have := Real.pi_pos; positivity
      linarith only [hl, hp2]
    have hKpos : 0 < K := by
      rw [hKdef]
      have h : (0:ℝ) < max (2*C0) 140 := lt_max_of_lt_left (show (0:ℝ) < 2*C0 by linarith only [hC0])
      linarith only [hCnum, h]
    have hK2C0 : 2*C0 ≤ K := by
      rw [hKdef]; have := le_max_left (2*C0) 140; linarith only [hCnum, this]
    have hK140 : (140:ℝ) ≤ K := by
      rw [hKdef]; have := le_max_right (2*C0) 140; linarith only [hCnum, this]
    have hKsmall : 2 + 7*(1+Real.log 4) + Real.pi^2/6 ≤ K := by
      rw [hKdef]; have := le_max_left (2*C0) 140; linarith only [hC0, this]
    obtain ⟨hq1, hw0, hy0, hry, hm1, hTle1, hTleY, hYle2T, ht_range⟩ :=
      czRangeFacts hw hwy hNwy hr1 hrR
    have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    set σr : ℝ := ∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ) with hσr
    have hσr1 : 1 ≤ σr := by
      rw [hσr]
      have h1 : (1:ℕ) ∈ r.divisors := Nat.one_mem_divisors.mpr (by omega)
      have hs := Finset.single_le_sum (s := r.divisors) (f := fun d : ℕ => 1/Real.sqrt (d:ℝ))
              (fun i _ => div_nonneg zero_le_one (Real.sqrt_nonneg _)) h1
      rwa [Nat.cast_one, Real.sqrt_one, div_one] at hs
    have hσr0 : 0 ≤ σr := le_trans zero_le_one hσr1
    have hkapnn : (0:ℝ) ≤ Work.ZeroDensity.Jutila.kap r/(r:ℝ) := div_nonneg (kap_pos r).le hrpos.le
    have hpinn : (0:ℝ) ≤ Real.pi^2/6 := by positivity
    have hcc : ∀ (s : ℕ) (a : ℝ),
        (if Nat.Coprime r s then a else 0) = (if Nat.Coprime s r then a else 0) := by
      intro s a; by_cases h : Nat.Coprime r s
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    have hsum : czInSum w y N q r
        = ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
            (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
              * (w * ((2 - czLv w y r t) + czPhiv (czSv w t) (czLv w y r t))) := by
      unfold czInSum
      apply Finset.sum_congr rfl
      intro t ht
      exact czTermRewrite hw0 hy0 hrpos (Finset.mem_Icc.mp ht).1 (ht_range t ht).1
    set S2 : ℝ := ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (2 - czLv w y r t) with hS2
    set Sp : ℝ := ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * czPhiv (czSv w t) (czLv w y r t) with hSp
    have hcidecomp : czInSum w y N q r = w*S2 + w*Sp := by
      rw [hsum, hS2, hSp, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht; ring
    rw [hcidecomp]
    rcases lt_or_ge (czTmax w y N q r) 2 with hTlt | hTge
    · -- small case: T ≤ 1
      have hkap : Work.ZeroDensity.Jutila.kap r / (r:ℝ) ≤ σr := by
        rw [hσr]; exact cz_kap_div_le_sigma hsf
      rw [← hcidecomp]
      have hsmall : |czInSum w y N q r + w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ))|
          ≤ w*(2 + 7*(1+Real.log 4)) + w*(Real.pi^2/6)*σr := by
        rcases Nat.eq_zero_or_pos (czTmax w y N q r) with hT0 | hTpos
        · have hcz0 : czInSum w y N q r = 0 := by rw [hsum, hT0]; simp
          have habs : |(0:ℝ) + w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ))|
              = w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ)) := by
            rw [zero_add, abs_of_nonneg (mul_nonneg (mul_nonneg hw0.le hpinn) hkapnn)]
          rw [hcz0, habs]
          have h1 : w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ)) ≤ w*(Real.pi^2/6)*σr :=
            mul_le_mul_of_nonneg_left hkap (mul_nonneg hw0.le hpinn)
          have h2 : (0:ℝ) ≤ w*(2 + 7*(1+Real.log 4)) := by
            apply mul_nonneg hw0.le
            have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith only [this]
          linarith only [h1, h2]
        · have hT1 : czTmax w y N q r = 1 := by omega
          have hY1 : (1:ℝ) ≤ czYv w y r := by
            have h := hTleY; rw [hT1] at h; simpa using h
          have hY2 : czYv w y r ≤ 4 := by
            have h := hYle2T (by omega); rw [hT1] at h; norm_num at h; linarith only [h]
          have hL10 : 0 ≤ czLv w y r 1 := by
            unfold czLv; simp only [Nat.cast_one, div_one]; exact Real.log_nonneg hY1
          have hL1log : czLv w y r 1 ≤ Real.log 4 := by
            unfold czLv; simp only [Nat.cast_one, div_one]
            exact Real.log_le_log (by linarith only [hY1]) hY2
          have hL12 : |2 - czLv w y r 1| ≤ 2 := by
            rw [abs_le]
            exact ⟨by linarith only [hL1log, log_four_le_two_cz, hL10], by linarith only [hL10]⟩
          have hw2 : (1:ℝ) ≤ w/2 := by
            have h := (ht_range 1 (by rw [hT1]; exact Finset.mem_Icc.mpr ⟨le_refl 1, le_refl 1⟩)).1
            simpa using h
          have hσ1 : |czSv w 1| ≤ 1 := by
            have hb : |czSv w 1| ≤ 2*(1:ℝ)/w := by
              have hw2' : (((1:ℕ)):ℝ) ≤ w/2 := by simpa using hw2
              have := czSv_bound hw0 le_rfl hw2'; simpa using this
            have h2w : 2*(1:ℝ)/w ≤ 1 := by rw [div_le_iff₀ hw0]; linarith only [hw2]
            linarith only [hb, h2w]
          have hΦ1 : |czPhiv (czSv w 1) (czLv w y r 1)| ≤ 7*(1+Real.log 4) := by
            have hb := czPhiv_bound (L := czLv w y r 1) hσ1
            have hsq : (czSv w 1)^2 ≤ 1 := by
              rw [pow_two]
              nlinarith only [hσ1, abs_nonneg (czSv w 1), sq_abs (czSv w 1)]
            have hLb : 1 + |czLv w y r 1| ≤ 1 + Real.log 4 := by
              rw [abs_of_nonneg hL10]; linarith only [hL1log]
            nlinarith only [hb, hsq, hLb, sq_nonneg (czSv w 1), abs_nonneg (czLv w y r 1), hL10, hL1log]
          have hterm : czInSum w y N q r
              = w*((2 - czLv w y r 1) + czPhiv (czSv w 1) (czLv w y r 1)) := by
            rw [hsum, hT1, Finset.Icc_self, Finset.sum_singleton]
            rw [if_pos (Nat.coprime_one_right r), ArithmeticFunction.moebius_apply_one, kap_one_cz]
            norm_num
          have hczsum : |czInSum w y N q r| ≤ w*(2 + 7*(1+Real.log 4)) := by
            rw [hterm, abs_mul, abs_of_pos hw0]
            have hbr : |(2 - czLv w y r 1) + czPhiv (czSv w 1) (czLv w y r 1)|
                ≤ 2 + 7*(1+Real.log 4) := by
              have := abs_add_le (2 - czLv w y r 1) (czPhiv (czSv w 1) (czLv w y r 1))
              linarith only [this, hL12, hΦ1]
            exact mul_le_mul_of_nonneg_left hbr hw0.le
          have hwm : |w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ))| ≤ w*(Real.pi^2/6)*σr := by
            rw [abs_of_nonneg (mul_nonneg (mul_nonneg hw0.le hpinn) hkapnn)]
            exact mul_le_mul_of_nonneg_left hkap (mul_nonneg hw0.le hpinn)
          have htri := abs_add_le (czInSum w y N q r) (w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ)))
          linarith only [htri, hczsum, hwm]
      have hDcge : 1 ≤ Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)
          + ((czTmax w y N q r : ℝ)/w)^2 := by
        rcases Nat.eq_zero_or_pos (czTmax w y N q r) with hT0 | hTpos
        · rw [hT0, Dc_zero_cz]; simp
        · have hT1 : czTmax w y N q r = 1 := by omega
          rw [hT1, Dc_one_cz]
          nlinarith only [sq_nonneg (((1:ℕ):ℝ)/w)]
      have hRHSge : K*w*σr ≤ K*w*σr*(Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)
          + ((czTmax w y N q r:ℝ)/w)^2) := by
        have hnn : 0 ≤ K*w*σr := mul_nonneg (mul_nonneg hKpos.le hw0.le) hσr0
        nlinarith only [hnn, hDcge]
      have hfin : w*(2 + 7*(1+Real.log 4)) + w*(Real.pi^2/6)*σr ≤ K*w*σr := by
        have h1 : w*(2 + 7*(1+Real.log 4)) ≤ w*σr*(2 + 7*(1+Real.log 4)) := by
          have hle : w ≤ w*σr := by nlinarith only [hw0, hσr1, hw]
          have hnn : (0:ℝ) ≤ 2 + 7*(1+Real.log 4) := by
            have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num); linarith only [this]
          calc w*(2 + 7*(1+Real.log 4)) = (2 + 7*(1+Real.log 4))*w := by ring
            _ ≤ (2 + 7*(1+Real.log 4))*(w*σr) := mul_le_mul_of_nonneg_left hle hnn
            _ = w*σr*(2 + 7*(1+Real.log 4)) := by ring
        have h2 : w*(Real.pi^2/6)*σr = w*σr*(Real.pi^2/6) := by ring
        have h3 : w*σr*(2 + 7*(1+Real.log 4)) + w*σr*(Real.pi^2/6)
            = w*σr*(2 + 7*(1+Real.log 4) + Real.pi^2/6) := by ring
        have h4 : w*σr*(2 + 7*(1+Real.log 4) + Real.pi^2/6) ≤ w*σr*K :=
          mul_le_mul_of_nonneg_left hKsmall (mul_nonneg hw0.le hσr0)
        have h5 : w*σr*K = K*w*σr := by ring
        linarith only [h1, h2, h3, h4, h5]
      linarith only [hsmall, hfin, hRHSge]
    · -- main case: T ≥ 2
      have hT1' : 1 ≤ czTmax w y N q r := by omega
      have hT2pos : (0:ℝ) < (czTmax w y N q r : ℝ) := by
        exact_mod_cast (by omega : 0 < czTmax w y N q r)
      have hctb : ∀ t : ℕ, |(if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)|
          ≤ (if Squarefree t then 1/kap t else 0) := by
        intro t
        by_cases h : Nat.Coprime r t
        · rw [if_pos h]
          by_cases hs : Squarefree t
          · rw [if_pos hs, abs_div, abs_of_pos (kap_pos t)]
            refine div_le_div_of_nonneg_right ?_ (kap_pos t).le
            have hm : |(ArithmeticFunction.moebius t : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
            have hm' : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
              rw [← Int.cast_abs]; exact_mod_cast hm
            exact hm'
          · rw [if_neg hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; simp
        · rw [if_neg h]
          by_cases hs : Squarefree t
          · rw [if_pos hs, abs_zero]; exact div_nonneg zero_le_one (kap_pos t).le
          · rw [if_neg hs]; simp
      have hSc_bound : |∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
            (if Nat.Coprime t r then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)|
          ≤ C0 * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
        have h := hcl2 r (czTmax w y N q r) hsf hTge
        rw [hσr]
        exact h
      have hSc_bound' : |∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
            (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)|
          ≤ C0 * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
        have he : (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0))
            = (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime t r then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)) :=
          Finset.sum_congr rfl (fun t ht => hcc t _)
        rw [he]; exact hSc_bound
      have hM_bound : |(∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (czLv w y r t - 1))
            - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
            - Real.log (czYv w y r / (czTmax w y N q r : ℝ))
              * (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                  (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0))|
          ≤ C0 * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
        have h := hcl1 r (czTmax w y N q r) (czYv w y r) hsf hTge hTleY
        have he1 : (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (czLv w y r t - 1))
            = (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime t r then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (Real.log (czYv w y r / (t:ℝ)) - 1)) := by
          apply Finset.sum_congr rfl; intro t ht
          rw [hcc t _]; rfl
        have he2 : (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0))
            = (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime t r then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)) :=
          Finset.sum_congr rfl (fun t ht => hcc t _)
        rw [he1, he2, hσr]
        exact h
      have hS2_eq : S2 = (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0))
          - (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (czLv w y r t - 1)) := by
        rw [hS2, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro t ht; ring
      have hSp_bound : w * |Sp| ≤ 140*(czTmax w y N q r : ℝ)^2/w := by
        rw [hSp]
        have hstep : ∀ t ∈ Finset.Icc 1 (czTmax w y N q r),
            |(if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * czPhiv (czSv w t) (czLv w y r t)|
              ≤ (if Squarefree t then 1/kap t else 0) * (7 * (2*(t:ℝ)/w)^2 * (1 + czLv w y r t)) := by
          intro t ht
          obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
          have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
          have htw : (t:ℝ) ≤ w/2 := (ht_range t ht).1
          have hL0 : 0 ≤ czLv w y r t := by
            unfold czLv; apply Real.log_nonneg; rw [le_div_iff₀ htpos]
            have h1 : (t:ℝ) ≤ (czTmax w y N q r:ℝ) := by exact_mod_cast htT
            linarith only [h1, hTleY]
          have hσb : |czSv w t| ≤ 1 := by
            have hb := czSv_bound hw0 ht1 htw
            have h2 : 2*(t:ℝ)/w ≤ 1 := by rw [div_le_iff₀ hw0]; linarith only [htw]
            linarith only [hb, h2]
          have hΦ := czPhiv_bound (L := czLv w y r t) hσb
          have hcs : (czSv w t)^2 ≤ (2*(t:ℝ)/w)^2 := by
            rw [pow_two, pow_two]
            have h2 := czSv_bound hw0 ht1 htw
            nlinarith only [h2, abs_nonneg (czSv w t), sq_abs (czSv w t), sq_nonneg (czSv w t)]
          calc |(if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                  * czPhiv (czSv w t) (czLv w y r t)|
              = |(if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)|
                  * |czPhiv (czSv w t) (czLv w y r t)| := abs_mul _ _
            _ ≤ (if Squarefree t then 1/kap t else 0) * (7*(czSv w t)^2*(1+|czLv w y r t|)) :=
                (by
                  have hctnn : (0:ℝ) ≤ (if Squarefree t then 1/kap t else 0) := by
                    by_cases hs : Squarefree t
                    · rw [if_pos hs]; exact div_nonneg zero_le_one (kap_pos t).le
                    · simp [hs]
                  exact mul_le_mul (hctb t) hΦ (abs_nonneg _) hctnn)
            _ = (if Squarefree t then 1/kap t else 0) * (7*(czSv w t)^2*(1+czLv w y r t)) := by
                rw [abs_of_nonneg hL0]
            _ ≤ (if Squarefree t then 1/kap t else 0) * (7*(2*(t:ℝ)/w)^2*(1+czLv w y r t)) := by
                have hctnn : (0:ℝ) ≤ (if Squarefree t then 1/kap t else 0) := by
                  by_cases hs : Squarefree t
                  · rw [if_pos hs]; exact div_nonneg zero_le_one (kap_pos t).le
                  · simp [hs]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcs (by norm_num)) (by linarith only [hL0])) hctnn
        calc w * |∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                  * czPhiv (czSv w t) (czLv w y r t)|
            ≤ w * (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                |(if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                  * czPhiv (czSv w t) (czLv w y r t)|) :=
                mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw0.le
          _ ≤ w * (∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                (if Squarefree t then 1/kap t else 0) * (7 * (2*(t:ℝ)/w)^2 * (1 + czLv w y r t))) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hw0.le
          _ = ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                w * ((if Squarefree t then 1/kap t else 0) * (7 * (2*(t:ℝ)/w)^2 * (1 + czLv w y r t))) := by
                rw [Finset.mul_sum]
          _ ≤ ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
                (28/w) * ((t:ℝ) * (1 + czLv w y r t)) := by
                apply Finset.sum_le_sum; intro t ht
                obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
                have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
                have hL0 : 0 ≤ czLv w y r t := by
                  unfold czLv; apply Real.log_nonneg; rw [le_div_iff₀ htpos]
                  have h1 : (t:ℝ) ≤ (czTmax w y N q r:ℝ) := by exact_mod_cast htT
                  linarith only [h1, hTleY]
                by_cases hs : Squarefree t
                · rw [if_pos hs]
                  have hk : (t:ℝ) ≤ kap t := cz_kap_ge_self hs
                  have heq : w * ((1/kap t) * (7*(2*(t:ℝ)/w)^2*(1+czLv w y r t)))
                      = (28/w) * ((1/kap t)*(t:ℝ)^2*(1+czLv w y r t)) := by field_simp; ring
                  rw [heq]
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  have he : (1/kap t)*(t:ℝ)^2 = (t:ℝ)^2/kap t := by ring
                  rw [he]
                  have hk' : (t:ℝ)^2/kap t ≤ (t:ℝ) := by
                    rw [div_le_iff₀ (kap_pos t)]; nlinarith only [hk, htpos]
                  exact mul_le_mul_of_nonneg_right hk' (by linarith only [hL0])
                · rw [if_neg hs]
                  simp only [zero_mul, mul_zero]
                  exact mul_nonneg (by positivity) (mul_nonneg htpos.le (by linarith only [hL0]))
          _ = (28/w) * (∑ t ∈ Finset.Icc 1 (czTmax w y N q r), (t:ℝ) * (1 + czLv w y r t)) := by
                rw [Finset.mul_sum]
          _ ≤ (28/w) * (5 * (czTmax w y N q r : ℝ)^2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                refine le_trans (Finset.sum_le_sum (fun t ht => ?_))
                  (czLogSum (czTmax w y N q r) (czYv w y r) hT1' hTleY (hYle2T hT1'))
                obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
                have htpos : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
                have hL0 : 0 ≤ czLv w y r t := by
                  unfold czLv; apply Real.log_nonneg; rw [le_div_iff₀ htpos]
                  have h1 : (t:ℝ) ≤ (czTmax w y N q r:ℝ) := by exact_mod_cast htT
                  linarith only [h1, hTleY]
                have hle : czLv w y r t ≤ |Real.log (czYv w y r/(t:ℝ))| := by
                  rw [show Real.log (czYv w y r/(t:ℝ)) = czLv w y r t from rfl, abs_of_nonneg hL0]
                exact mul_le_mul_of_nonneg_left (by linarith only [hle]) htpos.le
          _ = 140*(czTmax w y N q r : ℝ)^2/w := by ring
      have hS2_bound : |S2 + (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))|
          ≤ 2*C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
        set Sc := ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0) with hScdef
        set M := ∑ t ∈ Finset.Icc 1 (czTmax w y N q r),
              (if Nat.Coprime r t then (ArithmeticFunction.moebius t : ℝ)/kap t else 0)
                * (czLv w y r t - 1) with hMdef
        have hSc_b : |Sc| ≤ C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
          rw [hScdef]; exact hSc_bound'
        have hM_b : |M - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
            - Real.log (czYv w y r / (czTmax w y N q r : ℝ))*Sc|
            ≤ C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
          rw [hScdef, hMdef]; exact hM_bound
        have hS2e : S2 = Sc - M := by rw [hS2_eq, hScdef, hMdef]
        rw [hS2e]
        have hYT1 : 0 ≤ Real.log (czYv w y r / (czTmax w y N q r : ℝ)) := by
          apply Real.log_nonneg; rw [le_div_iff₀ hT2pos]; linarith only [hTleY]
        have hYT2 : Real.log (czYv w y r / (czTmax w y N q r : ℝ)) ≤ 2 := by
          have h : Real.log (czYv w y r / (czTmax w y N q r : ℝ)) ≤ Real.log 4 :=
            Real.log_le_log (by unfold czYv; positivity)
              (show czYv w y r / (czTmax w y N q r : ℝ) ≤ 4 by
                rw [div_le_iff₀ hT2pos]
                have h1 : czYv w y r ≤ 2*(czTmax w y N q r : ℝ) + 2 := hYle2T hT1'
                have h2 : (1:ℝ) ≤ (czTmax w y N q r : ℝ) := by exact_mod_cast hT1'
                linarith only [h1, h2])
          linarith only [h, log_four_le_two_cz]
        have he : (Sc - M) + (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
            = Sc*(1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ)))
              - (M - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
                  - Real.log (czYv w y r / (czTmax w y N q r : ℝ))*Sc) := by ring
        rw [he]
        have hsplit : |Sc*(1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ)))
              - (M - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
                  - Real.log (czYv w y r / (czTmax w y N q r : ℝ))*Sc)|
            ≤ |Sc*(1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ)))|
              + |M - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ))
                  - Real.log (czYv w y r / (czTmax w y N q r : ℝ))*Sc| := by
          have := abs_add_le (Sc*(1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ))))
            (-(M - (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r / (r:ℝ)) - Real.log (czYv w y r / (czTmax w y N q r : ℝ))*Sc))
          rwa [sub_eq_add_neg, abs_neg] at this
        refine le_trans hsplit ?_
        have h1 : |Sc*(1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ)))| ≤ |Sc| := by
          rw [abs_mul]
          have : |1 - Real.log (czYv w y r / (czTmax w y N q r : ℝ))| ≤ 1 := by
            rw [abs_le]; exact ⟨by linarith only [hYT2], by linarith only [hYT1]⟩
          nlinarith only [abs_nonneg Sc, this]
        have hdd : 0 ≤ C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) :=
          mul_nonneg (mul_nonneg hC0.le hσr0) (Work.ZeroDensity.Jutila.Dc_pos c0 _).le
        linarith only [h1, hM_b, hSc_b, hdd, hSc_bound', hM_bound]
      have heq : w*S2 + w*Sp + w*(Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ))
          = w*(S2 + (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ))) + w*Sp := by ring
      rw [heq]
      refine le_trans (abs_add_le _ _) ?_
      have h1 : |w*(S2 + (Real.pi^2/6)*(Work.ZeroDensity.Jutila.kap r/(r:ℝ)))|
          ≤ w * (2*C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)) := by
        rw [abs_mul, abs_of_pos hw0]
        exact mul_le_mul_of_nonneg_left hS2_bound hw0.le
      have h2 : |w*Sp| ≤ 140*(czTmax w y N q r : ℝ)^2/w := by
        rw [abs_mul, abs_of_pos hw0]; exact hSp_bound
      have hDcnn : 0 ≤ Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) :=
        (Work.ZeroDensity.Jutila.Dc_pos c0 _).le
      have hA : w * (2*C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r))
          ≤ K * w * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by
        have hwσ : 0 ≤ w*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) :=
          mul_nonneg (mul_nonneg hw0.le hσr0) hDcnn
        calc w * (2*C0*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r))
            = (2*C0) * (w*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)) := by ring
          _ ≤ K * (w*σr*Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)) :=
              mul_le_mul_of_nonneg_right hK2C0 hwσ
          _ = K * w * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r) := by ring
      have hB : 140*(czTmax w y N q r : ℝ)^2/w
          ≤ K * w * σr * ((czTmax w y N q r : ℝ)/w)^2 := by
        have hge : (140:ℝ) ≤ K * σr := by nlinarith only [hK140, hσr1, hKpos]
        calc 140*(czTmax w y N q r : ℝ)^2/w
            = 140 * ((czTmax w y N q r : ℝ)^2/w) := by ring
          _ ≤ (K*σr) * ((czTmax w y N q r : ℝ)^2/w) :=
              mul_le_mul_of_nonneg_right hge (by positivity)
          _ = K * w * σr * ((czTmax w y N q r : ℝ)/w)^2 := by field_simp
      have hRHS : K * w * σr * Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)
          + K * w * σr * ((czTmax w y N q r : ℝ)/w)^2
          = K * w * σr * (Work.ZeroDensity.Jutila.Dc c0 (czTmax w y N q r)
              + ((czTmax w y N q r : ℝ)/w)^2) := by ring
      rw [← hRHS]
      linarith only [le_trans h1 hA, le_trans h2 hB, h1, h2, hA, hB]

end

end Work.ZeroDensity.Jutila.LzDiffAux
