import Mathlib
import Submission.Commons.NumberTheory.Sieve.moebius_density_sum_le

namespace Commons.NumberTheory.Sieve

open Finset

noncomputable section

/-! ## Reindexing the Möbius sum along `b ↦ (gcd ν b, b / gcd ν b)` -/

/-- For squarefree `b`, `gcd (gcd a b) (b / gcd a b) = 1`. -/
private lemma gcd_gcd_div_gcd_eq_one (a b : ℕ) (hb : Squarefree b) :
    Nat.gcd (Nat.gcd a b) (b / Nat.gcd a b) = 1 := by
  set g := Nat.gcd a b with hg
  have hgb : g ∣ b := by rw [hg]; exact Nat.gcd_dvd_right a b
  have h1 : Nat.gcd g (b / g) * Nat.gcd g (b / g) ∣ b := by
    have h := mul_dvd_mul (Nat.gcd_dvd_left g (b / g)) (Nat.gcd_dvd_right g (b / g))
    rwa [Nat.mul_div_cancel' hgb] at h
  have h2 := hb (Nat.gcd g (b / g)) h1
  rwa [Nat.isUnit_iff] at h2

/-- For squarefree `b`, `b / gcd ν b` is coprime to `ν`. -/
private lemma coprime_div_gcd_of_squarefree {ν b : ℕ} (hb : Squarefree b) :
    Nat.Coprime (b / Nat.gcd ν b) ν := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g := Nat.gcd ν b with hg
  have hgb : g ∣ b := by rw [hg]; exact Nat.gcd_dvd_right ν b
  have hdvdb : b / g ∣ b := Nat.div_dvd_of_dvd hgb
  have hdvdg : Nat.gcd (b / g) ν ∣ g :=
    Nat.dvd_gcd (Nat.gcd_dvd_right (b / g) ν)
      (Nat.dvd_trans (Nat.gcd_dvd_left (b / g) ν) hdvdb)
  have hdvdbg : Nat.gcd (b / g) ν ∣ b / g := Nat.gcd_dvd_left (b / g) ν
  have h1 : Nat.gcd (b / g) ν * Nat.gcd (b / g) ν ∣ b := by
    have h := mul_dvd_mul hdvdg hdvdbg
    rwa [Nat.mul_div_cancel' hgb] at h
  have h2 := hb (Nat.gcd (b / g) ν) h1
  rwa [Nat.isUnit_iff] at h2

/-- If `b₁ ∣ ν` and `b₀` is coprime to `ν`, then `gcd ν (b₁ * b₀) = b₁`. -/
private lemma gcd_mul_of_dvd_coprime {ν b₁ b₀ : ℕ} (hb₁ : b₁ ∣ ν) (hcop : Nat.Coprime b₀ ν) :
    Nat.gcd ν (b₁ * b₀) = b₁ := by
  have hνeq : b₁ * (ν / b₁) = ν := Nat.mul_div_cancel' hb₁
  have hdv : ν / b₁ ∣ ν := Nat.div_dvd_of_dvd hb₁
  have hcd : Nat.Coprime (ν / b₁) b₀ := Nat.Coprime.coprime_dvd_left hdv hcop.symm
  calc Nat.gcd ν (b₁ * b₀)
      = Nat.gcd (b₁ * (ν / b₁)) (b₁ * b₀) := by rw [hνeq]
    _ = b₁ * Nat.gcd (ν / b₁) b₀ := Nat.gcd_mul_left b₁ (ν / b₁) b₀
    _ = b₁ * 1 := by rw [(Nat.coprime_iff_gcd_eq_one).mp hcd]
    _ = b₁ := mul_one b₁

private lemma moebius_mul_coprime_real {m n : ℕ} (h : Nat.Coprime m n) :
    ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  have hz : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_iff_gcd_eq_one.mp h)
  have := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa using this

private lemma abs_moebius_cast_le_one (n : ℕ) :
    |(((ArithmeticFunction.moebius n : ℤ)) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split <;> norm_num

/-- **Reindexing identity.**  Summing `b ↦ μ b · F (gcd ν b) (b / gcd ν b)` over squarefree
`b ≤ y` equals the double sum over divisors `b₁ ∣ ν` and `b₀ ≤ y / b₁` coprime to `ν`. -/
private lemma sum_div_gcd_reindex (F : ℕ → ℕ → ℝ) {ν y : ℕ} (hν : Squarefree ν) :
    (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * F (Nat.gcd ν b) (b / Nat.gcd ν b))
    = ∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) *
        ∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
          (ArithmeticFunction.moebius b₀ : ℝ) * F b₁ b₀ := by
  classical
  set C : Finset (Sigma (fun _ : ℕ => ℕ)) :=
    (ν.divisors).sigma (fun b₁ =>
      ((Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν)).filter
        (fun d => Squarefree d)) with hC
  have hbij :
      (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * F (Nat.gcd ν b) (b / Nat.gcd ν b))
      = ∑ c ∈ C, (ArithmeticFunction.moebius c.1 : ℝ) * (ArithmeticFunction.moebius c.2 : ℝ)
          * F c.1 c.2 := by
    refine Finset.sum_bij'
      (fun b _ => (⟨Nat.gcd ν b, b / Nat.gcd ν b⟩ : Sigma (fun _ : ℕ => ℕ)))
      (fun c _ => c.1 * c.2) ?_ ?_ ?_ ?_ ?_
    · -- `i` lands in `C`
      intro b hb
      rw [hC, Finset.mem_sigma]
      obtain ⟨hbIcc, hbsq⟩ := Finset.mem_filter.mp hb
      rw [Finset.mem_Icc] at hbIcc
      obtain ⟨hb1, hby⟩ := hbIcc
      have hbpos : 0 < b := by omega
      have hgb : Nat.gcd ν b ∣ b := Nat.gcd_dvd_right ν b
      have hgpos : 0 < Nat.gcd ν b := Nat.pos_of_dvd_of_pos hgb hbpos
      refine ⟨?_, ?_⟩
      · rw [Nat.mem_divisors]; exact ⟨Nat.gcd_dvd_left ν b, hν.ne_zero⟩
      · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨(Nat.one_le_div_iff hgpos).mpr (Nat.gcd_le_right ν hbpos),
                 Nat.div_le_div_right hby⟩,
                 coprime_div_gcd_of_squarefree hbsq⟩,
                 Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hgb) hbsq⟩
    · -- `j` lands in the squarefree-range
      intro c hc
      rw [hC, Finset.mem_sigma] at hc
      obtain ⟨hc1mem, hc2mem⟩ := hc
      rw [Finset.mem_filter, Finset.mem_filter] at hc2mem
      obtain ⟨⟨hc2Icc, hc2cop⟩, hc2sq⟩ := hc2mem
      rw [Finset.mem_Icc] at hc2Icc
      obtain ⟨hc21, hc2y⟩ := hc2Icc
      have hc1dvd : c.1 ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < c.1 := Nat.pos_of_mem_divisors hc1mem
      have hc1sq : Squarefree c.1 := Squarefree.squarefree_of_dvd hc1dvd hν
      have hcop : Nat.Coprime c.1 c.2 := Nat.Coprime.coprime_dvd_left hc1dvd hc2cop.symm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have : 0 < c.1 * c.2 := Nat.mul_pos hc1pos (by omega)
        omega
      · have := (Nat.le_div_iff_mul_le hc1pos).mp hc2y
        calc c.1 * c.2 ≤ c.2 * c.1 := by rw [mul_comm]
          _ ≤ y := this
      · exact (Nat.squarefree_mul hcop).mpr ⟨hc1sq, hc2sq⟩
    · -- `j ∘ i = id`
      intro b hb
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)
    · -- `i ∘ j = id`
      intro c hc
      rw [hC, Finset.mem_sigma] at hc
      obtain ⟨hc1mem, hc2mem⟩ := hc
      rw [Finset.mem_filter, Finset.mem_filter] at hc2mem
      obtain ⟨⟨hc2Icc, hc2cop⟩, _⟩ := hc2mem
      obtain ⟨b₁, b₀⟩ := c
      have hc1dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hc1mem).1
      have hc1pos : 0 < b₁ := Nat.pos_of_mem_divisors hc1mem
      rw [gcd_mul_of_dvd_coprime hc1dvd hc2cop, Nat.mul_div_right b₀ hc1pos]
    · -- agreement of summands
      intro b hb
      obtain ⟨_, hbsq⟩ := Finset.mem_filter.mp hb
      have hcop : Nat.Coprime (Nat.gcd ν b) (b / Nat.gcd ν b) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        exact gcd_gcd_div_gcd_eq_one ν b hbsq
      have hmu2 : ((ArithmeticFunction.moebius b : ℤ) : ℝ)
          = ((ArithmeticFunction.moebius (Nat.gcd ν b) : ℤ) : ℝ)
            * ((ArithmeticFunction.moebius (b / Nat.gcd ν b) : ℤ) : ℝ) := by
        conv_lhs => rw [show b = Nat.gcd ν b * (b / Nat.gcd ν b)
          from (Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)).symm]
        exact moebius_mul_coprime_real hcop
      rw [hmu2]
  rw [hbij, hC]
  rw [← Finset.sum_sigma' (ν.divisors)
        (fun b₁ => ((Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν)).filter
          (fun d => Squarefree d))
        (fun a b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) * F a b)]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  trans ∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
      (ArithmeticFunction.moebius b₁ : ℝ) * (ArithmeticFunction.moebius b₀ : ℝ) * F b₁ b₀
  · exact Finset.sum_subset (Finset.filter_subset _ _) (fun b₀ hb₀ hb₀not => by
      rw [Finset.mem_filter] at hb₀not
      push Not at hb₀not
      have hs : ¬ Squarefree b₀ := hb₀not hb₀
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      ring)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b₀ _ => by rw [mul_assoc])

/-! ## Elementary bounds on the truncation levels -/

/-- `2 b₁ ≤ y` for `b₁ ∈ ν.divisors` and `ν² ≤ y`, `y ≥ 2`. -/
private lemma two_mul_le_of_mem_divisors {ν b₁ y : ℕ} (hν : Squarefree ν) (hνy : ν ^ 2 ≤ y)
    (hy : 2 ≤ y) (hb₁ : b₁ ∈ ν.divisors) : 2 * b₁ ≤ y := by
  have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁
  have hb₁dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hb₁).1
  have hνpos : 0 < ν := Nat.pos_of_ne_zero hν.ne_zero
  have hb₁leν : b₁ ≤ ν := Nat.le_of_dvd hνpos hb₁dvd
  have hb₁sq : b₁ ^ 2 ≤ y := by
    have : b₁ ^ 2 ≤ ν ^ 2 := Nat.pow_le_pow_left hb₁leν 2
    omega
  rcases eq_or_lt_of_le (show 1 ≤ b₁ by omega) with h | h
  · omega
  · nlinarith [hb₁sq]

/-- For `y ≥ 2`, `b₁ ∈ ν.divisors`, `ν² ≤ y`, one has
`log⌊y/b₁⌋ ≥ (1/4) log y`. -/
private lemma log_div_ge_quarter {ν b₁ y : ℕ} (hν : Squarefree ν) (hνy : ν ^ 2 ≤ y)
    (hy : 2 ≤ y) (hb₁ : b₁ ∈ ν.divisors) :
    (1 / 4 : ℝ) * Real.log (y : ℝ) ≤ Real.log ((y / b₁ : ℕ) : ℝ) := by
  have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁
  have hb₁dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hb₁).1
  have hνpos : 0 < ν := Nat.pos_of_ne_zero hν.ne_zero
  have hb₁leν : b₁ ≤ ν := Nat.le_of_dvd hνpos hb₁dvd
  have h2b₁ : 2 * b₁ ≤ y := two_mul_le_of_mem_divisors hν hνy hy hb₁
  have hw2 : 2 ≤ y / b₁ := (Nat.le_div_iff_mul_le hb₁pos).mpr (by linarith [h2b₁])
  have hw2R : (2 : ℝ) ≤ ((y / b₁ : ℕ) : ℝ) := by exact_mod_cast hw2
  have hlog2 : Real.log 2 ≤ Real.log ((y / b₁ : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hw2R
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h, Real.log_pow]; ring
  by_cases hy16 : 16 ≤ y
  · -- large `y`: use the square root
    have hνle : (ν : ℝ) ≤ Real.sqrt y := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have : (↑(ν ^ 2) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hνy
      push_cast at this
      linarith
    have hb₁le : (b₁ : ℝ) ≤ Real.sqrt y := le_trans (by exact_mod_cast hb₁leν) hνle
    have hdiv : Real.sqrt y ≤ (y : ℝ) / b₁ := by
      have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ y by positivity)
        (by exact_mod_cast hb₁pos) hb₁le
      rwa [Real.div_sqrt] at h
    have hcast : (y : ℝ) / b₁ - 1 ≤ ((y / b₁ : ℕ) : ℝ) := by
      have hsucc : (y : ℝ) < (b₁ : ℝ) * (((y / b₁ : ℕ) : ℝ) + 1) := by
        have hmul := Nat.lt_mul_div_succ y hb₁pos
        have hcast' : ((b₁ * (y / b₁ + 1) : ℕ) : ℝ)
            = (b₁ : ℝ) * (((y / b₁ : ℕ) : ℝ) + 1) := by push_cast; ring
        calc (y : ℝ) < ((b₁ * (y / b₁ + 1) : ℕ) : ℝ) := by exact_mod_cast hmul
          _ = (b₁ : ℝ) * (((y / b₁ : ℕ) : ℝ) + 1) := hcast'
      have hb₁posR : (0 : ℝ) < (b₁ : ℝ) := by exact_mod_cast hb₁pos
      have : (y : ℝ) / b₁ < ((y / b₁ : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hb₁posR]
        nlinarith [hsucc]
      linarith
    have hlower : Real.sqrt y / 2 ≤ ((y / b₁ : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 4 ≤ y)
      have hsq2 : (2 : ℝ) ≤ Real.sqrt y := by
        rw [Real.le_sqrt' (by norm_num)]
        linarith
      linarith
    have hmono : Real.log (Real.sqrt y / 2) ≤ Real.log ((y / b₁ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hlower
    have hlogs : Real.log (Real.sqrt y / 2) = (1 / 2) * Real.log y - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity)]
      ring
    have hlog2le : Real.log 2 ≤ (1 / 4) * Real.log y := by
      have hy16' : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
      have h : Real.log 16 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) hy16'
      rw [hlog16] at h; linarith
    linarith
  · -- small `y`: `⌊y/b₁⌋ ≥ 2` and `log 16 ≥ log y`
    have hy16le : y ≤ 16 := by omega
    have hlogy : Real.log (y : ℝ) ≤ Real.log 16 :=
      Real.log_le_log (by positivity) (by exact_mod_cast hy16le)
    have hquarter : (1 / 4) * Real.log (y : ℝ) ≤ Real.log 2 := by
      rw [hlog16] at hlogy; linarith
    linarith

/-- `(log⌊y/b₁⌋)^{-6} ≤ 4096 (log y)^{-6}` under the standing hypotheses. -/
private lemma log_div_zpow_bound {ν b₁ y : ℕ} (hν : Squarefree ν) (hνy : ν ^ 2 ≤ y)
    (hy : 2 ≤ y) (hb₁ : b₁ ∈ ν.divisors) :
    (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-(6 : ℤ))
      ≤ 4096 * (Real.log (y : ℝ)) ^ (-(6 : ℤ)) := by
  have hq := log_div_ge_quarter hν hνy hy hb₁
  have hylogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hqpos : 0 < (1 / 4 : ℝ) * Real.log (y : ℝ) := by linarith
  have hrw : (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-6 : ℝ) ≤ 4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    have hmono := Real.rpow_le_rpow_of_nonpos hqpos hq (show (-6 : ℝ) ≤ 0 by norm_num)
    have hkey : ((1 / 4 : ℝ) * Real.log (y : ℝ)) ^ (-6 : ℝ)
        = 4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
      have h1 : ((1 / 4 : ℝ) * Real.log (y : ℝ)) = Real.log (y : ℝ) / 4 := by ring
      have h4 : (4 : ℝ) ^ (-6 : ℝ) = (1 / 4096 : ℝ) := by
        rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_natCast]
        norm_num
      rw [h1, Real.div_rpow (le_of_lt hylogpos) (by norm_num : (0 : ℝ) ≤ 4) (-6), h4]
      ring
    linarith [hmono, hkey]
  have e1 : (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-(6 : ℤ))
      = (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-6 : ℝ) := by
    rw [← Real.rpow_intCast]; norm_num
  have e2 : (Real.log (y : ℝ)) ^ (-(6 : ℤ)) = (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [e1, e2]; linarith [hrw]

/-- **Friedlander–Iwaniec, companion (2.4) with the `ν`-twist.** -/
theorem sum_mu_g_div_gcd_le {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℕ, Squarefree ν → ∀ y : ℕ, 2 ≤ y → ν ^ 2 ≤ y →
      |∑ b ∈ Finset.Icc 1 y,
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)|
        ≤ C * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (ν.divisors.card : ℝ) * (Real.log (y : ℝ)) ^ (-(6 : ℤ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := moebius_density_sum_le hmul hg1 hp hbound h9
  refine ⟨4096 * C₀, by positivity, ?_⟩
  intro ν hν y hy hνy
  set γ : ℝ := ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hγ
  have hν1 : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr hν.ne_zero
  have hγnn : 0 ≤ γ := by
    rw [hγ]
    exact Finset.prod_nonneg (fun p hp' => by
      have hp'' := Nat.prime_of_mem_primeFactors hp'
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp''.pos
      positivity)
  have hsq_eq : (∑ b ∈ Finset.Icc 1 y,
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b))
      = ∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : Squarefree b
    · rw [if_pos hb]
    · rw [if_neg hb, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]; ring
  rw [hsq_eq, sum_div_gcd_reindex (fun _ c => g c) hν]
  calc |∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) *
          ∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
            (ArithmeticFunction.moebius b₀ : ℝ) * g b₀|
      ≤ ∑ b₁ ∈ ν.divisors, |(ArithmeticFunction.moebius b₁ : ℝ) *
          ∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
            (ArithmeticFunction.moebius b₀ : ℝ) * g b₀| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b₁ ∈ ν.divisors,
          |∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
            (ArithmeticFunction.moebius b₀ : ℝ) * g b₀| := by
        apply Finset.sum_le_sum
        intro b₁ _
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b₁)
    _ ≤ ∑ b₁ ∈ ν.divisors, C₀ * γ * (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-(6 : ℤ)) := by
        apply Finset.sum_le_sum
        intro b₁ hb₁
        rw [hγ]
        exact hC₀ ν (y / b₁) hν1
          ((Nat.le_div_iff_mul_le (Nat.pos_of_mem_divisors hb₁)).mpr
            (two_mul_le_of_mem_divisors hν hνy hy hb₁))
    _ = C₀ * γ * ∑ b₁ ∈ ν.divisors, (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-(6 : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ C₀ * γ * ∑ b₁ ∈ ν.divisors, 4096 * (Real.log (y : ℝ)) ^ (-(6 : ℤ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀pos.le hγnn)
        apply Finset.sum_le_sum
        intro b₁ hb₁
        exact log_div_zpow_bound hν hνy hy hb₁
    _ = C₀ * γ * ((ν.divisors.card : ℝ) * (4096 * (Real.log (y : ℝ)) ^ (-(6 : ℤ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 4096 * C₀ * γ * (ν.divisors.card : ℝ) * (Real.log (y : ℝ)) ^ (-(6 : ℤ)) := by ring

end

end Commons.NumberTheory.Sieve
