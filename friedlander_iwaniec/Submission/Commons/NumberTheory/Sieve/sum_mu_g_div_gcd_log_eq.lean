import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_mu_g_log_coprime_rate

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
      intro b _
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

/-! ## The `log`-weighted reindexing -/

private lemma sum_moebius_divisors_nat (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n),
      ArithmeticFunction.moebius_mul_coe_zeta]
  rfl

private lemma sum_moebius_divisors_real (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := sum_moebius_divisors_nat n
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  simpa using h2

private lemma abs_moebius_cast_le_one (n : ℕ) :
    |(((ArithmeticFunction.moebius n : ℤ)) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ArithmeticFunction.abs_moebius]
  split <;> norm_num

/-- Splitting the inner `log`-sum: `∑ μ b₀ · g b₀ · log(b₁ b₀) = log b₁ · ∑ μ b₀ g b₀ + ∑ μ b₀ g b₀ log b₀`. -/
private lemma inner_log_split {g : ℕ → ℝ} {ν : ℕ} {b₁ : ℕ} (hb₁ : b₁ ≠ 0) (N : ℕ) :
    (∑ b₀ ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
        (ArithmeticFunction.moebius b₀ : ℝ) * (g b₀ * Real.log ((b₁ : ℝ) * (b₀ : ℝ))))
      = Real.log (b₁ : ℝ) *
            (∑ b₀ ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
              (ArithmeticFunction.moebius b₀ : ℝ) * g b₀)
          + (∑ b₀ ∈ (Finset.Icc 1 N).filter (fun d => Nat.Coprime d ν),
              (ArithmeticFunction.moebius b₀ : ℝ) * g b₀ * Real.log (b₀ : ℝ)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b₀ hb₀
  rw [Finset.mem_filter, Finset.mem_Icc] at hb₀
  have hb₀ne : b₀ ≠ 0 := by omega
  rw [Real.log_mul (by exact_mod_cast hb₁) (by exact_mod_cast hb₀ne)]
  ring

private lemma log_gcd_mul_div {ν b : ℕ} (_hb : b ≠ 0) :
    Real.log ((Nat.gcd ν b : ℝ) * (((b / Nat.gcd ν b) : ℕ) : ℝ)) = Real.log (b : ℝ) := by
  have hgdvd : Nat.gcd ν b ∣ b := Nat.gcd_dvd_right ν b
  have hcast : (Nat.gcd ν b : ℝ) * (((b / Nat.gcd ν b) : ℕ) : ℝ) = (b : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hgdvd]
  rw [hcast]

/-- **`log`-weighted reindexing identity.** -/
private lemma sum_div_gcd_reindex_log {g : ℕ → ℝ} {ν y : ℕ} (hν : Squarefree ν) :
    (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log (b : ℝ))
      = ∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) *
          (Real.log (b₁ : ℝ) *
             (∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
                (ArithmeticFunction.moebius b₀ : ℝ) * g b₀)
           + (∑ b₀ ∈ (Finset.Icc 1 (y / b₁)).filter (fun d => Nat.Coprime d ν),
                (ArithmeticFunction.moebius b₀ : ℝ) * g b₀ * Real.log (b₀ : ℝ))) := by
  have h := sum_div_gcd_reindex (y := y)
    (fun (x y : ℕ) => g y * Real.log ((x : ℝ) * (y : ℝ))) hν
  have hL : (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log (b : ℝ))
      = (∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
        (ArithmeticFunction.moebius b : ℝ)
          * ((fun (x y : ℕ) => g y * Real.log ((x : ℝ) * (y : ℝ))) (Nat.gcd ν b)
              (b / Nat.gcd ν b))) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    have hbne : b ≠ 0 := by omega
    simp only
    rw [log_gcd_mul_div hbne]
    ring
  rw [hL, h]
  apply Finset.sum_congr rfl
  intro b₁ hb₁
  have hb₁ne : b₁ ≠ 0 := (Nat.pos_of_mem_divisors hb₁).ne'
  rw [inner_log_split hb₁ne (y / b₁)]

/-! ## Bounds on the truncation level -/

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

/-- For `y ≥ 2`, `b₁ ∈ ν.divisors`, `ν² ≤ y`: `log⌊y/b₁⌋ ≥ (1/4) log y`. -/
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

/-- `(log⌊y/b₁⌋)^{-5} ≤ 1024 (log y)^{-5}` under the standing hypotheses. -/
private lemma log_div_rpow_neg5 {ν b₁ y : ℕ} (hν : Squarefree ν) (hνy : ν ^ 2 ≤ y)
    (hy : 2 ≤ y) (hb₁ : b₁ ∈ ν.divisors) :
    (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-5 : ℝ)
      ≤ 1024 * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
  have hq := log_div_ge_quarter hν hνy hy hb₁
  have hylogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hqpos : 0 < (1 / 4 : ℝ) * Real.log (y : ℝ) := by linarith
  have hmono := Real.rpow_le_rpow_of_nonpos hqpos hq (show (-5 : ℝ) ≤ 0 by norm_num)
  have hkey : ((1 / 4 : ℝ) * Real.log (y : ℝ)) ^ (-5 : ℝ)
      = 1024 * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
    have h1 : ((1 / 4 : ℝ) * Real.log (y : ℝ)) = Real.log (y : ℝ) / 4 := by ring
    have h4 : (4 : ℝ) ^ (-5 : ℝ) = (1 / 1024 : ℝ) := by
      rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        Real.rpow_natCast]
      norm_num
    rw [h1, Real.div_rpow (le_of_lt hylogpos) (by norm_num : (0 : ℝ) ≤ 4) (-5), h4]
    ring
  linarith

/-- `(log⌊y/b₁⌋)^{-6} ≤ 4096 (log y)^{-6}` under the standing hypotheses. -/
private lemma log_div_rpow_neg6 {ν b₁ y : ℕ} (hν : Squarefree ν) (hνy : ν ^ 2 ≤ y)
    (hy : 2 ≤ y) (hb₁ : b₁ ∈ ν.divisors) :
    (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-6 : ℝ)
      ≤ 4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
  have hq := log_div_ge_quarter hν hνy hy hb₁
  have hylogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hqpos : 0 < (1 / 4 : ℝ) * Real.log (y : ℝ) := by linarith
  have hmono := Real.rpow_le_rpow_of_nonpos hqpos hq (show (-6 : ℝ) ≤ 0 by norm_num)
  have hkey : ((1 / 4 : ℝ) * Real.log (y : ℝ)) ^ (-6 : ℝ)
      = 4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
    have h1 : ((1 / 4 : ℝ) * Real.log (y : ℝ)) = Real.log (y : ℝ) / 4 := by ring
    have h4 : (4 : ℝ) ^ (-6 : ℝ) = (1 / 4096 : ℝ) := by
      rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        Real.rpow_natCast]
      norm_num
    rw [h1, Real.div_rpow (le_of_lt hylogpos) (by norm_num : (0 : ℝ) ≤ 4) (-6), h4]
    ring
  linarith


private lemma log_mul_log_neg6 {L : ℝ} (hL : 0 < L) : L * L ^ (-6 : ℝ) = L ^ (-5 : ℝ) := by
  calc L * L ^ (-6 : ℝ) = L ^ (1 : ℝ) * L ^ (-6 : ℝ) := by rw [Real.rpow_one]
    _ = L ^ ((1 : ℝ) + (-6 : ℝ)) := (Real.rpow_add hL 1 (-6)).symm
    _ = L ^ (-5 : ℝ) := by norm_num

theorem sum_mu_g_div_gcd_log_eq {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-H)) ∧
      ∀ ν : ℕ, Squarefree ν → ∀ y : ℕ, 2 ≤ y → ν ^ 2 ≤ y →
        |(∑ b ∈ Finset.Icc 1 y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
          + (if ν = 1 then H else 0)|
        ≤ C * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (ν.divisors.card : ℝ) * (Real.log (y : ℝ)) ^ (-(5 : ℤ)) := by
  obtain ⟨C₁, H, hC₁pos, hHpos, hHlim, hcop⟩ := sum_mu_g_log_coprime_rate hmul hg1 hp hbound h9
  obtain ⟨C₂, hC₂pos, hUraw⟩ := moebius_density_sum_le hmul hg1 hp hbound h9
  have hc5 : ∀ t : ℝ, t ^ (-(5 : ℤ)) = t ^ (-5 : ℝ) := fun t => by
    rw [← Real.rpow_intCast]; norm_num
  have hc6 : ∀ t : ℝ, t ^ (-(6 : ℤ)) = t ^ (-6 : ℝ) := fun t => by
    rw [← Real.rpow_intCast]; norm_num
  refine ⟨4096 * (C₁ + C₂), H, by positivity, hHpos, hHlim, ?_⟩
  intro ν hν y hy hνy
  set β : ℝ := ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hβdef
  set U : ℕ → ℝ := fun x => ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Nat.Coprime d ν),
      (ArithmeticFunction.moebius d : ℝ) * g d with hUdef
  set V : ℕ → ℝ := fun x => ∑ d ∈ (Finset.Icc 1 x).filter (fun d => Nat.Coprime d ν),
      (ArithmeticFunction.moebius d : ℝ) * g d * Real.log (d : ℝ) with hVdef
  obtain ⟨Hν, hHνpos, hHνlim, hVbd0⟩ := hcop ν hν
  have hβnn : 0 ≤ β := by
    rw [hβdef]
    exact Finset.prod_nonneg (fun p hp' => by
      have := Nat.prime_of_mem_primeFactors hp'
      positivity)
  have hy1 : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 1 < y)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hA5nn : 0 ≤ (Real.log (y : ℝ)) ^ (-5 : ℝ) := Real.rpow_nonneg hlogy_pos.le _
  have hν1le : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr hν.ne_zero
  have hVbd : ∀ N : ℕ, 2 ≤ N → |V N + Hν| ≤ C₁ * β * (Real.log (N : ℝ)) ^ (-5 : ℝ) := by
    intro N hN
    have hh := hVbd0 N hN
    rw [hc5 (Real.log (N : ℝ)), ← hβdef] at hh
    simpa only [hVdef] using hh
  have hUbd : ∀ x : ℕ, 2 ≤ x → |U x| ≤ C₂ * β * (Real.log (x : ℝ)) ^ (-6 : ℝ) := by
    intro x hx
    have hh := hUraw ν x hν1le hx
    rw [hc6 (Real.log (x : ℝ)), ← hβdef] at hh
    simpa only [hUdef] using hh
  have hW : (∑ b ∈ Finset.Icc 1 y,
        (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log (b : ℝ))
      = ∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) *
          (Real.log (b₁ : ℝ) * U (y / b₁) + V (y / b₁)) := by
    have hsf : (∑ b ∈ Finset.Icc 1 y,
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log (b : ℝ))
        = ∑ b ∈ (Finset.Icc 1 y).filter (fun b => Squarefree b),
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log (b : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Squarefree b
      · rw [if_pos hb]
      · rw [if_neg hb, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]; ring
    rw [hsf, sum_div_gcd_reindex_log hν]
  by_cases hν1eq : ν = 1
  · subst hν1eq
    obtain ⟨H₁, hH₁pos, hH₁lim, hH₁bd⟩ := hcop 1 squarefree_one
    have hfilter1 : ∀ N : ℕ, (Finset.Icc 1 N).filter (fun d => Nat.Coprime d 1) = Finset.Icc 1 N := by
      intro N; apply Finset.filter_true_of_mem; intro d _; exact Nat.coprime_one_right d
    have hH₁lim' : Filter.Tendsto (fun N : ℕ =>
        ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log (d : ℝ))
        Filter.atTop (nhds (-H₁)) := by
      refine hH₁lim.congr (fun N => ?_)
      rw [hfilter1 N]
    have hHH : H₁ = H := by
      have h := tendsto_nhds_unique hH₁lim' hHlim
      linarith
    have hbdy : |(∑ d ∈ Finset.Icc 1 y,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log (d : ℝ)) + H|
        ≤ 4096 * (C₁ + C₂) * (Real.log (y : ℝ)) ^ (-(5 : ℤ)) := by
      have h := hH₁bd y hy
      rw [hfilter1 y, hHH] at h
      have hβ1 : (∏ p ∈ (1 : ℕ).primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) = 1 := by simp
      rw [hβ1, mul_one] at h
      calc |(∑ d ∈ Finset.Icc 1 y,
              (ArithmeticFunction.moebius d : ℝ) * g d * Real.log (d : ℝ)) + H|
          ≤ C₁ * (Real.log (y : ℝ)) ^ (-(5 : ℤ)) := h
        _ ≤ 4096 * (C₁ + C₂) * (Real.log (y : ℝ)) ^ (-(5 : ℤ)) := by
            apply mul_le_mul_of_nonneg_right _ (by rw [hc5]; exact hA5nn)
            nlinarith [hC₁pos, hC₂pos]
    rw [if_pos rfl]
    simp only [Nat.gcd_one_left, Nat.div_one, hβdef, Nat.primeFactors_one, Finset.prod_empty,
      Nat.divisors_one, Finset.card_singleton, Nat.cast_one, mul_one]
    exact hbdy
  · have hνge2 : 2 ≤ ν := by omega
    rw [hW, if_neg hν1eq]
    simp only [add_zero]
    have hmu0 : (∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ)) = 0 := by
      rw [sum_moebius_divisors_real, if_neg hν1eq]
    have hsplit : (∑ b₁ ∈ ν.divisors,
          (ArithmeticFunction.moebius b₁ : ℝ) * (Real.log (b₁ : ℝ) * U (y / b₁) + V (y / b₁)))
        = (∑ b₁ ∈ ν.divisors,
              (ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁))
          + (∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)) := by
      have hC : (∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν))
          = ∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * V (y / b₁) := by
        have hterm : ∀ b₁ : ℕ, (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)
            = (ArithmeticFunction.moebius b₁ : ℝ) * V (y / b₁)
              + (ArithmeticFunction.moebius b₁ : ℝ) * Hν := fun b₁ => by ring
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmu0, zero_mul, add_zero]
      rw [hC, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b₁ hb₁; ring
    rw [hsplit]
    have hpart1 : |∑ b₁ ∈ ν.divisors,
          (ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁)|
        ≤ (ν.divisors.card : ℝ) * (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ b₁ ∈ ν.divisors,
          |(ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁)|
          ≤ (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
        intro b₁ hb₁
        have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁
        have hb₁dvd : b₁ ∣ ν := (Nat.mem_divisors.mp hb₁).1
        have hb₁leν : b₁ ≤ ν := Nat.le_of_dvd (Nat.pos_of_ne_zero hν.ne_zero) hb₁dvd
        have hyb2 : 2 ≤ y / b₁ :=
          (Nat.le_div_iff_mul_le hb₁pos).mpr (two_mul_le_of_mem_divisors hν hνy hy hb₁)
        have hb₁1 : 1 ≤ b₁ := by omega
        have hlogb₁nn : 0 ≤ Real.log (b₁ : ℝ) := Real.log_nonneg (by exact_mod_cast hb₁1)
        have hνley : ν ≤ y := by nlinarith [hνy, hν1le]
        have hb₁y : b₁ ≤ y := le_trans hb₁leν hνley
        have hlogb₁le : Real.log (b₁ : ℝ) ≤ Real.log (y : ℝ) :=
          Real.log_le_log (by exact_mod_cast hb₁pos) (by exact_mod_cast hb₁y)
        calc |(ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁)|
            = |(ArithmeticFunction.moebius b₁ : ℝ)| * Real.log (b₁ : ℝ) * |U (y / b₁)| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hlogb₁nn]
          _ ≤ 1 * Real.log (y : ℝ) * (C₂ * β * (4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ))) := by
              apply mul_le_mul
              · exact mul_le_mul (abs_moebius_cast_le_one b₁) hlogb₁le hlogb₁nn (by norm_num)
              · calc |U (y / b₁)| ≤ C₂ * β * (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-6 : ℝ) :=
                    hUbd (y / b₁) hyb2
                  _ ≤ C₂ * β * (4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ)) :=
                    mul_le_mul_of_nonneg_left (log_div_rpow_neg6 hν hνy hy hb₁)
                      (mul_nonneg hC₂pos.le hβnn)
              · exact abs_nonneg _
              · positivity
          _ = (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
              rw [show (1 : ℝ) * Real.log (y : ℝ) * (C₂ * β * (4096 * (Real.log (y : ℝ)) ^ (-6 : ℝ)))
                    = (C₂ * β * 4096) * (Real.log (y : ℝ) * (Real.log (y : ℝ)) ^ (-6 : ℝ)) by ring,
                log_mul_log_neg6 hlogy_pos]
              ring
      calc ∑ b₁ ∈ ν.divisors,
              |(ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁)|
          ≤ ∑ _b₁ ∈ ν.divisors, (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (ν.divisors.card : ℝ) * ((β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (ν.divisors.card : ℝ) * (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by ring
    have hpart2 : |∑ b₁ ∈ ν.divisors,
          (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)|
        ≤ (ν.divisors.card : ℝ) * (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ b₁ ∈ ν.divisors,
          |(ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)|
          ≤ (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
        intro b₁ hb₁
        have hb₁pos : 0 < b₁ := Nat.pos_of_mem_divisors hb₁
        have hyb2 : 2 ≤ y / b₁ :=
          (Nat.le_div_iff_mul_le hb₁pos).mpr (two_mul_le_of_mem_divisors hν hνy hy hb₁)
        calc |(ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)|
            = |(ArithmeticFunction.moebius b₁ : ℝ)| * |V (y / b₁) + Hν| := abs_mul _ _
          _ ≤ 1 * (C₁ * β * (1024 * (Real.log (y : ℝ)) ^ (-5 : ℝ))) := by
              apply mul_le_mul (abs_moebius_cast_le_one b₁) ?_ (abs_nonneg _) (by norm_num)
              calc |V (y / b₁) + Hν| ≤ C₁ * β * (Real.log ((y / b₁ : ℕ) : ℝ)) ^ (-5 : ℝ) :=
                    hVbd (y / b₁) hyb2
                _ ≤ C₁ * β * (1024 * (Real.log (y : ℝ)) ^ (-5 : ℝ)) :=
                    mul_le_mul_of_nonneg_left (log_div_rpow_neg5 hν hνy hy hb₁)
                      (mul_nonneg hC₁pos.le hβnn)
          _ = (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by ring
      calc ∑ b₁ ∈ ν.divisors,
              |(ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)|
          ≤ ∑ _b₁ ∈ ν.divisors, (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (ν.divisors.card : ℝ) * ((β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (ν.divisors.card : ℝ) * (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by ring
    calc |(∑ b₁ ∈ ν.divisors,
              (ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁))
          + (∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν))|
        ≤ |∑ b₁ ∈ ν.divisors,
              (ArithmeticFunction.moebius b₁ : ℝ) * Real.log (b₁ : ℝ) * U (y / b₁)|
          + |∑ b₁ ∈ ν.divisors, (ArithmeticFunction.moebius b₁ : ℝ) * (V (y / b₁) + Hν)| :=
          abs_add_le _ _
      _ ≤ ((ν.divisors.card : ℝ) * (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ))
          + ((ν.divisors.card : ℝ) * (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ)) :=
          add_le_add hpart1 hpart2
      _ ≤ (ν.divisors.card : ℝ) * β * (4096 * (C₁ + C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by
          have hcoef : 4096 * C₂ + 1024 * C₁ ≤ 4096 * (C₁ + C₂) := by linarith [hC₁pos]
          have h1 : (ν.divisors.card : ℝ) * (β * (4096 * C₂)) * (Real.log (y : ℝ)) ^ (-5 : ℝ)
              + (ν.divisors.card : ℝ) * (β * (1024 * C₁)) * (Real.log (y : ℝ)) ^ (-5 : ℝ)
              = ((ν.divisors.card : ℝ) * β) * (4096 * C₂ + 1024 * C₁)
                  * (Real.log (y : ℝ)) ^ (-5 : ℝ) := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoef (mul_nonneg (Nat.cast_nonneg _) hβnn)) hA5nn
      _ = 4096 * (C₁ + C₂) * β * (ν.divisors.card : ℝ) * (Real.log (y : ℝ)) ^ (-(5 : ℤ)) := by
          rw [← hc5 (Real.log (y : ℝ))]; ring

end

end Commons.NumberTheory.Sieve
