/-
  Companion paper (§4): evaluation of the sum `T(x;Y)`.

  `T(x;y) = ∑_{n ≤ x} aₙ ρₙ L(n;y)` with `L(n;y) = ∑_{b ∣ n, b ≤ y} μ(b)(log n − log b)`.
  Following §§3–4 we split `T = T₁ + T₂` using the Möbius sum over `b`, evaluate the inner
  congruence sums through the sieve weights `λ_ν` (equation (4.3)), and obtain
  `T(x;y) = H·A(x) + O(A(x)(log y)^{-5} B + A(x)(log x)^{-2})`, where
  `H = ∏_p (1−g(p))(1−1/p)^{-1}` is the constant (1.13)–(1.14) of the companion and
  `B = ∑_{ν ≤ Δ} |λ_ν| g(ν) τ(ν) β_ν` controls the sieve weights.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel
import Submission.Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_log_eq
import Submission.Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le
import Submission.Commons.NumberTheory.Sieve.density_eulerProd_div_sigma_tendsto

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Multiplicativity of `g` at `lcm` -/

/-- For squarefree `b` and multiplicative `g`, `g(lcm ν b) = g(ν)·g(b/(ν,b))`. -/
lemma g_lcm_eqL {g : ℕ → ℝ} (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    {ν b : ℕ} (hb : Squarefree b) :
    g (Nat.lcm ν b) = g ν * g (b / Nat.gcd ν b) := by
  have hcop : Nat.Coprime ν (b / Nat.gcd ν b) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    set d := Nat.gcd ν (b / Nat.gcd ν b) with hd
    have hdb : d ∣ b := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right ν b))
    have hdν : d ∣ ν := Nat.gcd_dvd_left _ _
    have hdg : d ∣ Nat.gcd ν b := Nat.dvd_gcd hdν hdb
    have hdbg : d ∣ b / Nat.gcd ν b := Nat.gcd_dvd_right _ _
    have hdvd : d * d ∣ b := by
      have h := mul_dvd_mul hdg hdbg
      rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right ν b)] at h
    have := hb d hdvd
    rwa [Nat.isUnit_iff] at this
  have hlcm : Nat.lcm ν b = ν * (b / Nat.gcd ν b) := by
    rw [Nat.lcm, Nat.mul_div_assoc]
    exact Nat.gcd_dvd_right ν b
  rw [hlcm, hmul ν (b / Nat.gcd ν b) hcop]

/-! ### Discrete Abel summation for the `b`-congruence sums -/

/-- The discrete Abel functional attached to a step function `C`:
`C(N)·log N − ∑_{d ≤ N−1} C(d)·log((d+1)/d)`. -/
def abelForm (C : ℕ → ℝ) (N : ℕ) : ℝ :=
  C N * Real.log N
    - ∑ d ∈ Finset.Icc 1 (N - 1), C d * Real.log (((d : ℝ) + 1) / (d : ℝ))

/-- **(4.2)**: `∑_{n ≤ x, b ∣ n} aₙρₙ log n = V_b(x) log x − ∑_{d<x} V_b(d) log((d+1)/d)`. -/
theorem VbLog_eq_abel (a lam : ℕ → ℝ) (b : ℕ) (x : ℝ) :
    VbLog a lam b x = abelForm (fun d => Vb a lam b (d : ℝ)) ⌊x⌋₊ := by
  set N := ⌊x⌋₊ with hN
  have h := Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel
      (fun n => a n * rhoOf lam n * (if b ∣ n then 1 else 0)) N
  have hL : (∑ d ∈ Finset.Icc 1 N,
        (a d * rhoOf lam d * (if b ∣ d then 1 else 0)) * Real.log d)
      = VbLog a lam b x := by
    rw [VbLog, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn]
  have hS : ∀ m : ℕ, (∑ e ∈ Finset.Icc 1 m,
        a e * rhoOf lam e * (if b ∣ e then 1 else 0)) = Vb a lam b (m : ℝ) := by
    intro m
    have hm : ⌊(m : ℝ)⌋₊ = m := Nat.floor_natCast m
    rw [Vb, hm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hbn : b ∣ n <;> simp [hbn]
  rw [hL] at h
  rw [h]
  rw [abelForm]
  congr 1
  · rw [hS N]
  · apply Finset.sum_congr rfl
    intro d _
    rw [hS d]

/-- `abelForm` is additive in the first argument. -/
lemma abelForm_add (C₁ C₂ : ℕ → ℝ) (N : ℕ) :
    abelForm (fun d => C₁ d + C₂ d) N = abelForm C₁ N + abelForm C₂ N := by
  unfold abelForm
  have hsum : (∑ d ∈ Finset.Icc 1 (N - 1), (C₁ d + C₂ d) * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      = (∑ d ∈ Finset.Icc 1 (N - 1), C₁ d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        + ∑ d ∈ Finset.Icc 1 (N - 1), C₂ d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]; ring

/-- `abelForm` is homogeneous in the first argument. -/
lemma abelForm_smul (c : ℝ) (C : ℕ → ℝ) (N : ℕ) :
    abelForm (fun d => c * C d) N = c * abelForm C N := by
  unfold abelForm
  have hsum : (∑ d ∈ Finset.Icc 1 (N - 1), (c * C d) * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      = c * ∑ d ∈ Finset.Icc 1 (N - 1), C d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]; ring

/-- `∑_{n ≤ N} c n log n = abelForm (partial sums of c) N`. -/
lemma sum_mul_log_eq_abelForm (c : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, c n * Real.log n)
      = abelForm (fun m => ∑ n ∈ Finset.Icc 1 m, c n) N :=
  Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel c N

/-! ### The congruence sums at integer scales -/

/-- `A_d(m) = 0` whenever `d > m`. -/
lemma Ad_eq_zero_of_lt (a : ℕ → ℝ) {d m : ℕ} (h : m < d) : Ad a d (m : ℝ) = 0 := by
  rw [Ad, Nat.floor_natCast]
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnm⟩, hdn⟩ := hn
  exact absurd (le_trans (Nat.le_of_dvd (by omega) hdn) hnm) (by omega)

/-- `V_b(m) = ∑_{ν ≤ Δ} λ_ν A_{ν,b}(m)` at integer scale `m` ((4.3)), using that `λ`
vanishes above `Δ`. -/
lemma Vb_nat_eq_sum_lcm (a lam : ℕ → ℝ) {Δ : ℕ} (hΔ : ∀ ν, Δ < ν → lam ν = 0)
    {b m : ℕ} (hb0 : 0 < b) :
    Vb a lam b (m : ℝ) = ∑ ν ∈ Finset.Icc 1 Δ, lam ν * Ad a (Nat.lcm ν b) (m : ℝ) := by
  rw [Vb_eq_sum_lcm a lam b (m : ℝ), Nat.floor_natCast]
  have h1 : (∑ ν ∈ Finset.Icc 1 m, lam ν * Ad a (Nat.lcm ν b) (m : ℝ))
      = ∑ ν ∈ Finset.Icc 1 (max m Δ), lam ν * Ad a (Nat.lcm ν b) (m : ℝ) := by
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      have hxm : m < x := by omega
      have hlcm : m < Nat.lcm x b := lt_of_lt_of_le hxm (Nat.le_lcm_left x hb0)
      rw [Ad_eq_zero_of_lt a hlcm, mul_zero]
  have h2 : (∑ ν ∈ Finset.Icc 1 Δ, lam ν * Ad a (Nat.lcm ν b) (m : ℝ))
      = ∑ ν ∈ Finset.Icc 1 (max m Δ), lam ν * Ad a (Nat.lcm ν b) (m : ℝ) := by
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hxs
      simp only [Finset.mem_Icc] at hx hxs
      have hxΔ : Δ < x := by omega
      rw [hΔ x hxΔ, zero_mul]
  rw [h1, ← h2]

/-- The sieve coefficient `∑_{ν ≤ Δ} λ_ν g(lcm(ν,b)) = ∑_{ν ≤ Δ} λ_ν g(ν) g(b/(ν,b))`. -/
noncomputable def lamCoeff (g lam : ℕ → ℝ) (Δ b : ℕ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g ν * g (b / Nat.gcd ν b)

/-- For squarefree `b`, `∑_{ν ≤ Δ} λ_ν g(lcm(ν,b)) = lamCoeff g lam Δ b`. -/
lemma sum_lam_g_lcm_eqL_lamCoeff {g lam : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    {Δ b : ℕ} (hb : Squarefree b) :
    (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν b)) = lamCoeff g lam Δ b := by
  rw [lamCoeff]
  apply Finset.sum_congr rfl
  intro ν _
  rw [g_lcm_eqL hmul hb]
  ring

/-- **(4.3)–(4.4)**: `V_b(m) = lamCoeff·A(m) + ∑_ν λ_ν r_{lcm(ν,b)}(m)`. -/
lemma Vb_nat_eq_coeff {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ} {x : ℝ} {Δ : ℕ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hAd : Approx a g r x) (hΔ : ∀ ν, Δ < ν → lam ν = 0)
    {b m : ℕ} (hb0 : 0 < b) (hb : Squarefree b) :
    Vb a lam b (m : ℝ)
      = lamCoeff g lam Δ b * Acount a (m : ℝ)
        + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m := by
  rw [Vb_nat_eq_sum_lcm a lam hΔ hb0]
  have hpt : ∀ ν, lam ν * Ad a (Nat.lcm ν b) (m : ℝ)
      = lam ν * g (Nat.lcm ν b) * Acount a (m : ℝ) + lam ν * r (Nat.lcm ν b) m := by
    intro ν
    rw [hAd (Nat.lcm ν b) m]; ring
  have hsplit : (∑ ν ∈ Finset.Icc 1 Δ, lam ν * Ad a (Nat.lcm ν b) (m : ℝ))
      = (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν b)) * Acount a (m : ℝ)
        + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m := by
    calc (∑ ν ∈ Finset.Icc 1 Δ, lam ν * Ad a (Nat.lcm ν b) (m : ℝ))
        = ∑ ν ∈ Finset.Icc 1 Δ,
            (lam ν * g (Nat.lcm ν b) * Acount a (m : ℝ) + lam ν * r (Nat.lcm ν b) m) :=
          Finset.sum_congr rfl (fun ν _ => hpt ν)
      _ = (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν b) * Acount a (m : ℝ))
            + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m :=
          Finset.sum_add_distrib
      _ = (∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν b)) * Acount a (m : ℝ)
            + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m := by
          rw [Finset.sum_mul]
  rw [hsplit, sum_lam_g_lcm_eqL_lamCoeff hmul hb]

/-! ### Linearity of the Abel functional -/

lemma abelForm_congr {C₁ C₂ : ℕ → ℝ} (h : ∀ m, C₁ m = C₂ m) (N : ℕ) :
    abelForm C₁ N = abelForm C₂ N := by
  unfold abelForm
  rw [h N, Finset.sum_congr rfl (fun d _ => by rw [h d])]

lemma abelForm_zero (N : ℕ) : abelForm (fun _ => (0 : ℝ)) N = 0 := by
  unfold abelForm; simp

lemma abelForm_sum {ι : Type*} (s : Finset ι) (C : ι → ℕ → ℝ) (N : ℕ) :
    abelForm (fun m => ∑ i ∈ s, C i m) N = ∑ i ∈ s, abelForm (C i) N := by
  unfold abelForm
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ i ∈ s, C i N) * Real.log (N : ℝ) = ∑ i ∈ s, C i N * Real.log (N : ℝ) :=
    (Finset.sum_mul s (fun i => C i N) (Real.log (N : ℝ)))
  have h2 : (∑ d ∈ Finset.Icc 1 (N - 1),
        (∑ i ∈ s, C i d) * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      = ∑ d ∈ Finset.Icc 1 (N - 1),
          ∑ i ∈ s, C i d * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_mul]
  have h3 : (∑ d ∈ Finset.Icc 1 (N - 1),
          ∑ i ∈ s, C i d * Real.log (((d : ℝ) + 1) / (d : ℝ)))
      = ∑ i ∈ s, ∑ d ∈ Finset.Icc 1 (N - 1),
          C i d * Real.log (((d : ℝ) + 1) / (d : ℝ)) :=
    Finset.sum_comm
  rw [h1, h2, h3]

/-! ### The decomposition of `T₁` -/

/-- **§4, (4.1)–(4.4)**: the whole main term of `T₁` factors out, leaving the sieve
coefficient `∑_b μ(b)·lamCoeff(b)` times the Abel form of `A(·)`, plus a remainder. -/
lemma T1_eq {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ} {x y : ℝ} {Δ : ℕ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hAd : Approx a g r x) (hΔ : ∀ ν, Δ < ν → lam ν = 0) :
    T1 a lam x y
      = (∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) * lamCoeff g lam Δ b)
          * abelForm (fun m => Acount a (m : ℝ)) ⌊x⌋₊
        + ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
            (ArithmeticFunction.moebius b : ℝ) *
              ∑ ν ∈ Finset.Icc 1 Δ,
                lam ν * abelForm (fun m => r (Nat.lcm ν b) m) ⌊x⌋₊ := by
  have hpt : ∀ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
      (ArithmeticFunction.moebius b : ℝ) * VbLog a lam b x
      = (ArithmeticFunction.moebius b : ℝ)
          * (lamCoeff g lam Δ b * abelForm (fun m => Acount a (m : ℝ)) ⌊x⌋₊
              + ∑ ν ∈ Finset.Icc 1 Δ,
                  lam ν * abelForm (fun m => r (Nat.lcm ν b) m) ⌊x⌋₊) := by
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
    by_cases hbsq : Squarefree b
    · have hfun : (fun m : ℕ => Vb a lam b (m : ℝ))
          = fun m : ℕ => lamCoeff g lam Δ b * Acount a (m : ℝ)
              + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m := by
        funext m
        exact Vb_nat_eq_coeff hmul hAd hΔ (by omega) hbsq
      rw [VbLog_eq_abel, hfun]
      rw [show (fun m : ℕ => lamCoeff g lam Δ b * Acount a (m : ℝ)
              + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m)
            = (fun d => (fun m : ℕ => lamCoeff g lam Δ b * Acount a (m : ℝ)) d
                + (fun m : ℕ => ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) m) d)
            from rfl]
      rw [abelForm_add, abelForm_smul, abelForm_sum]
      simp only [abelForm_smul]
    · have hmu : (ArithmeticFunction.moebius b : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbsq]; norm_num
      rw [hmu, zero_mul, zero_mul]
  unfold T1
  rw [Finset.sum_congr rfl hpt]
  rw [show (∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
        (ArithmeticFunction.moebius b : ℝ)
          * (lamCoeff g lam Δ b * abelForm (fun m => Acount a (m : ℝ)) ⌊x⌋₊
              + ∑ ν ∈ Finset.Icc 1 Δ,
                  lam ν * abelForm (fun m => r (Nat.lcm ν b) m) ⌊x⌋₊))
      = ∑ b ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y),
          ((ArithmeticFunction.moebius b : ℝ)
              * (lamCoeff g lam Δ b * abelForm (fun m => Acount a (m : ℝ)) ⌊x⌋₊)
            + (ArithmeticFunction.moebius b : ℝ)
              * ∑ ν ∈ Finset.Icc 1 Δ,
                  lam ν * abelForm (fun m => r (Nat.lcm ν b) m) ⌊x⌋₊) from
      Finset.sum_congr rfl (fun b _ => by ring)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring


/-! ### Nonnegativity of the density at squarefree arguments -/

lemma g_nonneg_of_squarefree {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p) {n : ℕ} (hn : Squarefree n) : 0 ≤ g n := by
  rw [Commons.NumberTheory.Sieve.g_prod_primeFactors_of_squarefree hmul hg1 hn]
  exact Finset.prod_nonneg (fun p hp' => hp p (Nat.prime_of_mem_primeFactors hp'))

/-- The telescoping identity `∑_{d ≤ N-1} log((d+1)/d) = log N`. -/
lemma sum_log_ratio_Icc (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 (N - 1), Real.log (((d : ℝ) + 1) / (d : ℝ))) = Real.log (N : ℝ) := by
  have hIco : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext d; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco]
  have h : ∀ d ∈ Finset.Ico 1 N, Real.log (((d : ℝ) + 1) / (d : ℝ))
      = Real.log (((d + 1 : ℕ) : ℝ)) - Real.log ((d : ℕ) : ℝ) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [Real.log_div (by positivity) (by exact_mod_cast (by omega : d ≠ 0)), Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_congr rfl h, Finset.sum_Ico_sub (fun d : ℕ => Real.log ((d : ℕ) : ℝ)) (by omega)]
  simp

/-! ### Bounds for the sieve coefficients -/

/-- **§4, (4.4)**: `|∑_{b ≤ Y} μ(b) lamCoeff(b)| ≤ C₂₄·B·(log Y)^{-6}` where
`B = ∑_{ν ≤ Δ, ν squarefree} |λ_ν| g(ν) τ(ν) β_ν` and `C₂₄` is the constant of (2.4). -/
lemma sum_mu_lamCoeff_le {g lam : ℕ → ℝ} {Δ Y : ℕ} {C24 : ℝ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (h24 : ∀ ν y : ℕ, Squarefree ν → 2 ≤ y → ν ^ 2 ≤ y →
      |∑ b ∈ Finset.Icc 1 y,
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)|
        ≤ C24 * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) * (ν.divisors.card : ℝ)
            * (Real.log (y : ℝ)) ^ (-(6 : ℤ)))
    (hg1 : g 1 = 1) (hgp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hΔ : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hY : 2 ≤ Y) (hΔ2 : Δ ^ 2 ≤ Y) :
    |∑ b ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius b : ℝ) * lamCoeff g lam Δ b|
      ≤ C24 * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        * (Real.log (Y : ℝ)) ^ (-(6 : ℤ)) := by
  classical
  have h1 : (∑ b ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius b : ℝ) * lamCoeff g lam Δ b)
      = ∑ b ∈ Finset.Icc 1 Y, ∑ ν ∈ Finset.Icc 1 Δ,
          (ArithmeticFunction.moebius b : ℝ) * (lam ν * g ν * g (b / Nat.gcd ν b)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [lamCoeff, Finset.mul_sum]
  rw [h1, Finset.sum_comm]
  have hsplit : (∑ ν ∈ Finset.Icc 1 Δ, ∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius b : ℝ) * (lam ν * g ν * g (b / Nat.gcd ν b)))
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν _
    by_cases hνsq : Squarefree ν
    · rw [if_pos hνsq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    · rw [if_neg hνsq, hlam_sq ν hνsq, zero_mul]
      exact Finset.sum_eq_zero (fun b _ => by ring)
  rw [hsplit]
  calc |∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)|
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |(lam ν * g ν) * ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (C24 * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (Real.log (Y : ℝ)) ^ (-(6 : ℤ))) := by
        apply Finset.sum_le_sum
        intro ν hν
        rw [Finset.mem_filter, Finset.mem_Icc] at hν
        obtain ⟨⟨hν1, hνΔ⟩, hνsq⟩ := hν
        have hν2 : ν ^ 2 ≤ Y := le_trans (Nat.pow_le_pow_left hνΔ 2) hΔ2
        have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 hgp hνsq
        rw [abs_mul, show |lam ν * g ν| = |lam ν| * g ν from by rw [abs_mul, abs_of_nonneg hgnn]]
        refine le_trans (mul_le_mul_of_nonneg_left (h24 ν Y hνsq hY hν2)
          (mul_nonneg (abs_nonneg _) hgnn)) (le_of_eq ?_)
        ring
    _ = C24 * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        * (Real.log (Y : ℝ)) ^ (-(6 : ℤ)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ν _
        ring

/-- **§4, (4.4)**: `∑_{b ≤ Y} μ(b) log b · lamCoeff(b) = −H + O(B (log Y)^{-5})`. -/
lemma sum_mu_log_lamCoeff_eq {g lam : ℕ → ℝ} {Δ Y : ℕ} {C24 H : ℝ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (h24 : ∀ ν y : ℕ, Squarefree ν → 2 ≤ y → ν ^ 2 ≤ y →
      |(∑ b ∈ Finset.Icc 1 y,
          (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
          + (if ν = 1 then H else 0)|
        ≤ C24 * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) * (ν.divisors.card : ℝ)
            * (Real.log (y : ℝ)) ^ (-(5 : ℤ)))
    (hg1 : g 1 = 1) (hgp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hΔ : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_sq : ∀ ν, ¬ Squarefree ν → lam ν = 0)
    (hlam1 : lam 1 = 1) (hΔ1 : 1 ≤ Δ)
    (hY : 2 ≤ Y) (hΔ2 : Δ ^ 2 ≤ Y) :
    |(∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius b : ℝ) * Real.log b * lamCoeff g lam Δ b) + H|
      ≤ C24 * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        * (Real.log (Y : ℝ)) ^ (-(5 : ℤ)) := by
  classical
  have hmem1 : (1 : ℕ) ∈ (Finset.Icc 1 Δ).filter Squarefree := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hΔ1⟩, squarefree_one⟩
  have h1 : (∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius b : ℝ) * Real.log b * lamCoeff g lam Δ b)
      = ∑ b ∈ Finset.Icc 1 Y, ∑ ν ∈ Finset.Icc 1 Δ,
          (ArithmeticFunction.moebius b : ℝ) * Real.log b
            * (lam ν * g ν * g (b / Nat.gcd ν b)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [lamCoeff, Finset.mul_sum]
  rw [h1, Finset.sum_comm]
  have hsplit : (∑ ν ∈ Finset.Icc 1 Δ, ∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius b : ℝ) * Real.log b * (lam ν * g ν * g (b / Nat.gcd ν b)))
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ν _
    by_cases hνsq : Squarefree ν
    · rw [if_pos hνsq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    · rw [if_neg hνsq, hlam_sq ν hνsq, zero_mul]
      exact Finset.sum_eq_zero (fun b _ => by simp)
  rw [hsplit]
  have hH : (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        (lam ν * g ν) * (if ν = 1 then H else 0)) = H := by
    rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl, hlam1, hg1, one_mul, one_mul]
    · intro ν _ hν1
      rw [if_neg hν1, mul_zero]
    · intro hnot
      exact absurd hmem1 hnot
  have hmain : (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        (lam ν * g ν) * ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b) + H
      = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ((∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
            + (if ν = 1 then H else 0)) := by
    rw [show (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ((∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
            + (if ν = 1 then H else 0)))
        = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            ((lam ν * g ν) * (∑ b ∈ Finset.Icc 1 Y,
                (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
              + (lam ν * g ν) * (if ν = 1 then H else 0)) from
        Finset.sum_congr rfl (fun ν _ => by ring)]
    rw [Finset.sum_add_distrib, hH]
  rw [hmain]
  calc |∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (lam ν * g ν) * ((∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
            + (if ν = 1 then H else 0))|
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |(lam ν * g ν) * ((∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius b : ℝ) * g (b / Nat.gcd ν b) * Real.log b)
            + (if ν = 1 then H else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (C24 * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (Real.log (Y : ℝ)) ^ (-(5 : ℤ))) := by
        apply Finset.sum_le_sum
        intro ν hν
        rw [Finset.mem_filter, Finset.mem_Icc] at hν
        obtain ⟨⟨hν1, hνΔ⟩, hνsq⟩ := hν
        have hν2 : ν ^ 2 ≤ Y := le_trans (Nat.pow_le_pow_left hνΔ 2) hΔ2
        have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 hgp hνsq
        rw [abs_mul, show |lam ν * g ν| = |lam ν| * g ν from by rw [abs_mul, abs_of_nonneg hgnn]]
        refine le_trans (mul_le_mul_of_nonneg_left (h24 ν Y hνsq hY hν2)
          (mul_nonneg (abs_nonneg _) hgnn)) (le_of_eq ?_)
        ring
    _ = C24 * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          |lam ν| * g ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        * (Real.log (Y : ℝ)) ^ (-(5 : ℤ)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ν _
        ring

/-- The pointwise bound on `|abelForm (r ∘ lcm)|` used in the `T₁` remainder estimate. -/
private noncomputable def AbelR (r : ℕ → ℕ → ℝ) (N : ℕ) (b ν : ℕ) : ℝ :=
  |r (Nat.lcm ν b) N| * Real.log (N : ℝ)
    + ∑ d ∈ Finset.Icc 1 (N - 1), |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ))

/-- The `T₁` remainder: the `r`-terms of §4 contribute at most `2·log N·Rem`.  The chain keeps the
squarefree restrictions (`|μ b| = [b ♭]`, `λ_ν = 0` for non-squarefree `ν`), so that only the
squarefree part of the `(R′)`-sum is used. -/
lemma abelForm_r_bound {r : ℕ → ℕ → ℝ} {Δ Y D N : ℕ} {Rem : ℝ} {lam : ℕ → ℝ}
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hN : 1 ≤ N)
    (hRem : ∀ m : ℕ, m ≤ N → RemainderSum r D m ≤ Rem)
    (hΔY : Δ * Y ≤ D) :
    |∑ b ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius b : ℝ)
        * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * abelForm (fun m => r (Nat.lcm ν b) m) N|
      ≤ 2 * Real.log (N : ℝ) * Rem := by
  classical
  have hLnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlgnn : ∀ d ∈ Finset.Icc 1 (N - 1),
      0 ≤ Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    apply Real.log_nonneg
    rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < d))]
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  -- Pointwise bound on each `abelForm`
  have hpt : ∀ b ν : ℕ, |abelForm (fun m => r (Nat.lcm ν b) m) N| ≤ AbelR r N b ν := by
    intro b ν
    rw [AbelR]
    rw [abelForm]
    refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hLnn]
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro d hd
      rw [abs_mul, abs_of_nonneg (hlgnn d hd)]
  have hptnn : ∀ b ν : ℕ, 0 ≤ AbelR r N b ν := by
    intro b ν
    rw [AbelR]
    exact add_nonneg (mul_nonneg (abs_nonneg _) hLnn)
      (Finset.sum_nonneg (fun d hd => mul_nonneg (abs_nonneg _) (hlgnn d hd)))
  -- Reduce to a sum over squarefree `b, ν`
  have h2 : |∑ b ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius b : ℝ)
        * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * abelForm (fun m => r (Nat.lcm ν b) m) N|
      ≤ ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
          ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, AbelR r N b ν := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hstep1 : ∀ b : ℕ,
        |(ArithmeticFunction.moebius b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * abelForm (fun m => r (Nat.lcm ν b) m) N|
          ≤ |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * AbelR r N b ν := by
      intro b
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum
      intro ν _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpt b ν) (abs_nonneg _)
    refine le_trans (Finset.sum_le_sum (fun b _ => hstep1 b)) ?_
    exact sum_mu_lam_abs_le_sqfree (s := Finset.Icc 1 Y) (t := Finset.Icc 1 Δ)
      (F := AbelR r N) hptnn hlam_sq hlam
  refine le_trans h2 ?_
  have hAB : (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
        ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, AbelR r N b ν)
      = ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
          ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            (|r (Nat.lcm ν b) N| * Real.log (N : ℝ)
              + ∑ d ∈ Finset.Icc 1 (N - 1),
                  |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ))) := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro ν _
    rw [AbelR]
  rw [hAB]
  -- Split the double sum
  set S1 : ℝ := ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
      ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) N| with hS1
  set S2 : ℝ := ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
      ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        ∑ d ∈ Finset.Icc 1 (N - 1), |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ))
    with hS2
  have hsplit : (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
        ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          (|r (Nat.lcm ν b) N| * Real.log (N : ℝ)
            + ∑ d ∈ Finset.Icc 1 (N - 1),
                |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ))))
      = S1 * Real.log (N : ℝ) + S2 := by
    rw [hS1, hS2]
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
  rw [hsplit]
  -- Bound `S1`
  have hS1b : S1 ≤ Rem := by
    rw [hS1, Finset.sum_comm]
    exact le_trans (sum_lcm_le_remainderSum (Δ := Δ) (M := Y) (D := D) hΔY N) (hRem N le_rfl)
  -- Bound `S2`
  have hS2b : S2 ≤ Real.log (N : ℝ) * Rem := by
    rw [hS2]
    rw [show (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
          ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          ∑ d ∈ Finset.Icc 1 (N - 1),
            |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        = ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
            ∑ d ∈ Finset.Icc 1 (N - 1),
              ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
                |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    have hbd : ∀ d ∈ Finset.Icc 1 (N - 1),
        (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
          ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) d|) ≤ Rem := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [Finset.sum_comm]
      exact le_trans (sum_lcm_le_remainderSum (Δ := Δ) (M := Y) (D := D) hΔY d)
        (hRem d (by omega))
    have hfin : (∑ d ∈ Finset.Icc 1 (N - 1),
          ∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 (N - 1), Real.log (((d : ℝ) + 1) / (d : ℝ)) * Rem := by
      apply Finset.sum_le_sum
      intro d hd
      have h1 : (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              |r (Nat.lcm ν b) d| * Real.log (((d : ℝ) + 1) / (d : ℝ)))
          = (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
              ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) d|)
              * Real.log (((d : ℝ) + 1) / (d : ℝ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
      rw [h1]
      calc (∑ b ∈ (Finset.Icc 1 Y).filter Squarefree,
              ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) d|)
              * Real.log (((d : ℝ) + 1) / (d : ℝ))
          ≤ Rem * Real.log (((d : ℝ) + 1) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right (hbd d hd) (hlgnn d hd)
        _ = Real.log (((d : ℝ) + 1) / (d : ℝ)) * Rem := by ring
    refine le_trans hfin ?_
    rw [← Finset.sum_mul, sum_log_ratio_Icc N hN]
  have hS1' : S1 * Real.log (N : ℝ) ≤ Real.log (N : ℝ) * Rem := by
    refine le_trans (mul_le_mul_of_nonneg_right hS1b hLnn) (le_of_eq (by ring))
  linarith [hS1', hS2b]

/-! ### The main theorem of §4 -/

/-- The `abelForm` of the counting function equals `∑_{n ≤ N} aₙ log n`. -/
lemma abelForm_Acount_eq (a : ℕ → ℝ) (N : ℕ) :
    abelForm (fun m => Acount a (m : ℝ)) N
      = ∑ n ∈ Finset.Icc 1 N, a n * Real.log (n : ℝ) := by
  have hfun : (fun m : ℕ => Acount a (m : ℝ)) = fun m => ∑ n ∈ Finset.Icc 1 m, a n := by
    funext m
    rw [Acount, Nat.floor_natCast]
  rw [hfun, abelForm, ← Commons.NumberTheory.FriedlanderIwaniec.sum_mul_log_abel a N]

/-- `|abelForm(A(·))| ≤ A·log x`. -/
lemma abs_abelForm_Acount_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {N : ℕ} (hN : 1 ≤ N) :
    |abelForm (fun m => Acount a (m : ℝ)) N| ≤ Acount a (N : ℝ) * Real.log (N : ℝ) := by
  rw [abelForm_Acount_eq]
  calc |∑ n ∈ Finset.Icc 1 N, a n * Real.log (n : ℝ)|
      ≤ ∑ n ∈ Finset.Icc 1 N, |a n * Real.log (n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc 1 N, a n * Real.log (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [abs_of_nonneg (mul_nonneg (ha n) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))))]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, a n * Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hn.2)) (ha n)
    _ = Acount a (N : ℝ) * Real.log (N : ℝ) := by
        rw [Acount, Nat.floor_natCast, Finset.sum_mul]

/-- `∑_{e ≤ D, ♭} τ(e)²|r e m| ≤ RemainderSum r D m`, since `τ(e) ≥ 1`. -/
lemma sum_tau_sq_abs_le_remainderSum {r : ℕ → ℕ → ℝ} {D m : ℕ} :
    (∑ e ∈ (Finset.Icc 1 D).filter Squarefree, ((e.divisors.card : ℝ)) ^ 2 * |r e m|)
      ≤ RemainderSum r D m := by
  rw [RemainderSum]
  apply Finset.sum_le_sum
  intro e he
  rw [Finset.mem_filter, Finset.mem_Icc] at he
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h1 : (1 : ℝ) ≤ (e.divisors.card : ℝ) := by
    have hpos : 0 < e.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd e, by omega⟩⟩
    exact_mod_cast hpos
  calc ((e.divisors.card : ℝ)) ^ 2 = ((e.divisors.card : ℝ)) ^ 2 * 1 := by ring
    _ ≤ ((e.divisors.card : ℝ)) ^ 2 * ((e.divisors.card : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ h1) (by positivity)
    _ = ((e.divisors.card : ℝ)) ^ 5 := by ring

/-- **§4**: `T(x;y) = H·A(x) + O(A(x)·(B (log y)^{-5} + (log x)^{-2}))`. -/
theorem T_eval {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ}
    {N M D Δ : ℕ} {A Rem B : ℝ}
    (hx : 2 ≤ N) (hy : 2 ≤ M) (hyx : M ≤ N)
    (hlog2 : Real.log (N : ℝ) ≤ 2 * Real.log (M : ℝ))
    (ha : ∀ n : ℕ, 0 ≤ a n) (hA : A = Acount a N)
    (hAd : Approx a g r (N : ℝ))
    (hRem : ∀ m : ℕ, m ≤ N → RemainderSum r D m ≤ Rem) (hRem0 : 0 ≤ Rem)
    (hRem3 : Rem ≤ A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
    (hΔy : Δ * M ≤ D) (hΔ2 : Δ ^ 2 ≤ M) (hΔ1 : 1 ≤ Δ)
    (hlam1 : lam 1 = 1) (hΔsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        |lam ν| * g ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) ≤ B)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ z : ℝ, 2 ≤ z →
      |(∑ p ∈ (Finset.Icc 2 ⌊z⌋₊).filter Nat.Prime, g p) - Real.log (Real.log z) - c|
        ≤ C * (Real.log z) ^ (-(10 : ℤ))) :
    ∃ K H : ℝ, 0 < K ∧ 0 < H ∧
      Filter.Tendsto (fun n : ℕ => ∑ d ∈ Finset.Icc 1 n,
          (ArithmeticFunction.moebius d : ℝ) * g d * Real.log d) Filter.atTop (nhds (-H)) ∧
      |Tsum a lam (N : ℝ) (M : ℝ) - H * A|
        ≤ K * A * (B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
  classical
  obtain ⟨C24, hC24pos, h24⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le hgmul hg1 hp hbound h9
  obtain ⟨C24', H, hC24'pos, hHpos, hHtend, h24log⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_log_eq hgmul hg1 hp hbound h9
  have hgp : ∀ p : ℕ, p.Prime → 0 ≤ g p := fun p hp' => (hp p hp').1
  have hN1 : 1 ≤ N := by omega
  have hM1 : 1 ≤ M := by omega
  have hlogN1 : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogM1 : (0 : ℝ) < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hfl : ⌊(M : ℝ)⌋₊ ≤ N := by rw [Nat.floor_natCast]; exact hyx
  have hfil : (Finset.Icc 1 N).filter (fun b => ((b : ℕ) : ℝ) ≤ (M : ℝ)) = Finset.Icc 1 M := by
    rw [filter_Icc_eq_Icc_floor (by positivity) hfl, Nat.floor_natCast]
  have hAeq : A = Acount a (N : ℝ) := by rw [hA, Acount, Nat.floor_natCast]
  have hA0 : 0 ≤ A := by
    rw [hAeq, Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => ha n)
  have hB0 : 0 ≤ B := by
    refine le_trans (Finset.sum_nonneg ?_) hB
    intro ν hν
    rw [Finset.mem_filter] at hν
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 hgp hν.2
    refine mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hgnn) (by positivity)) ?_
    exact Finset.prod_nonneg (fun p hp' => by
      have : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp'))
      positivity)
  have hpow : ∀ k : ℤ, 0 ≤ (Real.log (M : ℝ)) ^ k := fun k => zpow_nonneg hlogM1.le k
  -- (1) `T₁`
  have hT1rw : T1 a lam (N : ℝ) (M : ℝ)
      = ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * VbLog a lam b (N : ℝ) := by
    rw [T1, Nat.floor_natCast, hfil]
  have hT1eq := T1_eq (a := a) (g := g) (r := r) (lam := lam) (x := (N : ℝ)) (y := (M : ℝ))
    (Δ := Δ) hgmul hAd hΔsupp
  rw [Nat.floor_natCast, hfil] at hT1eq
  have hcoeff : |∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * lamCoeff g lam Δ b|
      ≤ C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := by
    refine le_trans (sum_mu_lamCoeff_le hgmul (fun ν y hν hy hνy => h24 ν hν y hy hνy) hg1 hgp hΔsupp hlam_sq hy hΔ2) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC24pos.le)
      (zpow_nonneg hlogM1.le _)
  have hLMS : (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * Real.log (M : ℝ)
      = (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
    have h := zpow_add₀ (ne_of_gt hlogM1) (-(6 : ℤ)) 1
    rw [zpow_one, show (-(6 : ℤ)) + 1 = -(5 : ℤ) from by norm_num] at h
    exact h.symm
  have hT1b : |T1 a lam (N : ℝ) (M : ℝ)|
      ≤ 2 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ))
        + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    have hmain : C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * Real.log (N : ℝ))
        ≤ 2 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
      calc C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * Real.log (N : ℝ))
          ≤ C24 * B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (A * (2 * Real.log (M : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2 hA0) ?_
            exact mul_nonneg (mul_nonneg hC24pos.le hB0) (hpow _)
        _ = 2 * C24 * B * A * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
            rw [← hLMS]; ring
    have hrem : 2 * Real.log (N : ℝ) * Rem ≤ 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
      have h1 : 2 * Real.log (N : ℝ) * Rem
          ≤ 2 * Real.log (N : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) :=
        mul_le_mul_of_nonneg_left hRem3 (by linarith)
      refine le_trans h1 (le_of_eq ?_)
      have hLN3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))
          = (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
        have h := zpow_add₀ (ne_of_gt hlogN1) 1 (-(3 : ℤ))
        rw [zpow_one, show (1 : ℤ) + (-(3 : ℤ)) = -(2 : ℤ) from by norm_num] at h
        exact h.symm
      rw [← hLN3]; ring
    rw [hT1eq]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add ?_ ?_) (add_le_add hmain hrem)
    · have habelA : |abelForm (fun m => Acount a (m : ℝ)) N| ≤ A * Real.log (N : ℝ) := by
        rw [hAeq]
        exact abs_abelForm_Acount_le ha hN1
      rw [abs_mul]
      exact le_trans (mul_le_mul hcoeff habelA (abs_nonneg _)
        (mul_nonneg (mul_nonneg hC24pos.le hB0) (hpow _))) (le_of_eq rfl)
    · exact abelForm_r_bound (r := r) (Δ := Δ) (Y := M) (D := D) (N := N) (Rem := Rem)
        hlam_le hlam_sq hN1 (hRem) hΔy
  -- (2) `T₂`
  have hT2rw : T2 a lam (N : ℝ) (M : ℝ)
      = ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * Vb a lam b (N : ℝ) := by
    rw [T2, Nat.floor_natCast, hfil]
  have hT2eq : T2 a lam (N : ℝ) (M : ℝ) + H * A
      = A * ((∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * lamCoeff g lam Δ b) + H)
        + ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N := by
    rw [hT2rw]
    have hpt : ∀ b ∈ Finset.Icc 1 M,
        (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ) * Vb a lam b (N : ℝ)
          = (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * (lamCoeff g lam Δ b * Acount a (N : ℝ)
                  + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      by_cases hbsq : Squarefree b
      · rw [Vb_nat_eq_coeff hgmul hAd hΔsupp (by omega) hbsq]
      · have hmu : (ArithmeticFunction.moebius b : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbsq]; norm_num
        rw [hmu]; ring
    rw [Finset.sum_congr rfl hpt]
    rw [show (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * (lamCoeff g lam Δ b * Acount a (N : ℝ)
              + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N))
        = (∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * lamCoeff g lam Δ b * Acount a (N : ℝ))
          + ∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
              * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N from by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b _
        ring]
    rw [← Finset.sum_mul, hAeq]
    ring
  have hlogMN : Real.log (M : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ M)) (by exact_mod_cast hyx)
  have hLN3 : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))
      = (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    have h := zpow_add₀ (ne_of_gt hlogN1) 1 (-(3 : ℤ))
    rw [zpow_one, show (1 : ℤ) + (-(3 : ℤ)) = -(2 : ℤ) from by norm_num] at h
    exact h.symm
  have hrtail : Real.log (M : ℝ) * Rem ≤ A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hRem3 hlogM1.le) ?_
    calc Real.log (M : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
        = A * (Real.log (M : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) := by ring
      _ ≤ A * (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogMN (zpow_nonneg hlogN1.le _)) hA0
      _ = A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by rw [hLN3]
  have hcoefflog : |(∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * lamCoeff g lam Δ b) + H| ≤ C24' * B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := by
    refine le_trans (sum_mu_log_lamCoeff_eq hgmul (fun ν y hν hy hνy => h24log ν hν y hy hνy) hg1 hgp hΔsupp hlam_sq hlam1 hΔ1
      hy hΔ2) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC24'pos.le)
      (zpow_nonneg hlogM1.le _)
  have hr2 : |∑ b ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
          * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
      ≤ Real.log (M : ℝ) * Rem := by
    have h1 : ∀ b ∈ Finset.Icc 1 M,
        |(ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          ≤ |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      have hlogb0 : 0 ≤ Real.log (b : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
      have hlogbM : Real.log (b : ℝ) ≤ Real.log (M : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 1 ≤ b)) (by exact_mod_cast hb.2)
      have hle : |∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν b) N| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro ν _
        rw [abs_mul]
      calc |(ArithmeticFunction.moebius b : ℝ) * Real.log (b : ℝ)
            * ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|
          = |(ArithmeticFunction.moebius b : ℝ)|
              * (Real.log (b : ℝ) * |∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν b) N|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlogb0]; ring
        _ ≤ |(ArithmeticFunction.moebius b : ℝ)|
              * (Real.log (M : ℝ) * ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν b) N|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hlogbM hle (abs_nonneg _) hlogM1.le) (abs_nonneg _)
        _ = |(ArithmeticFunction.moebius b : ℝ)| * ∑ ν ∈ Finset.Icc 1 Δ,
              |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro ν _
            ring
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum h1) ?_
    have h2 : (∑ b ∈ Finset.Icc 1 M, |(ArithmeticFunction.moebius b : ℝ)|
          * ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|))
        ≤ ∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|) :=
      sum_mu_lam_abs_le_sqfree (s := Finset.Icc 1 M) (t := Finset.Icc 1 Δ)
        (F := fun b ν => Real.log (M : ℝ) * |r (Nat.lcm ν b) N|)
        (fun b ν => mul_nonneg hlogM1.le (abs_nonneg _)) hlam_sq hlam_le
    refine le_trans h2 ?_
    have h3 : (∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (Real.log (M : ℝ) * |r (Nat.lcm ν b) N|))
        = Real.log (M : ℝ) * ∑ b ∈ (Finset.Icc 1 M).filter Squarefree,
            ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν b) N| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    rw [h3]
    refine mul_le_mul_of_nonneg_left ?_ hlogM1.le
    rw [Finset.sum_comm]
    exact le_trans (sum_lcm_le_remainderSum (Δ := Δ) (M := M) (D := D) hΔy N) (hRem N le_rfl)
  have hT2b : |T2 a lam (N : ℝ) (M : ℝ) + H * A|
      ≤ A * (C24' * B * (Real.log (M : ℝ)) ^ (-(5 : ℤ))) + A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
    rw [hT2eq]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hA0]
    exact add_le_add (mul_le_mul_of_nonneg_left hcoefflog hA0) (le_trans hr2 hrtail)
  -- (3) assembly
  have hTsum : Tsum a lam (N : ℝ) (M : ℝ) - H * A
      = T1 a lam (N : ℝ) (M : ℝ) - (T2 a lam (N : ℝ) (M : ℝ) + H * A) := by
    rw [Tsum_eq, T1, T2]; ring
  refine ⟨2 * C24 + C24' + 3, H, by positivity, hHpos, hHtend, ?_⟩
  rw [hTsum]
  refine le_trans (le_trans (abs_sub _ _) (add_le_add hT1b hT2b)) ?_
  have hX : 0 ≤ B * (Real.log (M : ℝ)) ^ (-(5 : ℤ)) := mul_nonneg hB0 (zpow_nonneg hlogM1.le _)
  have hY : 0 ≤ (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := zpow_nonneg hlogN1.le _
  have hKA : 0 ≤ (2 * C24 + C24' + 3) * A := by positivity
  nlinarith [hA0, hX, hY, hC24pos, hC24'pos.le, mul_nonneg hA0 hX, mul_nonneg hA0 hY,
    mul_nonneg (by positivity : (0:ℝ) ≤ 2 * C24 + C24' + 3) hA0]

end

end Submission.ASP
