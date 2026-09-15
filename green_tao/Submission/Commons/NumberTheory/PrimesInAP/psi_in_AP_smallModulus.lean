import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum
import Submission.Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp
import Submission.Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime
import Submission.Commons.Analysis.Asymptotics.eventually_polylog_le_exp_sub_sqrt
import Submission.Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive

/-!
# Primes in arithmetic progressions for small moduli

We reduce the Siegel--Walfisz type estimate
`|psi(x; q, a) - x/phi(q)| <= C x exp(-c sqrt(log x / log(q+2)))`,
valid uniformly for `q <= (log x)^A`, to the twisted von Mangoldt estimate
`|sum_{n<=x} chi(n) Lambda(n)| <= C x exp(-c sqrt(log x / log(q+2)))`
for every non-trivial Dirichlet character `chi mod q` (the lemma
`Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound`), using the
character expansion of the individual progression and the prime number theorem
in the form `|psi(x) - x| <= x exp(-c sqrt(log x))`.
-/

open Finset Filter
namespace Commons.NumberTheory.PrimesInAP
set_option maxHeartbeats 2000000
noncomputable section

private lemma two_le_level {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : 2 ≤ N := by
  by_contra hcon
  push Not at hcon
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : N = 1 := by omega
  subst hN1
  exact hχ (Subsingleton.elim χ 1)

private lemma chi_apply_eq_primitive_or_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (n : ℕ) :
    χ (n : ZMod N) = if Nat.Coprime n N then χ.primitiveCharacter (n : ZMod χ.conductor) else 0 := by
  set d := χ.conductor with hd
  set χ₀ : DirichletCharacter ℂ d := χ.primitiveCharacter with hχ₀
  have hdiv : d ∣ N := by rw [hd]; exact χ.conductor_dvd_level
  have hchange : DirichletCharacter.changeLevel hdiv χ₀ = χ := by
    rw [hχ₀]; exact DirichletCharacter.changeLevel_primitiveCharacter χ
  by_cases h : Nat.Coprime n N
  · rw [if_pos h]
    have ha : IsCoprime (n : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hdiv ha
    rw [hchange, hχ₀] at h1
    simpa using h1
  · rw [if_neg h]
    have ha : ¬ IsCoprime (n : ℤ) (N : ℤ) := fun hh => h (Nat.isCoprime_iff_coprime.mp hh)
    simpa using (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr ha

private lemma chebyshev_sum_eq_filtered {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)
      = ∑ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Coprime n N),
          χ.primitiveCharacter (n : ZMod χ.conductor) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun n _ => by
    rw [chi_apply_eq_primitive_or_zero χ n]
    by_cases h : Nat.Coprime n N <;> simp [h])

private lemma not_coprime_sum_bound {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hM : 1 ≤ M) :
    ‖∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n N),
        χ.primitiveCharacter (n : ZMod χ.conductor) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ (N : ℝ) * Real.log M := by
  set F := (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n N) with hF
  set G := (Finset.Icc 1 M).filter (fun p => Nat.Prime p ∧ p ∣ N) with hG
  have h1 : ‖∑ n ∈ F, χ.primitiveCharacter (n : ZMod χ.conductor) *
        (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ∑ n ∈ F, ArithmeticFunction.vonMangoldt n := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
    rw [norm_mul]
    have hle : ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [h2]
    nlinarith [hle, ArithmeticFunction.vonMangoldt_nonneg (n := n)]
  have h2 : ∑ n ∈ F, ArithmeticFunction.vonMangoldt n = ∑ p ∈ G, (Nat.log p M : ℝ) * Real.log p := by
    rw [hF, hG]
    exact Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime N M
  have h3 : ∑ p ∈ G, (Nat.log p M : ℝ) * Real.log p ≤ ∑ p ∈ G, Real.log M := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [hG] at hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpM⟩, hpprime, hpdvd⟩ := hp
    have hpow : p ^ (Nat.log p M) ≤ M := Nat.pow_log_le_self p (Nat.one_le_iff_ne_zero.mp hM)
    have hle : Real.log ((p : ℝ) ^ (Nat.log p M)) ≤ Real.log M :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow] at hle
    linarith [hle]
  have h4 : ∑ p ∈ G, Real.log M = (G.card : ℝ) * Real.log M := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h5 : G.card ≤ N := by
    have hsub : G ⊆ Finset.Icc 1 N := by
      intro p hp
      rw [hG] at hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hpM⟩, hpprime, hpdvd⟩ := hp
      rw [Finset.mem_Icc]
      exact ⟨hp1, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpdvd⟩
    have := Finset.card_le_card hsub
    simpa using this
  have hlogMnn : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  calc _ ≤ ∑ n ∈ F, ArithmeticFunction.vonMangoldt n := h1
    _ = ∑ p ∈ G, (Nat.log p M : ℝ) * Real.log p := h2
    _ ≤ ∑ p ∈ G, Real.log M := h3
    _ = (G.card : ℝ) * Real.log M := h4
    _ ≤ (N : ℝ) * Real.log M := by
        apply mul_le_mul_of_nonneg_right _ hlogMnn
        exact_mod_cast h5

private lemma polylog_absorb (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (Real.log x) ^ (A + 1) ≤ x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log 3))) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c' : ℝ := c / Real.sqrt (Real.log 3) with hc'def
  have hc' : 0 < c' := by rw [hc'def]; positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A + 1 ≤ (k : ℝ) := ⟨Nat.ceil (A + 1), Nat.le_ceil _⟩
  obtain ⟨X, hX⟩ := Commons.Analysis.Asymptotics.eventually_polylog_le_exp_sub_sqrt c' hc' k 1 (by norm_num)
  refine ⟨max (max X 3) (Real.exp 3), ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_of_lt Real.exp_one_lt_three
    exact le_trans h3 (Real.log_le_log (by norm_num) hx3)
  have h1 : (Real.log x) ^ (A + 1) ≤ (Real.log x) ^ k := by
    have h := Real.rpow_le_rpow_of_exponent_le hlog1 hk
    simpa [Real.rpow_natCast] using h
  have h2 : (Real.log x) ^ k ≤ Real.exp (Real.log x - c' * Real.sqrt (Real.log x)) := by
    have h := hX x hxX
    simpa using h
  have h3 : Real.exp (Real.log x - c' * Real.sqrt (Real.log x)) =
      x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log 3))) := by
    rw [show Real.log x - c' * Real.sqrt (Real.log x)
        = Real.log x + (-(c * Real.sqrt (Real.log x / Real.log 3))) by
      rw [hc'def]
      rw [Real.sqrt_div (show (0:ℝ) ≤ Real.log x by positivity) (Real.log 3)]
      ring]
    rw [Real.exp_add, Real.exp_log hxpos]
  linarith [h1, h2, le_of_eq h3]

private theorem psiChi_bound_all (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (N : ℝ) ≤ (Real.log x) ^ A →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
  obtain ⟨c, C, hc, hC, x₁, hP⟩ :=
    Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive A hA
  obtain ⟨X₂, hX₂⟩ := polylog_absorb A c hA hc
  refine ⟨c, C + 1, hc, by linarith, max x₁ (max X₂ 3), ?_⟩
  intro x hx N hN χ hχ hNx
  haveI : NeZero N := hN
  have hxx₁ : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hflo1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1 : ((1:ℕ):ℝ) ≤ x)
  have hlog1 : 1 ≤ Real.log x := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; exact le_of_lt Real.exp_one_lt_three
    exact le_trans h3 (Real.log_le_log (by norm_num) hx3)
  have hN2 : 2 ≤ N := two_le_level χ hχ
  set d : ℕ := χ.conductor with hd
  haveI : NeZero d := ⟨by rw [hd]; exact χ.conductor_ne_zero⟩
  have hdvd : d ∣ N := by rw [hd]; exact χ.conductor_dvd_level
  have hdN : (d:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd
  have hdA : (d:ℝ) ≤ (Real.log x) ^ A := le_trans hdN hNx
  have hχ₀ne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, DirichletCharacter.changeLevel_one]
  have hχ₀prim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hP0 := hP x hxx₁ d χ.primitiveCharacter hχ₀ne hχ₀prim hdA
  -- bounds
  have hExpStep : Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((d:ℝ) + 2)))) ≤
      Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
    apply Real.exp_le_exp.mpr
    have hlogd : Real.log ((d:ℝ) + 2) ≤ Real.log ((N:ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hd2pos : 0 < Real.log ((d:ℝ) + 2) := Real.log_pos (by have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d; linarith)
    have hN2pos : 0 < Real.log ((N:ℝ) + 2) := Real.log_pos (by have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N; linarith)
    have h1 : Real.log x / Real.log ((N:ℝ) + 2) ≤ Real.log x / Real.log ((d:ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) hd2pos hlogd
    have h2 : Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)) ≤
        Real.sqrt (Real.log x / Real.log ((d:ℝ) + 2)) := Real.sqrt_le_sqrt h1
    nlinarith [h2, hc]
  have hpsplit : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ))
      = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n N),
            χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)
          + ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n N),
            χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 ⌊x⌋₊)
      (p := fun n => Nat.Coprime n N)
      (f := fun n => χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ))
    exact h.symm
  have hcorr := not_coprime_sum_bound (M := ⌊x⌋₊) χ hflo1
  have hfil_eq : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n N),
        χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ))
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ))
        - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n N),
            χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    rw [hpsplit]; ring
  have hchain : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) + (N:ℝ) * Real.log ⌊x⌋₊ := by
    rw [chebyshev_sum_eq_filtered (M := ⌊x⌋₊) χ, hfil_eq]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ.primitiveCharacter (n : ZMod d) *
        (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) :=
      le_trans hP0 (mul_le_mul_of_nonneg_left hExpStep (by positivity))
    have h2 : ‖∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n N),
        χ.primitiveCharacter (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ (N:ℝ) * Real.log ⌊x⌋₊ := hcorr
    linarith [h1, h2]
  -- absorb the polynomial
  have hNlog : (N:ℝ) * Real.log ⌊x⌋₊ ≤ (Real.log x) ^ (A + 1) := by
    have hlogflo : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x :=
      Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
    have hlogx0 : (0:ℝ) < Real.log x := by linarith
    have h1 : (N:ℝ) * Real.log ⌊x⌋₊ ≤ (Real.log x)^A * Real.log x :=
      mul_le_mul hNx hlogflo (Real.log_nonneg (by exact_mod_cast hflo1)) (Real.rpow_nonneg hlogx0.le A)
    have h2 : (Real.log x)^A * Real.log x = (Real.log x)^(A + 1) := by
      rw [Real.rpow_add hlogx0 A 1, Real.rpow_one]
    linarith [h1, le_of_eq h2]
  have habsorb : (N:ℝ) * Real.log ⌊x⌋₊ ≤ x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
    refine le_trans hNlog (le_trans (hX₂ x hxX₂) ?_)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hlogN2 : 0 < Real.log ((N:ℝ) + 2) := Real.log_pos (by have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N; linarith)
    have hNc : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
    have h3N : Real.log 3 ≤ Real.log ((N:ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
    have h1 : Real.log x / Real.log ((N:ℝ) + 2) ≤ Real.log x / Real.log 3 :=
      div_le_div_of_nonneg_left (by linarith) (Real.log_pos (by norm_num)) h3N
    have h2 : Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)) ≤ Real.sqrt (Real.log x / Real.log 3) :=
      Real.sqrt_le_sqrt h1
    nlinarith [h2, hc]
  calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
      ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) + (N:ℝ) * Real.log ⌊x⌋₊ := hchain
    _ ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) +
        x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by
        linarith [habsorb]
    _ = (C + 1) * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((N:ℝ) + 2)))) := by ring


private lemma psi_eq_sum_Icc_one (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  rw [show Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) from by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]

private lemma sum_range_succ_eq_sum_Icc (N : ℕ) (g : ℕ → ℂ) (hg0 : g 0 = 0) :
    (∑ n ∈ Finset.range (N+1), g n) = ∑ n ∈ Finset.Icc 1 N, g n := by
  have h : Finset.range (N+1) = insert 0 (Finset.Icc 1 N) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [h, Finset.sum_insert (by simp), hg0, zero_add]

private lemma sum_range_filter_eq_Icc_filter (N q a : ℕ) (f : ℕ → ℂ) (hf0 : f 0 = 0) :
    (∑ n ∈ (Finset.range (N+1)).filter (fun n => n % q = a % q), f n)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q), f n := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sum_range_succ_eq_sum_Icc N (fun n => if n % q = a % q then f n else 0) (by simp [hf0])

private lemma psi_AP_eq_charSum (q : ℕ) [NeZero q] (x : ℝ) (a : ℕ) (ha : a.Coprime q) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q),
        (ArithmeticFunction.vonMangoldt n : ℂ))
      = ((Nat.totient q : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) *
            (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) := by
  have h := Commons.NumberTheory.BombieriVinogradov.residue_vonMangoldt_char_sum q ⌊x⌋₊ a ha
  rw [sum_range_filter_eq_Icc_filter (⌊x⌋₊) q a _ (by simp)] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro χ _
  congr 1
  exact sum_range_succ_eq_sum_Icc (⌊x⌋₊) _ (by simp)

private lemma principal_one (q : ℕ) [NeZero q] (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  change (MulChar.trivial (ZMod q) ℂ) (n : ZMod q) = if n.Coprime q then 1 else 0
  rw [MulChar.trivial_apply]
  by_cases h : IsUnit ((n:ℕ) : ZMod q)
  · rw [if_pos h, if_pos ((ZMod.isUnit_iff_coprime n q).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((ZMod.isUnit_iff_coprime n q).mpr hc))]

private lemma card_primeFactors_le_log_div_log (q : ℕ) (hq : q ≠ 0) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2card : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2:ℕ) := (Finset.prod_const (s := q.primeFactors) (2:ℕ)).symm
      _ ≤ ∏ p ∈ q.primeFactors, p := by
          apply Finset.prod_le_prod
          · intro p _; exact Nat.zero_le _
          · intro p hp; exact (Nat.mem_primeFactors.mp hp).1.two_le
      _ = UniqueFactorizationMonoid.radical q := (Nat.radical_eq_prod_primeFactors (n := q)).symm
      _ ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (UniqueFactorizationMonoid.radical_dvd_self)
  have hcast : (2:ℝ) ^ q.primeFactors.card ≤ (q:ℝ) := by exact_mod_cast h2card
  have hlog := Real.log_le_log (by positivity) hcast
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ hlog2).mpr hlog

private lemma natlog_mul_log_le_log (p N : ℕ) (hp : 2 ≤ p) (hN : N ≠ 0) :
    ((Nat.log p N : ℕ) : ℝ) * Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
  have hppos : (0:ℝ) < p := by positivity
  have hpow : p ^ Nat.log p N ≤ N := Nat.pow_log_le_self p hN
  have hlog : Real.log ((p : ℝ) ^ Nat.log p N) ≤ Real.log (N : ℝ) := by
    refine Real.log_le_log (pow_pos hppos _) ?_
    calc (p : ℝ) ^ Nat.log p N = ((p ^ Nat.log p N : ℕ) : ℝ) := by rw [Nat.cast_pow]
      _ ≤ (N : ℝ) := by exact_mod_cast hpow
  rwa [Real.log_pow] at hlog


theorem psi_in_AP_of_char_bound (A : ℝ) (hA : 0 < A)
    (hchar : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (q : ℝ) ≤ (Real.log x) ^ A →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)))))
    : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q a : ℕ,
      1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ A → Nat.Coprime a q →
      |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q),
          ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)))) := by
  obtain ⟨cC, CC, hcC, hCC, x₁, hx₁⟩ := hchar
  obtain ⟨c₀, x₂, hc₀, hx₂⟩ := Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c' : ℝ := min cC (c₀ * Real.sqrt (Real.log 2)) / 2 with hc'def
  have hc'pos : 0 < c' := by
    rw [hc'def]
    exact div_pos (lt_min hcC (mul_pos hc₀ (Real.sqrt_pos.mpr hlog2))) (by norm_num)
  have hc'cC : c' ≤ cC := by
    rw [hc'def]; have := min_le_left cC (c₀ * Real.sqrt (Real.log 2)); linarith
  have hc'c0 : c' ≤ c₀ * Real.sqrt (Real.log 2) := by
    rw [hc'def]; have := min_le_right cC (c₀ * Real.sqrt (Real.log 2)); linarith
  set cs : ℝ := c' / Real.sqrt (Real.log 2) with hcsdef
  have hcspos : 0 < cs := by rw [hcsdef]; exact div_pos hc'pos (Real.sqrt_pos.mpr hlog2)
  have hcsle : cs ≤ c₀ := by
    rw [hcsdef, div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (Real.log 2))]
    have h : Real.sqrt (Real.log 2) * Real.sqrt (Real.log 2) = Real.log 2 := by rw [← sq, Real.sq_sqrt hlog2.le]
    nlinarith [hc'c0, Real.sqrt_nonneg (Real.log 2), h]
  obtain ⟨X₃, hX₃⟩ := Commons.Analysis.Asymptotics.eventually_polylog_le_exp_sub_sqrt cs hcspos 2 ((Real.log 2 + A) / Real.log 2) (by positivity)
  have htend : ∀ᶠ x : ℝ in atTop, (2:ℝ) ^ (1/A) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hev : ∀ᶠ x : ℝ in atTop,
      x₁ ≤ x ∧ x₂ ≤ x ∧ X₃ ≤ x ∧ 1 ≤ Real.log x ∧ 2 ≤ (Real.log x) ^ A ∧ 1 ≤ x := by
    filter_upwards [eventually_ge_atTop x₁, eventually_ge_atTop x₂, eventually_ge_atTop X₃,
      Real.tendsto_log_atTop.eventually_ge_atTop 1, htend, eventually_ge_atTop (1:ℝ)] with x h1 h2 h3 h4 h5 h6
    refine ⟨h1, h2, h3, h4, ?_, h6⟩
    calc (2:ℝ) = ((2:ℝ)^(1/A))^A := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), show (1/A)*A = 1 by field_simp, Real.rpow_one]
      _ ≤ (Real.log x)^A := Real.rpow_le_rpow (by positivity) h5 hA.le
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨c', CC + 2, hc'pos, by positivity, X₀, ?_⟩
  intro x hx q a hq1 hqx hcop
  obtain ⟨hxx₁, hxx₂, hxX₃, hxlog1, hxlogA, hx1⟩ := hX₀ x hx
  haveI : NeZero q := ⟨by omega⟩
  have hxpos1 : (0:ℝ) < x := by linarith
  have hflo1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1 : ((1:ℕ):ℝ) ≤ x)
  set E : ℝ := Real.exp (-(c' * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)))) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  -- ## character bound
  have hchi : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)‖ ≤ CC * x * E := by
    intro χ hχ
    have h1 := hx₁ x hxx₁ q χ hχ hqx
    rw [show (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) from
        Finset.sum_congr rfl (fun n _ => by ring)] at h1
    refine le_trans h1 ?_
    calc CC * x * Real.exp (-(cC * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2))))
        = CC * x * Real.exp (-(cC * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)))) := rfl
      _ ≤ CC * x * E := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hEdef]
          apply Real.exp_le_exp.mpr
          have hs : 0 ≤ Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)) := Real.sqrt_nonneg _
          nlinarith [hc'cC, hs]
  -- ## split characters
  set F : DirichletCharacter ℂ q → ℂ := fun χ => χ ((a : ZMod q)⁻¹) *
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) with hFdef
  have hBsum : (∑ χ : DirichletCharacter ℂ q, F χ)
      = F 1 + ∑ χ ∈ Finset.univ.filter (fun χ => χ ≠ 1), F χ := by
    rw [Finset.filter_ne', add_comm]
    exact (Finset.sum_erase_add Finset.univ F (Finset.mem_univ _)).symm
  have hunit : (1 : DirichletCharacter ℂ q) ((a : ZMod q)⁻¹) = 1 := by
    change (MulChar.trivial (ZMod q) ℂ) ((a : ZMod q)⁻¹) = 1
    rw [MulChar.trivial_apply]
    have hunit' : IsUnit ((a : ZMod q)⁻¹) := by
      obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr hcop
      rw [← hu]
      exact ⟨u⁻¹, by simp⟩
    rw [if_pos hunit']
  have hS1 : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q))
      = ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) : ℝ) := by
    have hterm : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q)
        = if Nat.Coprime n q then (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
      intro n
      rw [principal_one]
      by_cases h : Nat.Coprime n q <;> simp [h]
    calc (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q))
        = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) :=
          Finset.sum_congr rfl (fun n _ => hterm n)
      _ = ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), (ArithmeticFunction.vonMangoldt n : ℂ) := by
          rw [← Finset.sum_filter]
      _ = _ := (Complex.ofReal_sum _ _).symm
  have hF1 : F 1 = ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) : ℝ) := by
    rw [hFdef]
    simp only
    rw [hunit, one_mul, hS1]
  have hpsi1 := psi_eq_sum_Icc_one x
  have hS1sub : ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) : ℝ)
      = Chebyshev.psi x - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) (fun n => Nat.Coprime n q)
      (fun n => ArithmeticFunction.vonMangoldt n)
    linarith [h, hpsi1]
  -- ## correction bound
  have hcorr : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n)
      ≤ ((Real.log 2 + A * Real.log (Real.log x)) * Real.log x) / Real.log 2 := by
    have hsub : (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q)
        = (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q) := rfl
    rw [hsub, Commons.NumberTheory.Goldbach.sum_vonMangoldt_not_coprime q ⌊x⌋₊]
    have hle : ∀ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ∣ q),
        ((Nat.log p ⌊x⌋₊ : ℕ) : ℝ) * Real.log p ≤ Real.log x := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hp1, hpx⟩, hpprime, hpdvd⟩ := hp
      have hp2 : 2 ≤ p := hpprime.two_le
      have hfne : ⌊x⌋₊ ≠ 0 := by omega
      have h1 := natlog_mul_log_le_log p ⌊x⌋₊ hp2 hfne
      have h2 : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log (by positivity) (Nat.floor_le (by positivity))
      linarith
    have hcard : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ∣ q)).card ≤ q.primeFactors.card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2, (by omega : q ≠ 0)⟩
    calc (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ∣ q),
            ((Nat.log p ⌊x⌋₊ : ℕ) : ℝ) * Real.log p)
        ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ∣ q), Real.log x :=
          Finset.sum_le_sum hle
      _ = (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ∣ q)).card : ℝ) * Real.log x := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q.primeFactors.card : ℕ) : ℝ) * Real.log x := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_nonneg hx1)
      _ ≤ ((Real.log 2 + A * Real.log (Real.log x)) * Real.log x) / Real.log 2 := by
          have hq0 : q ≠ 0 := by omega
          have hlogq : Real.log (q:ℝ) ≤ Real.log 2 + A * Real.log (Real.log x) := by
            have hqm : (q:ℝ) ≤ 2 * (Real.log x)^A := by nlinarith [hqx, hxlogA]
            have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
            have hlog1 : Real.log (q:ℝ) ≤ Real.log (2 * (Real.log x)^A) := Real.log_le_log hqpos hqm
            have hlog2' : Real.log (2 * (Real.log x)^A) = Real.log 2 + A * Real.log (Real.log x) := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by positivity)]
            linarith [hlog1, le_of_eq hlog2']
          have hc1 := card_primeFactors_le_log_div_log q hq0
          have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
          calc ((q.primeFactors.card : ℕ) : ℝ) * Real.log x
              ≤ (Real.log (q:ℝ) / Real.log 2) * Real.log x :=
                mul_le_mul_of_nonneg_right hc1 hlx
            _ ≤ ((Real.log 2 + A * Real.log (Real.log x)) / Real.log 2) * Real.log x :=
                mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlogq hlog2.le) hlx
            _ = ((Real.log 2 + A * Real.log (Real.log x)) * Real.log x) / Real.log 2 := by
                rw [div_mul_eq_mul_div]
  -- ## nontrivial character sum bound
  have hS2 : ‖∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), F χ‖
      ≤ (Nat.totient q : ℝ) * (CC * x * E) := by
    have hterm : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ‖ ≤ CC * x * E := by
      intro χ hχ
      have h2 := hchi χ (Finset.mem_filter.mp hχ).2
      calc ‖F χ‖ = ‖χ ((a : ZMod q)⁻¹)‖ * ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)‖ := by
            rw [hFdef, norm_mul]
        _ ≤ 1 * (CC * x * E) := by
            apply mul_le_mul (DirichletCharacter.norm_le_one χ _) h2 (norm_nonneg _) (by norm_num)
        _ = CC * x * E := one_mul _
    have hcard : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ (Nat.totient q : ℝ) := by
      have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]
        rw [Nat.card_eq_fintype_card]
        exact ZMod.card_units_eq_totient q
      have h1 : (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
        calc (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card
            ≤ Finset.univ.card := Finset.card_filter_le _ _
          _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
          _ = q.totient := h2
      exact_mod_cast h1
    calc ‖∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), F χ‖
        ≤ ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖F χ‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), (CC * x * E) := Finset.sum_le_sum hterm
      _ = ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) * (CC * x * E) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.totient q : ℝ) * (CC * x * E) := mul_le_mul_of_nonneg_right hcard (by positivity)
  -- ## assemble
  have hexp := psi_AP_eq_charSum q x a hcop
  have hTcast : ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) : ℂ)
      = ((Nat.totient q : ℂ))⁻¹ * (∑ χ : DirichletCharacter ℂ q, F χ) := by
    rw [hexp]
  have hphi1 : (1:ℝ) ≤ (Nat.totient q : ℝ) := by
    have := Nat.totient_pos.mpr (by omega : 0 < q)
    exact_mod_cast this
  have hphipos : (0:ℝ) < (Nat.totient q : ℝ) := by linarith
  have hkey : ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) : ℂ)
        - (x : ℂ) / (Nat.totient q : ℂ)
      = ((Nat.totient q : ℂ))⁻¹ * ((∑ χ : DirichletCharacter ℂ q, F χ) - (x : ℂ)) := by
    rw [hTcast]
    have hne : (Nat.totient q : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hphipos)
    field_simp
  have hBdiff : ‖(∑ χ : DirichletCharacter ℂ q, F χ) - (x : ℂ)‖ ≤ (|Chebyshev.psi x - x| + (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n)) + (Nat.totient q : ℝ) * (CC * x * E) := by
    rw [hBsum]
    have hFF1 : F 1 - (x:ℂ) = ((((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) : ℝ) - x : ℝ) : ℂ) := by
      rw [hF1, ← Complex.ofReal_sub]
    have hcast : ((F 1 + ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), F χ)) - (x:ℂ)
        = (F 1 - (x:ℂ)) + ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), F χ := by ring
    rw [hcast]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖F 1 - (x:ℂ)‖ ≤ |Chebyshev.psi x - x| + (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) := by
      rw [hFF1, Complex.norm_real, Real.norm_eq_abs]
      have : ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) : ℝ) - x
          = (Chebyshev.psi x - x) - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) := by
        rw [hS1sub]; ring
      rw [this]
      have hnn : 0 ≤ (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) :=
        Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
      calc |(Chebyshev.psi x - x) - (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n)|
          ≤ |Chebyshev.psi x - x| + (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) := by
            have := abs_sub_le (Chebyshev.psi x - x) 0 (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n)
            rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg hnn] at this
            exact this
        _ = _ := rfl
    linarith [h1, hS2]
  -- ## final chain
  have hpsi_bd : |Chebyshev.psi x - x| ≤ x * Real.exp (-(cs * Real.sqrt (Real.log x))) := by
    have h := hx₂ x hxx₂
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [hcsle, Real.sqrt_nonneg (Real.log x)]
  have hExp_ge : Real.exp (-(cs * Real.sqrt (Real.log x))) ≤ E := by
    rw [hEdef]
    apply Real.exp_le_exp.mpr
    have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hb : Real.log 2 ≤ Real.log ((q:ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith [show (0:ℝ) ≤ (q:ℝ) by positivity])
    have hbpos : 0 < Real.log ((q:ℝ) + 2) := lt_of_lt_of_le hlog2 hb
    have h1 : Real.log x / Real.log ((q:ℝ)+2) ≤ Real.log x / Real.log 2 :=
      div_le_div_of_nonneg_left hlx hlog2 hb
    have h2 : Real.sqrt (Real.log x / Real.log ((q:ℝ)+2)) ≤ Real.sqrt (Real.log x) / Real.sqrt (Real.log 2) := by
      rw [Real.sqrt_div hlx]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hlog2) (Real.sqrt_le_sqrt hb)
    have h3 : c' * Real.sqrt (Real.log x / Real.log ((q:ℝ)+2)) ≤
        c' * (Real.sqrt (Real.log x) / Real.sqrt (Real.log 2)) := mul_le_mul_of_nonneg_left h2 hc'pos.le
    have h4 : cs * Real.sqrt (Real.log x) = c' * (Real.sqrt (Real.log x) / Real.sqrt (Real.log 2)) := by
      rw [hcsdef]; ring
    rw [h4]
    linarith
  have hcorr2 : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) ≤ x * E := by
    refine hcorr.trans ?_
    have hpoly := hX₃ x hxX₃
    have hlogu : Real.log (Real.log x) ≤ Real.log x := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.log x by linarith)
      linarith
    have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hu2 : Real.log x ≤ (Real.log x)^2 := by nlinarith [hxlog1]
    have hstep : ((Real.log 2 + A * Real.log (Real.log x)) * Real.log x) / Real.log 2
        ≤ ((Real.log 2 + A) / Real.log 2) * (Real.log x)^2 := by
      have e1 : Real.log 2 * Real.log x ≤ Real.log 2 * (Real.log x)^2 :=
        mul_le_mul_of_nonneg_left hu2 hlog2.le
      have e2 : A * Real.log (Real.log x) * Real.log x ≤ A * (Real.log x)^2 := by
        have h1 : Real.log (Real.log x) * Real.log x ≤ Real.log x * Real.log x :=
          mul_le_mul_of_nonneg_right hlogu hlx
        nlinarith [h1]
      rw [add_mul, add_div, div_mul_eq_mul_div, add_mul, add_div]
      exact add_le_add (div_le_div_of_nonneg_right e1 hlog2.le) (div_le_div_of_nonneg_right e2 hlog2.le)
    refine hstep.trans ?_
    have hpoly' : ((Real.log 2 + A) / Real.log 2) * (Real.log x)^2
        ≤ x * Real.exp (-(cs * Real.sqrt (Real.log x))) := by
      have hxpos : 0 < x := by linarith
      have hthis := hpoly
      rw [show Real.log x - cs * Real.sqrt (Real.log x) = Real.log x + (-(cs * Real.sqrt (Real.log x))) by ring,
        Real.exp_add, Real.exp_log hxpos] at hthis
      exact hthis
    calc ((Real.log 2 + A) / Real.log 2) * (Real.log x)^2
        ≤ x * Real.exp (-(cs * Real.sqrt (Real.log x))) := hpoly'
      _ ≤ x * E := mul_le_mul_of_nonneg_left hExp_ge (by positivity)
  have hpsiabs : |Chebyshev.psi x - x| ≤ x * E := by
    refine hpsi_bd.trans ?_
    exact mul_le_mul_of_nonneg_left hExp_ge (by positivity)
  -- conclusion
  have hmain : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)|
      ≤ (CC + 2) * x * E := by
    have habs : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) - x / (Nat.totient q : ℝ)|
        = ‖((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) : ℂ) - (x:ℂ) / (Nat.totient q : ℂ)‖ := by
      have hcast : ((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) : ℂ) - (x:ℂ) / (Nat.totient q : ℂ)
          = (((∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n) - x / (Nat.totient q : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    rw [habs, hkey, norm_mul]
    have hphi_norm : ‖((Nat.totient q : ℕ) : ℂ)‖ = (Nat.totient q : ℝ) := Complex.norm_natCast _
    rw [norm_inv, hphi_norm]
    have hle : ‖((∑ χ : DirichletCharacter ℂ q, F χ) - (x : ℂ))‖ ≤ (x*E + x*E) + (Nat.totient q : ℝ) * (CC * x * E) := by
      refine hBdiff.trans ?_
      have h1 : |Chebyshev.psi x - x| ≤ x * E := hpsiabs
      have h2 : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n) ≤ x * E := hcorr2
      linarith
    have hinv : ((Nat.totient q : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hphipos]
      exact hphi1
    have hphi_ne : (Nat.totient q : ℝ) ≠ 0 := ne_of_gt hphipos
    calc ((Nat.totient q : ℝ))⁻¹ * ‖((∑ χ : DirichletCharacter ℂ q, F χ) - (x : ℂ))‖
        ≤ ((Nat.totient q : ℝ))⁻¹ * ((x*E + x*E) + (Nat.totient q : ℝ) * (CC * x * E)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((Nat.totient q : ℝ))⁻¹ * (x*E + x*E) + (CC * x * E) := by
          field_simp
      _ ≤ (x*E + x*E) + (CC * x * E) := by
          have h3 : ((Nat.totient q : ℝ))⁻¹ * (x*E + x*E) ≤ x*E + x*E :=
            mul_le_of_le_one_left (by positivity) hinv
          linarith
      _ = (CC + 2) * x * E := by ring
  rw [hEdef]
  exact hmain



/-- **Primes in arithmetic progressions for small moduli** (Siegel--Walfisz form). -/
theorem psi_in_AP_smallModulus (A : ℝ) (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q a : ℕ,
      1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ A → Nat.Coprime a q →
      |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q),
          ArithmeticFunction.vonMangoldt n) - (x : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q:ℝ) + 2)))) :=
  psi_in_AP_of_char_bound A hA (psiChi_bound_all A hA)

end

end Commons.NumberTheory.PrimesInAP
