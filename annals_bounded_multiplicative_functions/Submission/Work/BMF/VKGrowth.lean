import Mathlib
import Submission.Work.BMF.VKGrowthDefs
import Submission.Work.BMF.HurwitzShift
import Submission.Work.BMF.VKBlockTools
import Submission.Commons.Analysis.ExponentialSums.kusmin_landau
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Growth of `ζ` and of the Hurwitz zeta function in the Vinogradov–Korobov strip

Given the exponential-sum input `Work.BMF.vk_exp_sum`, we prove
`‖ζ(σ+it,u)‖ ≤ A (u^{-σ} + (log(t+3))^{6/7})` for `σ ≥ 1 - c (log(t+3))^{-6/7}` and
`t ≥ 3`, uniformly in `u ∈ [0,1]`.
-/

namespace Work.BMF

open Finset Complex
open scoped Topology BigOperators

noncomputable section

/-! ## Elementary identities -/

/-- `(x^a) * (x^b) = x^(a+b)` for a positive real `x`. -/
lemma cpow_mul_cpow_ofReal {x : ℝ} (hx : 0 < x) (a b : ℂ) :
    (((x : ℝ) : ℂ) ^ a) * (((x : ℝ) : ℂ) ^ b) = (((x : ℝ) : ℂ)) ^ (a + b) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.cpow_def_of_ne_zero
    (by exact_mod_cast hx.ne'), Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- `(x : ℂ)^(-(I*t)) = exp (2*π*I* (-t * log x / (2*π)))` for `x > 0`. -/
lemma cpow_neg_I_mul_eq_exp {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (((x : ℝ) : ℂ)) ^ (-(Complex.I * (t : ℂ))) =
      Complex.exp (((2 * Real.pi * (-t * Real.log x / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 1
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have : (0:ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp
  try ring

/-! ## The dyadic block induction -/

/-- Splitting `Ioc a c` at `b`. -/
lemma sum_Ioc_split {f : ℕ → ℂ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ n ∈ Finset.Ioc a c, f n = (∑ n ∈ Finset.Ioc a b, f n) + ∑ n ∈ Finset.Ioc b c, f n := by
  have hset : Finset.Ioc a c = Finset.Ioc a b ∪ Finset.Ioc b c := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_union]
    omega
  rw [hset, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_Ioc] at hx1 hx2
  omega

/-- **Dyadic partial sums.**  If every block `(K, R]` with `K₀ ≤ K`, `R ≤ 2K` has partial sums
bounded by `B`, then for `K₀ 2^J ≤ M ≤ K₀ 2^(J+1)` the partial sum over `(K₀, M]` is at most
`(J+1) * B`. -/
lemma dyadic_partial_sum_le {f : ℕ → ℂ} {K₀ : ℕ} (hK₀ : 1 ≤ K₀) {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ K R : ℕ, K₀ ≤ K → K ≤ R → R ≤ 2 * K → ‖∑ n ∈ Finset.Ioc K R, f n‖ ≤ B) :
    ∀ (J M : ℕ), K₀ * 2 ^ J ≤ M → M ≤ K₀ * 2 ^ (J + 1) →
      ‖∑ n ∈ Finset.Ioc K₀ M, f n‖ ≤ (J + 1) * B := by
  intro J
  induction J with
  | zero =>
    intro M hM hM'
    have h := hblock K₀ M (le_refl _) (by simpa using hM)
      (by simpa [Nat.mul_comm] using hM')
    simpa using h
  | succ J ih =>
    intro M hM hM'
    have hKA : K₀ * 2 ^ J ≤ K₀ * 2 ^ (J + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hA : K₀ ≤ K₀ * 2 ^ (J + 1) := by
      calc K₀ = K₀ * 1 := (mul_one _).symm
        _ ≤ K₀ * 2 ^ (J + 1) := Nat.mul_le_mul_left _ (by
            have : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
            exact this)
    have h1 : ‖∑ n ∈ Finset.Ioc K₀ (K₀ * 2 ^ (J + 1)), f n‖ ≤ (J + 1) * B :=
      ih (K₀ * 2 ^ (J + 1)) hKA (le_refl _)
    have h2 : ‖∑ n ∈ Finset.Ioc (K₀ * 2 ^ (J + 1)) M, f n‖ ≤ B :=
      hblock (K₀ * 2 ^ (J + 1)) M hA hM (by
        calc M ≤ K₀ * 2 ^ (J + 1 + 1) := hM'
          _ = 2 * (K₀ * 2 ^ (J + 1)) := by ring)
    rw [sum_Ioc_split hA hM]
    have h3 : ‖(∑ n ∈ Finset.Ioc K₀ (K₀ * 2 ^ (J + 1)), f n) +
          ∑ n ∈ Finset.Ioc (K₀ * 2 ^ (J + 1)) M, f n‖ ≤ (↑J + 1) * B + B := by
      calc ‖(∑ n ∈ Finset.Ioc K₀ (K₀ * 2 ^ (J + 1)), f n) +
            ∑ n ∈ Finset.Ioc (K₀ * 2 ^ (J + 1)) M, f n‖
          ≤ ‖∑ n ∈ Finset.Ioc K₀ (K₀ * 2 ^ (J + 1)), f n‖ +
            ‖∑ n ∈ Finset.Ioc (K₀ * 2 ^ (J + 1)) M, f n‖ := norm_add_le _ _
        _ ≤ (↑J + 1) * B + B := add_le_add h1 h2
    have h4 : (↑J + 1 : ℝ) * B + B ≤ ((↑(J + 1) : ℝ) + 1) * B := by
      have hJJ : (↑(J + 1) : ℝ) = ↑J + 1 := by push_cast; ring
      have hkey : (↑J + 1 : ℝ) * B + B = ((↑(J + 1) : ℝ) + 1) * B := by
        rw [hJJ]; ring
      exact hkey.le
    exact le_trans h3 h4


/-! ## The trivial (short-block) bound -/

/-- **Harmonic-type bound.**  For `0 < σ ≤ 2` and `M : ℕ`,
`∑_{n=1}^{M} n^{-σ} ≤ exp (max (1-σ) 0 * log M) * (1 + log M)`.
For `σ ≥ 1` the exponential factor is `1` and this is the harmonic bound; for `σ < 1` it is the
factorisation `n^{-σ} = n^{-1} · n^{1-σ} ≤ n^{-1} · M^{1-σ}` followed by the harmonic bound. -/
lemma sum_Icc_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ)) ≤
      Real.exp (max (1 - σ) 0 * Real.log M) * (1 + Real.log M) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hE : 0 ≤ Real.exp (max (1 - σ) 0 * Real.log M) := Real.exp_nonneg _
  have hkey : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ) ≤
      Real.exp (max (1 - σ) 0 * Real.log M) * ((n : ℝ))⁻¹ := by
    intro n hn
    obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hsplit : (n : ℝ) ^ (-σ) = ((n : ℝ))⁻¹ * (n : ℝ) ^ (1 - σ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hnpos]
      congr 1
      ring
    have hbound : (n : ℝ) ^ (1 - σ) ≤ Real.exp (max (1 - σ) 0 * Real.log M) := by
      by_cases h : 1 ≤ σ
      · have hmax : max (1 - σ) 0 = 0 := by
          rw [max_eq_right]; linarith
        rw [hmax, zero_mul, Real.exp_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
      · have hσ1 : σ < 1 := lt_of_not_ge h
        have hmax : max (1 - σ) 0 = 1 - σ := max_eq_left (by linarith)
        have h1 : (n : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (1 - σ) := by
          refine Real.rpow_le_rpow (le_of_lt hnpos) ?_ (by linarith)
          exact_mod_cast hnM
        have h2 : (M : ℝ) ^ (1 - σ) = Real.exp ((1 - σ) * Real.log M) := by
          have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
          rw [Real.rpow_def_of_pos hMpos (1 - σ)]
          ring_nf
        calc (n : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (1 - σ) := h1
          _ = Real.exp ((1 - σ) * Real.log M) := h2
          _ = Real.exp (max (1 - σ) 0 * Real.log M) := by rw [hmax]
    rw [hsplit]
    calc ((n : ℝ))⁻¹ * (n : ℝ) ^ (1 - σ) ≤ ((n : ℝ))⁻¹ * Real.exp (max (1 - σ) 0 * Real.log M) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Real.exp (max (1 - σ) 0 * Real.log M) * ((n : ℝ))⁻¹ := by ring
  calc (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ))
      ≤ ∑ n ∈ Finset.Icc 1 M, Real.exp (max (1 - σ) 0 * Real.log M) * ((n : ℝ))⁻¹ :=
        Finset.sum_le_sum hkey
    _ = Real.exp (max (1 - σ) 0 * Real.log M) * (∑ n ∈ Finset.Icc 1 M, ((n : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
    _ = Real.exp (max (1 - σ) 0 * Real.log M) * (harmonic M : ℝ) := by
        congr 1
        simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ Real.exp (max (1 - σ) 0 * Real.log M) * (1 + Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) hE


/-- **The short-block (trivial) contribution.**  If `M ≤ exp κ + 2`, `0 < σ ≤ 2` and
`(1-σ) κ ≤ 1`, then `∑_{n ≤ M} n^{-σ} ≤ 5 e⁴ (2 + κ)`. -/
lemma short_block_bound {σ κ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (hκ : 0 ≤ κ)
    (hσκ : (1 - σ) * κ ≤ 1) (M : ℕ) (hM : (M : ℝ) ≤ Real.exp κ + 2) :
    (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ)) ≤ (Real.exp 4 * 5) * (2 + κ) := by
  have hexpκ1 : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
  have hexpκ0 : (0 : ℝ) < Real.exp κ := Real.exp_pos κ
  have hlogM : Real.log (M : ℝ) ≤ Real.log (Real.exp κ + 2) := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      rw [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith [hexpκ1])
    · have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast h
      exact Real.log_le_log hMpos hM
  have h2 : Real.exp κ + 2 ≤ 3 * Real.exp κ := by linarith
  have hlog2 : Real.log (3 * Real.exp κ) = Real.log 3 + κ := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero κ), Real.log_exp]
  have hlog3 : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hlogM' : Real.log (M : ℝ) ≤ 3 + κ := by
    have h := le_trans hlogM (Real.log_le_log (by linarith) h2)
    rw [hlog2] at h
    linarith
  have hmax : max (1 - σ) 0 * Real.log (M : ℝ) ≤ 4 := by
    by_cases h : 1 ≤ σ
    · have hz : max (1 - σ) 0 = 0 := max_eq_right (by linarith)
      rw [hz, zero_mul]
      norm_num
    · have hσ1 : σ < 1 := lt_of_not_ge h
      have hm : max (1 - σ) 0 = 1 - σ := max_eq_left (by linarith)
      rw [hm]
      have h1σ : 0 ≤ 1 - σ := by linarith
      have h1σ' : 1 - σ ≤ 1 := by linarith
      have h1 : (1 - σ) * Real.log (M : ℝ) ≤ (1 - σ) * (3 + κ) :=
        mul_le_mul_of_nonneg_left hlogM' h1σ
      nlinarith [h1, hσκ, h1σ, h1σ']
  calc (∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-σ))
      ≤ Real.exp (max (1 - σ) 0 * Real.log (M : ℝ)) * (1 + Real.log (M : ℝ)) :=
        sum_Icc_rpow_neg_le hσ0 hσ2 M
    _ ≤ Real.exp 4 * (1 + (3 + κ)) := by
        have h1 : Real.exp (max (1 - σ) 0 * Real.log (M : ℝ)) ≤ Real.exp 4 :=
          Real.exp_le_exp.mpr hmax
        have h2' : 1 + Real.log (M : ℝ) ≤ 1 + (3 + κ) := by linarith
        have h3 : (0 : ℝ) ≤ 1 + Real.log (M : ℝ) := by
          have := Real.log_natCast_nonneg M
          linarith
        exact mul_le_mul h1 h2' h3 (Real.exp_pos 4).le
    _ ≤ (Real.exp 4 * 5) * (2 + κ) := by
        have h1 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
        nlinarith [hκ, h1]


/-! ## The VK block bound -/

/-- **A single block bounded by the Vinogradov–Korobov saving.**  For `u ∈ (0,1]`, `0 < σ`, `t ≥ 3`
and a block `(K, R]` with `2 ≤ K`, `K ≤ t`, `R ≤ 2K` and `log t ≤ c_vk (log K)^{7/6}`,
`‖∑_{K<n≤R} (n+u)^{-σ-it}‖ ≤ C_vk · K^{-σ} · K^{1-γ}`, `γ = c_vk λ^{-2}/log(λ+2)`,
`λ = log t/log K`. -/
lemma vk_block_bound {Cvk cvk : ℝ} (hVK : VKExpInput Cvk cvk) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    {σ t : ℝ} (ht : 3 ≤ t) (hσ0 : 0 < σ) {K R : ℕ} (hRK : K < R)
    (hR2K : (R : ℝ) ≤ 2 * K) (hKt : (K : ℝ) ≤ t) (hK2 : 2 ≤ K)
    (hrange : Real.log t ≤ cvk * Real.log (K : ℝ) ^ (7 / 6 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      Cvk * (K : ℝ) ^ (-σ) *
        ((K : ℝ) ^ (1 - cvk * (Real.log (K : ℝ) / Real.log t) ^ 2 /
          Real.log (Real.log t / Real.log (K : ℝ) + 2))) := by
  obtain ⟨hC, hc, hb⟩ := hVK
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have ht0 : (0 : ℝ) < t := by linarith
  set γ : ℝ := cvk * (Real.log (K : ℝ) / Real.log t) ^ 2 /
      Real.log (Real.log t / Real.log (K : ℝ) + 2) with hγdef
  have hB0 : 0 ≤ Cvk * (K : ℝ) ^ (1 - γ) := by
    have := Real.rpow_nonneg (le_of_lt hKpos) (1 - γ)
    positivity
  have hB : ∀ r ∈ Finset.Ioc K R,
      ‖∑ n ∈ Finset.Ioc K r, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        Cvk * (K : ℝ) ^ (1 - γ) := by
    intro r hr
    obtain ⟨hKr, hrR⟩ := Finset.mem_Ioc.mp hr
    rcases eq_or_lt_of_le (le_of_lt hKr) with h | h
    · rw [← h]
      simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      exact hB0
    · have hrR' : ((r : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
        have : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
        linarith
      have hsub := hb (K : ℝ) t (by exact_mod_cast hK2) hKt hrange u hu hu1 (r : ℝ)
        (by exact_mod_cast h) hrR'
      simpa only [Nat.floor_natCast, hγdef] using hsub
  have hw : ∀ n : ℕ, (0 : ℝ) ≤ (((n : ℝ) + u)) ^ (-σ) := fun n =>
    Real.rpow_nonneg (by positivity) _
  have hmono : ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ) + u)) ^ (-σ) ≤ (((n : ℝ) + u)) ^ (-σ) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + u := by positivity
    have h2 : (n : ℝ) + u ≤ ((n + 1 : ℕ) : ℝ) + u := by push_cast; linarith
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
  have hmain := norm_sum_Ioc_mul_le (w := fun n : ℕ => (((n : ℝ) + u)) ^ (-σ))
    (e := fun n : ℕ => ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))) hw hmono hB0 hB
  have hterm2 : ∀ n ∈ Finset.Ioc K R,
      (((((n : ℝ) + u)) ^ (-σ) : ℝ) : ℂ) * ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    intro n _
    have hx : (0 : ℝ) < (n : ℝ) + u := by positivity
    have h1 : (((((n : ℝ) + u)) ^ (-σ) : ℝ) : ℂ) =
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ ((-σ : ℝ) : ℂ) := Complex.ofReal_cpow hx.le (-σ)
    rw [h1, cpow_mul_cpow_ofReal hx]
    congr 1
    push_cast
    ring
  have hsum_eq : (∑ n ∈ Finset.Ioc K R, (((((n : ℝ) + u)) ^ (-σ) : ℝ) : ℂ) *
      ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
      ∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    Finset.sum_congr rfl hterm2
  rw [hsum_eq] at hmain
  refine le_trans hmain ?_
  have hwK : ((((K + 1 : ℕ) : ℝ) + u)) ^ (-σ) ≤ (K : ℝ) ^ (-σ) := by
    have h2 : (K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) + u := by push_cast; linarith
    exact Real.rpow_le_rpow_of_nonpos hKpos h2 (by linarith)
  calc ((((K + 1 : ℕ) : ℝ) + u)) ^ (-σ) * (Cvk * (K : ℝ) ^ (1 - γ))
      ≤ (K : ℝ) ^ (-σ) * (Cvk * (K : ℝ) ^ (1 - γ)) :=
        mul_le_mul_of_nonneg_right hwK (by positivity)
    _ = Cvk * (K : ℝ) ^ (-σ) * (K : ℝ) ^ (1 - γ) := by ring



/-- **From the Hurwitz growth bound to the `L`-function growth bound.** -/
theorem LFunction_growth_of_hurwitz {Ah c : ℝ} (hAh : 0 < Ah) (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hHur : ∀ (a σ t : ℝ), 0 ≤ a → a ≤ 1 → 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖HurwitzZeta.hurwitzZeta (a : UnitAddCircle) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Ah * (a ^ (-σ) + Real.log (|t| + 3) ^ (6 / 7 : ℝ))) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ t : ℝ), 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * Ah * N * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  intro N _ χ σ t ht hσ hσ2
  set L : ℝ := Real.log (|t| + 3) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h1 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three
    have h2 : Real.log 3 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t, ht])
    linarith
  have hLnn : 0 ≤ L := le_trans zero_le_one hL1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hpow : (1 : ℝ) ≤ L ^ (6 / 7 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hσ0 : 0 < σ := by
    have h1 : L ^ (-(6 / 7 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    have h2 : 0 ≤ L ^ (-(6 / 7 : ℝ)) := Real.rpow_nonneg hLnn _
    have h3 : 1 - c ≤ σ := by nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
    linarith
  have hterm : ∀ j : ZMod N, ‖(χ j) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j)
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ah * ((((j.val : ℝ) / N) ^ (-σ)) + L ^ (6 / 7 : ℝ)) := by
    intro j
    have hj1 : (j.val : ℝ) ≤ (N : ℝ) := by
      have h := ZMod.val_lt j
      exact_mod_cast h.le
    have hjle : (j.val : ℝ) / N ≤ 1 := by
      rw [div_le_one hNpos]
      exact hj1
    have hj0 : 0 ≤ (j.val : ℝ) / N := by positivity
    have hχ : ‖χ j‖ ≤ 1 := DirichletCharacter.norm_le_one χ j
    have hH := hHur ((j.val : ℝ) / N) σ t hj0 hjle ht hσ hσ2
    rw [ZMod.toAddCircle_apply j]
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul hχ hH (norm_nonneg _) (by norm_num)) ?_
    rw [one_mul]
  have hpow2 : ∀ j : ZMod N, (((j.val : ℝ) / N) ^ (-σ)) ≤ (N : ℝ) ^ σ := by
    intro j
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, zero_div]
      rw [Real.zero_rpow (ne_of_lt (neg_neg_iff_pos.mpr hσ0))]
      exact Real.rpow_nonneg hNpos.le _
    · have hj1 : (1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hpos
      have hjσ : (1 : ℝ) ≤ (j.val : ℝ) ^ σ := Real.one_le_rpow hj1 hσ0.le
      have hbase : (0 : ℝ) < ((j.val : ℝ) / N) ^ σ :=
        Real.rpow_pos_of_pos (by positivity) _
      have key : 1 ≤ (N : ℝ) ^ σ * ((j.val : ℝ) / N) ^ σ := by
        rw [← Real.mul_rpow hNpos.le (by positivity : (0 : ℝ) ≤ (j.val : ℝ) / N)]
        have hc : (N : ℝ) * ((j.val : ℝ) / N) = (j.val : ℝ) := by field_simp
        rw [hc]
        exact hjσ
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (j.val : ℝ) / N)]
      exact (inv_le_iff_one_le_mul₀ hbase).mpr key
  have hsum : ‖∑ j : ZMod N, (χ j) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j)
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Ah * ((N : ℝ) ^ (1 + σ) + (N : ℝ) * L ^ (6 / 7 : ℝ)) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hAh.le
    have hrw : (N : ℝ) ^ (1 + σ) = (N : ℝ) ^ σ * (N : ℝ) := by
      rw [show (1 : ℝ) + σ = σ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hrw, Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · calc ∑ j : ZMod N, (((j.val : ℝ) / N) ^ (-σ))
          ≤ ∑ _j : ZMod N, (N : ℝ) ^ σ := Finset.sum_le_sum (fun j _ => hpow2 j)
        _ = (N : ℝ) ^ σ * (N : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
            ring
    · rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hnorm : ‖(((N : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ = (N : ℝ) ^ (-σ) := by
    have hcast : ((N : ℂ)) = (((N : ℝ)) : ℂ) := by norm_num
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    simp
  have hmain : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (N : ℝ) ^ (-σ) * (Ah * ((N : ℝ) ^ (1 + σ) + (N : ℝ) * L ^ (6 / 7 : ℝ))) := by
    rw [DirichletCharacter.LFunction, ZMod.LFunction]
    refine le_trans (norm_mul_le _ _) ?_
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hNpos.le _)
  refine le_trans hmain ?_
  have hkey : (N : ℝ) ^ (-σ) * ((N : ℝ) ^ (1 + σ) + (N : ℝ) * L ^ (6 / 7 : ℝ)) ≤
      2 * (N : ℝ) * L ^ (6 / 7 : ℝ) := by
    have h1 : (N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 + σ) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      have : -σ + (1 + σ) = 1 := by ring
      rw [this, Real.rpow_one]
    have h2 : (N : ℝ) ^ (-σ) * ((N : ℝ) * L ^ (6 / 7 : ℝ)) =
        (N : ℝ) ^ (1 - σ) * L ^ (6 / 7 : ℝ) := by
      have hNσ : (0 : ℝ) < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hNpos σ
      have hkey : (N : ℝ) ^ (-σ) * (N : ℝ) = (N : ℝ) ^ (1 - σ) := by
        rw [Real.rpow_neg hNpos.le, Real.rpow_sub hNpos, Real.rpow_one]
        field_simp
      calc (N : ℝ) ^ (-σ) * ((N : ℝ) * L ^ (6 / 7 : ℝ))
          = ((N : ℝ) ^ (-σ) * (N : ℝ)) * L ^ (6 / 7 : ℝ) := by ring
        _ = (N : ℝ) ^ (1 - σ) * L ^ (6 / 7 : ℝ) := by rw [hkey]
    rw [mul_add, h1, h2]
    have h3 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) := by
      calc (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = (N : ℝ) := Real.rpow_one _
    have h5 : (N : ℝ) ^ (1 - σ) * L ^ (6 / 7 : ℝ) ≤ (N : ℝ) * L ^ (6 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hLnn _)
    have h4 : (N : ℝ) ≤ (N : ℝ) * L ^ (6 / 7 : ℝ) := by
      calc (N : ℝ) = (N : ℝ) * 1 := by ring
        _ ≤ (N : ℝ) * L ^ (6 / 7 : ℝ) := mul_le_mul_of_nonneg_left hpow hNpos.le
    linarith
  calc (N : ℝ) ^ (-σ) * (Ah * ((N : ℝ) ^ (1 + σ) + (N : ℝ) * L ^ (6 / 7 : ℝ)))
      = Ah * ((N : ℝ) ^ (-σ) * ((N : ℝ) ^ (1 + σ) + (N : ℝ) * L ^ (6 / 7 : ℝ))) := by ring
    _ ≤ Ah * (2 * (N : ℝ) * L ^ (6 / 7 : ℝ)) := mul_le_mul_of_nonneg_left hkey hAh.le
    _ = 2 * Ah * N * L ^ (6 / 7 : ℝ) := by ring


/-! ## Splitting and bounds for the shift-difference series -/

/-- Splitting the shift-difference series at `M`. -/
lemma shiftTerm_split {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 0 < s.re) (M : ℕ) :
    (∑' m : ℕ, shiftTerm a m s) =
      (∑ m ∈ Finset.range M, shiftTerm a m s) + ∑' m : ℕ, shiftTerm a (M + m) s := by
  have hsum : Summable (fun m : ℕ => shiftTerm a m s) := by
    have h := summable_norm_shiftTerm (a := a) ha ha1 (s := s) hs 0
    simpa using h.of_norm
  simpa [Nat.add_comm] using (hsum.sum_add_tsum_nat_add M).symm

/-- Tail bound for the shift-difference series. -/
lemma shiftTerm_tail_le {a σ t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hσ : 0 < σ) (M : ℕ) :
    ‖∑' m : ℕ, shiftTerm a (M + m) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * ((M : ℝ) + a) ^ (-σ) := by
  have h := norm_tsum_shiftTerm_tail_le (a := a) ha ha1
    (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ) M
  simpa using h

/-- Conjugating a complex power of a nonnegative real base, with the exponent negated. -/
lemma star_cpow_ofReal_neg {x : ℝ} (hx : 0 ≤ x) (σ t : ℝ) :
    ((((x : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
      star ((((x : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) := by
  have h := Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hx
    (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))
  change ((((x : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
    (starRingEnd ℂ) ((((x : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)))
  rw [h]
  congr 1
  simp only [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The Kusmin–Landau block bound at an arbitrary height, from the positive-height form by
complex conjugation. -/
lemma kl_block_abs {σ t : ℝ} (hσ : 0 < σ) (ht : 3 ≤ |t|)
    (hkl : ∀ {u σ t : ℝ}, 0 < u → u ≤ 1 → 0 < σ → 3 ≤ t → ∀ {K R : ℕ}, K < R →
      (R : ℝ) ≤ 2 * K → t ≤ (K : ℝ) →
      ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        12 * Real.pi * (K : ℝ) ^ (1 - σ) / t)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {K R : ℕ} (hRK : K < R) (hR2K : (R : ℝ) ≤ 2 * K)
    (hKt : |t| ≤ (K : ℝ)) :
    ‖∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      12 * Real.pi * (K : ℝ) ^ (1 - σ) / |t| := by
  by_cases ht0 : 0 ≤ t
  · have ht3 : 3 ≤ t := by have h := ht; rwa [abs_of_nonneg ht0] at h
    have hKt' : t ≤ (K : ℝ) := by have h := hKt; rwa [abs_of_nonneg ht0] at h
    rw [abs_of_nonneg ht0]
    exact hkl hu hu1 hσ ht3 hRK hR2K hKt'
  · push_neg at ht0
    have ht3 : 3 ≤ -t := by have h := ht; rw [abs_of_neg ht0] at h; linarith
    have hKt' : -t ≤ (K : ℝ) := by have h := hKt; rw [abs_of_neg ht0] at h; exact h
    have hconj : ∀ n : ℕ, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
        star (((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) :=
      fun n => star_cpow_ofReal_neg (by positivity) σ t
    have hsum : (∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^
          (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
        star (∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^
          (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) := by
      rw [show star (∑ n ∈ Finset.Ioc K R, ((((n : ℝ) + u : ℝ)) : ℂ) ^
          (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) =
          ∑ n ∈ Finset.Ioc K R, star (((((n : ℝ) + u : ℝ)) : ℂ) ^
            (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) from
        map_sum (starRingEnd ℂ) (fun n : ℕ => ((((n : ℝ) + u : ℝ)) : ℂ) ^
          (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) _]
      exact Finset.sum_congr rfl (fun n _ => hconj n)
    rw [hsum, norm_star, abs_of_neg ht0]
    exact hkl hu hu1 hσ ht3 hRK hR2K hKt'



end

end Work.BMF
