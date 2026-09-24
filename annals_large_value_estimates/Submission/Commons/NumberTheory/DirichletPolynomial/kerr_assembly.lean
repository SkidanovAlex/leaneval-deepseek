import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.kerr_case1
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_square_bound
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length
import Submission.Commons.NumberTheory.DirichletPolynomial.kerr_coefficient_majorant
import Submission.Commons.Analysis.Sampling.card_le_separated_finset

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

noncomputable section

/-- Windowed difference sum with arbitrary coefficients (Kerr normalisation). -/
def kDSw (n : ℕ) (Δ : ℝ) (c : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    (if |t i - t j| ≤ Δ then
      ‖∑ m ∈ Finset.Icc n (2 * n),
        c m * (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2
     else 0)

/-- Unit-coefficient difference sum over the block `[n,2n]` with vacuous window. -/
def kDS (n : ℕ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    ‖∑ m ∈ Finset.Icc n (2 * n),
      (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2

/-- Number of pairs `(i,j)` with `|t i - t j| ≤ Δ`. -/
def kPC (Δ : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0)

lemma kDS_eq_kDSw (n : ℕ) (T : ℝ) (R : ℕ) (t : Fin R → ℝ)
    (hIcc : ∀ i, t i ∈ Set.Icc 0 T) :
    kDS n R t = kDSw n T (fun _ => 1) R t := by
  unfold kDS kDSw
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hw : |t i - t j| ≤ T := by
    have hi := hIcc i; have hj := hIcc j
    rw [abs_le]; exact ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩
  rw [if_pos hw]
  simp only [one_mul]

lemma kPC_eq (T : ℝ) (R : ℕ) (t : Fin R → ℝ)
    (hIcc : ∀ i, t i ∈ Set.Icc 0 T) : kPC T R t = (R : ℝ) ^ 2 := by
  unfold kPC
  have h1 : (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ T then (1 : ℝ) else 0))
      = ∑ _i : Fin R, ∑ _j : Fin R, (1 : ℝ) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hi := hIcc i; have hj := hIcc j
    have hw : |t i - t j| ≤ T := by
      rw [abs_le]; exact ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩
    rw [if_pos hw]
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma kDS_nonneg (n : ℕ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ kDS n R t := by
  unfold kDS
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))

lemma kterm_block_bound (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) :
    ‖∑ m ∈ Finset.Icc n (2 * n),
        (m : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ ≤ 2 * Real.sqrt (n : ℝ) := by
  have hNpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos hNpos
  have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hNpos.le
  have hterm : ∀ m ∈ Finset.Icc n (2 * n),
      ‖(m : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ = 1 / Real.sqrt (m : ℝ) := by
    intro m hm
    have hm1 : (1 : ℕ) ≤ m := le_trans hn (Finset.mem_Icc.mp hm).1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hnorm1 : ‖(m : ℂ) ^ (Complex.I * (τ : ℂ))‖ = 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
      simp
    have hnorm2 : ‖((Real.sqrt (m : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (m : ℝ) := by
      rw [show ‖((Real.sqrt (m : ℝ) : ℝ) : ℂ)‖ = |Real.sqrt (m : ℝ)| from RCLike.norm_ofReal _,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [norm_div, hnorm1, hnorm2, one_div]
  have hsum : ‖∑ m ∈ Finset.Icc n (2 * n),
        (m : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖
      ≤ ∑ m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (m : ℝ) := by
    calc _ ≤ ∑ m ∈ Finset.Icc n (2 * n),
            ‖(m : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (m : ℝ) := Finset.sum_congr rfl hterm
  have hstep : ∑ m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (m : ℝ)
      ≤ ∑ _m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (n : ℝ) := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    refine one_div_le_one_div_of_le hsqrtN ?_
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
  have hcard : (∑ _m ∈ Finset.Icc n (2 * n), (1 : ℝ) / Real.sqrt (n : ℝ))
      = ((n : ℝ) + 1) / Real.sqrt (n : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc]
    have h : 2 * n + 1 - n = n + 1 := by omega
    rw [h]; simp [nsmul_eq_mul]; ring
  have hfinal : ((n : ℝ) + 1) / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ hsqrtN]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hs, hsqrtN.le, hn1]
  calc _ ≤ ∑ m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (m : ℝ) := hsum
    _ ≤ ∑ _m ∈ Finset.Icc n (2 * n), 1 / Real.sqrt (n : ℝ) := hstep
    _ = ((n : ℝ) + 1) / Real.sqrt (n : ℝ) := hcard
    _ ≤ 2 * Real.sqrt (n : ℝ) := hfinal

lemma kDS_trivial (n : ℕ) (hn : 1 ≤ n) (R : ℕ) (t : Fin R → ℝ) :
    kDS n R t ≤ 4 * (n : ℝ) * (R : ℝ) ^ 2 := by
  unfold kDS
  have hpt : ∀ i j : Fin R,
      ‖∑ m ∈ Finset.Icc n (2 * n),
        (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2
      ≤ 4 * (n : ℝ) := by
    intro i j
    have h := kterm_block_bound n hn (t i - t j)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have : (2 * Real.sqrt (n : ℝ)) ^ 2 = 4 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    rwa [this] at h2
  calc (∑ i : Fin R, ∑ j : Fin R,
        ‖∑ m ∈ Finset.Icc n (2 * n),
          (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (m : ℝ) : ℂ)‖ ^ 2)
      ≤ ∑ i : Fin R, ∑ j : Fin R, 4 * (n : ℝ) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
    _ = 4 * (n : ℝ) * (R : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma card_le_of_icc_sep {R : ℕ} {t : Fin R → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hIcc : ∀ i, t i ∈ Set.Icc 0 T) (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) :
    (R : ℝ) ≤ T + 1 := by
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, abs_zero] at h
    linarith
  have hcard : ((Finset.univ.image t).card : ℝ) ≤ (T - 0) / 1 + 1 := by
    refine Commons.Analysis.Sampling.card_le_separated_finset (by norm_num : (0:ℝ) < 1) ?_ ?_ ?_ ?_
    · intro x hx y hy hxy
      rw [Finset.mem_image] at hx hy
      obtain ⟨i, -, rfl⟩ := hx
      obtain ⟨j, -, rfl⟩ := hy
      exact hsep i j (fun h => hxy (by rw [h]))
    · linarith
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx; exact (hIcc i).1
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx; exact (hIcc i).2
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simpa using hcard

/-- If `c^n ≤ x` with `c ≥ 0`, `x ≥ 0`, `n > 0`, then `c ≤ x^(1/n)`. -/
lemma le_rpow_one_div_of_pow_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : c ^ n ≤ x) : c ≤ x ^ ((1:ℝ)/n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (c ^ n) ^ ((1:ℝ)/n) ≤ x ^ ((1:ℝ)/n) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  have h2 : (c ^ n) ^ ((1:ℝ)/n) = c := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_mul hc]
    rw [show ((n:ℝ) * (1/(n:ℝ))) = 1 by field_simp]
    exact Real.rpow_one c
  linarith [h1, h2]

lemma star_le_quarter {T R : ℝ} (hT : 4096 ≤ T) (hR : 0 ≤ R) (hRT : R ≤ T + 1) :
    T ^ ((1:ℝ)/2) * R ^ ((1:ℝ)/4) ≤ T / 4 := by
  have hT0 : 0 < T := by linarith
  have h4q : (8:ℝ) ≤ T ^ ((1:ℝ)/4) :=
    le_rpow_one_div_of_pow_le hT0.le (by norm_num) (by norm_num : 0 < 4)
      (by norm_num1; linarith [hT])
  have h1 : R ^ ((1:ℝ)/4) ≤ (2*T) ^ ((1:ℝ)/4) := by
    refine Real.rpow_le_rpow hR ?_ (by norm_num); linarith
  have h2 : (2*T) ^ ((1:ℝ)/4) = (2:ℝ)^((1:ℝ)/4) * T^((1:ℝ)/4) :=
    Real.mul_rpow (by norm_num) hT0.le
  have h2p : (2:ℝ)^((1:ℝ)/4) ≤ 2 := by
    calc (2:ℝ)^((1:ℝ)/4) ≤ (2:ℝ)^(1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h3 : T ^ ((1:ℝ)/2) * T ^ ((1:ℝ)/4) = T ^ ((3:ℝ)/4) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hpow : T ^ ((1:ℝ)/4) * T ^ ((3:ℝ)/4) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have h4 : T ^ ((3:ℝ)/4) * 8 ≤ T := by
    calc T^((3:ℝ)/4) * 8 ≤ T^((3:ℝ)/4) * T^((1:ℝ)/4) := by
          nlinarith [h4q, Real.rpow_nonneg hT0.le ((3:ℝ)/4)]
      _ = T := by rw [mul_comm]; exact hpow
  have hmain : T^((1:ℝ)/2) * R^((1:ℝ)/4) ≤ (2:ℝ)^((1:ℝ)/4) * T^((3:ℝ)/4) := by
    calc T^((1:ℝ)/2) * R^((1:ℝ)/4)
        ≤ T^((1:ℝ)/2) * (2*T)^((1:ℝ)/4) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT0.le _)
      _ = T^((1:ℝ)/2) * ((2:ℝ)^((1:ℝ)/4) * T^((1:ℝ)/4)) := by rw [h2]
      _ = (2:ℝ)^((1:ℝ)/4) * (T^((1:ℝ)/2) * T^((1:ℝ)/4)) := by ring
      _ = (2:ℝ)^((1:ℝ)/4) * T^((3:ℝ)/4) := by rw [h3]
  calc T^((1:ℝ)/2) * R^((1:ℝ)/4) ≤ (2:ℝ)^((1:ℝ)/4) * T^((3:ℝ)/4) := hmain
    _ ≤ 2 * T^((3:ℝ)/4) := mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hT0.le _)
    _ ≤ T / 4 := by linarith [h4]


/-- From `N³ < 256 T²` and `T ≥ 16384` we get `2N < T/2`. -/
lemma two_N_lt_half_T {N : ℕ} {T : ℝ} (hT : 16384 ≤ T) (h : (N:ℝ)^3 < 256*T^2) :
    2*(N:ℝ) < T/2 := by
  have hT0 : 0 < T := by linarith
  have h1 : (2*(N:ℝ))^3 < (T/2)^3 := by
    have h2 : (2*(N:ℝ))^3 = 8*(N:ℝ)^3 := by ring
    have h3 : (T/2)^3 = T^3/8 := by ring
    rw [h2, h3]
    have h4 : (8:ℝ)*(N:ℝ)^3 < 8*(256*T^2) := by linarith
    have h5 : (8:ℝ)*(256*T^2) = 2048*T^2 := by ring
    rw [h5] at h4
    have h6 : (2048:ℝ)*T^2 ≤ T^3/8 := by nlinarith [hT0, hT]
    linarith
  exact lt_of_pow_lt_pow_left₀ 3 (by positivity) h1

/-- From `m³ ≤ 64 T²` and `T ≥ 0` we get `m ≤ 4 T^{2/3}`. -/
lemma le_four_rpow_two_thirds {m : ℕ} {T : ℝ} (hT : 0 ≤ T) (h : (m:ℝ)^3 ≤ 64*T^2) :
    (m:ℝ) ≤ 4 * T^((2:ℝ)/3) := by
  have h1 : ((m:ℝ)^3) ^ ((1:ℝ)/3) ≤ (64*T^2) ^ ((1:ℝ)/3) :=
    Real.rpow_le_rpow (by positivity) h (by norm_num)
  have h2 : ((m:ℝ)^3) ^ ((1:ℝ)/3) = (m:ℝ) := by
    rw [← Real.rpow_natCast (m:ℝ) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have h3 : (64*T^2) ^ ((1:ℝ)/3) = 4 * T^((2:ℝ)/3) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    · rw [show (64:ℝ) = 4^3 by norm_num, ← Real.rpow_natCast (4:ℝ) 3,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    · rw [← Real.rpow_natCast T 2, ← Real.rpow_mul hT]
      norm_num
  linarith [h1, h2, h3]

/-- From `256 T ≤ m²` and `T ≥ 0` we get `16 T^{1/2} ≤ m`. -/
lemma le_of_sq_ge {m : ℕ} {T : ℝ} (hT : 0 ≤ T) (h : 256*T ≤ (m:ℝ)^2) :
    16 * T^((1:ℝ)/2) ≤ (m:ℝ) := by
  have h1 : (16 * T^((1:ℝ)/2))^2 ≤ (m:ℝ)^2 := by
    have h2 : (16 * T^((1:ℝ)/2))^2 = 256*T := by
      rw [mul_pow, show (16:ℝ)^2 = 256 by norm_num]
      congr 1
      rw [← Real.rpow_natCast (T^((1:ℝ)/2)) 2, ← Real.rpow_mul hT]
      rw [show ((1:ℝ)/2 * ((2:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one]
    rw [h2]; exact h
  exact le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) (by positivity) h1



/-- `16 ≤ T^{1/2}` when `256 ≤ T`. -/
lemma sixteen_le_rpow_half {T : ℝ} (hT : 0 ≤ T) (h : 256 ≤ T) : (16:ℝ) ≤ T^((1:ℝ)/2) := by
  have h2 : (16:ℝ)^2 ≤ (T^((1:ℝ)/2))^2 := by
    rw [show (16:ℝ)^2 = 256 by norm_num]
    rw [← Real.rpow_natCast (T^((1:ℝ)/2)) 2, ← Real.rpow_mul hT]
    rw [show ((1:ℝ)/2 * ((2:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one]
    exact h
  exact le_of_pow_le_pow_left₀ (by norm_num : (2:ℕ) ≠ 0) (by positivity) h2

/-- `√(x+y) ≤ √x + √y`. -/
lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]


lemma mul_Cu_le {D K Tε G : ℝ} (h : D ≤ K) (hTε : 0 ≤ Tε) (hG : 0 ≤ G) :
    D * Tε * G ≤ K * Tε * G :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hTε) hG


set_option maxHeartbeats 50000000 in
/-- The proof of Theorem 1.1 reduces to the reference estimate `hRef` (`=REF`), the
Cauchy–Schwarz improvement `SQ`, the length increase `INCR` and the case-1 estimate `CASE1`
(`= kerr_case1`).  We follow Kerr, arXiv:1909.12075, §4. -/
theorem kerr_assembly
    (hRef : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
      ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      ≤ C * B ^ 2 * Δ ^ ε *
        ((∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ Δ then
            ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)),
              (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
           else 0))
        + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0))
        + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T → (N : ℝ) ≤ T → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ T then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * T ^ ε *
      ((R : ℝ) ^ 2 + (N : ℝ) * (R : ℝ)
        + T ^ ((1 : ℝ) / 2) * (R : ℝ) ^ ((5 : ℝ) / 4)) := by
  intro ε hε
  set e : ℝ := ε / 8 with hedef
  have hepos : 0 < e := by rw [hedef]; linarith
  have helee : e ≤ ε := by rw [hedef]; linarith
  have h3e : 3 * e ≤ ε := by rw [hedef]; linarith
  have h2e : 2 * e ≤ ε := by rw [hedef]; linarith
  obtain ⟨C1, hC1, hREF⟩ := hRef e hepos
  obtain ⟨C2, hC2, hSQ⟩ := dirichlet_poly_square_bound e hepos
  obtain ⟨C3, hC3, hINCR⟩ := dirichlet_poly_increase_length e hepos
  obtain ⟨C4, hC4, hCASE1⟩ := kerr_case1 hRef e hepos
  obtain ⟨C5, hC5, hMAJ⟩ := kerr_coefficient_majorant
  have hC1nn : (0:ℝ) ≤ C1 := hC1.le
  have hC2nn : (0:ℝ) ≤ C2 := hC2.le
  have hC3nn : (0:ℝ) ≤ C3 := hC3.le
  have hC4nn : (0:ℝ) ≤ C4 := hC4.le
  set sqc : ℝ := Real.sqrt (C2*C4) with hsqc
  have hsqcnn : 0 ≤ sqc := by rw [hsqc]; positivity
  have hsqc2 : sqc^2 = C2*C4 := by rw [hsqc]; rw [Real.sq_sqrt]; positivity
  set Tbig : ℝ := (10:ℝ)^30 with hTbig
  have hTbig1 : (1:ℝ) ≤ Tbig := by rw [hTbig]; norm_num
  have hTbig256 : (256:ℝ) ≤ Tbig := by rw [hTbig]; norm_num
  have hTbig2048 : (2048:ℝ) ≤ Tbig := by rw [hTbig]; norm_num
  set Au : ℝ := 4*Tbig + 2*C4 + 1 with hAu
  set Bu : ℝ := 131072 + 1 with hBu
  set Du : ℝ := 200*C3*C1*(sqc+1) + 1 with hDu
  set Eu : ℝ := 20*C3*C4 + 1 with hEu
  set Fu : ℝ := 50*C3^2*C4 + 1 with hFu
  set Cu : ℝ := max Au (max Bu (max Du (max Eu Fu))) with hCu
  have hCunn : 0 ≤ Cu := by rw [hCu]; positivity
  have hAuC : Au ≤ Cu := by rw [hCu]; exact le_max_left _ _
  have hBuC : Bu ≤ Cu := by
    rw [hCu]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDuC : Du ≤ Cu := by
    rw [hCu]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hEuC : Eu ≤ Cu := by
    rw [hCu]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hFuC : Fu ≤ Cu := by
    rw [hCu]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hupper : 2*C4 ≤ Cu := by
    rw [hCu, hAu]
    have : (2*C4 : ℝ) ≤ 4*Tbig + 2*C4 + 1 := by linarith [hTbig1]
    exact le_trans this (le_max_left _ _)
  have hDu' : 100*C3*C1*(sqc+1) ≤ Cu := by
    have hnn : (0:ℝ) ≤ C3*C1*(sqc+1) := by positivity
    have : 100*C3*C1*(sqc+1) ≤ Du := by rw [hDu]; linarith
    linarith [this, hDuC]
  have hEu' : 5*C3*C4 ≤ Cu := by
    have hnn : (0:ℝ) ≤ C3*C4 := by positivity
    have : 5*C3*C4 ≤ Eu := by rw [hEu]; linarith
    linarith [this, hEuC]
  have hFu' : 9*C3^2*C4 ≤ Cu := by
    have hnn : (0:ℝ) ≤ C3^2*C4 := by positivity
    have : 9*C3^2*C4 ≤ Fu := by rw [hFu]; linarith
    linarith [this, hFuC]
  have hBu' : (131072:ℝ) ≤ Cu := by
    have : (131072:ℝ) ≤ Bu := by rw [hBu]; linarith
    linarith [this, hBuC]
  refine ⟨C5 * Cu + 1, by positivity, ?_⟩
  intro N hN T hT hNT B hB c hc R t hIcc hsep
  set G : ℝ := (R:ℝ)^2 + (N:ℝ)*(R:ℝ) + T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) with hG
  have hT0 : (0:ℝ) < T := by linarith
  have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg R
  have hNRnn : (0:ℝ) ≤ (N:ℝ)*(R:ℝ) := mul_nonneg (Nat.cast_nonneg N) hR0
  have hXnn : (0:ℝ) ≤ T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hR0 _)
  have hTepos : (0:ℝ) ≤ T^ε := Real.rpow_nonneg hT0.le _
  have hGnn : 0 ≤ G := by rw [hG]; linarith [sq_nonneg (R:ℝ), hNRnn, hXnn]
  have hR2G : (R:ℝ)^2 ≤ G := by rw [hG]; linarith [hNRnn, hXnn]
  have hNRG : (N:ℝ)*(R:ℝ) ≤ G := by rw [hG]; linarith [sq_nonneg (R:ℝ), hXnn]
  have hXG : T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) ≤ G := by rw [hG]; linarith [sq_nonneg (R:ℝ), hNRnn]
  have hRG : (R:ℝ) ≤ G := by
    have h1 : (R:ℝ) ≤ (N:ℝ)*(R:ℝ) := le_mul_of_one_le_left hR0 hN1R
    linarith [hNRG, h1]
  change kDSw N T c R t ≤ (C5 * Cu + 1) * B^2 * T^ε * G
  have hunit : kDS N R t ≤ Cu * T^ε * G := by
    rcases Nat.eq_zero_or_pos R with hRz | hRpos
    · subst hRz
      have hzero : kDS N 0 t = 0 := by unfold kDS; simp
      rw [hzero, hG]
      positivity
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hRpos
    have hR0pos : (0:ℝ) < (R:ℝ) := by linarith
    by_cases hTsmall : T < Tbig
    · have h1 : kDS N R t ≤ Au * G := by
        have h := kDS_trivial N hN R t
        have hNle : (N:ℝ) ≤ Tbig := le_of_lt (lt_of_le_of_lt hNT hTsmall)
        have hRsq : (0:ℝ) ≤ (R:ℝ)^2 := by positivity
        have h4 : 4*(N:ℝ)*(R:ℝ)^2 ≤ 4*Tbig*G := by
          calc 4*(N:ℝ)*(R:ℝ)^2 ≤ 4*Tbig*(R:ℝ)^2 := by nlinarith [hNle, hR0, hRsq, hTbig1]
            _ ≤ 4*Tbig*G := by
                refine mul_le_mul_of_nonneg_left hR2G (by positivity)
        calc kDS N R t ≤ 4*(N:ℝ)*(R:ℝ)^2 := h
          _ ≤ 4*Tbig*G := h4
          _ ≤ Au*G := by
              refine mul_le_mul_of_nonneg_right ?_ hGnn
              rw [hAu]; linarith [hTbig1, hC4nn]
      calc kDS N R t ≤ Au*G := h1
        _ ≤ Au*T^ε*G := by
            have hT1 : (1:ℝ) ≤ T^ε := Real.one_le_rpow hT hε.le
            rw [show Au*T^ε*G = (Au*G)*T^ε by ring]
            exact le_mul_of_one_le_right (by positivity) hT1
        _ ≤ Cu*T^ε*G := mul_Cu_le hAuC hTepos hGnn
    · rw [not_lt] at hTsmall
      have hT256 : (256:ℝ) ≤ T := le_trans hTbig256 hTsmall
      have hT2048 : (2048:ℝ) ≤ T := le_trans hTbig2048 hTsmall
      set star : ℝ := T^((1:ℝ)/2) * (R:ℝ)^((1:ℝ)/4) with hstar
      have hstarnn : 0 ≤ star := by rw [hstar]; positivity
      set m : ℕ := max (2*N) (Nat.ceil star) with hm
      have hm2N : (2*(N:ℝ)) ≤ (m:ℝ) := by
        have h : ((2*N : ℕ) : ℝ) ≤ (m:ℝ) := by
          have := (show (2*N : ℕ) ≤ m from by rw [hm]; exact le_max_left _ _)
          exact_mod_cast this
        push_cast at h
        linarith [h]
      have hm1 : 1 ≤ m := by
        have : (1:ℝ) ≤ (m:ℝ) := by linarith [hm2N, hN1R]
        exact_mod_cast this
      have hmpos : (0:ℝ) < (m:ℝ) := by linarith [hm1]
      have hstarm : star ≤ (m:ℝ) := by
        have h : ((Nat.ceil star : ℕ) : ℝ) ≤ (m:ℝ) := by
          have := (show (Nat.ceil star : ℕ) ≤ m from by rw [hm]; exact le_max_right _ _)
          exact_mod_cast this
        linarith [Nat.le_ceil star, h]
      have hRle : (R:ℝ) ≤ T + 1 := card_le_of_icc_sep hT0.le hIcc hsep
      have hstar_le : star ≤ T/4 := by rw [hstar]; exact star_le_quarter (by linarith [hT256]) hR0 hRle
      have hT13 : (10000000000:ℝ) ≤ T^((1:ℝ)/3) := by
        have h1 : ((10:ℝ)^30)^((1:ℝ)/3) ≤ T^((1:ℝ)/3) :=
          Real.rpow_le_rpow (by positivity) hTsmall (by norm_num)
        have h2 : ((10:ℝ)^30)^((1:ℝ)/3) = (10000000000:ℝ) := by
          rw [← Real.rpow_natCast (10:ℝ) 30, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
          norm_num
        linarith [h1, h2]
      have hT23le : T^((2:ℝ)/3) ≤ T/100000 := by
        have h1 : T^((2:ℝ)/3) = T * (T^((1:ℝ)/3))⁻¹ := by
          rw [show (2:ℝ)/3 = 1 - 1/3 by norm_num, Real.rpow_sub hT0, Real.rpow_one, div_eq_mul_inv]
        rw [h1]
        have h2 : (T^((1:ℝ)/3))⁻¹ ≤ ((10:ℝ)^10)⁻¹ := by
          refine (inv_le_inv₀ (Real.rpow_pos_of_pos hT0 _) (by positivity)).mpr ?_
          calc (10:ℝ)^10 = 10000000000 := by norm_num
            _ ≤ T^((1:ℝ)/3) := hT13
        calc T * (T^((1:ℝ)/3))⁻¹ ≤ T * ((10:ℝ)^10)⁻¹ := mul_le_mul_of_nonneg_left h2 hT0.le
          _ ≤ T/100000 := by
              have h3 : ((10:ℝ)^10)⁻¹ ≤ 1/100000 := by norm_num
              calc T * ((10:ℝ)^10)⁻¹ ≤ T * (1/100000) := mul_le_mul_of_nonneg_left h3 hT0.le
                _ = T/100000 := by ring
      have hmub : (m:ℝ) ≤ 2*(N:ℝ) + star + 1 := by
        have h : (m:ℝ) = max ((2*N:ℕ):ℝ) ((Nat.ceil star:ℕ):ℝ) := by
          rw [hm]; exact Nat.cast_max (2*N) (Nat.ceil star)
        rw [h]
        have hceil : ((Nat.ceil star : ℕ) : ℝ) ≤ star + 1 := le_of_lt (Nat.ceil_lt_add_one hstarnn)
        push_cast
        exact max_le (by linarith) (by linarith)
      have hmR : (m:ℝ)*(R:ℝ) ≤ 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ) := by
        have h1 : (m:ℝ)*(R:ℝ) ≤ (2*(N:ℝ) + star + 1)*(R:ℝ) :=
          mul_le_mul_of_nonneg_right hmub hR0
        have hR4 : (R:ℝ)^((1:ℝ)/4) * (R:ℝ) = (R:ℝ)^((5:ℝ)/4) := by
          nth_rewrite 2 [← Real.rpow_one (R:ℝ)]
          rw [← Real.rpow_add hR0pos]
          norm_num
        have h2 : star*(R:ℝ) = T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) := by
          rw [hstar, mul_assoc, hR4]
        nlinarith [h1, h2]
      by_cases hcase1 : 256 * T^2 ≤ (N:ℝ)^3
      · have h := hCASE1 N hN T hT hNT hcase1 R t hIcc hsep
        have hTe1 : (1:ℝ) ≤ T^e := Real.one_le_rpow hT hepos.le
        have hTee : T^e ≤ T^ε := Real.rpow_le_rpow_of_exponent_le hT helee
        have h2G : (R:ℝ)^2 + (N:ℝ)*(R:ℝ) ≤ 2*G := by linarith [hR2G, hNRG]
        calc kDS N R t ≤ C4 * T^e * ((R:ℝ)^2 + (N:ℝ)*(R:ℝ)) := h
          _ ≤ C4 * T^e * (2*G) := by
              refine mul_le_mul_of_nonneg_left h2G (by positivity)
          _ = (2*C4*T^e)*G := by ring
          _ ≤ (2*C4*T^ε)*G := by
              refine mul_le_mul_of_nonneg_right ?_ hGnn
              exact mul_le_mul_of_nonneg_left hTee (by positivity)
          _ ≤ Cu*T^ε*G := by
              refine mul_Cu_le ?_ hTepos hGnn
              linarith [hupper]
      · rw [not_le] at hcase1
        have h2NltT : 2*(N:ℝ) < T/2 := two_N_lt_half_T (by linarith [hT2048]) hcase1
        have hm_le_T : (m:ℝ) ≤ T := by linarith [hmub, hstar_le, h2NltT, hT2048]
        by_cases hma : (m:ℝ)^2 < 256*T
        · -- trivial branch
          have hN8 : (N:ℝ) < 8 * T^((1:ℝ)/2) := by
            have h3 : (2*(N:ℝ))^2 ≤ (m:ℝ)^2 := pow_le_pow_left₀ (by positivity) hm2N 2
            have h4 : (N:ℝ)^2 < 64*T := by nlinarith [lt_of_le_of_lt h3 hma]
            have h5 : (8*T^((1:ℝ)/2))^2 = 64*T := by
              rw [mul_pow, show (8:ℝ)^2 = 64 by norm_num]
              congr 1
              rw [← Real.rpow_natCast (T^((1:ℝ)/2)) 2, ← Real.rpow_mul hT0.le]
              rw [show ((1:ℝ)/2 * ((2:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one]
            exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [h5]; exact h4)
          have hR65536 : (R:ℝ) < 65536 := by
            have h4 : star^4 ≤ (m:ℝ)^4 := pow_le_pow_left₀ hstarnn hstarm 4
            have h5 : star^4 = T^2 * (R:ℝ) := by
              rw [hstar, mul_pow]
              congr 1
              · rw [← Real.rpow_natCast (T^((1:ℝ)/2)) 4, ← Real.rpow_mul hT0.le]; norm_num
              · rw [← Real.rpow_natCast ((R:ℝ)^((1:ℝ)/4)) 4, ← Real.rpow_mul hR0]; norm_num
            have h6 : (m:ℝ)^4 < (256*T)^2 := by
              have h7 : ((m:ℝ)^2)^2 < (256*T)^2 := pow_lt_pow_left₀ hma (by positivity) (by norm_num)
              rwa [show ((m:ℝ)^2)^2 = (m:ℝ)^4 by ring] at h7
            have h7 : T^2 * (R:ℝ) < 65536*T^2 := by
              have e1 : T^2 * (R:ℝ) ≤ (m:ℝ)^4 := by rw [← h5]; exact h4
              have e3 : (256*T)^2 = 65536*T^2 := by ring
              linarith [e1, h6, e3]
            have hT2 : (0:ℝ) < T^2 := by positivity
            have h7' : T^2 * (R:ℝ) < T^2 * 65536 := by linarith [h7]
            exact lt_of_mul_lt_mul_left h7' hT2.le
          have hR34 : (R:ℝ)^((3:ℝ)/4) ≤ 4096 := by
            have hh := Real.rpow_lt_rpow hR0 hR65536 (by norm_num : (0:ℝ) < 3/4)
            have h2 : ((65536:ℝ))^((3:ℝ)/4) = 4096 := by
              rw [show (65536:ℝ) = 2^16 by norm_num, ← Real.rpow_natCast (2:ℝ) 16,
                ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              norm_num
            linarith [hh, h2]
          have hsplit : (R:ℝ)^2 = (R:ℝ)^((3:ℝ)/4) * (R:ℝ)^((5:ℝ)/4) := by
            rw [← Real.rpow_add hR0pos]; norm_num
          have htriv : kDS N R t ≤ Bu * G := by
            have h := kDS_trivial N hN R t
            have hN8' : (N:ℝ) ≤ 8*T^((1:ℝ)/2) := le_of_lt hN8
            rw [hBu]
            calc kDS N R t ≤ 4*(N:ℝ)*(R:ℝ)^2 := h
              _ ≤ 32*T^((1:ℝ)/2)*(R:ℝ)^2 := by
                    have hR2 : (0:ℝ) ≤ (R:ℝ)^2 := by positivity
                    have h4N : (4:ℝ)*(N:ℝ) ≤ 4*(8*T^((1:ℝ)/2)) := by linarith [hN8']
                    have hmm := mul_le_mul_of_nonneg_right h4N hR2
                    linarith [hmm]
              _ = 32*T^((1:ℝ)/2)*((R:ℝ)^((3:ℝ)/4) * (R:ℝ)^((5:ℝ)/4)) := by rw [← hsplit]
              _ ≤ 32*T^((1:ℝ)/2)*(4096 * (R:ℝ)^((5:ℝ)/4)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact mul_le_mul_of_nonneg_right hR34 (Real.rpow_nonneg hR0 _)
              _ = 131072 * (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) := by ring
              _ ≤ 131072 * G := mul_le_mul_of_nonneg_left hXG (by norm_num)
              _ ≤ (131072+1) * G := by nlinarith [hGnn]
          calc kDS N R t ≤ Bu*G := htriv
            _ ≤ Bu*T^ε*G := by
                have hT1 : (1:ℝ) ≤ T^ε := Real.one_le_rpow hT hε.le
                rw [show Bu*T^ε*G = (Bu*G)*T^ε by ring]
                exact le_mul_of_one_le_right (by positivity) hT1
            _ ≤ Cu*T^ε*G := mul_Cu_le hBuC hTepos hGnn
        · rw [not_lt] at hma
          have hm16 : 16 * T^((1:ℝ)/2) ≤ (m:ℝ) := le_of_sq_ge hT0.le hma
          by_cases hmb : (m:ℝ)^3 ≤ 64*T^2
          · -- P branch
            set A : ℕ := Nat.ceil (4*T/(m:ℝ)) with hAdef
            set M : ℕ := 8*A^2 with hMdef
            have hA1 : 1 ≤ A := by
              have h : (0:ℝ) < (A:ℝ) := lt_of_lt_of_le (by positivity) (Nat.le_ceil _)
              exact_mod_cast h
            have hM_ge : 8*A^2 ≤ M := by rw [hMdef]
            have hM1 : 1 ≤ M := by
              have hA1R : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA1
              have : (1:ℝ) ≤ (M:ℝ) := by rw [hMdef]; push_cast; nlinarith [hA1R]
              exact_mod_cast this
            have hAle : (A:ℝ) < 4*T/(m:ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
            have h4 : 4*T/(m:ℝ) ≤ T^((1:ℝ)/2)/4 := by
              have hsqq : T^((1:ℝ)/2) * T^((1:ℝ)/2) = T := by
                rw [← Real.rpow_add hT0]; norm_num
              have hprod := mul_le_mul_of_nonneg_right hm16 (Real.rpow_nonneg hT0.le ((1:ℝ)/2))
              rw [div_le_iff₀ hmpos]
              rw [show T^((1:ℝ)/2)/4 * (m:ℝ) = T^((1:ℝ)/2)*(m:ℝ)/4 by ring]
              rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
              nlinarith [hprod, hsqq]
            have hAub : (A:ℝ) ≤ 5*T^((1:ℝ)/2)/16 := by
              have h1 : (1:ℝ) ≤ T^((1:ℝ)/2)/16 := by
                rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
                linarith [sixteen_le_rpow_half hT0.le hT256]
              linarith [hAle, h4, h1]
            have hM_leT : (M:ℝ) ≤ T := by
              have hA2 : (A:ℝ)^2 ≤ (5*T^((1:ℝ)/2)/16)^2 := pow_le_pow_left₀ (by positivity) hAub 2
              have heq : (5*T^((1:ℝ)/2)/16)^2 = 25*T/256 := by
                have hh : (T^((1:ℝ)/2))^2 = T := by
                  rw [← Real.rpow_natCast (T^((1:ℝ)/2)) 2, ← Real.rpow_mul hT0.le]
                  rw [show ((1:ℝ)/2 * ((2:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one]
                rw [div_pow, mul_pow, hh]
                norm_num
              rw [hMdef]; push_cast
              nlinarith [hA2, heq, hT0]
            have hM256 : 256*T^2 ≤ (M:ℝ)^3 := by
              have hAm : 4*T ≤ (A:ℝ)*(m:ℝ) := by
                have h := Nat.le_ceil (4*T/(m:ℝ))
                rw [div_le_iff₀ hmpos] at h
                linarith [h]
              have hcube : (64:ℝ)*T^3 ≤ ((A:ℝ)*(m:ℝ))^3 := by
                have h1 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*T) hAm 3
                rw [mul_pow] at h1
                nlinarith [h1]
              have hA3 : T ≤ (A:ℝ)^3 := by
                have h2 : ((A:ℝ)*(m:ℝ))^3 ≤ (A:ℝ)^3 * (64*T^2) := by
                  rw [mul_pow]
                  exact mul_le_mul_of_nonneg_left hmb (by positivity)
                have h3 : (64:ℝ)*T^3 ≤ (A:ℝ)^3 * (64*T^2) := le_trans hcube h2
                have hTp : (0:ℝ) < 64*T^2 := by positivity
                nlinarith [h3, hTp]
              rw [hMdef]; push_cast
              nlinarith [hA3, sq_nonneg ((A:ℝ)^3)]
            have hme : (m:ℝ)^e ≤ T^e := Real.rpow_le_rpow (by positivity) hm_le_T hepos.le
            have hMe : (M:ℝ)^e ≤ T^e := Real.rpow_le_rpow (by positivity) hM_leT hepos.le
            have href : kDS m R t ≤ C1 * T^e * (kDS A R t + kPC T R t + (m:ℝ)^(1+e)*((R:ℝ)+1)) := by
              rw [kDS_eq_kDSw m T R t hIcc, kDS_eq_kDSw A T R t hIcc]
              have h0 := hREF m hm1 T hT hm_le_T 1 (le_refl 1) (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
              simpa only [kDSw, kPC, one_mul, mul_one, one_pow] using h0
            rw [kPC_eq T R t hIcc] at href
            have hsq : (kDS A R t)^2 ≤ C2 * (M:ℝ)^e * kPC T R t * kDS M R t := by
              rw [kDS_eq_kDSw A T R t hIcc, kDS_eq_kDSw M T R t hIcc]
              have h0 := hSQ A M hA1 hM_ge T hT 1 (le_refl 1) (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
              simpa only [kDSw, kPC, one_mul, mul_one, one_pow] using h0
            rw [kPC_eq T R t hIcc] at hsq
            have hcase := hCASE1 M hM1 T hT hM_leT hM256 R t hIcc hsep
            have hmexp : (m:ℝ)^(1+e) * ((R:ℝ)+1) ≤ 2*(m:ℝ)*(R:ℝ)*T^e := by
              have h1 : (m:ℝ)^(1+e) = (m:ℝ) * (m:ℝ)^e := by
                rw [Real.rpow_add hmpos, Real.rpow_one]
              rw [h1]
              have h2 : (R:ℝ) + 1 ≤ 2*(R:ℝ) := by linarith
              have h3 : (m:ℝ) * (m:ℝ)^e ≤ (m:ℝ) * T^e :=
                mul_le_mul_of_nonneg_left hme (by positivity)
              have h4 : (m:ℝ) * T^e * ((R:ℝ)+1) ≤ (m:ℝ) * T^e * (2*(R:ℝ)) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
              nlinarith [h3, h4]
            have hrefS : kDS m R t ≤ C1 * T^e * (kDS A R t + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e) := by
              calc kDS m R t ≤ C1 * T^e * (kDS A R t + (R:ℝ)^2 + (m:ℝ)^(1+e)*((R:ℝ)+1)) := href
                _ ≤ C1 * T^e * (kDS A R t + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    linarith [hmexp]
            have hsqrtM : Real.sqrt (M:ℝ) ≤ 12 * T / (m:ℝ) := by
              have hAm : (A:ℝ)*(m:ℝ) ≤ 4*T + (m:ℝ) := by
                have hh := le_of_lt hAle
                have h2 := mul_le_mul_of_nonneg_right hh hmpos.le
                rw [show (4*T/(m:ℝ) + 1) * (m:ℝ) = 4*T + (m:ℝ) by
                  rw [add_mul, div_mul_cancel₀ _ hmpos.ne', one_mul]] at h2
                linarith [h2]
              have hsqrt8 : Real.sqrt (8:ℝ) ≤ 2.83 := by
                rw [Real.sqrt_le_iff]; norm_num
              have hMval : (M:ℝ) = 8*(A:ℝ)^2 := by rw [hMdef]; push_cast; ring
              rw [hMval, show (8:ℝ)*(A:ℝ)^2 = 8*(A:ℝ)^2 by rfl, Real.sqrt_mul (by norm_num),
                Real.sqrt_sq (by positivity)]
              have hmT : (m:ℝ) ≤ 4*T^((2:ℝ)/3) := le_four_rpow_two_thirds hT0.le hmb
              have hmT2 : (m:ℝ) ≤ T/25000 := by nlinarith [hmT, hT23le]
              rw [le_div_iff₀ hmpos]
              have hcn : Real.sqrt 8 * ((A:ℝ)*(m:ℝ)) ≤ 2.83 * (4*T + (m:ℝ)) := by
                calc Real.sqrt 8 * ((A:ℝ)*(m:ℝ)) ≤ Real.sqrt 8 * (4*T + (m:ℝ)) :=
                      mul_le_mul_of_nonneg_left hAm (Real.sqrt_nonneg 8)
                  _ ≤ 2.83 * (4*T + (m:ℝ)) := mul_le_mul_of_nonneg_right hsqrt8 (by linarith [hAm, hmpos])
              have hcn2 : 2.83 * (4*T + (m:ℝ)) ≤ 12*T := by nlinarith [hmT2, hT0]
              calc Real.sqrt 8 * (A:ℝ) * (m:ℝ) = Real.sqrt 8 * ((A:ℝ)*(m:ℝ)) := by ring
                _ ≤ 2.83 * (4*T + (m:ℝ)) := hcn
                _ ≤ 12*T := hcn2
            have hTm : (T/(m:ℝ)) * (R:ℝ)^((3:ℝ)/2) ≤ T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) := by
              have hR14 : (R:ℝ)^((1:ℝ)/4) * (R:ℝ)^((5:ℝ)/4) = (R:ℝ)^((3:ℝ)/2) := by
                rw [← Real.rpow_add hR0pos]; norm_num
              have h1 : star * (R:ℝ)^((5:ℝ)/4) ≤ (m:ℝ) * (R:ℝ)^((5:ℝ)/4) :=
                mul_le_mul_of_nonneg_right hstarm (Real.rpow_nonneg hR0 _)
              rw [hstar, mul_assoc, hR14] at h1
              have h2 : T^((1:ℝ)/2) * (T^((1:ℝ)/2) * (R:ℝ)^((3:ℝ)/2))
                  ≤ T^((1:ℝ)/2) * ((m:ℝ) * (R:ℝ)^((5:ℝ)/4)) :=
                mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT0.le _)
              have h3 : T^((1:ℝ)/2) * T^((1:ℝ)/2) = T := by
                rw [← Real.rpow_add hT0]; norm_num
              rw [div_mul_eq_mul_div, div_le_iff₀ hmpos]
              calc T * (R:ℝ)^((3:ℝ)/2)
                  = (T^((1:ℝ)/2) * T^((1:ℝ)/2)) * (R:ℝ)^((3:ℝ)/2) := by rw [h3]
                _ = T^((1:ℝ)/2) * (T^((1:ℝ)/2) * (R:ℝ)^((3:ℝ)/2)) := by ring
                _ ≤ T^((1:ℝ)/2) * ((m:ℝ) * (R:ℝ)^((5:ℝ)/4)) := h2
                _ = T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) * (m:ℝ) := by ring
            have hSA : kDS A R t ≤ sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4))) := by
              have hsq2 : (kDS A R t)^2 ≤ C2*C4*T^e*T^e*((R:ℝ)^2*((R:ℝ)^2 + (M:ℝ)*(R:ℝ))) := by
                have h1 : (kDS A R t)^2 ≤ C2 * (M:ℝ)^e * (R:ℝ)^2 * kDS M R t := hsq
                have h2 : C2 * (M:ℝ)^e * (R:ℝ)^2 * kDS M R t
                    ≤ C2 * (M:ℝ)^e * (R:ℝ)^2 * (C4*T^e*((R:ℝ)^2+(M:ℝ)*(R:ℝ))) := by
                  refine mul_le_mul_of_nonneg_left hcase (by positivity)
                have h3 : C2 * (M:ℝ)^e * (R:ℝ)^2 * (C4*T^e*((R:ℝ)^2+(M:ℝ)*(R:ℝ)))
                    ≤ C2 * T^e * (R:ℝ)^2 * (C4*T^e*((R:ℝ)^2+(M:ℝ)*(R:ℝ))) := by
                  have hh : C2 * (M:ℝ)^e ≤ C2 * T^e := mul_le_mul_of_nonneg_left hMe hC2nn
                  have hh2 : C2 * (M:ℝ)^e * (R:ℝ)^2 ≤ C2 * T^e * (R:ℝ)^2 :=
                    mul_le_mul_of_nonneg_right hh (by positivity)
                  exact mul_le_mul_of_nonneg_right hh2 (by positivity)
                have h4 : C2 * T^e * (R:ℝ)^2 * (C4*T^e*((R:ℝ)^2+(M:ℝ)*(R:ℝ)))
                    = C2*C4*T^e*T^e*((R:ℝ)^2*((R:ℝ)^2 + (M:ℝ)*(R:ℝ))) := by ring
                linarith [h1, h2, h3, h4.symm.le, h4.le]
              have hsqrt : kDS A R t ≤ Real.sqrt (C2*C4*T^e*T^e*((R:ℝ)^2*((R:ℝ)^2 + (M:ℝ)*(R:ℝ)))) := by
                rw [← Real.sqrt_sq (kDS_nonneg A R t)]
                exact Real.sqrt_le_sqrt hsq2
              have hsl : Real.sqrt (C2*C4*T^e*T^e*((R:ℝ)^2*((R:ℝ)^2 + (M:ℝ)*(R:ℝ))))
                  = sqc * T^e * (R:ℝ) * Real.sqrt ((R:ℝ)^2 + (M:ℝ)*(R:ℝ)) := by
                have hsqT : Real.sqrt (T^e*T^e) = T^e := by
                  rw [show T^e*T^e = (T^e)^2 by ring, Real.sqrt_sq (Real.rpow_nonneg hT0.le e)]
                have hsR : Real.sqrt ((R:ℝ)^2) = (R:ℝ) := Real.sqrt_sq hR0
                have hXnn : (0:ℝ) ≤ (C2*C4)*(T^e*T^e) := by positivity
                have hC24nn : (0:ℝ) ≤ C2*C4 := by positivity
                have hYnn : (0:ℝ) ≤ (R:ℝ)^2 := by positivity
                rw [show C2*C4*T^e*T^e*((R:ℝ)^2*((R:ℝ)^2 + (M:ℝ)*(R:ℝ)))
                    = ((C2*C4)*(T^e*T^e)) * ((R:ℝ)^2 * ((R:ℝ)^2 + (M:ℝ)*(R:ℝ))) by ring]
                rw [Real.sqrt_mul hXnn ((R:ℝ)^2 * ((R:ℝ)^2 + (M:ℝ)*(R:ℝ))),
                  Real.sqrt_mul hC24nn (T^e*T^e),
                  Real.sqrt_mul hYnn ((R:ℝ)^2 + (M:ℝ)*(R:ℝ))]
                rw [hsR, hsqT, hsqc]
                ring
              rw [hsl] at hsqrt
              have h7 : Real.sqrt ((R:ℝ)^2 + (M:ℝ)*(R:ℝ)) ≤ (R:ℝ) + Real.sqrt ((M:ℝ)*(R:ℝ)) := by
                have hh := sqrt_add_le' (x := (R:ℝ)^2) (y := (M:ℝ)*(R:ℝ))
                  (by positivity) (by positivity)
                rwa [Real.sqrt_sq hR0] at hh
              have h9 : Real.sqrt ((M:ℝ)*(R:ℝ)) = Real.sqrt (M:ℝ) * Real.sqrt (R:ℝ) :=
                Real.sqrt_mul (by positivity) _
              have h10 : Real.sqrt (M:ℝ) * Real.sqrt (R:ℝ) ≤ (12 * T / (m:ℝ)) * (R:ℝ)^((1:ℝ)/2) := by
                rw [Real.sqrt_eq_rpow (R:ℝ)]
                exact mul_le_mul_of_nonneg_right hsqrtM (Real.rpow_nonneg hR0 _)
              have h11 : (12 * T / (m:ℝ)) * (R:ℝ)^((1:ℝ)/2) * (R:ℝ) ≤ 12 * (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) := by
                have hrr : (R:ℝ)^((1:ℝ)/2) * (R:ℝ) = (R:ℝ)^((3:ℝ)/2) := by
                  nth_rewrite 2 [← Real.rpow_one (R:ℝ)]
                  rw [← Real.rpow_add hR0pos]; norm_num
                rw [show (12 * T / (m:ℝ)) * (R:ℝ)^((1:ℝ)/2) * (R:ℝ)
                    = (12 * T / (m:ℝ)) * ((R:ℝ)^((1:ℝ)/2) * (R:ℝ)) by ring]
                rw [hrr]
                rw [show (12 * T / (m:ℝ)) * (R:ℝ)^((3:ℝ)/2) = (T/(m:ℝ)) * (R:ℝ)^((3:ℝ)/2) * 12 by ring]
                nlinarith [hTm]
              calc kDS A R t ≤ sqc * T^e * (R:ℝ) * Real.sqrt ((R:ℝ)^2 + (M:ℝ)*(R:ℝ)) := hsqrt
                _ ≤ sqc * T^e * (R:ℝ) * ((R:ℝ) + Real.sqrt ((M:ℝ)*(R:ℝ))) := by
                    refine mul_le_mul_of_nonneg_left h7 (by positivity)
                _ = sqc * T^e * ((R:ℝ)^2 + (R:ℝ)*Real.sqrt ((M:ℝ)*(R:ℝ))) := by ring
                _ ≤ sqc * T^e * ((R:ℝ)^2 + (R:ℝ)*((12 * T / (m:ℝ)) * (R:ℝ)^((1:ℝ)/2))) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    have := mul_le_mul_of_nonneg_left (le_trans (le_of_eq h9) h10) hR0
                    linarith [this]
                _ ≤ sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4))) := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    have := h11
                    nlinarith [this, hR0]
            have hinc : kDS N R t ≤ C3 * (m:ℝ)^e * kDS m R t := by
              rw [kDS_eq_kDSw N T R t hIcc, kDS_eq_kDSw m T R t hIcc]
              have h0 := hINCR N m hN (by rw [hm]; exact le_max_left _ _) T hT 1 (le_refl 1)
                (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
              simpa only [kDSw, one_mul, mul_one, one_pow] using h0
            have hEE : T^e * T^e ≤ T^ε := by
              rw [← Real.rpow_add hT0]
              exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h2e])
            have hEEE : T^e * (T^e * T^e) ≤ T^ε := by
              rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
              exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h3e])
            have hstep1 : kDS N R t ≤ C3 * (m:ℝ)^e * kDS m R t := hinc
            have hstep2 : C3 * (m:ℝ)^e * kDS m R t
                ≤ C3 * T^e * (C1 * T^e * (kDS A R t + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e)) := by
              have hA : C3 * (m:ℝ)^e ≤ C3 * T^e := mul_le_mul_of_nonneg_left hme hC3nn
              calc C3 * (m:ℝ)^e * kDS m R t ≤ C3 * T^e * kDS m R t :=
                    mul_le_mul_of_nonneg_right hA (kDS_nonneg m R t)
                _ ≤ C3 * T^e * (C1 * T^e * (kDS A R t + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e)) :=
                    mul_le_mul_of_nonneg_left hrefS (by positivity)
            have hstep3 : C3 * T^e * (C1 * T^e * (kDS A R t + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e))
                ≤ C3 * T^e * (C1 * T^e * (sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                    + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
              linarith [hSA]
            have hX : T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4) ≤ G := hXG
            have hEE : T^e * T^e ≤ T^ε := by
              rw [← Real.rpow_add hT0]
              exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h2e])
            have hEEE : T^e * (T^e * T^e) ≤ T^ε := by
              rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
              exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h3e])
            have hXY : (R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) ≤ 13*G := by linarith [hR2G, hXG]
            have hexp : C3 * T^e * (C1 * T^e * (sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                  + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e))
                = C3*C1*(sqc*(T^e*(T^e*T^e))*((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                  + (T^e*T^e)*((R:ℝ)^2) + 2*((m:ℝ)*(R:ℝ))*(T^e*(T^e*T^e))) := by ring
            have hstep4 : kDS N R t ≤ C3 * T^e * (C1 * T^e * (sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e)) := le_trans hstep1 (le_trans hstep2 hstep3)
            have e1 : sqc*(T^e*(T^e*T^e))*((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                ≤ sqc*T^ε*(13*G) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hEEE hsqcnn) hXY (by positivity) (by positivity)
            have e2 : (T^e*T^e)*((R:ℝ)^2) ≤ T^ε*G :=
              mul_le_mul hEE hR2G (by positivity) (by positivity)
            have e3 : 2*((m:ℝ)*(R:ℝ))*(T^e*(T^e*T^e))
                ≤ 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))*T^ε := by
              have hmR' : 2*((m:ℝ)*(R:ℝ))
                  ≤ 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) := by linarith [hmR]
              exact mul_le_mul hmR' hEEE (by positivity) (by positivity)
            calc kDS N R t ≤ C3 * T^e * (C1 * T^e * (sqc * T^e * ((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                  + (R:ℝ)^2 + 2*(m:ℝ)*(R:ℝ)*T^e)) := hstep4
              _ = C3*C1*(sqc*(T^e*(T^e*T^e))*((R:ℝ)^2 + 12*(T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)))
                  + (T^e*T^e)*((R:ℝ)^2) + 2*((m:ℝ)*(R:ℝ))*(T^e*(T^e*T^e))) := hexp
              _ ≤ C3*C1*(sqc*T^ε*(13*G) + T^ε*G
                  + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))*T^ε) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  linarith [e1, e2, e3]
              _ ≤ C3*C1*T^ε*((13*sqc+9)*G) := by
                  have hthis : 13*sqc*G + G + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))
                      ≤ (13*sqc+9)*G := by linarith [hNRG, hXG, hRG]
                  calc C3*C1*(sqc*T^ε*(13*G) + T^ε*G
                        + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))*T^ε)
                      = C3*C1*(T^ε*(13*sqc*G + G + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)))) := by ring
                    _ = C3*C1*T^ε*(13*sqc*G + G + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))) := by ring
                    _ ≤ C3*C1*T^ε*((13*sqc+9)*G) := mul_le_mul_of_nonneg_left hthis (by positivity)
              _ ≤ 100*C3*C1*(sqc+1)*T^ε*G := by
                  have h1 : (13*sqc+9)*G ≤ (100*(sqc+1))*G :=
                    mul_le_mul_of_nonneg_right (by linarith [hsqcnn]) hGnn
                  calc C3*C1*T^ε*((13*sqc+9)*G) ≤ C3*C1*T^ε*((100*(sqc+1))*G) :=
                        mul_le_mul_of_nonneg_left h1 (by positivity)
                    _ = 100*C3*C1*(sqc+1)*T^ε*G := by ring
              _ ≤ Cu*T^ε*G := mul_Cu_le hDu' hTepos hGnn
          · rw [not_le] at hmb
            by_cases hmc : 300*T^2 ≤ (m:ℝ)^3
            · -- CASE1 at m
              have hmc' : 256*T^2 ≤ (m:ℝ)^3 := by linarith [hmc]
              have h := hCASE1 m hm1 T hT hm_le_T hmc' R t hIcc hsep
              have hinc : kDS N R t ≤ C3 * (m:ℝ)^e * kDS m R t := by
                rw [kDS_eq_kDSw N T R t hIcc, kDS_eq_kDSw m T R t hIcc]
                have h0 := hINCR N m hN (by rw [hm]; exact le_max_left _ _) T hT 1 (le_refl 1)
                  (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
                simpa only [kDSw, one_mul, mul_one, one_pow] using h0
              have hEE : T^e * T^e ≤ T^ε := by
                rw [← Real.rpow_add hT0]
                exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h2e])
              have hme : (m:ℝ)^e ≤ T^e := Real.rpow_le_rpow (by positivity) hm_le_T hepos.le
              have hb : G + 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ) ≤ 5*G := by
                linarith [hNRG, hXG, hRG]
              calc kDS N R t ≤ C3*(m:ℝ)^e*kDS m R t := hinc
                _ ≤ C3*T^e*(C4*T^e*((R:ℝ)^2 + (m:ℝ)*(R:ℝ))) := by
                    have h1 : C3*(m:ℝ)^e ≤ C3*T^e := mul_le_mul_of_nonneg_left hme hC3nn
                    calc C3*(m:ℝ)^e*kDS m R t ≤ C3*T^e*kDS m R t :=
                          mul_le_mul_of_nonneg_right h1 (kDS_nonneg m R t)
                      _ ≤ C3*T^e*(C4*T^e*((R:ℝ)^2 + (m:ℝ)*(R:ℝ))) :=
                          mul_le_mul_of_nonneg_left h (by positivity)
                _ = C3*C4*(T^e*T^e)*((R:ℝ)^2 + (m:ℝ)*(R:ℝ)) := by ring
                _ ≤ C3*C4*T^ε*(G + 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) := by
                    have h1 : (T^e*T^e)*((R:ℝ)^2 + (m:ℝ)*(R:ℝ))
                        ≤ T^ε*(G + 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) :=
                      mul_le_mul hEE (by linarith [hR2G, hmR]) (by positivity) (by positivity)
                    calc C3*C4*(T^e*T^e)*((R:ℝ)^2 + (m:ℝ)*(R:ℝ))
                        = C3*C4*((T^e*T^e)*((R:ℝ)^2 + (m:ℝ)*(R:ℝ))) := by ring
                      _ ≤ C3*C4*(T^ε*(G + 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))) :=
                          mul_le_mul_of_nonneg_left h1 (by positivity)
                      _ = C3*C4*T^ε*(G + 2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) := by ring
                _ ≤ C3*C4*T^ε*(5*G) := mul_le_mul_of_nonneg_left hb (by positivity)
                _ = 5*C3*C4*T^ε*G := by ring
                _ ≤ Cu*T^ε*G := mul_Cu_le hEu' hTepos hGnn
            · -- gap: 64T^2 < m^3 < 300T^2, increase to 2m
              rw [not_le] at hmc
              have h2m1 : 1 ≤ 2*m := by omega
              have hm_ub : (m:ℝ) < (300*T^2)^((1:ℝ)/3) := by
                have h1 : ((m:ℝ)^3)^((1:ℝ)/3) < (300*T^2)^((1:ℝ)/3) :=
                  Real.rpow_lt_rpow (by positivity) hmc (by norm_num)
                have h2 : ((m:ℝ)^3)^((1:ℝ)/3) = (m:ℝ) := by
                  rw [← Real.rpow_natCast (m:ℝ) 3, ← Real.rpow_mul (by positivity)]
                  norm_num
                linarith [h1, h2]
              have h300 : (300:ℝ)^((1:ℝ)/3) ≤ 7 := by
                have h1 : ((300:ℝ)^((1:ℝ)/3))^3 ≤ (7:ℝ)^3 := by
                  rw [← Real.rpow_natCast ((300:ℝ)^((1:ℝ)/3)) 3,
                    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 300)]
                  rw [show ((1:ℝ)/3 * ((3:ℕ):ℝ)) = 1 by norm_num, Real.rpow_one]
                  norm_num
                exact le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ) ≠ 0) (by norm_num : (0:ℝ) ≤ 7) h1
              have h3 : (300*T^2)^((1:ℝ)/3) = (300:ℝ)^((1:ℝ)/3) * T^((2:ℝ)/3) := by
                rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 300) (by positivity)]
                congr 1
                rw [← Real.rpow_natCast T 2, ← Real.rpow_mul hT0.le]
                norm_num
              have hm_ub2 : (m:ℝ) ≤ 7*T^((2:ℝ)/3) := by
                rw [h3] at hm_ub
                nlinarith [hm_ub, h300, Real.rpow_nonneg hT0.le ((2:ℝ)/3)]
              have h2m_leT : ((2*m : ℕ) : ℝ) ≤ T := by
                have h14 : 14*T^((2:ℝ)/3) ≤ T := by
                  have h15 := mul_le_mul_of_nonneg_left hT23le (by norm_num : (0:ℝ) ≤ 14)
                  linarith [h15, hT0]
                push_cast
                linarith [hm_ub2, h14]
              have h2m256 : 256*T^2 ≤ (((2*m : ℕ)) : ℝ)^3 := by
                have h1 : (((2*m : ℕ)) : ℝ)^3 = 8*(m:ℝ)^3 := by push_cast; ring
                rw [h1]
                nlinarith [hmb, hT0]
              have hinc1 : kDS N R t ≤ C3 * (m:ℝ)^e * kDS m R t := by
                rw [kDS_eq_kDSw N T R t hIcc, kDS_eq_kDSw m T R t hIcc]
                have h0 := hINCR N m hN (by rw [hm]; exact le_max_left _ _) T hT 1 (le_refl 1)
                  (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
                simpa only [kDSw, one_mul, mul_one, one_pow] using h0
              have hinc2 : kDS m R t ≤ C3 * (((2*m : ℕ)) : ℝ)^e * kDS (2*m) R t := by
                rw [kDS_eq_kDSw m T R t hIcc, kDS_eq_kDSw (2*m) T R t hIcc]
                have h0 := hINCR m (2*m) hm1 (by omega) T hT 1 (le_refl 1)
                  (fun _ => (1:ℂ)) (fun n => by simp) R t hsep
                simpa only [kDSw, one_mul, mul_one, one_pow] using h0
              have hcase := hCASE1 (2*m) h2m1 T hT h2m_leT h2m256 R t hIcc hsep
              have hEEE : T^e * (T^e * T^e) ≤ T^ε := by
                rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
                exact Real.rpow_le_rpow_of_exponent_le hT (by linarith [h3e])
              have hme : (m:ℝ)^e ≤ T^e := Real.rpow_le_rpow (by positivity) hm_le_T hepos.le
              have h2me : (((2*m : ℕ)) : ℝ)^e ≤ T^e := Real.rpow_le_rpow (by positivity) h2m_leT hepos.le
              have h2mR : (((2*m : ℕ)) : ℝ)*(R:ℝ)
                  ≤ 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) := by
                push_cast
                nlinarith [hmR]
              have hb : (R:ℝ)^2 + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)) ≤ 9*G := by
                linarith [hR2G, hNRG, hXG, hRG]
              calc kDS N R t ≤ C3*(m:ℝ)^e*kDS m R t := hinc1
                _ ≤ C3*(m:ℝ)^e*(C3*(((2*m : ℕ)) : ℝ)^e*kDS (2*m) R t) :=
                    mul_le_mul_of_nonneg_left hinc2 (by positivity)
                _ ≤ C3*(m:ℝ)^e*(C3*(((2*m : ℕ)) : ℝ)^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)))) := by
                    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcase (by positivity)) (by positivity)
                _ ≤ C3^2*C4*(T^e*(T^e*T^e))*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)) := by
                    have hZ : (0:ℝ) ≤ C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)) := by positivity
                    have s1 : C3*(m:ℝ)^e*(C3*(((2*m : ℕ)) : ℝ)^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))))
                        ≤ C3*T^e*(C3*(((2*m : ℕ)) : ℝ)^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)))) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hme hC3nn) (by positivity)
                    have s2 : C3*T^e*(C3*(((2*m : ℕ)) : ℝ)^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))))
                        ≤ C3*T^e*(C3*T^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)))) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2me hC3nn) (by positivity))
                        (by positivity)
                    have h3 : C3*T^e*(C3*T^e*(C4*T^e*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))))
                        = C3^2*C4*(T^e*(T^e*T^e))*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ)) := by ring
                    linarith [s1, s2, h3.le, h3.symm.le]
                _ ≤ C3^2*C4*T^ε*((R:ℝ)^2 + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))) := by
                    have h1 : (T^e*(T^e*T^e))*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))
                        ≤ T^ε*((R:ℝ)^2 + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))) :=
                      mul_le_mul hEEE (by linarith [hR2G, h2mR]) (by positivity) (by positivity)
                    calc C3^2*C4*(T^e*(T^e*T^e))*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))
                        = C3^2*C4*((T^e*(T^e*T^e))*((R:ℝ)^2 + (((2*m : ℕ)) : ℝ)*(R:ℝ))) := by ring
                      _ ≤ C3^2*C4*(T^ε*((R:ℝ)^2 + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ)))) :=
                          mul_le_mul_of_nonneg_left h1 (by positivity)
                      _ = C3^2*C4*T^ε*((R:ℝ)^2 + 2*(2*(N:ℝ)*(R:ℝ) + (T^((1:ℝ)/2) * (R:ℝ)^((5:ℝ)/4)) + (R:ℝ))) := by ring
                _ ≤ C3^2*C4*T^ε*(9*G) := by
                    refine mul_le_mul_of_nonneg_left hb (by positivity)
                _ = 9*C3^2*C4*T^ε*G := by ring
                _ ≤ Cu*T^ε*G := mul_Cu_le hFu' hTepos hGnn
  have hmaj : kDSw N T c R t ≤ C5 * B^2 * kDS N R t := by
    have h := hMAJ N hN T hT0 B hB c hc R t hsep
    rw [kDS_eq_kDSw N T R t hIcc]
    simpa only [kDSw, one_mul] using h
  have hB2 : (0:ℝ) ≤ B^2 := by positivity
  calc kDSw N T c R t ≤ C5 * B^2 * kDS N R t := hmaj
    _ ≤ C5 * B^2 * (Cu * T^ε * G) := mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = (C5 * Cu) * (B^2 * T^ε * G) := by ring
    _ ≤ (C5 * Cu + 1) * (B^2 * T^ε * G) := by
        refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (C5 * Cu + 1) * B^2 * T^ε * G := by ring

end
end Commons.NumberTheory.DirichletPolynomial
