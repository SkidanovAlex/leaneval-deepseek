import Submission.S3g
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold
import Submission.Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge

/-!
# The hypothesis `(R)` of the companion "Asymptotic sieve for primes" for `X² + Y⁴`

The companion paper (J. Friedlander, H. Iwaniec, *Asymptotic sieve for primes*,
Ann. of Math. **148** (1998) 1041–1065) proves its main theorem under two
hypotheses on the sequence `a = (a_n)` and its error terms
`r_d(t) = A_d(t) − g(d)A(t)`:

* `(R)  ∑_{d ≤ D} μ²(d) |r_d(t)| ≤ A(x)(log x)^{-22}` for all `t ≤ x`,
* `(B)` a bilinear-form estimate,

for a suitable `D = D(x)` with `x^{2/3} < D(x) < x`.

This file verifies `(R)` for the Friedlander–Iwaniec sequence
`a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}`, i.e. `A(t) = #{a² + c⁴ ≤ t}` and the density
`g(d) = N(d)/d²`, `N(d) = #{x ∈ (ℤ/d)² : x₁² + x₂⁴ ≡ 0}`.

The choice is `D = ⌊x^{11/16}⌋`, which satisfies `x^{2/3} < D < x`.  The proof uses
Proposition 3.5 (`Submission.prop35_unconditional`), i.e. the paper's Lemma 3.1
`(3.3)` in the range `D ≤ t^{3/4}`, together with elementary estimates on
`∑_{d ≤ D} A_d(t)` and `∑_{d ≤ D} g(d)` for the complementary range.
-/

namespace Submission

open Finset Filter

/-- The logarithmic exponent in the hypothesis `(R)`.  The paper takes `2^22`; any sufficiently
large value works (the bound we prove decays like a fixed power of `x`), and we take `2^50` so
that it dominates `3·2^48 + 12`, as required by the Hölder step `Rprime_of_R_and_23'` of
`Submission.ASP.S2b`. -/
def LamR : ℝ := (2 : ℝ) ^ 50


/-- The modulus cut-off used for `(R)`: `D(x) = ⌊x^{11/16}⌋`.  This lies between
`x^{2/3}` and `x^{3/4}` (indeed `2/3 < 11/16 < 3/4`), as required by the companion
paper's `(R1)`. -/
noncomputable def Rcut (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊

/-- The left hand side of `(R)`: `∑_{d ≤ D} μ²(d) |A_d(t) − g(d)A(t)|`. -/
noncomputable def Rsum (x t : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d),
    |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)|

/-! ## Auxiliary estimates for `A` -/

lemma Aseq_mono : Monotone Aseq := by
  intro m n hmn
  unfold Aseq
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Nat.zero_le _

/-- `A(t) ≤ C t^{3/4}`. -/
lemma Aseq_le_const_mul_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t → (Aseq t : ℝ) ≤ C * (t : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨C, hC, h⟩ := Aseq_asymptotic
  have hκpos : 0 < ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    lt_of_lt_of_le (by norm_num) Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  refine ⟨4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) + C, by positivity, fun t ht => ?_⟩
  have h1 := (abs_le.mp (h t ht)).2
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have h2 : Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow]
    calc (t : ℝ) ^ ((1 : ℝ) / 2) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
      _ = (t : ℝ) ^ ((3 : ℝ) / 4) := rfl
  nlinarith [h1, h2, Real.rpow_nonneg ht0 ((3:ℝ)/4)]

/-- `A(x) ≫ x^{3/4}` for large `x`. -/
lemma exists_const_mul_rpow_le_Aseq :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x → c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Aseq x : ℝ) := by
  obtain ⟨C, hC, h⟩ := Aseq_asymptotic
  set κ : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hκdef
  have hκ : (87215 : ℝ) / 100000 ≤ κ := Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  set T : ℝ := C / (2 * ((87215 : ℝ) / 100000)) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨2 * (87215 / 100000), by norm_num, ⌈T ^ 4⌉₊ + 1, fun x hx => ?_⟩
  have hxT : T ^ 4 ≤ (x : ℝ) := by
    have h2 : T ^ 4 ≤ ((⌈T ^ 4⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((⌈T ^ 4⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : ⌈T ^ 4⌉₊ ≤ x)
    linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have hx1' : 1 ≤ x := by omega
    exact_mod_cast hx1'
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hrpow : T ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (T ^ 4) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hxT (by norm_num)
    rwa [← Real.rpow_natCast T 4, ← Real.rpow_mul (le_of_lt hTpos), show ((4 : ℕ) : ℝ) * (1/4) = 1 by norm_num,
      Real.rpow_one] at h1
  have hCsq : C ≤ 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have := mul_le_mul_of_nonneg_left hrpow (by norm_num : (0:ℝ) ≤ 2 * ((87215:ℝ)/100000))
    rw [hTdef] at this
    field_simp at this
    linarith
  have hsplit : (x : ℝ) ^ ((3 : ℝ) / 4) = (x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hCsqrt : C * Real.sqrt (x : ℝ) ≤ 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow]
    calc C * (x : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((1 : ℝ) / 4)) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hCsq (Real.rpow_nonneg hx0 _)
      _ = 2 * ((87215 : ℝ) / 100000) * ((x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ = 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by rw [← hsplit]
  have h1 := (abs_le.mp (h x (by omega))).1
  have hκ' : 2 * ((87215 : ℝ) / 100000) ≤ 4 * κ - 2 * ((87215 : ℝ) / 100000) := by linarith
  have hmain : 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * κ - 2 * ((87215 : ℝ) / 100000)) * (x : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right hκ' (Real.rpow_nonneg hx0 _)
  have h1' : 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - C * Real.sqrt (x : ℝ) ≤ (Aseq x : ℝ) := by
    linarith [h1]
  refine le_trans ?_ h1'
  calc 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * κ - 2 * ((87215 : ℝ) / 100000)) * (x : ℝ) ^ ((3 : ℝ) / 4) := hmain
    _ = 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - 2 * ((87215 : ℝ) / 100000) * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
    _ ≤ 4 * κ * (x : ℝ) ^ ((3 : ℝ) / 4) - C * Real.sqrt (x : ℝ) := by linarith [hCsqrt]


/-! ## Elementary bounds entering the two cases -/

/-- `an 0 = 1`: the only lattice point with `a² + c⁴ = 0` is the origin. -/
lemma an_zero : an 0 = 1 := by
  unfold an
  rw [Set.ncard_eq_one]
  refine ⟨(0, 0), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [Nat.cast_zero] at hx
    have h1 : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg x.1
    have h2 : (0 : ℤ) ≤ x.2 ^ 4 := by positivity
    have hx1 : x.1 ^ 2 = 0 := by linarith
    have hx2 : x.2 ^ 4 = 0 := by linarith
    exact Prod.ext (sq_eq_zero_iff.mp hx1) ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hx2)
  · rintro rfl
    norm_num

/-- A sum over the squarefree `d ≤ D` of a nonnegative summand is at most the
`cubeSum` over the cubefree moduli `d = d₁ d₂² ≤ D` (the pairs `(d, 1)`). -/
lemma sqfree_sum_le_cubeSum (D : ℕ) (hD : 1 ≤ D) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), F d)
      ≤ cubeSum D (fun d₁ d₂ => F (d₁ * d₂ ^ 2)) := by
  have hL : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), F d)
      = ∑ d ∈ Finset.Icc 1 D, if Squarefree d then F d else 0 := by
    rw [Finset.sum_filter]
  rw [hL, cubeSum]
  refine Finset.sum_le_sum fun d₁ hd₁ => ?_
  have h1mem : 1 ∈ Finset.Icc 1 (Nat.sqrt D) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.le_sqrt'.mpr (by simpa using hD)⟩
  by_cases hs : Squarefree d₁
  · have hnot4 : ¬ 4 ∣ d₁ * 1 ^ 2 := by
      intro h
      have h4 : (2 : ℕ) * 2 ∣ d₁ := by simpa using h
      exact absurd (hs 2 h4) (by norm_num)
    have hcond : cubeCond D d₁ 1 :=
      ⟨hs, squarefree_one, Nat.coprime_one_right d₁, hnot4,
        by simpa using (Finset.mem_Icc.mp hd₁).2⟩
    rw [if_pos hs]
    have hterm : (if cubeCond D d₁ 1 then F (d₁ * 1 ^ 2) else 0) = F d₁ := by
      rw [if_pos hcond]; simp
    rw [← hterm]
    refine Finset.single_le_sum (f := fun d₂ => if cubeCond D d₁ d₂ then F (d₁ * d₂ ^ 2) else 0)
      (fun d₂ _ => ?_) h1mem
    by_cases h : cubeCond D d₁ d₂
    · rw [if_pos h]; exact hF _
    · rw [if_neg h]
  · rw [if_neg hs]
    exact Finset.sum_nonneg fun d₂ _ => by
      by_cases h : cubeCond D d₁ d₂
      · rw [if_pos h]; exact hF _
      · rw [if_neg h]

/-- `∑_{d ∈ Icc 1 D} A_d(t) ≤ D + C t^{1/100} A(t)`: the lattice points `a² + c⁴ ≤ t`
weighted by the number of their divisors `d ≤ D`. -/
lemma sum_Ad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ,
      (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
        ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
  obtain ⟨C, hC, hb⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 100 : ℝ)
    (by norm_num)
  refine ⟨C, hC, fun D t => ?_⟩
  have hswap : (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
      = ∑ n ∈ Finset.range (t + 1),
          (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D, (Ad d t : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (t + 1),
            (if d ∣ n then (an n : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold Ad
      rw [Finset.sum_filter]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hswap]
  have hsplit : ∀ n ∈ Finset.range (t + 1),
      (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
        ≤ (an n : ℝ) * (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hcard : ((Finset.Icc 1 D).filter (fun d => d ∣ 0)).card = D := by
        rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d), Nat.card_Icc]
        simp
      rw [if_pos rfl, hcard]
    · have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ Nat.divisors n := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
      have hcard : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ ((Nat.divisors n).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have htau : ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 100) := hb n
      have hnt : (n : ℝ) ≤ (t : ℝ) := by
        have := Finset.mem_range.mp hn
        exact_mod_cast (by omega : n ≤ t)
      have hlt : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (t : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnt (by norm_num)
      have hfin : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) :=
        le_trans hcard (le_trans htau (mul_le_mul_of_nonneg_left hlt hC.le))
      rw [if_neg (by omega : n ≠ 0)]
      exact mul_le_mul_of_nonneg_left hfin (by positivity)
  have hshift : (∑ n ∈ Finset.range t, (an (n + 1) : ℝ)) ≤ (Aseq t : ℝ) := by
    rw [Aseq, Nat.cast_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    have hnn : (0 : ℝ) ≤ (an 0 : ℝ) := by positivity
    linarith
  calc ∑ n ∈ Finset.range (t + 1),
        (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
      ≤ ∑ n ∈ Finset.range (t + 1),
          (an n : ℝ) * (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) :=
        Finset.sum_le_sum hsplit
    _ = (an 0 : ℝ) * (D : ℝ) + ∑ n ∈ Finset.range t,
          (an (n + 1) : ℝ) * (C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
        rw [Finset.sum_range_succ']
        have h0 : (an 0 : ℝ) * (if 0 = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100))
            = (an 0 : ℝ) * (D : ℝ) := by rw [if_pos rfl]
        rw [h0, add_comm]
        refine congrArg (fun z => (an 0 : ℝ) * (D : ℝ) + z) ?_
        exact Finset.sum_congr rfl fun n _ => by rw [if_neg (by omega : ¬ n + 1 = 0)]
    _ = (an 0 : ℝ) * (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) *
          (∑ n ∈ Finset.range t, (an (n + 1) : ℝ)) := by
        rw [Finset.mul_sum]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun n _ => by ring)
    _ ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
        rw [an_zero]
        push_cast
        have h1 : (0 : ℝ) ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) := by positivity
        nlinarith [hshift, h1]

/-- `∑_{d ≤ D, d squarefree} g(d) ≪ (log D)^A`: the local-density summatory bound,
through the cubefree `cubeSum` bound of §3. -/
lemma sum_gdens_sqfree_le :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ D : ℕ, 2 ≤ D →
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
        ≤ C * (Real.log D) ^ A := by
  obtain ⟨C, A, hC, h⟩ := cubeSum_gdens_le
  have hCpos : 0 < C * max 1 ((Real.log 2) ^ (A - max A 0)) :=
    mul_pos hC (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨C * max 1 ((Real.log 2) ^ (A - max A 0)), max A 0, hCpos, le_max_right _ _, fun D hD => ?_⟩
  have hA' : A ≤ max A 0 := le_max_left _ _
  have hgn : ∀ d : ℕ, 0 ≤ (gdens d : ℝ) := fun d => Rat.cast_nonneg.mpr (gdens_nonneg d)
  have hsq : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
      ≤ cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := by
    have h1 := sqfree_sum_le_cubeSum D (by omega) (fun d => |(gdens d : ℝ)|) (fun d => abs_nonneg _)
    rwa [Finset.sum_congr rfl (fun d _ => abs_of_nonneg (hgn d))] at h1
  have hbound := rpow_log_le_const_mul (B := A) (A := max A 0) hA' hD
  have hlogD0 : 0 ≤ (Real.log D) ^ (max A 0) :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))) _
  have hmul : (Real.log 2) ^ (A - max A 0) * (Real.log D) ^ (max A 0)
      ≤ max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0) :=
    mul_le_mul_of_nonneg_right (le_max_right 1 _) hlogD0
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d), (gdens d : ℝ))
      ≤ cubeSum D (fun d₁ d₂ => |(gdens (d₁ * d₂ ^ 2) : ℝ)|) := hsq
    _ ≤ C * (Real.log D) ^ A := h D hD
    _ ≤ C * ((Real.log 2) ^ (A - max A 0) * (Real.log D) ^ (max A 0)) :=
        mul_le_mul_of_nonneg_left hbound hC.le
    _ ≤ C * (max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0)) :=
        mul_le_mul_of_nonneg_left hmul hC.le
    _ = C * max 1 ((Real.log 2) ^ (A - max A 0)) * (Real.log D) ^ (max A 0) := by ring

lemma poly_tail_aux {K α β cA x : ℝ} (hx : 0 < x) (hu : 0 < Real.log x) (hcA : 0 < cA)
    (lam : ℝ) (h : (K / cA) * (Real.log x) ^ (β + lam) ≤ x ^ ((3:ℝ)/4 - α)) :
    K * x ^ α * (Real.log x) ^ β ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-lam) := by
  have hu0 : 0 ≤ Real.log x := le_of_lt hu
  have hx0 : 0 ≤ x := le_of_lt hx
  -- step A
  have hA : (K / cA) * (Real.log x) ^ (β + lam) * x ^ (α - (3:ℝ)/4) ≤ 1 := by
    have hp : x ^ ((3:ℝ)/4 - α) * x ^ (α - (3:ℝ)/4) = 1 := by
      rw [← Real.rpow_add hx, show (3:ℝ)/4 - α + (α - 3/4) = 0 by ring, Real.rpow_zero]
    rw [← hp]
    exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx0 _)
  -- step B : drop the division by cA
  have hB : K * (Real.log x) ^ (β + lam) * x ^ (α - (3:ℝ)/4) ≤ cA := by
    have heq : (K / cA) * (Real.log x) ^ (β + lam) * x ^ (α - (3:ℝ)/4)
        = (K * (Real.log x) ^ (β + lam) * x ^ (α - (3:ℝ)/4)) / cA := by ring
    rw [heq] at hA
    have := (div_le_iff₀ hcA).mp hA
    simpa using this
  -- step C : multiply by x^(3/4-α)
  have hC : K * (Real.log x) ^ (β + lam) ≤ cA * x ^ ((3:ℝ)/4 - α) := by
    have hp : x ^ (α - (3:ℝ)/4) * x ^ ((3:ℝ)/4 - α) = 1 := by
      rw [← Real.rpow_add hx, show α - 3/4 + ((3:ℝ)/4 - α) = 0 by ring, Real.rpow_zero]
    have h2 : K * (Real.log x) ^ (β + lam) * x ^ (α - (3:ℝ)/4) * x ^ ((3:ℝ)/4 - α) ≤ cA * x ^ ((3:ℝ)/4 - α) :=
      mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hx0 _)
    rwa [mul_assoc, hp, mul_one] at h2
  -- step D : multiply by x^α
  have hD : K * (Real.log x) ^ (β + lam) * x ^ α ≤ cA * x ^ ((3:ℝ)/4) := by
    have hp : x ^ ((3:ℝ)/4 - α) * x ^ α = x ^ ((3:ℝ)/4) := by
      rw [← Real.rpow_add hx, show (3:ℝ)/4 - α + α = (3:ℝ)/4 by ring]
    have h2 := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx0 α)
    calc K * (Real.log x) ^ (β + lam) * x ^ α
        = (K * (Real.log x) ^ (β + lam)) * x ^ α := by ring
      _ ≤ (cA * x ^ ((3:ℝ)/4 - α)) * x ^ α := h2
      _ = cA * (x ^ ((3:ℝ)/4 - α) * x ^ α) := by ring
      _ = cA * x ^ ((3:ℝ)/4) := by rw [hp]
  -- step E : divide by u^22
  have hE : K * x ^ α * (Real.log x) ^ (β + lam) * (Real.log x) ^ (-lam)
      ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-lam) :=
    mul_le_mul_of_nonneg_right (by linarith [hD, mul_comm (K * (Real.log x) ^ (β + lam)) (x ^ α)]
      : K * x ^ α * (Real.log x) ^ (β + lam) ≤ cA * x ^ ((3:ℝ)/4))
      (Real.rpow_nonneg hu0 _)
  have hsplit : (Real.log x) ^ (β + lam) * (Real.log x) ^ (-lam) = (Real.log x) ^ β := by
    rw [← Real.rpow_add hu, show β + lam + (-lam) = β by ring]
  calc K * x ^ α * (Real.log x) ^ β
      = K * x ^ α * ((Real.log x) ^ (β + lam) * (Real.log x) ^ (-lam)) := by rw [hsplit]
    _ = K * x ^ α * (Real.log x) ^ (β + lam) * (Real.log x) ^ (-lam) := by ring
    _ ≤ cA * x ^ ((3:ℝ)/4) * (Real.log x) ^ (-lam) := hE

lemma poly_tail_le (K α β cA lam : ℝ) (hK : 0 < K) (hα : α < 3/4) (hcA : 0 < cA)
    (hlam : 0 < lam) :
    ∃ X : ℕ, 5 ≤ X ∧ ∀ x : ℕ, X ≤ x →
      K * (x : ℝ) ^ α * (Real.log x) ^ β
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
  obtain ⟨X₁, -, hX₁⟩ :=
    Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold (K := K / cA) (by positivity)
      (n := ⌈β + lam⌉₊) (r := (3:ℝ)/4 - α) (by linarith)
  refine ⟨max 5 ⌈X₁⌉₊ + 1, by omega, fun x hx => ?_⟩
  have hx5 : 5 ≤ x := by omega
  have hxX : X₁ ≤ (x : ℝ) := by
    have h1 : ((max 5 ⌈X₁⌉₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h1
    have h2 : ((⌈X₁⌉₊ : ℕ) : ℝ) ≤ ((max 5 ⌈X₁⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 5 ⌈X₁⌉₊
    push_cast at h2
    have h3 : X₁ ≤ ((⌈X₁⌉₊ : ℕ) : ℝ) := Nat.le_ceil X₁
    linarith
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9, hxR]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hmain := hX₁ (x : ℝ) hxX
  refine poly_tail_aux hxpos hlogpos hcA lam ?_
  refine le_trans ?_ hmain
  have hβ : (Real.log x) ^ (β + lam) ≤ (Real.log x) ^ (⌈β + lam⌉₊ : ℕ) := by
    simpa [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil (β + lam))
  simpa using mul_le_mul_of_nonneg_left hβ (by positivity : (0:ℝ) ≤ K / cA)

/-- `⌊x^{11/16}⌋ ≥ 2` for `x ≥ 5`. -/
lemma two_le_Rcut {x : ℕ} (hx : 5 ≤ x) : 2 ≤ Rcut x := by
  unfold Rcut
  refine Nat.le_floor ?_
  have hx5 : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have h4 : (2 : ℝ) ^ 2 ≤ (x : ℝ) := by nlinarith
  have hs : (2 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    calc (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt h4
  have hsplit : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  rw [Real.sqrt_eq_rpow] at hs
  linarith

/-- `A_d(t) ≤ A(t)`. -/
lemma Ad_le_Aseq (d t : ℕ) : Ad d t ≤ Aseq t := by
  unfold Ad Aseq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => Nat.zero_le _)

/-- `Rcut x ≤ x^{11/16}`. -/
lemma Rcut_le_rpow (x : ℕ) : (Rcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

/-- `Rcut x ≤ x`. -/
lemma Rcut_le_self (x : ℕ) : Rcut x ≤ x := by
  rcases Nat.eq_zero_or_pos x with h0 | hp
  · subst h0
    unfold Rcut
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num : ((11 : ℝ) / 16) ≠ 0)]
    simp
  · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hp
    have hle : (x : ℝ) ^ ((11 : ℝ) / 16) ≤ (x : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : ((11 : ℝ) / 16) ≤ 1)
      rwa [Real.rpow_one] at h
    calc Rcut x = ⌊(x : ℝ) ^ ((11 : ℝ) / 16)⌋₊ := rfl
      _ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono hle
      _ = x := Nat.floor_natCast x

/-- **(R) of the companion paper for the Friedlander–Iwaniec sequence.**
With the cut-off `D = ⌊x^{11/16}⌋` (which satisfies `x^{2/3} < D(x) < x`) one has
`∑_{d ≤ D} μ²(d) |A_d(t) − g(d)A(t)| ≤ A(x) (log x)^{-22}` for every `t ≤ x`. -/
theorem X2Y4_R_generic (lam : ℝ) (hlam : 0 < lam) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      Rsum x t ≤ (Aseq x : ℝ) * (Real.log x) ^ (-lam) := by
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨CA, hCA, hAup⟩ := Aseq_le_const_mul_rpow
  obtain ⟨CAd, hCAd, hAd⟩ := sum_Ad_le
  obtain ⟨Cg, Ag, hCg, hAg, hGg⟩ := sum_gdens_sqfree_le
  obtain ⟨C35, A35, hC35, hA35, h35⟩ := prop35_unconditional
  obtain ⟨Y1, hY1x, hY1⟩ :=
    poly_tail_le C35 ((47 : ℝ) / 64 + 1 / 100) 0 (cA / 2) lam hC35 (by norm_num) (by positivity)
    hlam
  obtain ⟨Y2, hY2x, hY2⟩ :=
    poly_tail_le (C35 * 2 ^ A35) (1 / 2) A35 (cA / 2) lam (by positivity) (by norm_num) (by positivity)
    hlam
  obtain ⟨Y3, hY3x, hY3⟩ :=
    poly_tail_le 1 ((11 : ℝ) / 16) 0 (cA / 3) lam (by norm_num) (by norm_num) (by positivity)
    hlam
  obtain ⟨Y4, hY4x, hY4⟩ :=
    poly_tail_le (CAd * CA) ((11 : ℝ) / 16 + 1 / 100) 0 (cA / 3) lam (by positivity) (by norm_num)
    (by positivity) hlam
  obtain ⟨Y5, hY5x, hY5⟩ :=
    poly_tail_le (Cg * CA) ((11 : ℝ) / 16) Ag (cA / 3) lam (by positivity) (by norm_num) (by positivity)
    hlam
  refine ⟨max (max (max (max Y1 Y2) Y3) Y4) (max Y5 (max XA 5)) + 1, fun x hx t ht2 htx => ?_⟩
  have hxY1 : Y1 ≤ x := by omega
  have hxY2 : Y2 ≤ x := by omega
  have hxY3 : Y3 ≤ x := by omega
  have hxY4 : Y4 ≤ x := by omega
  have hxY5 : Y5 ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hx5 : 5 ≤ x := by omega
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx5
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have hlog0 : 0 ≤ Real.log x := le_of_lt hlogpos
  have hAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Aseq x : ℝ) := hAlow x hxXA
  have ht1 : 1 ≤ t := by omega
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have hlogz : (0 : ℝ) ≤ (Real.log x) ^ (-lam) := Real.rpow_nonneg hlog0 _
  by_cases hcase : Rcut x ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊
  · -- ## Case A : `D ≤ t^{3/4}`, so Proposition 3.5 applies directly
    have hD2 : 2 ≤ Rcut x := two_le_Rcut hx5
    have h35' := h35 (Rcut x) t hD2 ht2 hcase
    have hR1 : Rsum x t ≤ cubeSum (Rcut x)
        (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) :=
      sqfree_sum_le_cubeSum (Rcut x) (by omega)
        (fun d => |(Ad d t : ℝ) - (gdens d : ℝ) * (Aseq t : ℝ)|) (fun d => abs_nonneg _)
    have hDpow : (Rcut x : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((11 : ℝ) / 64) := by
      have h1 := Real.rpow_le_rpow (Nat.cast_nonneg (Rcut x)) (Rcut_le_rpow x)
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have h2 : ((x : ℝ) ^ ((11 : ℝ) / 16)) ^ ((1 : ℝ) / 4) = (x : ℝ) ^ ((11 : ℝ) / 64) := by
        rw [← Real.rpow_mul hx0]; norm_num
      rwa [h2] at h1
    have htpow : (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
    have hterm1 : (Rcut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        ≤ (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100) := by
      have h3 : (11 : ℝ) / 64 + ((9 : ℝ) / 16 + 1 / 100) = (47 : ℝ) / 64 + 1 / 100 := by norm_num
      refine le_trans (mul_le_mul hDpow htpow (Real.rpow_nonneg (Nat.cast_nonneg t) _)
        (Real.rpow_nonneg hx0 _)) ?_
      rw [← h3, ← Real.rpow_add hxpos]
    have hlogar0 : 0 ≤ Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have h1 : (0 : ℝ) ≤ (Rcut x : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (t : ℝ) := by positivity
      linarith
    have hlogbound : Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) ≤ 2 * Real.log x := by
      have h1 : (Rcut x : ℝ) + (t : ℝ) + 2 ≤ 3 * (x : ℝ) := by
        have h2 : (Rcut x : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Rcut_le_self x)
        linarith [h2, htle, hxR]
      have h2 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
        Real.log_mul (by norm_num) (ne_of_gt hxpos)
      have h3 : Real.log 3 ≤ Real.log x := by
        have h4 : (3 : ℝ) ≤ (x : ℝ) := by
          have : (3 : ℕ) ≤ x := by omega
          exact_mod_cast this
        exact Real.log_le_log (by norm_num) h4
      have h4 : (0 : ℝ) < (Rcut x : ℝ) + (t : ℝ) + 2 := by
        have h5 : (0 : ℝ) ≤ (Rcut x : ℝ) := by positivity
        have h6 : (0 : ℝ) ≤ (t : ℝ) := by positivity
        linarith
      calc Real.log ((Rcut x : ℝ) + (t : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
            Real.log_le_log h4 h1
        _ = Real.log 3 + Real.log x := h2
        _ ≤ 2 * Real.log x := by linarith
    have hterm2 : Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35
        ≤ 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by
      have hs : Real.sqrt (t : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have hl : (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35 ≤ (2 * Real.log x) ^ A35 :=
        Real.rpow_le_rpow hlogar0 hlogbound hA35
      have hl2 : (2 * Real.log x) ^ A35 = 2 ^ A35 * (Real.log x) ^ A35 :=
        Real.mul_rpow (by norm_num) hlog0
      have h2nn : (0 : ℝ) ≤ 2 ^ A35 * (Real.log x) ^ A35 :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hlog0 _)
      calc Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35
          ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (2 ^ A35 * (Real.log x) ^ A35) :=
            mul_le_mul hs (hl2 ▸ hl) (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx0 _)
        _ = 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35) := by ring
    have hY1' : C35 * (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
      have h := hY1 x hxY1
      simpa only [Real.rpow_zero, mul_one] using h
    have hY2'' : C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
        ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
      have h := hY2 x hxY2
      calc C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35))
          = C35 * 2 ^ A35 * (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35 := by ring
        _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := h
    calc Rsum x t
        ≤ cubeSum (Rcut x)
            (fun d₁ d₂ => |(Ad (d₁ * d₂ ^ 2) t : ℝ) - (gdens (d₁ * d₂ ^ 2) : ℝ) * (Aseq t : ℝ)|) := hR1
      _ ≤ C35 * ((Rcut x : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            + Real.sqrt (t : ℝ) * (Real.log ((Rcut x : ℝ) + (t : ℝ) + 2)) ^ A35) := h35'
      _ ≤ C35 * ((x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
            + 2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) :=
          mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC35.le
      _ = C35 * (x : ℝ) ^ ((47 : ℝ) / 64 + 1 / 100)
            + C35 * (2 ^ A35 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ A35)) := by ring
      _ ≤ cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam)
            + cA / 2 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) :=
          add_le_add hY1' hY2''
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ (-lam) := mul_le_mul_of_nonneg_right hAx hlogz
  · -- ## Case B : `D > t^{3/4}`, elementary bounds suffice
    have hD2 : 2 ≤ Rcut x := two_le_Rcut hx5
    have hlt : ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ < Rcut x := Nat.lt_of_not_le hcase
    have ht34 : (t : ℝ) ^ ((3 : ℝ) / 4) < (x : ℝ) ^ ((11 : ℝ) / 16) := by
      have h1 : (t : ℝ) ^ ((3 : ℝ) / 4) < ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 ≤ (Rcut x : ℝ) := by
        exact_mod_cast hlt
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (Rcut_le_rpow x)
    have hAt : (Aseq t : ℝ) ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) := by
      calc (Aseq t : ℝ) ≤ CA * (t : ℝ) ^ ((3 : ℝ) / 4) := hAup t ht1
        _ ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) :=
            mul_le_mul_of_nonneg_left (le_of_lt ht34) hCA.le
    have hgn : ∀ d : ℕ, 0 ≤ (gdens d : ℝ) := fun d => Rat.cast_nonneg.mpr (gdens_nonneg d)
    have hR1 : Rsum x t ≤ (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
        + (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ)) := by
      have h1 : Rsum x t ≤ ∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d),
          ((Ad d t : ℝ) + (Aseq t : ℝ) * (gdens d : ℝ)) := by
        unfold Rsum
        refine Finset.sum_le_sum fun d _ => ?_
        have hx0' : (0 : ℝ) ≤ (Ad d t : ℝ) := by positivity
        have hy0 : (0 : ℝ) ≤ (Aseq t : ℝ) * (gdens d : ℝ) := by
          have := hgn d; positivity
        have := abs_sub_le_iff.mp (le_refl (|(Ad d t : ℝ) - (Aseq t : ℝ) * (gdens d : ℝ)|))
        simp only [abs_sub_le_iff]
        constructor <;> linarith [abs_nonneg ((Ad d t : ℝ) - (Aseq t : ℝ) * (gdens d : ℝ))]
      refine le_trans h1 ?_
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      refine add_le_add ?_ le_rfl
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => by positivity
    have hpiece1 : (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
      have h1 := hAd (Rcut x) t
      have h3 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htle (by norm_num)
      have h4 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ) := by
        have h5 : (0 : ℝ) ≤ (Aseq t : ℝ) := by positivity
        have h6 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_left h3 hCAd.le
        exact mul_le_mul_of_nonneg_right h6 h5
      have h7 : (Rcut x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 16) := Rcut_le_rpow x
      linarith
    have hpiece2 : (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ))
        ≤ CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := by
      have h1 := hGg (Rcut x) hD2
      have hR1' : (1 : ℕ) ≤ Rcut x := by omega
      have hlogx1 : (1 : ℝ) ≤ (Rcut x : ℝ) := by exact_mod_cast hR1'
      have hlogR0 : 0 ≤ Real.log (Rcut x) := Real.log_nonneg hlogx1
      have hlogR : Real.log (Rcut x) ≤ Real.log x := by
        have h3 : (0 : ℝ) < (Rcut x : ℝ) := by linarith
        have h4 : (Rcut x : ℝ) ≤ (x : ℝ) := by
          exact_mod_cast (Rcut_le_self x)
        exact Real.log_le_log h3 h4
      have hAg' : (Real.log (Rcut x)) ^ Ag ≤ (Real.log x) ^ Ag :=
        Real.rpow_le_rpow hlogR0 hlogR hAg
      have h2 : (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ))
          ≤ Cg * (Real.log x) ^ Ag :=
        le_trans h1 (mul_le_mul_of_nonneg_left hAg' hCg.le)
      have h4 : (0 : ℝ) ≤ Cg * (Real.log x) ^ Ag :=
        mul_nonneg hCg.le (Real.rpow_nonneg hlog0 _)
      exact mul_le_mul hAt h2 (Finset.sum_nonneg fun d _ => hgn d) (by positivity)
    have hY3' : (x : ℝ) ^ ((11 : ℝ) / 16)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
      have h := hY3 x hxY3
      simpa only [Real.rpow_zero, mul_one, one_mul] using h
    have hY4' : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
      have h := hY4 x hxY4
      simp only [Real.rpow_zero, mul_one] at h
      have h5 : CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          ≤ CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (CA * (x : ℝ) ^ ((11 : ℝ) / 16)) :=
        mul_le_mul_of_nonneg_left hAt (by positivity)
      refine le_trans h5 ?_
      calc CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (CA * (x : ℝ) ^ ((11 : ℝ) / 16))
          = CAd * CA * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((11 : ℝ) / 16)) := by ring
        _ = CAd * CA * (x : ℝ) ^ ((11 : ℝ) / 16 + 1 / 100) := by
              rw [← Real.rpow_add hxpos]; norm_num
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := h
    have hY5' : CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag)
        ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by
      have h := hY5 x hxY5
      calc CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag)
          = Cg * CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Real.log x) ^ Ag := by ring
        _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := h
    calc Rsum x t
        ≤ (∑ d ∈ Finset.Icc 1 (Rcut x), (Ad d t : ℝ))
          + (Aseq t : ℝ) * (∑ d ∈ (Finset.Icc 1 (Rcut x)).filter (fun d => Squarefree d), (gdens d : ℝ)) := hR1
      _ ≤ ((x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ))
          + CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := add_le_add hpiece1 hpiece2
      _ = (x : ℝ) ^ ((11 : ℝ) / 16) + CAd * (x : ℝ) ^ ((1 : ℝ) / 100) * (Aseq t : ℝ)
          + CA * (x : ℝ) ^ ((11 : ℝ) / 16) * (Cg * (Real.log x) ^ Ag) := by ring
      _ ≤ cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam)
          + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam)
          + cA / 3 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) :=
          add_le_add (add_le_add hY3' hY4') hY5'
      _ = cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lam) := by ring
      _ ≤ (Aseq x : ℝ) * (Real.log x) ^ (-lam) := mul_le_mul_of_nonneg_right hAx hlogz

/-- **(R) of the companion paper for the Friedlander–Iwaniec sequence**, at the fixed exponent
`LamR = 2^50` used by the companion assembly. -/
theorem X2Y4_R_hypothesis :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      Rsum x t ≤ (Aseq x : ℝ) * (Real.log x) ^ (-LamR) :=
  X2Y4_R_generic LamR (by unfold LamR; positivity)

end Submission
