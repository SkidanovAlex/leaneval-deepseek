/-
  Companion paper ("Asymptotic sieve for primes"), §9: the constants of the passage to `ã`.

  This file proves

    * **(R₃) for the sequence `A` in the companion's normalisation** — i.e. for the remainder
      `r_d(t) = A_d(t) − g(d)A(t)` with `A(x) = ∑_{1 ≤ n ≤ x} a_n` (which is `FIr` for the
      Friedlander–Iwaniec sequence).  It is derived *crudely* from the main paper's Proposition 3.5
      (`X2Y4_R3_all`, which bounds `|Ad d t − gdens d · Aseq t|`): the two differ by
      `FIg d − 1`, whose sum over `d ≤ Y` is `≤ Y`, and `Y = x^{7/10}(log x)^{2^25} ≤ A(x)(log x)^{−2^24}`
      for large `x` (the same astronomical threshold already used by `X2Y4_R3`).

    * Each of the two identities `(9.10)` and `(9.12)` of the companion.
-/
import Mathlib
import Submission.ASP.S28
import Submission.ASP.S22
import Submission.ASP.S9i
import Mathlib.Data.Finset.Sort
import Submission.ASP.Defs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree
import Submission.Commons.NumberTheory.Divisors.card_divisors_prod_prime_pow
import Submission.Commons.NumberTheory.Divisors.primeFactors_prod_prime_pow
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.ASP.S9l
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Defs
import Submission.ASP.S9k
import Submission.ASP.S9m
import Submission.ASP.S9n
import Submission.ASP_R
import Submission.ASP_S92
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_sqrt
import Submission.Commons.NumberTheory.EulerProduct.tsum_moebius_mul_eq_tprod_of_pow_bound
import Submission.Commons.NumberTheory.EulerProduct.sum_gt_pow_bound_inv_sqrt_le
import Submission.Commons.NumberTheory.EulerProduct.abs_sum_moebius_mul_sub_tprod_le_inv_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset

noncomputable section

/-! ### The main paper's remainder over the cubefree moduli -/

/-- The remainder of the *main paper's* objects: `Ad d t − gdens d · Aseq t` (with the `n = 0`
term present on both sides).  It differs from the companion's `FIr d t` by `FIg d − 1`. -/
noncomputable def rMain (d t : ℕ) : ℝ :=
  (Submission.Ad d t : ℝ) - FIg d * (Submission.Aseq t : ℝ)

lemma FIr_eq_rMain (d t : ℕ) : FIr d t = rMain d t + (FIg d - 1) := by
  rw [FIr, FI_Ad_eq, FI_Acount_eq, rMain]; ring

lemma FIr_abs_le (d t : ℕ) : |FIr d t| ≤ |rMain d t| + |FIg d - 1| := by
  rw [FIr_eq_rMain]
  exact abs_add_le _ _

/-- `|FIg d − 1| ≤ 1`. -/
lemma FIg_sub_one_abs_le (d : ℕ) : |FIg d - 1| ≤ 1 := by
  have h1 : 0 ≤ FIg d := FIg_nonneg d
  have h2 : FIg d ≤ 1 := by
    rw [FIg]
    have := Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one d
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- **(R₃) for the companion's remainder `r_d = A_d − g d·A`** (the Friedlander–Iwaniec case),
crudely from the main paper's Proposition 3.5. -/
theorem FIr_cubefree_sum_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
      (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIr d t|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
  obtain ⟨X1, h1⟩ := X2Y4_R3_all
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨X2, hX2, htail⟩ := Submission.X2Y4R3.poly_tail_gen 1 ((7 : ℝ) / 10)
    ((2 : ℝ) ^ 25) cA ((2 : ℝ) ^ 25) (by norm_num) (by norm_num) hcA
  refine ⟨max X1 (max XA X2), fun x hx t ht2 htx => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hxA : XA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hlog0 : (0 : ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hlnn : 0 ≤ (Real.log x) ^ (-((2 : ℝ) ^ 25)) := Real.rpow_nonneg hlog0 _
  -- piece 1: the main paper's remainder
  have hp1 : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
      ≤ 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
    have h := h1 x hx1 t ht2 htx
    have hsum : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
        = ∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
            (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)| := by
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [rMain, FIg]
    rw [hsum]
    calc (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
            (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))) := h
      _ = 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by ring
  -- piece 2: the discrepancy `FIg d − 1`
  have hp2 : (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN,
        |FIg d - 1|) ≤ (Submission.X2Y4R3.R3cut x : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun d _ => FIg_sub_one_abs_le d)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((((Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN).card : ℕ) : ℝ)
        ≤ ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) := by
      have := Finset.card_filter_le (Finset.range (Submission.X2Y4R3.R3cut x)) CubefreeN
      rw [Finset.card_range] at this
      exact_mod_cast this
    exact hcard
  have hp2' : (Submission.X2Y4R3.R3cut x : ℝ) ≤ (Submission.Aseq x : ℝ) *
      (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
    have hthis := htail x hx2
    simp only [one_mul] at hthis
    have hR3 : ((Submission.X2Y4R3.R3cut x : ℕ) : ℝ) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) *
        (Real.log x) ^ ((2 : ℝ) ^ 25) := by
      rw [Submission.X2Y4R3.R3cut]
      exact_mod_cast Nat.floor_le (by positivity)
    refine le_trans hR3 ?_
    refine le_trans hthis ?_
    have hA := hAlow x hxA
    exact mul_le_mul_of_nonneg_right hA hlnn
  calc (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIr d t|)
      ≤ ∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN,
          (|rMain d t| + |FIg d - 1|) :=
        Finset.sum_le_sum (fun d _ => FIr_abs_le d t)
    _ = (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |rMain d t|)
        + (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN, |FIg d - 1|) :=
        Finset.sum_add_distrib
    _ ≤ 2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))
        + (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) :=
        add_le_add hp1 (le_trans hp2 hp2')
    _ ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
        have hA : 0 ≤ (Submission.Aseq x : ℝ) := by positivity
        have hl : 0 ≤ (Real.log x) ^ (-((2 : ℝ) ^ 25)) := hlnn
        nlinarith [hA, hl]


/-! ### (9.8) for the Friedlander–Iwaniec density -/

/-- The local density decay `g(p^{2k}) ≤ 3p^{−k−1}` (from `X2Y4_pair_ncard_prime_pow_sqrt`). -/
lemma FI_sq_pow_bound : ∀ p k : ℕ, p.Prime → 1 ≤ k →
    |FIg (p ^ (2 * k))| ≤ 3 / (p : ℝ) ^ (k + 1) := by
  intro p k hp hk
  have hb := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_ncard_prime_pow_sqrt
    (p := p) (e := 2 * k) hp (by omega)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hval : FIg (p ^ (2 * k))
      = (({x : ZMod (p ^ (2 * k)) × ZMod (p ^ (2 * k)) |
            x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / ((p : ℝ) ^ (2 * k)) ^ 2 := by
    rw [FIg, Submission.gdens, Submission.N]
    push_cast
    ring
  have hsqrt : Real.sqrt ((p : ℝ) ^ (2 * k)) = (p : ℝ) ^ k := by
    have hs : (p : ℝ) ^ (2 * k) = ((p : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]; congr 1; omega
    rw [hs, Real.sqrt_sq (by positivity)]
  have h1 : (p : ℝ) ^ (2 * k - 1) * (p : ℝ) ^ k = (p : ℝ) ^ (3 * k - 1) := by
    rw [← pow_add]; congr 1; omega
  have h2 : ((p : ℝ) ^ (2 * k)) ^ 2 = (p : ℝ) ^ (4 * k) := by
    rw [← pow_mul]; congr 1; omega
  have h3 : (p : ℝ) ^ (3 * k - 1) * (p : ℝ) ^ (k + 1) = (p : ℝ) ^ (4 * k) := by
    rw [← pow_add]; congr 1; omega
  have key : (3 : ℝ) * (p : ℝ) ^ (2 * k - 1) * (p : ℝ) ^ k / ((p : ℝ) ^ (2 * k)) ^ 2
      = 3 / (p : ℝ) ^ (k + 1) := by
    rw [h2, div_eq_div_iff (by positivity) (pow_ne_zero _ (ne_of_gt hp0))]
    calc 3 * (p : ℝ) ^ (2 * k - 1) * (p : ℝ) ^ k * (p : ℝ) ^ (k + 1)
        = 3 * ((p : ℝ) ^ (2 * k - 1) * (p : ℝ) ^ k) * (p : ℝ) ^ (k + 1) := by ring
      _ = 3 * (p : ℝ) ^ (3 * k - 1) * (p : ℝ) ^ (k + 1) := by rw [h1]
      _ = 3 * ((p : ℝ) ^ (3 * k - 1) * (p : ℝ) ^ (k + 1)) := by ring
      _ = 3 * (p : ℝ) ^ (4 * k) := by rw [h3]
  rw [abs_of_nonneg (FIg_nonneg _)]
  calc FIg (p ^ (2 * k))
      = (({x : ZMod (p ^ (2 * k)) × ZMod (p ^ (2 * k)) |
            x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / ((p : ℝ) ^ (2 * k)) ^ 2 := hval
    _ ≤ (3 * (p : ℝ) ^ (2 * k - 1) * Real.sqrt ((p : ℝ) ^ (2 * k)))
          / ((p : ℝ) ^ (2 * k)) ^ 2 :=
        div_le_div_of_nonneg_right hb (by positivity)
    _ = (3 * (p : ℝ) ^ (2 * k - 1) * (p : ℝ) ^ k) / ((p : ℝ) ^ (2 * k)) ^ 2 := by rw [hsqrt]
    _ = 3 / (p : ℝ) ^ (k + 1) := key

/-- **(9.8)** for the Friedlander–Iwaniec density: `G = ∏_p (1 − g(p²)) = ∑'_ν μ(ν)·g(ν²)`. -/
theorem FI_Gprod_eq_tsum :
    Gprod FIg = ∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2) := by
  refine (Commons.NumberTheory.EulerProduct.tsum_moebius_mul_eq_tprod_of_pow_bound
    (f := fun ν : ℕ => FIg (ν ^ 2)) (C := 3) (by norm_num) ?_ ?_ ?_).symm
  · intro m n hmn
    rw [mul_pow]
    exact FI_gdens_mul ((hmn.pow_left 2).pow_right 2)
  · rw [one_pow]; exact FI_gdens_one
  · intro p k hp hk
    have heq : (p ^ k) ^ 2 = p ^ (2 * k) := by ring
    rw [heq]
    exact FI_sq_pow_bound p k hp hk

/-- **The two convergence rates of §9 for the Friedlander–Iwaniec density**:
`∑_{ν ≤ m} μ(ν)g(ν²) → G` at rate `1/√m`, and `∑_{ν > L} g(ν²) ≪ 1/√L`.  Both are applications of
the commons lemmas with `f(ν) = FIg(ν²)` and `C = 3` (via `FI_sq_pow_bound`). -/
theorem FI_sq_rates :
    (∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m →
      |(∑ ν ∈ Finset.Icc 1 m, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) - Gprod FIg|
        ≤ K / Real.sqrt (m : ℝ))
    ∧ (∃ K : ℝ, 0 < K ∧ ∀ N L : ℕ, 1 ≤ L →
      (∑ ν ∈ (Finset.Icc 1 N).filter (fun n => L < n), abs (FIg (ν ^ 2)))
        ≤ K / Real.sqrt (L : ℝ)) := by
  have h1 : ∀ m n : ℕ, Nat.Coprime m n →
      (fun ν : ℕ => FIg (ν ^ 2)) (m * n) = (fun ν : ℕ => FIg (ν ^ 2)) m * (fun ν : ℕ => FIg (ν ^ 2)) n :=
    fun m n hmn => by
      show FIg ((m * n) ^ 2) = FIg (m ^ 2) * FIg (n ^ 2)
      rw [mul_pow]
      exact FI_gdens_mul ((hmn.pow_left 2).pow_right 2)
  have h2 : (fun ν : ℕ => FIg (ν ^ 2)) 1 = 1 := by
    show FIg (1 ^ 2) = 1
    rw [one_pow]; exact FI_gdens_one
  have h3 : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      |(fun ν : ℕ => FIg (ν ^ 2)) (p ^ k)| ≤ 3 / (p : ℝ) ^ (k + 1) := by
    intro p k hp hk
    show |FIg ((p ^ k) ^ 2)| ≤ 3 / (p : ℝ) ^ (k + 1)
    rw [show (p ^ k) ^ 2 = p ^ (2 * k) from by ring]
    exact FI_sq_pow_bound p k hp hk
  constructor
  · obtain ⟨K, hK, h⟩ := Commons.NumberTheory.EulerProduct.abs_sum_moebius_mul_sub_tprod_le_inv_sqrt
      (f := fun ν : ℕ => FIg (ν ^ 2)) (C := 3) (by norm_num) h1 h2 h3
    exact ⟨K, hK, h⟩
  · obtain ⟨K, hK, h⟩ := Commons.NumberTheory.EulerProduct.sum_gt_pow_bound_inv_sqrt_le
      (f := fun ν : ℕ => FIg (ν ^ 2)) (C := 3) (by norm_num) h1 h2 h3
    exact ⟨K, hK, h⟩
/-! ### (9.10): the counting function of `ã` -/

lemma Ad_eq_zero_of_lt_s29 (a : ℕ → ℝ) {d m : ℕ} (h : m < d) : Ad a d (m : ℝ) = 0 := by
  rw [Ad, Nat.floor_natCast]
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnm⟩, hdn⟩ := hn
  exact absurd (le_trans (Nat.le_of_dvd (by omega) hdn) hnm) (by omega)

lemma filter_sq_le_eq_Icc_sqrt (x : ℕ) :
    (Finset.Icc 1 x).filter (fun ν => ν ^ 2 ≤ x) = Finset.Icc 1 x.sqrt := by
  ext ν
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, (Nat.le_sqrt').mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, le_trans h2 (Nat.sqrt_le_self x)⟩, (Nat.le_sqrt').mp h2⟩

/-- **(9.10)** for the Friedlander–Iwaniec sequence, in the companion's objects:
`Ã(x) = ∑_{ν ≤ √x} μ(ν)·(g(ν²)·A(x) + r_{ν²}(x))`. -/
theorem Acount_atil_FI_eq (x : ℕ) :
    Acount (atil FIa) (x : ℝ)
      = ∑ ν ∈ Finset.Icc 1 x.sqrt,
          (ArithmeticFunction.moebius ν : ℝ)
            * (FIg (ν ^ 2) * Acount FIa (x : ℝ) + FIr (ν ^ 2) x) := by
  rw [Acount_atil_eq FIa x, AtilAd_eq_sum_lcm FIa 1 x]
  simp only [Nat.lcm_one_right]
  have h2 : ∀ ν : ℕ,
      (ArithmeticFunction.moebius ν : ℝ) * Ad FIa (ν ^ 2) (x : ℝ)
        = (ArithmeticFunction.moebius ν : ℝ)
            * (FIg (ν ^ 2) * Acount FIa (x : ℝ) + FIr (ν ^ 2) x) := by
    intro ν
    rw [FI_approx (x : ℝ) (ν ^ 2) x]
  rw [Finset.sum_congr rfl (fun ν _ => h2 ν)]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x) (fun ν => ν ^ 2 ≤ x)]
  have hzero : (∑ ν ∈ (Finset.Icc 1 x).filter (fun ν => ¬ ν ^ 2 ≤ x),
      (ArithmeticFunction.moebius ν : ℝ)
        * (FIg (ν ^ 2) * Acount FIa (x : ℝ) + FIr (ν ^ 2) x)) = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    rw [Finset.mem_filter] at hν
    have hxν : x < ν ^ 2 := by omega
    have hAd : Ad FIa (ν ^ 2) (x : ℝ) = 0 := Ad_eq_zero_of_lt_s29 FIa hxν
    have happ := FI_approx (x : ℝ) (ν ^ 2) x
    rw [hAd] at happ
    rw [← happ]
    ring
  rw [hzero, add_zero, filter_sq_le_eq_Icc_sqrt]

/-! ### The `ν ≤ L` part of (9.10) -/

/-- The contribution of the squarefree `ν ≤ L` to `∑_{ν ≤ √x}|FIr(ν²)x|`: map `ν ↦ ν²` (injective,
into the cubefree moduli) and apply `(R₃)`. -/
theorem FIr_sq_small_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ L : ℕ, 1 ≤ L →
      L ^ 2 < Submission.X2Y4R3.R3cut x →
      (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree, |FIr (ν ^ 2) x|)
        ≤ 4 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
  obtain ⟨X1, h1⟩ := FIr_cubefree_sum_le
  refine ⟨max X1 2, fun x hx L hL1 hL2 => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  set S : Finset ℕ := (Finset.Icc 1 L).filter Squarefree with hS
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a ^ 2 = b ^ 2 → a = b :=
    fun a _ b _ hab => Nat.pow_left_injective (n := 2) (by norm_num) hab
  have hsub : S.image (fun ν => ν ^ 2)
      ⊆ (Finset.range (Submission.X2Y4R3.R3cut x)).filter CubefreeN := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨ν, hνS, rfl⟩ := hk
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hνS
    obtain ⟨⟨hν1, hνL⟩, hνsf⟩ := hνS
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.pow_le_pow_left hνL 2) hL2
    · rw [← Nat.lcm_one_right (ν ^ 2)]
      exact cubefreeN_lcm_sq hνsf squarefree_one
  have heq := (Finset.sum_image (s := S) (f := fun k : ℕ => abs (FIr k x))
    (g := fun ν : ℕ => ν ^ 2) hinj).symm
  rw [heq]
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
    (h1 x hx1 x hx2 le_rfl)

/-! ### The `ν > L` part of (9.10) -/

lemma EtwoA_one_eq (a : ℕ → ℝ) (t Y : ℕ) :
    EtwoA a t 1 (Y + 1) t
      = ∑ ν ∈ (Finset.Icc (Y + 1) t).filter Squarefree, Ad a (ν ^ 2) t := by
  rw [EtwoA]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  have h1 : (Finset.Icc 1 1).filter Squarefree = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; omega
    · rintro rfl; exact ⟨⟨le_rfl, le_rfl⟩, squarefree_one⟩
  rw [h1, Finset.sum_singleton, Nat.lcm_one_right]

/-- `an 1 ≥ 1` (the pair `(1,0)` represents `1`). -/
lemma an_one_pos' : 1 ≤ Submission.an 1 := by
  have hfin : ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = 1}).Finite := by
    have h1 : ({a : ℤ | a ^ 2 ≤ 1}).Finite := by
      have h : {a : ℤ | a ^ 2 ≤ 1} = Set.Icc (-1) 1 := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · intro ha; exact ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
        · rintro ⟨ha1, ha2⟩; nlinarith
      rw [h]; exact Set.finite_Icc _ _
    have h2 : ({b : ℤ | b ^ 4 ≤ 1}).Finite := by
      have h : {b : ℤ | b ^ 4 ≤ 1} = {b : ℤ | b ^ 2 ≤ 1} := by
        ext b
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro hb <;> nlinarith [sq_nonneg b, sq_nonneg (b ^ 2)]
      rw [h]; exact h1
    refine (h1.prod h2).subset ?_
    rintro ⟨a, b⟩ hab
    simp only [Set.mem_prod, Set.mem_ofPred_eq] at hab ⊢
    exact ⟨by nlinarith [hab, sq_nonneg a, show (0:ℤ) ≤ b ^ 4 by positivity],
           by nlinarith [hab, sq_nonneg a, show (0:ℤ) ≤ b ^ 4 by positivity]⟩
  rw [Submission.an]
  exact Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt ((Set.ncard_pos hfin).mpr ⟨(1, 0), by norm_num⟩))

/-- The `ν > L` part of `∑_{ν ≤ √x}|FIr(ν²)x|`: Cauchy–Schwarz plus `(9.2)` for the `Ad`-part
(which uses `L ≥ x^{1/3}(log x)^{75}`), and the convergence of `∑_ν g(ν²)` for the `g`-part. -/
theorem FIr_sq_large_le {K : ℝ} (hK : 0 < K)
    (hTail : ∀ N L : ℕ, 1 ≤ L →
      (∑ ν ∈ (Finset.Icc 1 N).filter (fun n => L < n), abs (FIg (ν ^ 2)))
        ≤ K / Real.sqrt (L : ℝ)) :
    ∃ X₀ : ℕ, ∃ K3 : ℝ, 0 < K3 ∧ ∀ x : ℕ, X₀ ≤ x → ∀ L : ℕ, 1 ≤ L → L ≤ x.sqrt →
      (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≤ (L : ℝ) →
      (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIr (ν ^ 2) x))
        ≤ Acount FIa (x : ℝ) * K3 / (Real.log ((x : ℝ) + 2)) ^ 2
          + Acount FIa (x : ℝ) * K3 / Real.sqrt (L : ℝ) := by
  obtain ⟨X1a, hS92⟩ := X2Y4_S92
  obtain ⟨C2, hC2pos, hC2⟩ := sum_tau_cube_sqr_dvd_gt_le
  refine ⟨max X1a 4, max (2 * Real.sqrt C2) K + 1, by positivity,
    fun x hx L hL1 hLx hLbig => ?_⟩
  have hx1 : X1a ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hxt : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hsL : (0 : ℝ) < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL0
  -- `A(x) ≥ 1`
  have hA1 : 1 ≤ Acount FIa (x : ℝ) := by
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hxt⟩
    have h := Finset.single_le_sum (f := FIa) (fun i _ => FIa_nonneg i) hmem
    rw [Acount, Nat.floor_natCast]
    have h2 : (1 : ℝ) ≤ FIa 1 := by
      rw [FIa]
      exact_mod_cast an_one_pos'
    linarith
  have hA0 : (0 : ℝ) ≤ Acount FIa (x : ℝ) := le_trans zero_le_one hA1
  have hAseq : (Submission.Aseq x : ℝ) ≤ 2 * Acount FIa (x : ℝ) := by
    have h4 : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by rw [FI_Acount_eq]; ring
    linarith
  -- log facts
  have hlog2 : (1 : ℝ) ≤ Real.log ((x : ℝ) + 2) := by
    have h5 : (5 : ℝ) ≤ (x : ℝ) + 2 := by
      have h6 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
      linarith
    have he : Real.exp 1 ≤ 5 := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he h5)
    rwa [Real.log_exp] at h
  have hlogpos : (0 : ℝ) < Real.log ((x : ℝ) + 2) := lt_of_lt_of_le one_pos hlog2
  -- the pointwise splitting
  have hsplit : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIr (ν ^ 2) x))
      ≤ (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
        + Acount FIa (x : ℝ)
            * (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ν _ => ?_)
    have h1 : 0 ≤ Ad FIa (ν ^ 2) x := Finset.sum_nonneg (fun n _ => FIa_nonneg n)
    have h2 : 0 ≤ FIg (ν ^ 2) := FIg_nonneg _
    have h4 : 0 ≤ FIg (ν ^ 2) * Acount FIa (x : ℝ) := mul_nonneg h2 hA0
    have heq : FIr (ν ^ 2) x = Ad FIa (ν ^ 2) x - FIg (ν ^ 2) * Acount FIa (x : ℝ) := rfl
    rw [heq]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  -- `(9.2)`: the square sum
  have hA2 : (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
      ≤ 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
    have h1 : (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2) ≤ ∑ n ∈ Finset.range (x + 1), FIa n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        rw [Finset.mem_Icc] at hn
        exact Finset.mem_range.mpr (by omega)) (fun n _ _ => by positivity)
    have h2 : (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
        ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Submission.Aseq x : ℝ) ^ 2 := by
      simpa only [FIa] using hS92 x hx1
    have h5 : (Submission.Aseq x : ℝ) ^ 2 ≤ 4 * Acount FIa (x : ℝ) ^ 2 := by
      have h4 : (Submission.Aseq x : ℝ) = Acount FIa (x : ℝ) + 1 := by rw [FI_Acount_eq]; ring
      rw [h4]; nlinarith [hA0, hA1]
    have hstep : (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
        ≤ 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
      calc (∑ n ∈ Finset.range (x + 1), FIa n ^ 2)
          ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Submission.Aseq x : ℝ) ^ 2 := h2
        _ ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (4 * Acount FIa (x : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hx0.le _)
        _ = 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by ring
    exact le_trans h1 hstep
  -- the `Ad`-part, via `EtwoA_gt_le`
  have hAd : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
      ≤ 2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ)
          * Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)) := by
    have hEtwo : EtwoA FIa x 1 (L + 1) x
        ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
          * Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)) := by
      refine EtwoA_gt_le FIa (fun n => FIa_nonneg n) x 1 L hxt ?_
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hC2 x L hL1 hxt)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsub : sqdvCount n (L + 1) x
          ≤ ((Finset.Icc 1 x).filter (fun ν => L < ν ∧ ν ^ 2 ∣ n)).card := by
        rw [sqdvCount]
        refine Finset.card_le_card ?_
        intro ν hν
        rw [Finset.mem_filter] at hν
        obtain ⟨hν1, hν2⟩ := hν
        rw [Finset.mem_filter] at hν1
        obtain ⟨hν1a, _⟩ := hν1
        rw [Finset.mem_Icc] at hν1a
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hν1a.2⟩, by omega, hν2⟩
      exact_mod_cast hsub
    have hstep : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
        ≤ EtwoA FIa x 1 (L + 1) x := by
      rw [EtwoA_one_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro ν hν
        rw [Finset.mem_filter] at hν
        obtain ⟨hν1, hν2⟩ := hν
        rw [Finset.mem_Icc] at hν1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
          le_trans hν1.2 (Nat.sqrt_le_self x)⟩, hν2⟩)
        (fun ν _ _ => Finset.sum_nonneg (fun n _ => FIa_nonneg n))
    refine le_trans hstep (le_trans hEtwo ?_)
    have hsA : Real.sqrt (∑ n ∈ Finset.Icc 1 x, FIa n ^ 2)
        ≤ 2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ) := by
      refine le_trans (Real.sqrt_le_sqrt hA2) ?_
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h2 : (2 * (x : ℝ) ^ (-(1 : ℝ) / 3) * Acount FIa (x : ℝ)) ^ 2
          = 4 * (x : ℝ) ^ (-(2 : ℝ) / 3) * Acount FIa (x : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ (-(1:ℝ)/3)) 2,
          ← Real.rpow_mul hx0.le]
        norm_num
      rw [h2]
    exact mul_le_mul_of_nonneg_right hsA (Real.sqrt_nonneg _)
  -- the `g`-part
  have hg : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2))
      ≤ K / Real.sqrt (L : ℝ) := by
    have heq : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, FIg (ν ^ 2))
        = ∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, abs (FIg (ν ^ 2)) := by
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      exact (abs_of_nonneg (FIg_nonneg _)).symm
    rw [heq]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ν _ _ => abs_nonneg _))
      (hTail x L hL1)
    intro ν hν
    rw [Finset.mem_filter] at hν
    obtain ⟨hν1, hν2⟩ := hν
    rw [Finset.mem_Icc] at hν1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
      le_trans hν1.2 (Nat.sqrt_le_self x)⟩, by omega⟩
  -- the numerical comparison
  have hsqrt_bound : Real.sqrt (C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ))
      ≤ Real.sqrt C2 * (x : ℝ) ^ ((1 : ℝ) / 3) / (Real.log ((x : ℝ) + 2)) ^ 2 := by
    have hmid : C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)
        ≤ C2 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (-(4 : ℝ)) := by
      have h1 : C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71 / (L : ℝ)
          ≤ C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71
            / ((x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)) :=
        div_le_div_of_nonneg_left (b := (L : ℝ))
          (c := (x : ℝ) ^ ((1 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ))
          (by positivity) (by positivity) hLbig
      refine le_trans h1 (le_of_eq ?_)
      rw [div_eq_iff (by positivity : (x : ℝ) ^ ((1 : ℝ) / 3)
        * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ) ≠ 0)]
      rw [show C2 * (x : ℝ) * (Real.log ((x : ℝ) + 2)) ^ 71
          = C2 * ((x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((2 : ℝ) / 3))
            * ((Real.log ((x : ℝ) + 2)) ^ (-(4 : ℝ))
              * (Real.log ((x : ℝ) + 2)) ^ (75 : ℝ)) from by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hlogpos]
        norm_num]
      ring
    have hmid2 : Real.sqrt (C2 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (-(4 : ℝ)))
        = Real.sqrt C2 * (x : ℝ) ^ ((1 : ℝ) / 3) / (Real.log ((x : ℝ) + 2)) ^ 2 := by
      rw [show C2 * (x : ℝ) ^ ((2 : ℝ) / 3) * (Real.log ((x : ℝ) + 2)) ^ (-(4 : ℝ))
          = C2 * ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ (-(2 : ℝ))) ^ 2 from by
        rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hx0.le,
          ← Real.rpow_natCast ((Real.log ((x : ℝ) + 2)) ^ (-(2 : ℝ))) 2,
          ← Real.rpow_mul hlogpos.le]
        norm_num]
      rw [show C2 * ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ (-(2 : ℝ))) ^ 2
          = C2 * (((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2
            * ((Real.log ((x : ℝ) + 2)) ^ (-(2 : ℝ))) ^ 2) from by ring]
      rw [Real.sqrt_mul hC2pos.le,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2),
        Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
      rw [show (Real.log ((x : ℝ) + 2)) ^ (-(2 : ℝ)) = ((Real.log ((x : ℝ) + 2)) ^ 2)⁻¹ from by
        rw [Real.rpow_neg hlogpos.le]
        norm_num]
      ring
    exact le_trans (Real.sqrt_le_sqrt hmid) (le_of_eq hmid2)
  have hAd' : (∑ ν ∈ (Finset.Icc (L + 1) x.sqrt).filter Squarefree, Ad FIa (ν ^ 2) x)
      ≤ Acount FIa (x : ℝ) * (2 * Real.sqrt C2) / (Real.log ((x : ℝ) + 2)) ^ 2 := by
    refine le_trans hAd (le_trans (mul_le_mul_of_nonneg_left hsqrt_bound (by positivity)) ?_)
    have h2 : (x : ℝ) ^ (-(1:ℝ)/3) * (x : ℝ) ^ ((1:ℝ)/3) = 1 := by
      rw [← Real.rpow_add hx0]; norm_num
    have h3 : 2 * (x : ℝ) ^ (-(1:ℝ)/3) * Acount FIa (x : ℝ)
          * (Real.sqrt C2 * (x : ℝ) ^ ((1:ℝ)/3) / (Real.log ((x : ℝ) + 2)) ^ 2)
        = Acount FIa (x : ℝ) * (2 * Real.sqrt C2) / (Real.log ((x : ℝ) + 2)) ^ 2 := by
      rw [show 2 * (x : ℝ) ^ (-(1:ℝ)/3) * Acount FIa (x : ℝ)
            * (Real.sqrt C2 * (x : ℝ) ^ ((1:ℝ)/3) / (Real.log ((x : ℝ) + 2)) ^ 2)
          = 2 * Real.sqrt C2 * Acount FIa (x : ℝ)
            * ((x : ℝ) ^ (-(1:ℝ)/3) * (x : ℝ) ^ ((1:ℝ)/3))
            / (Real.log ((x : ℝ) + 2)) ^ 2 from by ring, h2]
      ring
    rw [h3]
  have hK3 : 2 * Real.sqrt C2 ≤ max (2 * Real.sqrt C2) K + 1 := by
    linarith [le_max_left (2 * Real.sqrt C2) K]
  have hK3' : K ≤ max (2 * Real.sqrt C2) K + 1 := by
    linarith [le_max_right (2 * Real.sqrt C2) K]
  have hlog2sq : (0 : ℝ) < (Real.log ((x : ℝ) + 2)) ^ 2 := pow_pos hlogpos 2
  refine le_trans hsplit (le_trans (add_le_add hAd' (mul_le_mul_of_nonneg_left hg hA0)) ?_)
  have h1 : Acount FIa (x : ℝ) * (2 * Real.sqrt C2) / (Real.log ((x : ℝ) + 2)) ^ 2
      ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1) / (Real.log ((x : ℝ) + 2)) ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ hlog2sq.le
    exact mul_le_mul_of_nonneg_left hK3 hA0
  have h2 : Acount FIa (x : ℝ) * (K / Real.sqrt (L : ℝ))
      ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1) / Real.sqrt (L : ℝ) := by
    calc Acount FIa (x : ℝ) * (K / Real.sqrt (L : ℝ))
        = Acount FIa (x : ℝ) * K / Real.sqrt (L : ℝ) := by ring
      _ ≤ Acount FIa (x : ℝ) * (max (2 * Real.sqrt C2) K + 1) / Real.sqrt (L : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hsL.le
          exact mul_le_mul_of_nonneg_left hK3' hA0
  exact add_le_add h1 h2

end

end Submission.ASP
