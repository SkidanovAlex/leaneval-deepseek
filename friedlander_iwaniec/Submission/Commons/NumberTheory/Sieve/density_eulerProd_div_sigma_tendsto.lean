import Mathlib
import Mathlib.NumberTheory.EulerProduct.Basic
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges
import Submission.Commons.NumberTheory.Mertens.primeSmoothLimit_of_secondMertens
import Submission.Commons.NumberTheory.Mertens.prime_euler_constant_identity
import Submission.Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Sieve

noncomputable section

/-! ### The quadratic remainder of `log (1 - x)` -/

/-- `dlt x = -log (1 - x) - x`, the `O(x^2)` remainder of `log (1 - x) = -x + O(x^2)`. -/
def dlt (x : ℝ) : ℝ := -Real.log (1 - x) - x

lemma dlt_nonneg {x : ℝ} (h1 : x < 1) : 0 ≤ dlt x := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  rw [dlt]
  linarith

lemma abs_dlt_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |dlt x| ≤ 2 * x ^ 2 := by
  have hx1 : |x| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le hx1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at h
  have h2 : |x| ^ 2 / (1 - |x|) ≤ 2 * x ^ 2 := by
    rw [sq_abs, div_le_iff₀ (by linarith : (0:ℝ) < 1 - |x|)]
    have := abs_nonneg x
    nlinarith
  rw [dlt, show -Real.log (1 - x) - x = -(Real.log (1 - x) + x) by ring, abs_neg]
  calc |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    _ ≤ |x| ^ 2 / (1 - |x|) := h
    _ ≤ 2 * x ^ 2 := h2

lemma log_one_sub_eq (x : ℝ) : Real.log (1 - x) = -x - dlt x := by
  rw [dlt]; ring

/-- For `0 ≤ x ≤ 1/2`, `-log (1 - x) ≤ 2x`. -/
lemma neg_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hx2 : 1 / (1 - x) ≤ 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have h1' : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp
    ring
  calc -Real.log (1 - x) = Real.log ((1 - x)⁻¹) := by rw [Real.log_inv]
    _ ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = x / (1 - x) := h1'
    _ ≤ 2 * x := by
        rw [div_le_iff₀ hpos]
        nlinarith

lemma dlt_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) : dlt x ≤ dlt y := by
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy
  have h1x : 0 < 1 - x := by linarith
  set w : ℝ := (y - x) / (1 - x) with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) h1x.le
  have hw1 : w < 1 := by
    rw [hw, div_lt_one h1x]; linarith
  have hy' : 1 - y = (1 - x) * (1 - w) := by
    rw [hw]; field_simp; ring
  have h1w : 0 < 1 - w := by linarith
  have h1 : Real.log (1 - x) - Real.log (1 - y) = -Real.log (1 - w) := by
    rw [hy', Real.log_mul (ne_of_gt h1x) (ne_of_gt h1w)]
    ring
  have h2 : x - y = -w * (1 - x) := by
    rw [hw]; field_simp; ring
  have hkey : dlt y - dlt x = dlt w + w * x := by
    have h3 : (-Real.log (1 - y) - y) - (-Real.log (1 - x) - x)
        = (Real.log (1 - x) - Real.log (1 - y)) + (x - y) := by ring
    rw [dlt, dlt, h3, h1, h2, dlt]
    ring
  have h0 : 0 ≤ dlt w := dlt_nonneg hw1
  nlinarith [h0, hw0, hx]

lemma continuousAt_dlt {x : ℝ} (hx : x < 1) : ContinuousAt dlt x := by
  have h1 : (1 - x) ≠ 0 := by linarith
  have h2 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log h1
  have h3 : ContinuousAt (fun y : ℝ => -Real.log (1 - y) - y) x := h2.neg.sub continuousAt_id
  exact h3

/-- For a prime `p`, `dlt (1/p) = log (p/(p-1)) - 1/p`. -/
lemma dlt_inv_eq {p : ℕ} (hp : p.Prime) :
    dlt (1 / (p : ℝ)) = Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1 : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  have h2 : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
    rw [h1]; exact div_ne_zero (by linarith) (ne_of_gt hp0)
  rw [dlt, h1, ← Real.log_inv, inv_div]


/-! ### Converting between `Nat.Primes` and `ℕ` -/

lemma tsum_primes_eq (f : ℕ → ℝ) :
    (∑' p : Nat.Primes, f (p : ℕ)) = ∑' n : ℕ, if n.Prime then f n else 0 := by
  have key : (∑' (x : {n : ℕ // Nat.Prime n}), f (x : ℕ)) = ∑' n : ℕ, if n.Prime then f n else 0 := by
    have h := tsum_subtype {n : ℕ | Nat.Prime n} (fun n => f n)
    have h2 : (∑' (x : {n : ℕ // Nat.Prime n}), f (x : ℕ))
        = ∑' (x : ℕ), {n | Nat.Prime n}.indicator (fun n => f n) x := h
    rw [h2]
    refine tsum_congr fun n => ?_
    by_cases hh : n.Prime <;> simp [Set.indicator, hh]
  exact key


/-! ### Summability of the Dirichlet series of the density -/

lemma norm_moebius_mul_g_rpow_prime {g : ℕ → ℝ} {σ : ℝ} {p : ℕ} (hpp : Nat.Prime p)
    (hg0 : 0 ≤ g p) :
    ‖(ArithmeticFunction.moebius p : ℝ) * g p * (p : ℝ) ^ (-σ)‖ = g p * (p : ℝ) ^ (-σ) := by
  have hval : (ArithmeticFunction.moebius p : ℝ) * g p * (p : ℝ) ^ (-σ)
      = -(g p * (p : ℝ) ^ (-σ)) := by
    rw [ArithmeticFunction.moebius_apply_prime hpp, Int.cast_neg, Int.cast_one]
    ring
  rw [hval, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (mul_nonneg hg0 (Real.rpow_nonneg (Nat.cast_nonneg p) _))]

lemma summable_norm_moebius_mul_g_rpow {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun d : ℕ => ‖(ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)‖) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnn : 0 ≤ C := by
    have h2 : g 2 ≤ C / 2 := hC 2 Nat.prime_two
    have := hp 2 Nat.prime_two
    linarith
  let F : ℕ → ℝ := fun d => ‖(ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)‖
  have hF1 : F 1 = 1 := by simp [F, hg1]
  have hFmul : ∀ m n : ℕ, Nat.Coprime m n → F (m * n) = F m * F n := by
    intro m n hmn
    have hcast : (((ArithmeticFunction.moebius (m * n) : ℤ)) : ℝ)
        = (((ArithmeticFunction.moebius m : ℤ)) : ℝ) * (((ArithmeticFunction.moebius n : ℤ)) : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
      push_cast
      ring
    have hprod : (((ArithmeticFunction.moebius m : ℤ)) : ℝ) * (((ArithmeticFunction.moebius n : ℤ)) : ℝ)
          * (g m * g n) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
        = ((((ArithmeticFunction.moebius m : ℤ)) : ℝ) * g m * (m : ℝ) ^ (-σ))
          * ((((ArithmeticFunction.moebius n : ℤ)) : ℝ) * g n * (n : ℝ) ^ (-σ)) := by ring
    simp only [F]
    rw [hcast, hmul m n hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      hprod, norm_mul]
  have hFzeta : ∀ M : ℕ, ∑ i ∈ Finset.range M, F i
      ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(1 + σ))) := by
    intro M
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; rw [Finset.sum_range_zero]; exact Real.exp_nonneg _
    · obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
      have hsum_eq : ∑ i ∈ Finset.range (N + 1), F i
          = ∑ i ∈ (Finset.Icc 1 N).filter Squarefree, F i := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_Icc] at hi
          exact Finset.mem_range.mpr (by omega)
        · intro i hi hni
          simp only [Finset.mem_range] at hi
          by_cases hi0 : i = 0
          · subst hi0
            simp [F, ArithmeticFunction.moebius.map_zero]
          · have h1i : 1 ≤ i := by omega
            have hnsq : ¬ Squarefree i := by
              intro hsq
              exact hni (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1i, by omega⟩, hsq⟩)
            simp [F, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      rw [hsum_eq]
      refine le_trans
        (Commons.NumberTheory.Sieve.squarefree_sum_g_le F (fun n => norm_nonneg _) hFmul hF1 N) ?_
      have hprodb : ∏ p ∈ (N + 1).primesBelow, (1 + F p)
          ≤ ∏ p ∈ (N + 1).primesBelow, Real.exp (C * (p : ℝ) ^ (-(1 + σ))) := by
        refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hmem => ?_)
        have hpp : Nat.Prime p := (Nat.mem_primesBelow.mp hmem).2
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have hFp : F p = g p * (p : ℝ) ^ (-σ) := by
          simp only [F]
          exact norm_moebius_mul_g_rpow_prime hpp (hp p hpp)
        rw [hFp]
        have h1 : g p * (p : ℝ) ^ (-σ) ≤ C * (p : ℝ) ^ (-(1 + σ)) := by
          have h3 : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
          calc g p * (p : ℝ) ^ (-σ) ≤ (C / (p : ℝ)) * (p : ℝ) ^ (-σ) :=
                mul_le_mul_of_nonneg_right (hC p hpp) h3
            _ = C * (p : ℝ) ^ (-(1 + σ)) := by
                rw [show (-(1 + σ) : ℝ) = -1 + (-σ) by ring, Real.rpow_add hp0, Real.rpow_neg_one,
                  div_eq_mul_inv]
                ring
        calc 1 + g p * (p : ℝ) ^ (-σ) ≤ 1 + C * (p : ℝ) ^ (-(1 + σ)) := by linarith
          _ ≤ Real.exp (C * (p : ℝ) ^ (-(1 + σ))) := by
              have := Real.add_one_le_exp (C * (p : ℝ) ^ (-(1 + σ)))
              linarith
      refine le_trans hprodb ?_
      rw [← Real.exp_sum]
      refine Real.exp_le_exp.mpr ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hCnn
      calc ∑ p ∈ (N + 1).primesBelow, (p : ℝ) ^ (-(1 + σ))
            ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-(1 + σ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_
              (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
            intro p hp
            exact Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1
        _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(1 + σ)) :=
            Summable.sum_le_tsum (Finset.range (N + 1))
              (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
              (Real.summable_nat_rpow.mpr (by linarith : -(1 + σ) < -1))
  exact summable_of_sum_range_le (fun n => norm_nonneg _) hFzeta

/-! ### The Euler product -/

lemma euler_product_moebius_mul_g_rpow {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)) =
      ∏' n : ℕ, (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1) := by
  let f : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)
  change (∑' d : ℕ, f d) = ∏' n : ℕ, (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1)
  have hsum : Summable (fun d : ℕ => ‖f d‖) :=
    summable_norm_moebius_mul_g_rpow hmul hg1 hp hbound hσ
  have hf1 : f 1 = 1 := by simp [f, hg1]
  have hfmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    have hcast : (((ArithmeticFunction.moebius (m * n) : ℤ)) : ℝ)
        = (((ArithmeticFunction.moebius m : ℤ)) : ℝ) * (((ArithmeticFunction.moebius n : ℤ)) : ℝ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
      push_cast
      ring
    have hprod : (((ArithmeticFunction.moebius m : ℤ)) : ℝ) * (((ArithmeticFunction.moebius n : ℤ)) : ℝ)
          * (g m * g n) * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
        = ((((ArithmeticFunction.moebius m : ℤ)) : ℝ) * g m * (m : ℝ) ^ (-σ))
          * ((((ArithmeticFunction.moebius n : ℤ)) : ℝ) * g n * (n : ℝ) ^ (-σ)) := by ring
    simp only [f]
    rw [hcast, hmul m n hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      hprod]
  have hf0 : f 0 = 0 := by simp [f, ArithmeticFunction.moebius.map_zero]
  have hprod := EulerProduct.eulerProduct_hasProd_mulIndicator (f := f) hf1
    (fun {m n} h => hfmul m n h) hsum hf0
  have ht := hprod.tprod_eq
  have hloc : ∀ n : ℕ, Set.mulIndicator {p : ℕ | Nat.Prime p} (fun p => ∑' e : ℕ, f (p ^ e)) n
      = (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1) := by
    intro n
    by_cases hn : n.Prime
    · rw [Set.mulIndicator_of_mem (show n ∈ {p : ℕ | Nat.Prime p} from hn), if_pos hn]
      have hzero : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) → f (n ^ e) = 0 := by
        intro e he
        have he0 : e ≠ 0 := by intro h; exact he (by simp [h])
        have he1 : e ≠ 1 := by intro h; exact he (by simp [h])
        have hmu : ArithmeticFunction.moebius (n ^ e) = 0 := by
          rw [ArithmeticFunction.moebius_apply_prime_pow hn he0, if_neg he1]
        simp [f, hmu]
      rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) hzero, Finset.sum_insert (by simp),
        Finset.sum_singleton]
      have h0 : f (n ^ 0) = 1 := by simp [f, hg1]
      have h1 : f (n ^ 1) = -(g n * (n : ℝ) ^ (-σ)) := by
        simp only [f, pow_one, ArithmeticFunction.moebius_apply_prime hn, Int.cast_neg,
          Int.cast_one, neg_mul, one_mul]
      rw [h0, h1]
      ring
    · rw [Set.mulIndicator_of_notMem (show n ∉ {p : ℕ | Nat.Prime p} from hn), if_neg hn]
  rw [← ht]
  exact tprod_congr hloc

/-! ### `g` on squarefree numbers -/

lemma g_prod_primeFactors_of_squarefree {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    {n : ℕ} (hn : Squarefree n) : g n = ∏ p ∈ n.primeFactors, g p := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) → g (∏ p ∈ s, p) = ∏ p ∈ s, g p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp [hg1]
    | insert a s ha ih =>
        intro hs
        have ha' : Nat.Prime a := hs a (Finset.mem_insert_self a s)
        have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
          rw [Nat.coprime_prod_right_iff]
          intro p hp
          rw [ha'.coprime_iff_not_dvd]
          intro hdvd
          have hp' : Nat.Prime p := hs' p hp
          have hpe : p = a := (hp'.dvd_iff_eq ha'.ne_one).1 hdvd
          exact ha (hpe ▸ hp)
        rw [hmul a (∏ p ∈ s, p) hcop, ih hs']
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  exact key _ (fun p hp => Nat.prime_of_mem_primeFactors hp)

/-! ### Positivity and summability of the logarithm of the local factors -/

lemma one_sub_g_mul_rpow_pos {g : ℕ → ℝ} (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    {p : ℕ} (hpp : p.Prime) {σ : ℝ} (hσ : 0 < σ) :
    0 < 1 - g p * (p : ℝ) ^ (-σ) := by
  have hr : (p : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.one_le) (by linarith : -σ ≤ 0)
  have hle : g p * (p : ℝ) ^ (-σ) ≤ g p := by
    calc g p * (p : ℝ) ^ (-σ) ≤ g p * 1 := mul_le_mul_of_nonneg_left hr (hp p hpp).1
      _ = g p := by ring
  linarith [(hp p hpp).2]

lemma summable_log_one_sub_g_mul_rpow {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => Real.log (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnn : 0 ≤ C := by
    have h2 : g 2 ≤ C / 2 := hC 2 Nat.prime_two
    have := (hp 2 Nat.prime_two).1
    linarith
  set P0 : ℕ := Nat.ceil (2 * C) + 1 with hP0
  have hP0ge : 2 * C ≤ (P0 : ℝ) := by
    have h1 : 2 * C ≤ ((Nat.ceil (2 * C) : ℕ) : ℝ) := Nat.le_ceil (2 * C)
    have h2 : ((Nat.ceil (2 * C) : ℕ) : ℝ) ≤ (P0 : ℝ) := by
      rw [hP0]; push_cast; linarith
    linarith
  have hev : ∀ᶠ n : ℕ in Filter.cofinite,
      ‖Real.log (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1)‖
        ≤ 2 * C * (n : ℝ) ^ (-(1 + σ)) := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat P0).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hcon
    push_neg at hcon
    have hnP : (P0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcon
    have hbd : ‖Real.log (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1)‖
        ≤ 2 * C * (n : ℝ) ^ (-(1 + σ)) := by
      by_cases hnp : n.Prime
      · rw [if_pos hnp]
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnp.pos
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.one_le
        have hr : (n : ℝ) ^ (-σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith : -σ ≤ 0)
        have hx0 : 0 ≤ g n * (n : ℝ) ^ (-σ) :=
          mul_nonneg (hp n hnp).1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        have hx1 : g n * (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
          have h1 : g n ≤ C / (n : ℝ) := hC n hnp
          have h2 : g n * (n : ℝ) ^ (-σ) ≤ (C / (n : ℝ)) * 1 :=
            mul_le_mul h1 hr (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
          have h3 : C / (n : ℝ) ≤ 1 / 2 := by
            rw [div_le_iff₀ hn0]
            nlinarith
          linarith
        have h4 : ‖Real.log (1 - g n * (n : ℝ) ^ (-σ))‖ ≤ 2 * (g n * (n : ℝ) ^ (-σ)) := by
          have h5 : 1 - g n * (n : ℝ) ^ (-σ) ≤ 1 := by linarith
          rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (by linarith) h5)]
          exact neg_log_one_sub_le hx0 hx1
        have h6 : 2 * (g n * (n : ℝ) ^ (-σ)) ≤ 2 * C * (n : ℝ) ^ (-(1 + σ)) := by
          have h7 : g n * (n : ℝ) ^ (-σ) ≤ C * (n : ℝ) ^ (-(1 + σ)) := by
            calc g n * (n : ℝ) ^ (-σ) ≤ (C / (n : ℝ)) * (n : ℝ) ^ (-σ) :=
                  mul_le_mul_of_nonneg_right (hC n hnp) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              _ = C * (n : ℝ) ^ (-(1 + σ)) := by
                  rw [show (-(1 + σ) : ℝ) = -1 + (-σ) by ring, Real.rpow_add hn0,
                    Real.rpow_neg_one, div_eq_mul_inv]
                  ring
          linarith
        linarith
      · rw [if_neg hnp, Real.log_one, norm_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact absurd hbd hn
  have hsumm : Summable (fun n : ℕ => 2 * C * (n : ℝ) ^ (-(1 + σ))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(1 + σ) < -1)).mul_left (2 * C)
  exact Summable.of_norm_bounded_eventually hsumm hev


/-! ### Summability of prime-supported series -/

lemma summable_prime_dlt_of_bound {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ p : ℕ, p.Prime → f p ≤ C / (p : ℝ))
    (hpos : ∀ p : ℕ, p.Prime → 0 ≤ f p) :
    Summable (fun n : ℕ => if n.Prime then dlt (f n) else 0) := by
  set P0 : ℕ := Nat.ceil (2 * C) + 1 with hP0
  have hP0ge : 2 * C ≤ (P0 : ℝ) := by
    have h1 : 2 * C ≤ ((Nat.ceil (2 * C) : ℕ) : ℝ) := Nat.le_ceil (2 * C)
    have h2 : ((Nat.ceil (2 * C) : ℕ) : ℝ) ≤ (P0 : ℝ) := by
      rw [hP0]; push_cast; linarith
    linarith
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ)) ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left _
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat P0).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hcon
    push_neg at hcon
    have hnP : (P0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcon
    have hbd' : ‖(if n.Prime then dlt (f n) else 0)‖ ≤ 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
      by_cases hnp : n.Prime
      · rw [if_pos hnp]
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnp.pos
        have hx1 : f n ≤ 1 / 2 := by
          have h3 : C / (n : ℝ) ≤ 1 / 2 := by
            rw [div_le_iff₀ hn0]; nlinarith
          linarith [hbd n hnp]
        have hx0 : 0 ≤ f n := hpos n hnp
        have h4 : |dlt (f n)| ≤ 2 * (f n) ^ 2 :=
          abs_dlt_le (by rw [abs_of_nonneg hx0]; linarith)
        have h5 : (f n) ^ 2 ≤ (C / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 (hbd n hnp) 2
        have hneg2 : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.rpow_natCast]
          norm_num
        have h6 : (C / (n : ℝ)) ^ 2 = C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
          rw [hneg2, div_pow, div_eq_mul_inv]
        rw [Real.norm_eq_abs]
        calc |dlt (f n)| ≤ 2 * (f n) ^ 2 := h4
          _ ≤ 2 * (C / (n : ℝ)) ^ 2 := by linarith
          _ = 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by rw [h6]; ring
      · rw [if_neg hnp, norm_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact absurd hbd' hn

lemma summable_prime_dlt_inv :
    Summable (fun n : ℕ => if n.Prime then dlt (1 / (n : ℝ)) else 0) :=
  summable_prime_dlt_of_bound (C := 1) (by norm_num)
    (fun p _ => le_of_eq rfl) (fun p _ => by positivity)

lemma summable_prime_g_rpow {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => if n.Prime then g n * (n : ℝ) ^ (-σ) else 0) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnn : 0 ≤ C := by
    have h2 : g 2 ≤ C / 2 := hC 2 Nat.prime_two
    have := hp 2 Nat.prime_two
    linarith
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * (n : ℝ) ^ (-(1 + σ)))
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + σ) < -1)).mul_left C) fun n => ?_
  by_cases hn : n.Prime
  · rw [if_pos hn, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hp n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
    calc g n * (n : ℝ) ^ (-σ) ≤ (C / (n : ℝ)) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (hC n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * (n : ℝ) ^ (-(1 + σ)) := by
          rw [show (-(1 + σ) : ℝ) = -1 + (-σ) by ring, Real.rpow_add hn0, Real.rpow_neg_one,
            div_eq_mul_inv]
          ring
  · rw [if_neg hn, norm_zero]
    exact mul_nonneg hCnn (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_prime_rpow {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => if n.Prime then (n : ℝ) ^ (-(1 + σ)) else 0) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-(1 + σ)))
    (Real.summable_nat_rpow.mpr (by linarith : -(1 + σ) < -1)) fun n => ?_
  by_cases hn : n.Prime
  · rw [if_pos hn, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  · rw [if_neg hn, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma summable_prime_dlt_g_rpow {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnn : 0 ≤ C := by
    have h2 : g 2 ≤ C / 2 := hC 2 Nat.prime_two
    have := hp 2 Nat.prime_two
    linarith
  set P0 : ℕ := Nat.ceil (2 * C) + 1 with hP0
  have hP0ge : 2 * C ≤ (P0 : ℝ) := by
    have h1 : 2 * C ≤ ((Nat.ceil (2 * C) : ℕ) : ℝ) := Nat.le_ceil (2 * C)
    have h2 : ((Nat.ceil (2 * C) : ℕ) : ℝ) ≤ (P0 : ℝ) := by
      rw [hP0]; push_cast; linarith
    linarith
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ)) ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left _
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat P0).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hcon
    push_neg at hcon
    have hnP : (P0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcon
    have hbd' : ‖(if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0)‖
        ≤ 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
      by_cases hnp : n.Prime
      · rw [if_pos hnp]
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnp.pos
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.one_le
        have hr : (n : ℝ) ^ (-σ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith : -σ ≤ 0)
        have hx0 : 0 ≤ g n * (n : ℝ) ^ (-σ) :=
          mul_nonneg (hp n hnp) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        have hxle : g n * (n : ℝ) ^ (-σ) ≤ C / (n : ℝ) := by
          calc g n * (n : ℝ) ^ (-σ) ≤ (C / (n : ℝ)) * 1 :=
                mul_le_mul (hC n hnp) hr (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
            _ = C / (n : ℝ) := by ring
        have hxhalf : g n * (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
          have h3 : C / (n : ℝ) ≤ 1 / 2 := by
            rw [div_le_iff₀ hn0]; nlinarith
          linarith
        have h4 : |dlt (g n * (n : ℝ) ^ (-σ))| ≤ 2 * (g n * (n : ℝ) ^ (-σ)) ^ 2 :=
          abs_dlt_le (by rw [abs_of_nonneg hx0]; linarith)
        have h5 : (g n * (n : ℝ) ^ (-σ)) ^ 2 ≤ (C / (n : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hx0 hxle 2
        have hneg2 : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.rpow_natCast]
          norm_num
        have h6 : (C / (n : ℝ)) ^ 2 = C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
          rw [hneg2, div_pow, div_eq_mul_inv]
        rw [Real.norm_eq_abs]
        calc |dlt (g n * (n : ℝ) ^ (-σ))| ≤ 2 * (g n * (n : ℝ) ^ (-σ)) ^ 2 := h4
          _ ≤ 2 * (C / (n : ℝ)) ^ 2 := by linarith
          _ = 2 * C ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by rw [h6]; ring
      · rw [if_neg hnp, norm_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact absurd hbd' hn

lemma summable_prime_log_g_rpow {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0) := by
  have h := summable_log_one_sub_g_mul_rpow hp hbound hσ
  refine h.congr fun n => ?_
  by_cases hn : n.Prime <;> simp [hn]

lemma summable_prime_g_sub_inv_rpow {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnn : 0 ≤ C := by
    have h2 : g 2 ≤ C / 2 := hC 2 Nat.prime_two
    have := hp 2 Nat.prime_two
    linarith
  refine Summable.of_norm_bounded (g := fun n : ℕ => (C + 1) * (n : ℝ) ^ (-(1 + σ)))
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + σ) < -1)).mul_left (C + 1)) fun n => ?_
  by_cases hn : n.Prime
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.pos
    rw [if_pos hn]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    have h2 : |g n - 1 / (n : ℝ)| ≤ (C + 1) / (n : ℝ) := by
      have h3 : |g n - 1 / (n : ℝ)| ≤ g n + 1 / (n : ℝ) := by
        have := abs_sub (g n) (1 / (n : ℝ))
        rw [abs_of_nonneg (hp n hn),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(n:ℝ))] at this
        exact this
      rw [le_div_iff₀ hn0]
      have h4 : g n * (n : ℝ) ≤ C := (le_div_iff₀ hn0).mp (hC n hn)
      have h5 : (g n + 1 / (n : ℝ)) * (n : ℝ) = g n * (n : ℝ) + 1 := by
        field_simp
      calc |g n - 1 / (n : ℝ)| * (n : ℝ) ≤ (g n + 1 / (n : ℝ)) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right h3 hn0.le
        _ = g n * (n : ℝ) + 1 := h5
        _ ≤ C + 1 := by linarith
    calc |g n - 1 / (n : ℝ)| * (n : ℝ) ^ (-σ)
        ≤ ((C + 1) / (n : ℝ)) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (C + 1) * (n : ℝ) ^ (-(1 + σ)) := by
          rw [show (-(1 + σ) : ℝ) = -1 + (-σ) by ring, Real.rpow_add hn0, Real.rpow_neg_one,
            div_eq_mul_inv]
          ring
  · rw [if_neg hn]
    simp only [norm_mul, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma norm_one_sub_inv_prime_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-! ### The logarithm of the Dirichlet series -/

lemma dirichlet_eq_exp {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ))
      = Real.exp (∑' n : ℕ, (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0)) := by
  have hep := euler_product_moebius_mul_g_rpow hmul hg1 (fun p h => (hp p h).1) hbound hσ
  have hpos : ∀ n : ℕ, 0 < (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1) := by
    intro n
    by_cases hn : n.Prime
    · rw [if_pos hn]; exact one_sub_g_mul_rpow_pos hp hn hσ
    · rw [if_neg hn]; norm_num
  have hsum := summable_log_one_sub_g_mul_rpow hp hbound hσ
  have hlog : (fun n : ℕ => Real.log (if n.Prime then 1 - g n * (n : ℝ) ^ (-σ) else 1))
      = fun n : ℕ => (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0) := by
    funext n; by_cases hn : n.Prime <;> simp [hn]
  have h := Real.rexp_tsum_eq_tprod hpos hsum
  rw [hep, ← h, hlog]

lemma log_dirichlet_eq {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    {σ : ℝ} (hσ : 0 < σ) :
    Real.log (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ))
      = ∑' n : ℕ, (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0) := by
  rw [dirichlet_eq_exp hmul hg1 hp hbound hσ, Real.log_exp]


/-! ### The shifted prime sums -/

lemma primesBelow_eq_primesLE_pred {N : ℕ} (hN : 1 ≤ N) :
    Nat.primesBelow N = (N - 1).primesLE := by
  ext p
  rw [Nat.mem_primesBelow, Nat.mem_primesLE]
  constructor
  · rintro ⟨hlt, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hle, hp⟩; exact ⟨by omega, hp⟩

lemma primesLE_eq_Icc_filter (N : ℕ) :
    (Finset.Icc 2 N).filter Nat.Prime = N.primesLE := by
  ext p
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨h2, h3⟩, hp⟩; exact ⟨h3, hp⟩
  · rintro ⟨h3, hp⟩; exact ⟨⟨hp.two_le, h3⟩, hp⟩

/-- The second Mertens theorem together with the hypothesis
`∑_{p ≤ y} g p = log log y + c + O((log y)^{-10})` gives `∑_{p < N} (g p - 1/p) → c - M`. -/
lemma tendsto_primesBelow_g_sub_inv {g : ℕ → ℝ} {c M : ℝ}
    (h9 : ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ)))
    (hM : Filter.Tendsto (fun x : ℝ =>
        Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x))
        Filter.atTop (nhds M)) :
    Filter.Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, (g p - 1 / (p : ℝ)))
      Filter.atTop (nhds (c - M)) := by
  obtain ⟨C, hC⟩ := h9
  have hlog_tend : Tendsto (fun y : ℝ => (Real.log y) ^ (-(10 : ℤ))) atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (f := fun y : ℝ => (Real.log y) ^ (-(10 : ℤ)))
      (a := fun y : ℝ => (Real.log y)⁻¹) ?_
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with y hy
    have hlogpos : 0 < Real.log y := by linarith
    have hconv : ((Real.log y) ^ (10 : ℕ))⁻¹ = (Real.log y) ^ (-(10 : ℤ)) := by
      rw [← zpow_natCast, ← zpow_neg]
      norm_num
    have hpow : Real.log y ≤ (Real.log y) ^ (10 : ℕ) := le_self_pow₀ hy (by norm_num)
    rw [← hconv, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((Real.log y) ^ (10:ℕ))⁻¹)]
    exact (inv_le_inv₀ (by positivity) hlogpos).mpr hpow
  have hE1 : Tendsto (fun y : ℝ => (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p)
      - Real.log (Real.log y) - c) atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (f := fun y : ℝ => (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p)
        - Real.log (Real.log y) - c)
      (a := fun y : ℝ => C * (Real.log y) ^ (-(10 : ℤ))) ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
      rw [Real.norm_eq_abs]
      exact hC y hy
    · simpa using hlog_tend.const_mul C
  have hE2 : Tendsto (fun y : ℝ => (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
      - Real.log (Real.log y)) atTop (nhds M) := by
    simpa only [Commons.NumberTheory.Mertens.primeRecips] using hM
  have hcomb : Tendsto (fun y : ℝ => ((∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p))
      - (∑ p ∈ (⌊y⌋₊).primesLE, (1 : ℝ) / (p : ℝ))) atTop (nhds (c - M)) := by
    have h := (hE1.sub hE2).add_const c
    have hlim : (0 - M) + c = c - M := by ring
    rw [hlim] at h
    refine h.congr fun y => ?_
    ring
  have hnat : Tendsto (fun N : ℕ => (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, g p)
      - (∑ p ∈ N.primesLE, (1 : ℝ) / (p : ℝ))) atTop (nhds (c - M)) := by
    have h := hcomb.comp tendsto_natCast_atTop_atTop
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, Nat.floor_natCast]
  have hshift : Tendsto (fun N : ℕ => (∑ p ∈ (Finset.Icc 2 (N - 1)).filter Nat.Prime, g p)
      - (∑ p ∈ (N - 1).primesLE, (1 : ℝ) / (p : ℝ))) atTop (nhds (c - M)) :=
    hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b + 1, fun a ha => by omega⟩))
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [primesLE_eq_Icc_filter (N - 1), primesBelow_eq_primesLE_pred hN]
  rw [Finset.sum_sub_distrib]


/-! ### The main theorem -/

theorem density_eulerProd_div_sigma_tendsto {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ H : ℝ, 0 < H ∧
      Filter.Tendsto (fun σ : ℝ => (∑' d : ℕ,
          (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)) / σ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds H) ∧
      Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
          (1 - g p) / (1 - 1 / (p : ℝ))) Filter.atTop (nhds H) := by
  obtain ⟨c, C9, hC9⟩ := h9
  obtain ⟨Cb, hCb⟩ := hbound
  obtain ⟨M, hM⟩ := Commons.NumberTheory.Mertens.second_mertens_converges
  have hCbnn : 0 ≤ Cb := by
    have h2 : g 2 ≤ Cb / 2 := hCb 2 Nat.prime_two
    have h1 := (hp 2 Nat.prime_two).1
    linarith
  set S1p : ℝ := ∑' n : ℕ, (if n.Prime then dlt (1 / (n : ℝ)) else 0) with hS1p
  set S2 : ℝ := ∑' n : ℕ, (if n.Prime then dlt (g n) else 0) with hS2
  have hS2sum : Summable (fun n : ℕ => if n.Prime then dlt (g n) else 0) :=
    summable_prime_dlt_of_bound hCbnn hCb (fun p h => (hp p h).1)
  have hgamma : M + S1p = Real.eulerMascheroniConstant := by
    have h3 := Commons.NumberTheory.Mertens.prime_euler_constant_identity hM
    have h2a : (∑' n : ℕ, (if n.Prime then dlt (1 / (n : ℝ)) else 0))
        = ∑' n : ℕ, (if n.Prime then
            (Real.log ((n : ℝ) / ((n : ℝ) - 1)) - 1 / (n : ℝ)) else 0) := by
      refine tsum_congr fun n => ?_
      by_cases hn : n.Prime
      · rw [if_pos hn, if_pos hn, dlt_inv_eq hn]
      · rw [if_neg hn, if_neg hn]
    have h2b : (∑' n : ℕ, (if n.Prime then
          (Real.log ((n : ℝ) / ((n : ℝ) - 1)) - 1 / (n : ℝ)) else 0))
        = ∑' p : Nat.Primes,
            (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - 1 / (p : ℝ)) := by
      rw [tsum_primes_eq
        (fun n : ℕ => (Real.log ((n : ℝ) / ((n : ℝ) - 1)) - 1 / (n : ℝ)))]
    rw [← h2b, ← h2a, ← hS1p] at h3
    exact h3
  refine ⟨Real.exp (Real.eulerMascheroniConstant - c - S2), Real.exp_pos _, ?_, ?_⟩
  · have hA1 : Tendsto (fun σ : ℝ => ∑' n : ℕ,
        (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c - M)) := by
      have ha0 : (fun n : ℕ => if n.Prime then g n - 1 / (n : ℝ) else 0) 0 = 0 := by
        show (if (0 : ℕ).Prime then g 0 - 1 / (0 : ℝ) else 0) = 0
        rw [if_neg (by decide : ¬ Nat.Prime 0)]
      have hpartial : Tendsto (fun N : ℕ =>
          ∑ n ∈ Finset.range N, (if n.Prime then g n - 1 / (n : ℝ) else 0))
          atTop (nhds (c - M)) := by
        have h := tendsto_primesBelow_g_sub_inv ⟨C9, hC9⟩ hM
        refine h.congr fun N => ?_
        rw [show Nat.primesBelow N = (Finset.range N).filter Nat.Prime from rfl,
          Finset.sum_filter]
      have habel := Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional
        ha0 hpartial
      refine habel.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ' : 0 < σ := hσ
      have hsum : Summable (fun n : ℕ =>
          (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ)) :=
        summable_prime_g_sub_inv_rpow (fun p h => (hp p h).1) ⟨Cb, hCb⟩ hσ'
      have hcs : HasSum (fun n : ℕ =>
            (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ))
          (∑' n : ℕ, (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ))
          (SummationFilter.conditional ℕ) := by
        rw [Commons.Analysis.DirichletSeries.hasSum_conditionalNat_iff]
        exact hsum.hasSum.tendsto_sum_nat
      exact hcs.tsum_eq
    have hA2 : Tendsto (fun σ : ℝ => (∑' n : ℕ, (if n.Prime then (n : ℝ) ^ (-(1 + σ)) else 0))
        + Real.log σ) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (M - Real.eulerMascheroniConstant)) := by
      have h := Commons.NumberTheory.Mertens.primeSmoothLimit_of_secondMertens hM
      refine h.congr fun σ => ?_
      rw [tsum_primes_eq (fun n : ℕ => (n : ℝ) ^ (-(1 + σ)))]
    have hS2sigma : Tendsto (fun σ : ℝ => ∑' n : ℕ,
        (if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds S2) := by
      refine tendsto_tsum_of_dominated_convergence
        (f := fun (σ : ℝ) (n : ℕ) => (if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0))
        (g := fun (n : ℕ) => (if n.Prime then dlt (g n) else 0))
        (bound := fun (n : ℕ) => (if n.Prime then dlt (g n) else 0)) ?_ ?_ ?_
      · simpa [hS2] using hS2sum
      · intro n
        by_cases hn : n.Prime
        · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
          have hcont1 : ContinuousAt (fun σ : ℝ => (n : ℝ) ^ (-σ)) 0 :=
            ((Real.continuous_const_rpow (ne_of_gt hn0)).comp continuous_neg).continuousAt
          have hlim0 : Tendsto (fun σ : ℝ => g n * (n : ℝ) ^ (-σ)) (nhds (0 : ℝ)) (nhds (g n)) := by
            have h : ContinuousAt (fun σ : ℝ => g n * (n : ℝ) ^ (-σ)) 0 :=
              (continuousAt_const (y := g n)).mul hcont1
            simpa [Real.rpow_zero] using h.tendsto
          have hlim : Tendsto (fun σ : ℝ => dlt (g n * (n : ℝ) ^ (-σ))) (nhds (0 : ℝ))
              (nhds (dlt (g n))) :=
            (continuousAt_dlt (hp n hn).2).tendsto.comp hlim0
          simp only [if_pos hn]
          exact hlim.mono_left nhdsWithin_le_nhds
        · simp [if_neg hn]
      · filter_upwards [self_mem_nhdsWithin] with σ hσ n
        have hσ' : 0 < σ := hσ
        by_cases hn : n.Prime
        · rw [if_pos hn, if_pos hn]
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
          have hr : (n : ℝ) ^ (-σ) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith : -σ ≤ 0)
          have hx0 : 0 ≤ g n * (n : ℝ) ^ (-σ) :=
            mul_nonneg (hp n hn).1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          have hxy : g n * (n : ℝ) ^ (-σ) ≤ g n := by
            calc g n * (n : ℝ) ^ (-σ) ≤ g n * 1 :=
                  mul_le_mul_of_nonneg_left hr (hp n hn).1
              _ = g n := by ring
          rw [Real.norm_eq_abs, abs_of_nonneg (dlt_nonneg (lt_of_le_of_lt hxy (hp n hn).2))]
          exact dlt_mono hx0 hxy (hp n hn).2
        · simp [if_neg hn]
    have hL : Tendsto (fun σ : ℝ => (∑' n : ℕ,
        (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0)) - Real.log σ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.eulerMascheroniConstant - c - S2)) := by
      have hcomb := (hA1.neg.sub hA2).sub hS2sigma
      have hlim : -(c - M) - (M - Real.eulerMascheroniConstant) - S2
          = Real.eulerMascheroniConstant - c - S2 := by ring
      rw [hlim] at hcomb
      refine hcomb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ' : 0 < σ := hσ
      have hS1 : Summable (fun n : ℕ =>
          (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ)) :=
        summable_prime_g_sub_inv_rpow (fun p h => (hp p h).1) ⟨Cb, hCb⟩ hσ'
      have hS2s : Summable (fun n : ℕ => if n.Prime then (n : ℝ) ^ (-(1 + σ)) else 0) :=
        summable_prime_rpow hσ'
      have hS3 : Summable (fun n : ℕ => if n.Prime then g n * (n : ℝ) ^ (-σ) else 0) :=
        summable_prime_g_rpow (fun p h => (hp p h).1) ⟨Cb, hCb⟩ hσ'
      have hS4 : Summable (fun n : ℕ => if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0) :=
        summable_prime_dlt_g_rpow (fun p h => (hp p h).1) ⟨Cb, hCb⟩ hσ'
      have hsplit : (∑' n : ℕ, (if n.Prime then g n * (n : ℝ) ^ (-σ) else 0))
          = (∑' n : ℕ, (if n.Prime then g n - 1 / (n : ℝ) else 0) * (n : ℝ) ^ (-σ))
            + ∑' n : ℕ, (if n.Prime then (n : ℝ) ^ (-(1 + σ)) else 0) := by
        rw [← hS1.tsum_add hS2s]
        refine tsum_congr fun n => ?_
        by_cases hn : n.Prime
        · rw [if_pos hn, if_pos hn, if_pos hn]
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
          rw [show (-(1 + σ) : ℝ) = -1 + (-σ) by ring, Real.rpow_add hn0, Real.rpow_neg_one,
            div_eq_mul_inv]
          ring
        · simp [if_neg hn]
      have hlogsplit : (∑' n : ℕ, (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0))
          = -(∑' n : ℕ, (if n.Prime then g n * (n : ℝ) ^ (-σ) else 0))
            - ∑' n : ℕ, (if n.Prime then dlt (g n * (n : ℝ) ^ (-σ)) else 0) := by
        have h := hS3.neg.tsum_sub hS4
        rw [tsum_neg] at h
        rw [← h]
        refine tsum_congr fun n => ?_
        by_cases hn : n.Prime
        · rw [if_pos hn, if_pos hn, if_pos hn, log_one_sub_eq]
        · simp [if_neg hn]
      rw [hlogsplit, hsplit]
      ring
    refine (Real.continuous_exp.continuousAt.tendsto.comp hL).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : 0 < σ := hσ
    have hD := dirichlet_eq_exp hmul hg1 hp ⟨Cb, hCb⟩ hσ'
    have hinv : Real.exp (-Real.log σ) = σ⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hσ']
    show Real.exp ((∑' n : ℕ,
        (if n.Prime then Real.log (1 - g n * (n : ℝ) ^ (-σ)) else 0)) - Real.log σ)
      = (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) * g d * (d : ℝ) ^ (-σ)) / σ
    rw [hD, div_eq_mul_inv, ← hinv, ← Real.exp_add, sub_eq_add_neg]
  · have hsum1 : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, (1 / (p : ℝ) - g p))
        atTop (nhds (M - c)) := by
      have h := (tendsto_primesBelow_g_sub_inv ⟨C9, hC9⟩ hM).neg
      have hlim : -(c - M) = M - c := by ring
      rw [hlim] at h
      refine h.congr fun N => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hsum2 : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, dlt (g p))
        atTop (nhds S2) := by
      have h := hS2sum.hasSum.tendsto_sum_nat
      rw [← hS2] at h
      refine h.congr fun N => ?_
      rw [show Nat.primesBelow N = (Finset.range N).filter Nat.Prime from rfl,
        Finset.sum_filter]
    have hsum3 : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, dlt (1 / (p : ℝ)))
        atTop (nhds S1p) := by
      have h := summable_prime_dlt_inv.hasSum.tendsto_sum_nat
      rw [← hS1p] at h
      refine h.congr fun N => ?_
      rw [show Nat.primesBelow N = (Finset.range N).filter Nat.Prime from rfl,
        Finset.sum_filter]
    have hK : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N,
        (Real.log (1 - g p) - Real.log (1 - 1 / (p : ℝ)))) atTop
        (nhds (Real.eulerMascheroniConstant - c - S2)) := by
      have hcomb := (hsum1.sub hsum2).add hsum3
      have hlim : (M - c) - S2 + S1p = Real.eulerMascheroniConstant - c - S2 := by
        linarith [hgamma]
      rw [hlim] at hcomb
      refine hcomb.congr fun N => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [log_one_sub_eq, log_one_sub_eq]
      ring
    refine (Real.continuous_exp.continuousAt.tendsto.comp hK).congr fun N => ?_
    show Real.exp (∑ p ∈ Nat.primesBelow N,
        (Real.log (1 - g p) - Real.log (1 - 1 / (p : ℝ))))
      = ∏ p ∈ Nat.primesBelow N, (1 - g p) / (1 - 1 / (p : ℝ))
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun p hmem => ?_
    have hpp : Nat.Prime p := (Nat.mem_primesBelow.mp hmem).2
    rw [Real.exp_sub, Real.exp_log (by linarith [(hp p hpp).2] : (0 : ℝ) < 1 - g p),
      Real.exp_log (norm_one_sub_inv_prime_pos hpp)]


end

end Commons.NumberTheory.Sieve
