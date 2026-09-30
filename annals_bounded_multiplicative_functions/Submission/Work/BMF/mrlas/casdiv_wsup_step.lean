import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.HL.sum_log_div_prime_le
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp
import Submission.Work.BMF.ioc_abel_identity
import Submission.Work.BMF.sum_Icc_sub_telescope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex

/-!
# Almost-monotonicity of `exp ∘ Wsup` in the exponent `α`

Target: `Work.BMF.mrlas.casdiv_wsup_step`.  Route:

1. both summands of `vF` share the phase `(p:ℂ)^{-(t*I)}`, so
   `(f p · p^{-(1+α)-tI}).re = p^{-(1+α)} · (f p · p^{-tI}).re` (`re_mul_cpow_eq`);
2. termwise comparison of the summands with exponents `b ≥ a` (`re_cpow_exp_diff_le`);
3. the sup-level sandwich `Wsup f x b T ≤ Wsup f x a T + Σ_p (p^{-(1+a)} - p^{-(1+b)})`
   (`Wsup_le_Wsup_add_rpow_diff`);
4. the arithmetic bounds `Σ_{p ≤ x} (log p) p^{-(1+a)} ≤ K/a` (`casdiv_prime_log_rpow_sum_le`) and
   `Σ_p (p^{-(1+a)} - p^{-(1+b)}) ≤ C'` (`prime_rpow_diff_sum_le`);
5. exponentiation of the sandwich.
-/

/-- **Splitting off the phase.**  For a prime `p` and reals `α, t`,
`(f p · p^{-(1+α)-it}).re = p^{-(1+α)} · (f p · p^{-it}).re`. -/
lemma re_mul_cpow_eq (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (α t : ℝ) :
    (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
      = (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(t * Complex.I))).re := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  have hsplit : -((1 + α : ℝ) + t * Complex.I)
      = Complex.ofReal (-(1 + α)) + (-(t * Complex.I)) := by
    push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hp0]
  have hof : (p : ℂ) ^ (Complex.ofReal (-(1 + α)))
      = Complex.ofReal ((p : ℝ) ^ (-(1 + α))) := by
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-(1 + α))).symm
  rw [hof]
  rw [show (f p * (Complex.ofReal ((p : ℝ) ^ (-(1 + α))) * (p : ℂ) ^ (-(t * Complex.I))))
      = Complex.ofReal ((p : ℝ) ^ (-(1 + α))) * (f p * (p : ℂ) ^ (-(t * Complex.I))) by ring]
  rw [Complex.re_ofReal_mul]

/-- The phase `p^{-it}` is a unit complex number for `0 < p`. -/
lemma norm_cpow_neg_mul_I (p : ℕ) (hp : 0 < p) (t : ℝ) : ‖(p : ℂ) ^ (-(t * Complex.I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  have hre : (-(t * Complex.I)).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- `‖f p · p^{-it}‖ ≤ 1` for a `1`-bounded `f` and `0 < p`. -/
lemma norm_mul_cpow_neg_mul_I_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : 0 < p)
    (t : ℝ) : ‖f p * (p : ℂ) ^ (-(t * Complex.I))‖ ≤ 1 := by
  rw [norm_mul, norm_cpow_neg_mul_I p hp, mul_one]
  exact hf p

/-- **Pointwise comparison of the summands with exponents `b ≥ a`.** -/
theorem re_cpow_exp_diff_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {a b t : ℝ} (hab : a ≤ b) :
    (f p * (p : ℂ) ^ (-((1 + b : ℝ) + t * Complex.I))).re
      ≤ (f p * (p : ℂ) ^ (-((1 + a : ℝ) + t * Complex.I))).re
        + ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))) := by
  rw [re_mul_cpow_eq f hp b t, re_mul_cpow_eq f hp a t]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h := hp.two_le
    exact_mod_cast (by omega : 1 ≤ p)
  have hba : (p : ℝ) ^ (-(1 + b)) ≤ (p : ℝ) ^ (-(1 + a)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hc : -(1 : ℝ) ≤ (f p * (p : ℂ) ^ (-(t * Complex.I))).re := by
    have h1 : |(f p * (p : ℂ) ^ (-(t * Complex.I))).re| ≤ 1 :=
      le_trans (Complex.abs_re_le_norm _) (norm_mul_cpow_neg_mul_I_le f hf hp.pos t)
    exact (abs_le.mp h1).1
  have hprod : ((p : ℝ) ^ (-(1 + b)) - (p : ℝ) ^ (-(1 + a)))
      * ((f p * (p : ℂ) ^ (-(t * Complex.I))).re + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-- `Re vF f x ((1+α) + it) ≤ Zrcp x` for `α ≥ 0` and a `1`-bounded `f`. -/
lemma re_vF_le_Zrcp (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    ∀ t : ℝ, (vF f x ((1 + α : ℝ) + t * Complex.I)).re ≤ Zrcp x := by
  intro t
  rw [vF, Zrcp]
  rw [show (∑ p ∈ (⌊x⌋₊).primesLE, f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
      = ∑ p ∈ (⌊x⌋₊).primesLE,
          (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
      from map_sum Complex.reAddGroupHom _ _]
  exact Finset.sum_le_sum (fun p hp =>
    re_mul_cpow_le_inv f hf (Nat.prime_of_mem_primesLE hp) α t hα)

/-- **The sup-level sandwich, taking the exponent down from `b` to `a`.** -/
theorem Wsup_le_Wsup_add_rpow_diff (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Wsup f x b T ≤ Wsup f x a T +
      ∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))) := by
  set D : ℝ := ∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))) with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    refine Finset.sum_nonneg fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have h := (Nat.prime_of_mem_primesLE hp).two_le
      exact_mod_cast (by omega : 1 ≤ p)
    have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -(1 + b) ≤ -(1 + a) by linarith)
    linarith
  have key : ∀ t : {t : ℝ // |t| ≤ T},
      (vF f x ((1 + b : ℝ) + t.1 * Complex.I)).re ≤ Wsup f x a T + D := by
    intro t
    have h1 : (vF f x ((1 + b : ℝ) + t.1 * Complex.I)).re
        ≤ (vF f x ((1 + a : ℝ) + t.1 * Complex.I)).re + D := by
      rw [vF, vF, hD]
      rw [show (∑ p ∈ (⌊x⌋₊).primesLE,
            f p * (p : ℂ) ^ (-((1 + b : ℝ) + t.1 * Complex.I))).re
          = ∑ p ∈ (⌊x⌋₊).primesLE,
              (f p * (p : ℂ) ^ (-((1 + b : ℝ) + t.1 * Complex.I))).re
          from map_sum Complex.reAddGroupHom _ _]
      rw [show (∑ p ∈ (⌊x⌋₊).primesLE,
            f p * (p : ℂ) ^ (-((1 + a : ℝ) + t.1 * Complex.I))).re
          = ∑ p ∈ (⌊x⌋₊).primesLE,
              (f p * (p : ℂ) ^ (-((1 + a : ℝ) + t.1 * Complex.I))).re
          from map_sum Complex.reAddGroupHom _ _]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun p hp =>
        re_cpow_exp_diff_le f hf (Nat.prime_of_mem_primesLE hp) hab)
    have h2 : (vF f x ((1 + a : ℝ) + t.1 * Complex.I)).re ≤ Wsup f x a T := by
      have hBdd : BddAbove (Set.range (fun s : {s : ℝ // |s| ≤ T} =>
          (vF f x ((1 + a : ℝ) + s.1 * Complex.I)).re)) :=
        ⟨Zrcp x, by rintro y ⟨s, rfl⟩; exact re_vF_le_Zrcp f hf x ha s.1⟩
      exact le_ciSup hBdd t
    linarith
  unfold Wsup
  by_cases hT : 0 ≤ T
  · haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by simp [abs_zero]; exact hT⟩⟩
    exact ciSup_le key
  · have hE : IsEmpty {t : ℝ // |t| ≤ T} :=
      ⟨fun t => hT (le_trans (abs_nonneg t.1) t.2)⟩
    have hz : ∀ α : ℝ, (⨆ (t : {t : ℝ // |t| ≤ T}),
        (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re) = 0 := by
      intro α
      rw [show (⨆ (t : {t : ℝ // |t| ≤ T}),
          (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)
          = sSup (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
              (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) from rfl]
      rw [Set.range_eq_empty_iff.mpr hE, Real.sSup_empty]
    rw [hz b, hz a]
    linarith

/-! ### The arithmetic input: `Σ_{p ≤ x} (log p) · p^{-(1+a)} ≤ K/a`

Elementary: the head `p ≤ exp (1/a)` is controlled by Mertens
(`Work.BMF.HL.sum_log_div_prime_le`), the tail by partial summation against Chebyshev's
`θ t ≤ log 4 · t`. -/

/-- Real form of the discrete Abel identity on `Ioc` (the `ℂ`-valued
`Work.BMF.ioc_abel_identity` read through `Complex.ofReal`). -/
lemma abel_identity_real (c w A : ℕ → ℝ) (N M : ℕ) (hA0 : A N = 0)
    (hstep : ∀ k, N ≤ k → A (k + 1) = A k + c (k + 1)) (hNM : N < M) :
    ∑ n ∈ Finset.Ioc N M, w n * c n
      = w M * A M + ∑ n ∈ Finset.Ioc N (M - 1), (w n - w (n + 1)) * A n := by
  have h := Work.BMF.ioc_abel_identity (fun n => (c n : ℂ)) (fun n => (w n : ℂ))
    (fun n => (A n : ℂ)) N M (by simp [hA0]) (fun k hk => by simp [hstep k hk]) hNM
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
    ← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

/-- Chebyshev's `θ` increases by exactly `log (k+1)` at the prime `k+1`. -/
lemma theta_succ_sub (k : ℕ) :
    Chebyshev.theta ((k + 1 : ℕ) : ℝ) - Chebyshev.theta (k : ℝ)
      = if (k + 1).Prime then Real.log ((k + 1 : ℕ) : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log (k + 1), Chebyshev.theta_eq_sum_primesLE_log k,
    Nat.primesLE_succ]
  by_cases hp : Nat.Prime (k + 1)
  · rw [if_pos hp, if_pos hp,
      Finset.sum_insert (by simp only [Nat.mem_primesLE, not_and]; omega)]
    ring
  · rw [if_neg hp, if_neg hp, sub_self]

/-- The telescoping inequality `n·(n^{-(1+a)} - (n+1)^{-(1+a)}) ≤ (1+1/a)(n^{-a} - (n+1)^{-a})`
for `n ≥ 1` and `0 < a ≤ 1`.  With `h := 1/(n+1)` this is the pair of Bernoulli inequalities
`1 - (1-h)^(1+a) ≤ (1+a)h` and `a·h ≤ 1 - (1-h)^a`. -/
lemma mul_rpow_sub_le {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (n : ℝ) * ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)))
      ≤ (1 + 1 / a) * ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a)) := by
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  set x : ℝ := (n : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hxp : 0 < x + 1 := by linarith
  set h : ℝ := 1 / (x + 1) with hh
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by rw [hh, div_le_one hxp]; linarith
  have hxh : 1 - h = x / (x + 1) := by
    rw [hh]
    field_simp
    ring
  have hB1 : 1 - (1 - h) ^ (1 + a) ≤ (1 + a) * h := by
    have hs : -1 ≤ -h := by linarith
    have hbm := one_add_mul_self_le_rpow_one_add (s := -h) hs (p := 1 + a) (by linarith)
    simp only [show (1 : ℝ) + -h = 1 - h by ring,
      show (1 : ℝ) + (1 + a) * (-h) = 1 - (1 + a) * h by ring] at hbm
    linarith
  have hB2 : a * h ≤ 1 - (1 - h) ^ a := by
    have hs : -1 ≤ -h := by linarith
    have hbm := rpow_one_add_le_one_add_mul_self (s := -h) hs (p := a) ha.le ha1
    simp only [show (1 : ℝ) + -h = 1 - h by ring,
      show (1 : ℝ) + a * (-h) = 1 - a * h by ring] at hbm
    linarith
  have hpow1 : (1 - h) ^ (1 + a) = x ^ (1 + a) * (x + 1) ^ (-(1 + a)) := by
    rw [hxh, Real.div_rpow hx0.le hxp.le, div_eq_mul_inv, ← Real.rpow_neg hxp.le]
  have hpow2 : (1 - h) ^ a = x ^ a * (x + 1) ^ (-a) := by
    rw [hxh, Real.div_rpow hx0.le hxp.le, div_eq_mul_inv, ← Real.rpow_neg hxp.le]
  have hxa' : x ^ (1 : ℝ) * x ^ (-(1 + a)) = x ^ (-a) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hxa : x * x ^ (-(1 + a)) = x ^ (-a) := by
    simpa [Real.rpow_one] using hxa'
  have key1 : x ^ (-a) * (x ^ (1 + a) * (x + 1) ^ (-(1 + a))) = x * (x + 1) ^ (-(1 + a)) := by
    rw [← mul_assoc, ← Real.rpow_add hx0, show -a + (1 + a) = 1 by ring, Real.rpow_one]
  have key2 : x ^ (-a) * (x ^ a * (x + 1) ^ (-a)) = (x + 1) ^ (-a) := by
    rw [← mul_assoc, ← Real.rpow_add hx0, show -a + a = 0 by ring, Real.rpow_zero, one_mul]
  have hL : x * (x ^ (-(1 + a)) - (x + 1) ^ (-(1 + a)))
      = x ^ (-a) * (1 - (1 - h) ^ (1 + a)) := by
    calc x * (x ^ (-(1 + a)) - (x + 1) ^ (-(1 + a)))
        = x * x ^ (-(1 + a)) - x * (x + 1) ^ (-(1 + a)) := by ring
      _ = x ^ (-a) - x * (x + 1) ^ (-(1 + a)) := by rw [hxa]
      _ = x ^ (-a) - x ^ (-a) * (x ^ (1 + a) * (x + 1) ^ (-(1 + a))) := by rw [← key1]
      _ = x ^ (-a) * 1 - x ^ (-a) * (x ^ (1 + a) * (x + 1) ^ (-(1 + a))) := by rw [mul_one]
      _ = x ^ (-a) * (1 - x ^ (1 + a) * (x + 1) ^ (-(1 + a))) := by ring
      _ = x ^ (-a) * (1 - (1 - h) ^ (1 + a)) := by rw [hpow1]
  have hR : x ^ (-a) - (x + 1) ^ (-a) = x ^ (-a) * (1 - (1 - h) ^ a) := by
    calc x ^ (-a) - (x + 1) ^ (-a)
        = x ^ (-a) - x ^ (-a) * (x ^ a * (x + 1) ^ (-a)) := by
            conv_lhs => rw [← key2]
      _ = x ^ (-a) * 1 - x ^ (-a) * (x ^ a * (x + 1) ^ (-a)) := by rw [mul_one]
      _ = x ^ (-a) * (1 - x ^ a * (x + 1) ^ (-a)) := by ring
      _ = x ^ (-a) * (1 - (1 - h) ^ a) := by rw [hpow2]
  rw [hL, hR]
  have hxna : 0 ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
  have hca : 0 ≤ 1 + 1 / a := by positivity
  have hmid : x ^ (-a) * ((1 + a) * h) = (1 + 1 / a) * (x ^ (-a) * (a * h)) := by
    have he : (1 + 1 / a) * a = 1 + a := by
      field_simp
      ring
    rw [← he]
    ring
  calc x ^ (-a) * (1 - (1 - h) ^ (1 + a))
      ≤ x ^ (-a) * ((1 + a) * h) := mul_le_mul_of_nonneg_left hB1 hxna
    _ = (1 + 1 / a) * (x ^ (-a) * (a * h)) := hmid
    _ ≤ (1 + 1 / a) * (x ^ (-a) * (1 - (1 - h) ^ a)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB2 hxna) hca

/-- Telescoping: `Σ_{n ∈ Ioc N (M-1)} (n^{-a} - (n+1)^{-a}) ≤ N^{-a} - M^{-a}` for `1 ≤ N ≤ M`. -/
lemma sum_Ioc_rpow_sub_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {a : ℝ} (ha : 0 < a) :
    ∑ n ∈ Finset.Ioc N (M - 1), ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a))
      ≤ (N : ℝ) ^ (-a) - (M : ℝ) ^ (-a) := by
  have hcast : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := fun n => by push_cast; ring
  have hmono : ∀ n : ℕ, 1 ≤ n → (((n + 1 : ℕ) : ℝ)) ^ (-a) ≤ (n : ℝ) ^ (-a) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hcast n]
    exact Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by linarith)
  have hsub : Finset.Ioc N (M - 1) ⊆ Finset.Icc N (M - 1) := by
    intro k hk
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    omega
  calc ∑ n ∈ Finset.Ioc N (M - 1), ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a))
      ≤ ∑ n ∈ Finset.Icc N (M - 1), ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro n hn _
        have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
        exact sub_nonneg.mpr (hmono n hn1)
    _ = (N : ℝ) ^ (-a) - (M : ℝ) ^ (-a) := by
        rw [Work.BMF.sum_Icc_sub_telescope (fun n : ℕ => (n : ℝ) ^ (-a)) N (M - 1) (by omega),
          Nat.sub_add_cancel (show 1 ≤ M by omega)]

/-- **Tail bound.**  For `1 ≤ N ≤ M` and `0 < a ≤ 1`,
`Σ_{N < p ≤ M} (log p)·p^{-(1+a)} ≤ log 4 · M^{-a} + log 4 (1 + 1/a)(N^{-a} - M^{-a})`. -/
lemma prime_tail_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∑ p ∈ M.primesLE \ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
      ≤ Real.log 4 * (M : ℝ) ^ (-a)
        + Real.log 4 * (1 + 1 / a) * ((N : ℝ) ^ (-a) - (M : ℝ) ^ (-a)) := by
  have hset : (M.primesLE \ N.primesLE : Finset ℕ) = (Finset.Ioc N M).filter Nat.Prime := by
    ext p
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpM, hpp⟩, hpN⟩
      exact ⟨⟨Nat.lt_of_not_le fun h => hpN ⟨h, hpp⟩, hpM⟩, hpp⟩
    · rintro ⟨⟨hNp, hpM⟩, hpp⟩
      exact ⟨⟨hpM, hpp⟩, fun h => absurd h.1 (not_le.mpr hNp)⟩
  rw [hset, Finset.sum_filter]
  have hconv : (∑ n ∈ Finset.Ioc N M,
        (if Nat.Prime n then Real.log n * (n : ℝ) ^ (-(1 + a)) else 0))
      = ∑ n ∈ Finset.Ioc N M,
          ((n : ℝ) ^ (-(1 + a)) * (if Nat.Prime n then Real.log n else 0)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hnp : Nat.Prime n
    · rw [if_pos hnp, if_pos hnp, mul_comm]
    · rw [if_neg hnp, if_neg hnp, mul_zero]
  rw [hconv]
  have hM1 : 1 ≤ M := le_trans hN hNM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  rcases lt_or_eq_of_le hNM with hlt | heq
  · set A : ℕ → ℝ := fun n => Chebyshev.theta (n : ℝ) - Chebyshev.theta (N : ℝ) with hA
    have hA0 : A N = 0 := by simp [hA]
    have hstep : ∀ k, N ≤ k → A (k + 1) = A k + (fun m => if Nat.Prime m then Real.log m else 0) (k + 1) := by
      intro k _
      have h := theta_succ_sub k
      simp only [hA]
      linarith
    have hAb := abel_identity_real (fun m => if Nat.Prime m then Real.log m else 0)
      (fun m => (m : ℝ) ^ (-(1 + a))) A N M hA0 hstep hlt
    have hA_le : ∀ n, 1 ≤ n → A n ≤ Real.log 4 * (n : ℝ) := by
      intro n hn
      have h1 : Chebyshev.theta (n : ℝ) ≤ Real.log 4 * (n : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
      have h2 : 0 ≤ Chebyshev.theta (N : ℝ) := Chebyshev.theta_nonneg _
      simp only [hA]
      linarith
    have hMterm : (M : ℝ) ^ (-(1 + a)) * A M ≤ Real.log 4 * (M : ℝ) ^ (-a) := by
      have hw0 : 0 ≤ (M : ℝ) ^ (-(1 + a)) := Real.rpow_nonneg hMpos.le _
      have h1 : (M : ℝ) ^ (-(1 + a)) * A M ≤ (M : ℝ) ^ (-(1 + a)) * (Real.log 4 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (hA_le M hM1) hw0
      have hkey : (M : ℝ) ^ (-(1 + a)) * (M : ℝ) = (M : ℝ) ^ (-a) := by
        have h' : (M : ℝ) ^ (-(1 + a)) * (M : ℝ) ^ (1 : ℝ) = (M : ℝ) ^ (-a) := by
          rw [← Real.rpow_add hMpos]
          congr 1
          ring
        simpa [Real.rpow_one] using h'
      have h2 : (M : ℝ) ^ (-(1 + a)) * (Real.log 4 * (M : ℝ)) = Real.log 4 * (M : ℝ) ^ (-a) := by
        calc (M : ℝ) ^ (-(1 + a)) * (Real.log 4 * (M : ℝ))
            = Real.log 4 * ((M : ℝ) ^ (-(1 + a)) * (M : ℝ)) := by ring
          _ = Real.log 4 * (M : ℝ) ^ (-a) := by rw [hkey]
      linarith
    have hsumterm : (∑ n ∈ Finset.Ioc N (M - 1),
          ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a))) * A n)
        ≤ Real.log 4 * (1 + 1 / a) * ((N : ℝ) ^ (-a) - (M : ℝ) ^ (-a)) := by
      have hlog4 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
      have hca : 0 ≤ 1 + 1 / a := by positivity
      have hcast : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := fun n => by push_cast; ring
      calc (∑ n ∈ Finset.Ioc N (M - 1),
            ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a))) * A n)
          ≤ ∑ n ∈ Finset.Ioc N (M - 1),
              Real.log 4 * ((n : ℝ) * ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)))) := by
            refine Finset.sum_le_sum fun n hn => ?_
            rw [Finset.mem_Ioc] at hn
            have hn1 : 1 ≤ n := le_trans hN (le_of_lt hn.1)
            have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
            have hmono : (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)) ≤ (n : ℝ) ^ (-(1 + a)) := by
              rw [hcast n]
              exact Real.rpow_le_rpow_of_nonpos hnp (by linarith) (by linarith)
            have hw0 : 0 ≤ (n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)) := by linarith
            have := mul_le_mul_of_nonneg_left (hA_le n hn1) hw0
            calc ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a))) * A n
                ≤ ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)))
                    * (Real.log 4 * (n : ℝ)) := this
              _ = Real.log 4 * ((n : ℝ) * ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)))) := by
                  ring
        _ = Real.log 4 * ∑ n ∈ Finset.Ioc N (M - 1),
              ((n : ℝ) * ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a)))) := by
            rw [Finset.mul_sum]
        _ ≤ Real.log 4 * ∑ n ∈ Finset.Ioc N (M - 1),
              (1 + 1 / a) * ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) hlog4
            rw [Finset.mem_Ioc] at hn
            exact mul_rpow_sub_le (le_trans hN (le_of_lt hn.1)) ha ha1
        _ = Real.log 4 * (1 + 1 / a) * ∑ n ∈ Finset.Ioc N (M - 1),
              ((n : ℝ) ^ (-a) - (((n + 1 : ℕ) : ℝ)) ^ (-a)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
        _ ≤ Real.log 4 * (1 + 1 / a) * ((N : ℝ) ^ (-a) - (M : ℝ) ^ (-a)) :=
            mul_le_mul_of_nonneg_left (sum_Ioc_rpow_sub_le hN hNM ha) (mul_nonneg hlog4 hca)
    have hAb' : (∑ n ∈ Finset.Ioc N M,
          (n : ℝ) ^ (-(1 + a)) * (if Nat.Prime n then Real.log n else 0))
        = (M : ℝ) ^ (-(1 + a)) * A M
          + ∑ n ∈ Finset.Ioc N (M - 1),
              ((n : ℝ) ^ (-(1 + a)) - (((n + 1 : ℕ) : ℝ)) ^ (-(1 + a))) * A n := by
      simpa only [Nat.cast_add, Nat.cast_one] using hAb
    linarith [hAb', hMterm, hsumterm]
  · subst heq
    rw [Finset.Ioc_self, Finset.sum_empty, sub_self, mul_zero, add_zero]
    exact mul_nonneg (Real.log_pos (by norm_num)).le (Real.rpow_nonneg (by positivity) _)

/-- **Uniform bound `Σ_{p ≤ x} (log p) · p^{-(1+a)} ≤ K/a`.** -/
theorem casdiv_prime_log_rpow_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (x a : ℝ), 2 ≤ x → 0 < a → a ≤ 1 →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p : ℝ) ^ (-(1 + a))) ≤ K / a := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.BMF.HL.sum_log_div_prime_le
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1 + 1, ?_, ?_⟩
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    have h5 : 0 < 4 * Real.log 4 / Real.exp 1 := div_pos (by linarith) he
    linarith
  · intro x a hx ha ha1
    have hterm_gen : ∀ p : ℕ, Nat.Prime p →
        Real.log p * (p : ℝ) ^ (-(1 + a)) ≤ Real.log p / (p : ℝ) := by
      intro p hpp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
      have hle : (p : ℝ) ^ (-(1 + a)) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      rw [Real.rpow_neg_one] at hle
      calc Real.log p * (p : ℝ) ^ (-(1 + a))
          ≤ Real.log p * ((p : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hle hlogp
        _ = Real.log p / (p : ℝ) := by rw [div_eq_mul_inv]
    set y : ℝ := Real.exp (1 / a) with hy
    have hypos : 0 < y := by rw [hy]; exact Real.exp_pos _
    have hy2 : 2 ≤ y := by
      rw [hy]
      exact le_trans (le_of_lt Real.exp_one_gt_two)
        (Real.exp_le_exp.mpr (by rw [one_le_div ha]; exact ha1))
    have hlogy : Real.log y = 1 / a := by rw [hy, Real.log_exp]
    by_cases hxy : x < y
    · have hxpos : (0 : ℝ) < x := by linarith
      calc (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
          ≤ ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / (p : ℝ) :=
            Finset.sum_le_sum fun p hp => hterm_gen p (Nat.prime_of_mem_primesLE hp)
        _ ≤ CL * Real.log x := hCL x hx
        _ ≤ CL * (1 / a) := by
            refine mul_le_mul_of_nonneg_left ?_ hCLpos.le
            rw [← hlogy]
            exact Real.log_le_log hxpos hxy.le
        _ ≤ (CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1 + 1) / a := by
            rw [mul_one_div]
            refine div_le_div_of_nonneg_right ?_ ha.le
            have h5 : 0 < 4 * Real.log 4 / Real.exp 1 := div_pos (by linarith) (Real.exp_pos 1)
            linarith
    · have hyx : y ≤ x := not_lt.mp hxy
      set N : ℕ := ⌊y⌋₊ with hNdef
      set M : ℕ := ⌊x⌋₊ with hMdef
      have hN1 : 1 ≤ N := by
        rw [hNdef]
        exact Nat.le_floor (by push_cast; linarith)
      have hNM : N ≤ M := by
        rw [hNdef, hMdef]
        exact Nat.floor_mono hyx
      have hM1 : 1 ≤ M := le_trans hN1 hNM
      have hfirst : (∑ p ∈ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a))) ≤ CL / a := by
        calc (∑ p ∈ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
            ≤ ∑ p ∈ N.primesLE, Real.log p / (p : ℝ) :=
              Finset.sum_le_sum fun p hp => hterm_gen p (Nat.prime_of_mem_primesLE hp)
          _ ≤ CL * Real.log y := by
              rw [hNdef]
              exact hCL y hy2
          _ = CL / a := by rw [hlogy]; ring
      have hMa : (M : ℝ) ^ (-a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM1) (by linarith)
      have hNa : (N : ℝ) ^ (-a) ≤ 2 / Real.exp 1 := by
        have hNge : y / 2 ≤ (N : ℝ) := by
          rw [hNdef]
          have h := Nat.lt_floor_add_one y
          linarith
        have h1 : (N : ℝ) ^ (-a) ≤ (y / 2) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hNge (by linarith)
        have hya : y ^ a = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hypos, hlogy]
          congr 1
          field_simp
        have h2 : (y / 2) ^ (-a) = 2 ^ a / Real.exp 1 := by
          rw [Real.div_rpow hypos.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg hypos.le a,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a, hya, div_inv_eq_mul,
            div_eq_mul_inv]
          ring
        have h3 : (2 : ℝ) ^ a ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
        calc (N : ℝ) ^ (-a) ≤ (y / 2) ^ (-a) := h1
          _ = 2 ^ a / Real.exp 1 := h2
          _ ≤ 2 / Real.exp 1 := div_le_div_of_nonneg_right h3 (Real.exp_pos 1).le
      have htail' : (∑ p ∈ M.primesLE \ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
          ≤ Real.log 4 + Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1) := by
        have htail := prime_tail_le hN1 hNM ha ha1
        have h1 : (N : ℝ) ^ (-a) - (M : ℝ) ^ (-a) ≤ (N : ℝ) ^ (-a) := by
          have h0 : 0 ≤ (M : ℝ) ^ (-a) := Real.rpow_nonneg (by positivity) _
          linarith
        have h2 : Real.log 4 * (1 + 1 / a) * ((N : ℝ) ^ (-a) - (M : ℝ) ^ (-a))
            ≤ Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h4.le (by positivity))
        have h3 : Real.log 4 * (M : ℝ) ^ (-a) ≤ Real.log 4 :=
          mul_le_of_le_one_right h4.le hMa
        linarith
      have hsplit : (∑ p ∈ M.primesLE \ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
            + (∑ p ∈ N.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
          = ∑ p ∈ M.primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)) :=
        Finset.sum_sdiff (Nat.primesLE_mono hNM)
      have htot : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p : ℝ) ^ (-(1 + a)))
          ≤ CL / a + (Real.log 4 + Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1)) := by
        rw [← hMdef]
        linarith [hsplit, hfirst, htail']
      have h1 : Real.log 4 ≤ Real.log 4 / a := by
        rw [le_div_iff₀ ha]
        nlinarith [h4]
      have h2 : Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1)
          ≤ (4 * Real.log 4 / Real.exp 1) / a := by
        rw [le_div_iff₀ ha]
        have hk : (1 + 1 / a) * a = a + 1 := by
          field_simp
        have hexpand : Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1) * a
            = 2 * Real.log 4 * (a + 1) / Real.exp 1 := by
          calc Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1) * a
              = Real.log 4 * ((1 + 1 / a) * a) * (2 / Real.exp 1) := by ring
            _ = Real.log 4 * (a + 1) * (2 / Real.exp 1) := by rw [hk]
            _ = 2 * Real.log 4 * (a + 1) / Real.exp 1 := by ring
        rw [hexpand]
        have hnum : 2 * Real.log 4 * (a + 1) ≤ 4 * Real.log 4 := by nlinarith [h4, ha1]
        exact div_le_div_of_nonneg_right hnum (Real.exp_pos 1).le
      have hfinal : CL / a + (Real.log 4 + Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1))
          ≤ (CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1 + 1) / a := by
        have hsum : CL / a + (Real.log 4 + Real.log 4 * (1 + 1 / a) * (2 / Real.exp 1))
            ≤ CL / a + (Real.log 4 / a + (4 * Real.log 4 / Real.exp 1) / a) := by
          have := add_le_add h1 h2
          linarith
        have hcomb : CL / a + (Real.log 4 / a + (4 * Real.log 4 / Real.exp 1) / a)
            = (CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1) / a := by
          rw [add_div, add_div]
          ring
        have hK : (CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1) / a
            ≤ (CL + Real.log 4 + 4 * Real.log 4 / Real.exp 1 + 1) / a :=
          div_le_div_of_nonneg_right (by linarith) ha.le
        linarith
      linarith [htot, hfinal]

/-- **Difference of the weighted prime sums is bounded.** -/
theorem prime_rpow_diff_sum_le (K : ℝ) (hK : 0 < K)
    (hlog : ∀ (x a : ℝ), 2 ≤ x → 0 < a → a ≤ 1 →
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p : ℝ) ^ (-(1 + a))) ≤ K / a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x a b : ℝ), 2 ≤ x → 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
      (∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b)))) ≤ C := by
  refine ⟨K, hK, ?_⟩
  intro x a b hx ha hab hb2a hb1
  have ha1 : a ≤ 1 := le_trans hab hb1
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      (p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))
        ≤ (b - a) * (Real.log p * (p : ℝ) ^ (-(1 + a))) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))
        = (p : ℝ) ^ (-(1 + a)) * (1 - (p : ℝ) ^ (-(b - a))) := by
      rw [mul_sub, mul_one, ← Real.rpow_add hp0,
        show -(1 + a) + (-(b - a)) = -(1 + b) by ring]
    rw [h1]
    have h2 : (p : ℝ) ^ (-(b - a)) = Real.exp (-((b - a) * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]; ring_nf
    have h3 : 1 - Real.exp (-((b - a) * Real.log p)) ≤ (b - a) * Real.log p := by
      have h := Real.one_sub_le_exp_neg ((b - a) * Real.log p)
      linarith
    have hw : 0 ≤ (p : ℝ) ^ (-(1 + a)) := Real.rpow_nonneg (le_of_lt hp0) _
    calc (p : ℝ) ^ (-(1 + a)) * (1 - (p : ℝ) ^ (-(b - a)))
        = (p : ℝ) ^ (-(1 + a)) * (1 - Real.exp (-((b - a) * Real.log p))) := by rw [h2]
      _ ≤ (p : ℝ) ^ (-(1 + a)) * ((b - a) * Real.log p) := mul_le_mul_of_nonneg_left h3 hw
      _ = (b - a) * (Real.log p * (p : ℝ) ^ (-(1 + a))) := by ring
  calc (∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))))
      ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (b - a) * (Real.log p * (p : ℝ) ^ (-(1 + a))) :=
        Finset.sum_le_sum hterm
    _ = (b - a) * ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log p * (p : ℝ) ^ (-(1 + a))) := by
        rw [Finset.mul_sum]
    _ ≤ (b - a) * (K / a) :=
        mul_le_mul_of_nonneg_left (hlog x a hx ha ha1) (by linarith)
    _ = K * ((b - a) / a) := by ring
    _ ≤ K * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hK)
        rw [div_le_one ha]
        linarith
    _ = K := mul_one K

/-- **Almost-monotonicity of `exp ∘ Wsup` in the exponent `α`.**  For `0 < a ≤ b ≤ 2a ≤ 1` the
sup over the window of `Re Σ_{p ≤ x} f(p) p^{-1-α-it}` can only increase by an absolute constant
when `α` is lowered from `b` to `a`: the difference of the two prime sums is at most
`Σ_{p ≤ x} (p^{-1-a} - p^{-1-b})`, and `Σ_{p ≤ x} (log p) p^{-1-a} ≤ C/a` (the part `p ≤ e^{1/a}`
by `Work.BMF.HL.sum_log_div_prime_le`, the rest by Abel summation against Chebyshev's bound
`θ(t) ≤ log 4 · t`), so the difference is `O((b-a)/a) = O(1)`. -/
theorem casdiv_wsup_step : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T' a b : ℝ, 2 ≤ x → 0 < a → a ≤ b → b ≤ 2 * a → b ≤ 1 →
        Real.exp (Work.BMF.Wsup f x b T') ≤ C * Real.exp (Work.BMF.Wsup f x a T') := by
  obtain ⟨K, hKpos, hlog⟩ := casdiv_prime_log_rpow_sum_le
  obtain ⟨C₁, hC₁pos, hC₁⟩ := prime_rpow_diff_sum_le K hKpos hlog
  refine ⟨Real.exp C₁, Real.exp_pos C₁, ?_⟩
  intro f hf x T' a b hx ha hab hb2a hb1
  have hsum : (∑ p ∈ (⌊x⌋₊).primesLE,
      ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b)))) ≤ C₁ := hC₁ x a b hx ha hab hb2a hb1
  have hstep : Wsup f x b T' ≤ Wsup f x a T' +
      ∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b))) :=
    Wsup_le_Wsup_add_rpow_diff f hf (le_of_lt ha) hab
  have hexp : Real.exp (Wsup f x b T') ≤ Real.exp (Wsup f x a T') * Real.exp C₁ := by
    calc Real.exp (Wsup f x b T')
        ≤ Real.exp (Wsup f x a T'
            + ∑ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b)))) :=
          Real.exp_le_exp.mpr hstep
      _ = Real.exp (Wsup f x a T') * Real.exp (∑ p ∈ (⌊x⌋₊).primesLE,
            ((p : ℝ) ^ (-(1 + a)) - (p : ℝ) ^ (-(1 + b)))) := Real.exp_add _ _
      _ ≤ Real.exp (Wsup f x a T') * Real.exp C₁ :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (Real.exp_pos _).le
  calc Real.exp (Wsup f x b T') ≤ Real.exp (Wsup f x a T') * Real.exp C₁ := hexp
    _ = Real.exp C₁ * Real.exp (Wsup f x a T') := by ring

end Work.BMF.mrlas
