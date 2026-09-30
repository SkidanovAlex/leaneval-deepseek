import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.exp_cube_integral_le
import Submission.Work.BMF.sum_exp_le_integral_add_max
import Submission.Commons.Analysis.Summation.abel_prefix_bound
import Submission.Work.BMF.int_exp_cube_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Partial sums of the Riemann zeta series in the strip `1/2 ≤ σ < 1`

Main result: `Work.BMF.zeta_partial_sum_bound`.  Given the Vinogradov–Korobov
exponential-sum hypothesis `VKExpSum C D`, the partial sums
`∑_{n ≤ ⌊|t|⌋} n^{-σ-it}` are bounded by `A |t|^{B(1-σ)^{3/2}} (log |t|)^{2/3}`
with `B = (2/9)√(3D)`.

The proof follows Ford's Lemma 7.3: split `[1, ⌊T⌋]` into dyadic blocks
`(2^j, 2^{j+1}]`, bound each block by Abel summation against the VK bound, and
sum the resulting exponentials `exp(η j log 2 - (j log 2)^3/(D log^2 T))` by
comparing with the integral `∫_0^∞ exp(η x log 2 - (x log 2)^3/(D log^2 T)) dx`.
-/

namespace Work.BMF

open Finset

noncomputable section

/-! ## Dyadic decompositions of `Finset.Icc 1 T₀` -/

private lemma sum_Icc_split (f : ℕ → ℂ) (A B C : ℕ) (h1 : A ≤ B) (h2 : B ≤ C) :
    ∑ n ∈ Finset.Icc A C, f n = ∑ n ∈ Finset.Icc A B, f n + ∑ n ∈ Finset.Ioc B C, f n := by
  have hdisj : Disjoint (Finset.Icc A B) (Finset.Ioc B C) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ioc] at hx'
    omega
  rw [← Finset.sum_union hdisj]
  congr 1
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
  omega

private lemma sum_Icc_two_pow (f : ℕ → ℂ) (J : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2^J), f n
      = f 1 + ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    exact sum_Icc_split f 1 (2^J) (2^(J+1)) (Nat.one_le_two_pow)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))

private lemma sum_range_eq_zero_add (g : ℕ → ℂ) (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.range J, g j = g 0 + ∑ j ∈ Finset.Icc 1 (J-1), g j := by
  have hset : Finset.range J = insert 0 (Finset.Icc 1 (J-1)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hset, Finset.sum_insert (by simp)]

/-- Decomposition of `∑_{n ≤ T₀}` into the first two terms, the interior dyadic blocks
`(2^j, 2^{j+1}]` for `1 ≤ j ≤ J-1`, and the final block `(2^J, T₀]`. -/
private lemma dyadic_decomp (f : ℕ → ℂ) (T0 J : ℕ) (hJ : 1 ≤ J) (h2J : 2^J ≤ T0) :
    ∑ n ∈ Finset.Icc 1 T0, f n
      = f 1 + f 2 + ∑ j ∈ Finset.Icc 1 (J-1), ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n
        + ∑ n ∈ Finset.Ioc (2^J) T0, f n := by
  have h1 := sum_Icc_two_pow f J
  have h2 := sum_range_eq_zero_add
    (fun j => ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n) J hJ
  have hz : (∑ n ∈ Finset.Ioc (2^0) (2^(0+1)), f n) = f 2 := by
    have : Finset.Ioc (2^0) (2^(0+1)) = ({2} : Finset ℕ) := by decide
    rw [this, Finset.sum_singleton]
  rw [sum_Icc_split f 1 (2^J) T0 Nat.one_le_two_pow h2J, h1, h2, hz]
  ring

/-- Norm version of `dyadic_decomp`. -/
private lemma dyadic_norm_bound (f : ℕ → ℂ) (T0 J : ℕ) (hJ : 1 ≤ J) (h2J : 2^J ≤ T0)
    (h1 : ‖f 1‖ ≤ 1) (h2 : ‖f 2‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 T0, f n‖ ≤
      2 + ∑ j ∈ Finset.Icc 1 (J-1), ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖
        + ‖∑ n ∈ Finset.Ioc (2^J) T0, f n‖ := by
  rw [dyadic_decomp f T0 J hJ h2J]
  have hS : ‖∑ j ∈ Finset.Icc 1 (J-1), ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖
      ≤ ∑ j ∈ Finset.Icc 1 (J-1), ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖ := norm_sum_le _ _
  have h12 : ‖f 1 + f 2‖ ≤ 1 + 1 := by
    have := norm_add_le (f 1) (f 2); linarith
  have ht : ‖f 1 + f 2 + (∑ j ∈ Finset.Icc 1 (J-1), ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
      + (∑ n ∈ Finset.Ioc (2^J) T0, f n)‖ ≤
      (2 + ∑ j ∈ Finset.Icc 1 (J-1), ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖)
        + ‖∑ n ∈ Finset.Ioc (2^J) T0, f n‖ := by
    have ha := norm_add_le
      (f 1 + f 2 + (∑ j ∈ Finset.Icc 1 (J-1), ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n))
      (∑ n ∈ Finset.Ioc (2^J) T0, f n)
    have hb := norm_add_le (f 1 + f 2)
      (∑ j ∈ Finset.Icc 1 (J-1), ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n)
    linarith
  exact ht

/-! ## Rewriting the VK block bound in exponential form -/

private lemma two_pow_eq_exp (j : ℕ) : (2:ℝ)^j = Real.exp ((j:ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]

private lemma rpow_two_pow_neg (σ : ℝ) (j : ℕ) :
    ((2:ℝ)^j) ^ (-σ) = Real.exp (-σ * ((j:ℝ)*Real.log 2)) := by
  rw [two_pow_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1; ring

private lemma rpow_two_pow_one_sub (D L : ℝ) (hD : 0 < D) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) :
    ((2:ℝ)^j) ^ (1 - 1/(D*(L/Real.log ((2:ℝ)^j))^2))
      = Real.exp ((1 - 1/(D*(L/((j:ℝ)*Real.log 2))^2)) * ((j:ℝ)*Real.log 2)) := by
  rw [two_pow_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1; ring

/-- `(1 + C N^{1-δ}) N^{-σ} = N^{-σ} + C exp(η j log 2 - (j log 2)^3/(D L^2))` for `N = 2^j`. -/
private lemma block_glue (C D T σ : ℝ) (hD : 0 < D) (hT : 2 ≤ T) (j : ℕ) (hj : 1 ≤ j) :
    (1 + C * ((2:ℝ)^j) ^ (1 - 1/(D*(Real.log T/Real.log ((2:ℝ)^j))^2))) * ((2:ℝ)^j) ^ (-σ)
      = ((2:ℝ)^j) ^ (-σ)
        + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2 - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by
  have hln2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hGpos : 0 < (j:ℝ) * Real.log 2 := mul_pos hjpos hln2
  have harg : (1 - 1 / (D * (Real.log T / ((j:ℝ) * Real.log 2)) ^ 2)) * ((j:ℝ) * Real.log 2)
      + -σ * ((j:ℝ) * Real.log 2)
      = (1 - σ) * (j:ℝ) * Real.log 2 - ((j:ℝ) * Real.log 2) ^ 3 / (D * (Real.log T) ^ 2) := by
    field_simp
    ring
  rw [rpow_two_pow_neg σ j, rpow_two_pow_one_sub D (Real.log T) hD hLpos j hj]
  rw [add_mul, one_mul, mul_assoc, ← Real.exp_add, harg]

private lemma norm_nat_cpow (n : ℕ) (w : ℂ) (hn : 0 < n) :
    ‖((n : ℂ) ^ w)‖ = (n : ℝ) ^ (w.re) := by
  rw [← Complex.ofReal_natCast (n := n)]
  exact Complex.norm_cpow_eq_rpow_re_of_pos (x := (n:ℝ)) (by exact_mod_cast hn) w

/-! ## The weighted block bound, derived from `VKExpSum` -/

/-- Telescoping: `∑_{n ∈ Icc a b} (w n - w (n+1)) = w a - w (b+1)`. -/
private lemma sum_Icc_telescope {G : Type*} [AddCommGroup G] (w : ℕ → G) (a b : ℕ)
    (h : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a b, (w n - w (n + 1)) = w a - w (b + 1) := by
  rcases eq_or_lt_of_le h with h1 | h1
  · have hempty : Finset.Icc a b = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty, ← h1]
    simp
  · have h2 : a ≤ b := by omega
    have h3 := Finset.sum_Icc_sub h2 w
    have h4 : ∑ n ∈ Finset.Icc a b, (w n - w (n + 1))
        = - ∑ n ∈ Finset.Icc a b, (w (n + 1) - w n) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by abel)
    rw [h4, h3]
    abel

/-- Abel summation by parts on `(N, M]`, bounding by the partial sums. -/
private lemma zps_abel (a : ℕ → ℂ) (w : ℕ → ℝ) (N M : ℕ) (B : ℝ)
    (hNM : N < M) (hB : 0 ≤ B)
    (hw0 : ∀ n ∈ Finset.Ioc N M, 0 ≤ w n)
    (hwmono : ∀ n, N ≤ n → n < M → w (n + 1) ≤ w n)
    (hpartial : ∀ k, N < k → k ≤ M → ‖∑ j ∈ Finset.Ioc N k, a j‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖ ≤ B * w (N + 1) := by
  have hN1M : N + 1 ≤ M := by omega
  have hB' : ∀ n, N + 1 ≤ n → n ≤ M → ‖∑ k ∈ Finset.Icc (N + 1) n, a k‖ ≤ B := by
    intro n hn1 hnM
    rw [Finset.Icc_add_one_left_eq_Ioc]
    exact hpartial n (by omega) hnM
  have hstep := Commons.Analysis.Summation.abel_prefix_bound a (fun n => (w n : ℂ)) B
    hN1M (by omega) hB'
  have hL : (∑ k ∈ Finset.Icc (N + 1) M, a k * (w k : ℂ))
      = ∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n := by
    rw [Finset.Icc_add_one_left_eq_Ioc]
    exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)
  rw [hL] at hstep
  have hwM : 0 ≤ w M := hw0 M (by rw [Finset.mem_Ioc]; exact ⟨hNM, le_rfl⟩)
  have h1 : ‖(w M : ℂ)‖ = w M := Complex.norm_of_nonneg hwM
  have h2 : ∀ n ∈ Finset.Icc (N + 1) (M - 1),
      ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ = w n - w (n + 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hle : w (n + 1) ≤ w n := hwmono n (by omega) (by omega)
    rw [← Complex.ofReal_sub]
    exact Complex.norm_of_nonneg (sub_nonneg.mpr hle)
  have h3 : ∑ n ∈ Finset.Icc (N + 1) (M - 1), (w n - w (n + 1)) = w (N + 1) - w M := by
    have hh := sum_Icc_telescope w (N + 1) (M - 1) (by omega)
    rwa [show M - 1 + 1 = M by omega] at hh
  calc ‖∑ n ∈ Finset.Ioc N M, (w n : ℂ) * a n‖
      ≤ B * ‖(w M : ℂ)‖
          + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), ‖(w n : ℂ) - (w (n + 1) : ℂ)‖ := hstep
    _ = B * w M + B * ∑ n ∈ Finset.Icc (N + 1) (M - 1), (w n - w (n + 1)) := by
        rw [h1, Finset.sum_congr rfl h2]
    _ = B * w M + B * (w (N + 1) - w M) := by rw [h3]
    _ = B * w (N + 1) := by ring

/-- Reindexing a sum over `(a, b]` by `n ↦ n+1`. -/
private lemma sum_Ioc_succ (f : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, f (n + 1) = ∑ m ∈ Finset.Ioc (a + 1) (b + 1), f m := by
  induction b with
  | zero =>
      have h1 : Finset.Ioc a 0 = ∅ := by rw [Finset.Ioc_eq_empty_iff]; omega
      have h2 : Finset.Ioc (a + 1) 1 = ∅ := by rw [Finset.Ioc_eq_empty_iff]; omega
      rw [h1, h2, Finset.sum_empty, Finset.sum_empty]
  | succ b ih =>
      by_cases hab : a ≤ b
      · rw [Finset.sum_Ioc_succ_top hab (f := fun n => f (n + 1)),
          Finset.sum_Ioc_succ_top (by omega : a + 1 ≤ b + 1) (f := f), ih]
      · have h1 : Finset.Ioc a (b + 1) = ∅ := by
          rw [Finset.Ioc_eq_empty_iff]; omega
        have h2 : Finset.Ioc (a + 1) (b + 1 + 1) = ∅ := by
          rw [Finset.Ioc_eq_empty_iff]; omega
        rw [h1, h2, Finset.sum_empty, Finset.sum_empty]

/-- For `0 < x ≤ y` and `σ ≥ 0`, `y^{-σ} ≤ x^{-σ}`. -/
private lemma rpow_neg_anti (σ : ℝ) (hσ : 0 ≤ σ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y ^ (-σ) ≤ x ^ (-σ) := by
  have hy : 0 ≤ y := le_trans hx.le hxy
  rw [Real.rpow_neg hy, Real.rpow_neg hx.le]
  simpa using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx σ)
    (Real.rpow_le_rpow hx.le hxy hσ)

/-- Partial sums of `n^{-iT}` over `(N, k]`, straight from `VKExpSum` with `u = 1`. -/
private lemma vk_partial_bound (C D : ℝ) (hVK : VKExpSum C D) (N k : ℕ) (T : ℝ)
    (hN : 2 ≤ N) (hNT : (N : ℝ) ≤ T) (hk1 : N + 2 ≤ k) (hk2 : k ≤ 2 * N + 1) :
    ‖∑ m ∈ Finset.Ioc (N + 1) k, ((m : ℂ) ^ (-(Complex.I * (T : ℂ))))‖
      ≤ C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2)) := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlt : (N:ℝ) < (((k - 1 : ℕ)) : ℝ) := by
    have h3 : N < k - 1 := by omega
    exact_mod_cast h3
  have hle : (((k - 1 : ℕ)) : ℝ) ≤ 2 * (N:ℝ) := by
    have h3 : k - 1 ≤ 2 * N := by omega
    exact_mod_cast h3
  have hvk := hVK (N:ℝ) T hN2 hNT 1 (by norm_num) (by norm_num) (((k - 1 : ℕ)) : ℝ) hlt hle
  rw [Nat.floor_natCast, Nat.floor_natCast] at hvk
  have hcongr : (∑ n ∈ Finset.Ioc N (k-1), ((((n:ℝ)+1:ℝ)) : ℂ) ^ (-(Complex.I * (T:ℂ))))
      = ∑ n ∈ Finset.Ioc N (k-1), ((((n+1 : ℕ)) : ℂ) ^ (-(Complex.I * (T:ℂ)))) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hpush : ((((n:ℝ)+1:ℝ)) : ℂ) = ((((n+1 : ℕ)) : ℂ)) := by push_cast; ring
    rw [hpush]
  have hsum : (∑ n ∈ Finset.Ioc N (k-1), ((((n:ℝ)+1:ℝ)) : ℂ) ^ (-(Complex.I * (T:ℂ))))
      = ∑ m ∈ Finset.Ioc (N+1) k, ((m : ℂ) ^ (-(Complex.I * (T:ℂ)))) := by
    rw [hcongr, sum_Ioc_succ (fun m => ((m : ℂ) ^ (-(Complex.I * (T:ℂ))))) N (k-1),
      show k - 1 + 1 = k by omega]
  rwa [hsum] at hvk

/-- Partial sums of `n^{-iT}` over `(N, k]` for `N < k ≤ 2N+1`, at the cost of an extra `1`. -/
private lemma vk_partial_bound' (C D : ℝ) (hC : 0 ≤ C) (hVK : VKExpSum C D) (N k : ℕ) (T : ℝ)
    (hN : 2 ≤ N) (hNT : (N : ℝ) ≤ T) (hk1 : N < k) (hk2 : k ≤ 2 * N + 1) :
    ‖∑ m ∈ Finset.Ioc N k, ((m : ℂ) ^ (-(Complex.I * (T : ℂ))))‖
      ≤ 1 + C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2)) := by
  rcases le_or_gt k (N + 1) with h | h
  · have hk : k = N + 1 := by omega
    subst hk
    have hsingle : Finset.Ioc N (N + 1) = ({(N + 1)} : Finset ℕ) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [hsingle, Finset.sum_singleton]
    have hn : ‖(((N+1 : ℕ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ = 1 := by
      rw [norm_nat_cpow (N+1) _ (by omega)]
      have hre : (-(Complex.I * (T : ℂ))).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    rw [hn]
    have : (0:ℝ) ≤ C * (N:ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2)) :=
      mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    linarith
  · have h2 : N + 2 ≤ k := by omega
    have hsp := vk_partial_bound C D hVK N k T hN hNT h2 hk2
    have hIns : Finset.Ioc N k = insert (N + 1) (Finset.Ioc (N + 1) k) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    rw [hIns, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega)]
    have hn : ‖(((N+1 : ℕ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖ = 1 := by
      rw [norm_nat_cpow (N+1) _ (by omega)]
      have hre : (-(Complex.I * (T : ℂ))).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    calc ‖(((N+1 : ℕ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))
            + ∑ m ∈ Finset.Ioc (N+1) k, ((m : ℂ) ^ (-(Complex.I * (T : ℂ))))‖
        ≤ ‖(((N+1 : ℕ)) : ℂ) ^ (-(Complex.I * (T : ℂ)))‖
            + ‖∑ m ∈ Finset.Ioc (N+1) k, ((m : ℂ) ^ (-(Complex.I * (T : ℂ))))‖ :=
          norm_add_le _ _
      _ ≤ 1 + C * (N : ℝ) ^ (1 - 1 / (D * (Real.log T / Real.log N) ^ 2)) := by
          rw [hn]; linarith

/-- The interior dyadic blocks. -/
private lemma vk_block_bound_dyadic (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (hVK : VKExpSum C D)
    (T σ : ℝ) (hT : 2 ≤ T) (hσ : 0 ≤ σ) (J : ℕ) (hJ1 : 1 ≤ J)
    (hNT : (((2:ℕ)^J : ℕ) : ℝ) ≤ T) :
    ∀ j ∈ Finset.Icc 1 (J-1),
      ‖∑ n ∈ Finset.Ioc (2^j : ℕ) (2^(j+1) : ℕ),
          (((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
        ((2:ℝ)^j)^(-σ)
          + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2
              - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  set N : ℕ := 2^j with hNdef
  set M : ℕ := 2^(j+1) with hMdef
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNTj : (N : ℝ) ≤ T := by
    rw [hNdef]
    have h1 : (2:ℕ)^j ≤ (2:ℕ)^J := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans (by exact_mod_cast h1) hNT
  have hNM : N < M := by rw [hNdef, hMdef]; rw [pow_succ]; omega
  have hM2 : M ≤ 2 * N := by rw [hNdef, hMdef]; rw [pow_succ]; omega
  set B : ℝ := 1 + C * (N:ℝ) ^ (1 - 1/(D*(Real.log T/Real.log N)^2)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hpartial : ∀ k, N < k → k ≤ M →
      ‖∑ j' ∈ Finset.Ioc N k, ((j' : ℂ) ^ (-(Complex.I * (T:ℂ))))‖ ≤ B := by
    intro k hk1 hk2
    have h := vk_partial_bound' C D hC.le hVK N k T hN2 hNTj hk1 (by omega)
    simpa [hBdef] using h
  have hwmono : ∀ n, N ≤ n → n < M → ((((n+1 : ℕ)) : ℝ)) ^ (-σ) ≤ (n:ℝ) ^ (-σ) := by
    intro n hn1 _
    have hnpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le hNpos (by exact_mod_cast hn1)
    have h1 : 1 ≤ 1 + 1/(n:ℝ) := by
      have : 0 < 1/(n:ℝ) := by positivity
      linarith
    have hpush : ((((n+1 : ℕ)) : ℝ)) = (n:ℝ) + 1 := by push_cast; ring
    rw [hpush]
    calc ((n:ℝ) + 1) ^ (-σ) = ((n:ℝ) * (1 + 1/(n:ℝ))) ^ (-σ) := by
          congr 1; field_simp
      _ = (n:ℝ) ^ (-σ) * (1 + 1/(n:ℝ)) ^ (-σ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ (n:ℝ) ^ (-σ) * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _)
      _ = (n:ℝ) ^ (-σ) := by ring
  have habel := zps_abel (fun n => ((n:ℂ) ^ (-(Complex.I * (T:ℂ))))) (fun n => (n:ℝ)^(-σ))
    N M B hNM hBnn
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hwmono hpartial
  have hsum_eq : ∑ n ∈ Finset.Ioc N M, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (T : ℂ)))
      = ∑ n ∈ Finset.Ioc N M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hnp : (0 : ℝ) < n := by
      have : N ≤ n := le_of_lt (Finset.mem_Ioc.mp hn).1
      exact lt_of_lt_of_le hNpos (by exact_mod_cast this)
    have hnne : (n : ℂ) ≠ 0 := by
      intro h0
      have h1 : (n:ℝ) = 0 := by exact_mod_cast h0
      exact (ne_of_gt hnp) h1
    rw [Complex.ofReal_cpow hnp.le (-σ), Complex.ofReal_natCast, Complex.ofReal_neg,
      ← Complex.cpow_add _ _ hnne]
    congr 1
    ring
  rw [hsum_eq] at habel
  have hcast : (N : ℝ) = (2:ℝ)^j := by rw [hNdef, Nat.cast_pow, Nat.cast_ofNat]
  have hBcast : B = 1 + C * ((2:ℝ)^j) ^ (1 - 1/(D*(Real.log T/Real.log ((2:ℝ)^j))^2)) := by
    rw [hBdef, hcast]
  have hw : (((N + 1 : ℕ)) : ℝ) ^ (-σ) ≤ ((2:ℝ)^j) ^ (-σ) := by
    have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
    have h1 : ((2:ℝ)^j) ≤ (((N + 1 : ℕ)) : ℝ) := by
      rw [← hcast]; push_cast; linarith
    exact rpow_neg_anti σ hσ h2jpos h1
  calc ‖∑ n ∈ Finset.Ioc N M, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖
      ≤ B * (((N + 1 : ℕ)) : ℝ) ^ (-σ) := habel
    _ ≤ B * ((2:ℝ)^j) ^ (-σ) :=
        mul_le_mul_of_nonneg_left hw hBnn
    _ = (1 + C * ((2:ℝ)^j) ^ (1 - 1/(D*(Real.log T/Real.log ((2:ℝ)^j))^2)))
          * ((2:ℝ)^j) ^ (-σ) := by rw [hBcast]
    _ = ((2:ℝ)^j) ^ (-σ)
          + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2
              - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) :=
        block_glue C D T σ hD hT j hj1

/-- The final dyadic block `(2^J, T₀]`. -/
private lemma vk_block_bound_last (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (hVK : VKExpSum C D)
    (T σ : ℝ) (hT : 2 ≤ T) (hσ : 0 ≤ σ) (T0 J : ℕ) (hJ1 : 1 ≤ J)
    (hNT : (((2:ℕ)^J : ℕ) : ℝ) ≤ T) (hM : T0 ≤ 2 * 2^J) :
    ‖∑ n ∈ Finset.Ioc (2^J : ℕ) (T0 : ℕ),
        (((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
      ((2:ℝ)^J)^(-σ)
        + C * Real.exp ((1-σ) * (J:ℝ) * Real.log 2
            - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by
  set N : ℕ := 2^J with hNdef
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hJ1
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNTj : (N : ℝ) ≤ T := by
    rw [hNdef]; exact hNT
  set B : ℝ := 1 + C * (N:ℝ) ^ (1 - 1/(D*(Real.log T/Real.log N)^2)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hpartial : ∀ k, N < k → k ≤ T0 →
      ‖∑ j' ∈ Finset.Ioc N k, ((j' : ℂ) ^ (-(Complex.I * (T:ℂ))))‖ ≤ B := by
    intro k hk1 hk2
    have h := vk_partial_bound' C D hC.le hVK N k T hN2 hNTj hk1 (by omega)
    simpa [hBdef] using h
  have hwmono : ∀ n, N ≤ n → n < T0 → ((((n+1 : ℕ)) : ℝ)) ^ (-σ) ≤ (n:ℝ) ^ (-σ) := by
    intro n hn1 _
    have hnpos : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le hNpos (by exact_mod_cast hn1)
    have h1 : 1 ≤ 1 + 1/(n:ℝ) := by
      have : 0 < 1/(n:ℝ) := by positivity
      linarith
    have hpush : ((((n+1 : ℕ)) : ℝ)) = (n:ℝ) + 1 := by push_cast; ring
    rw [hpush]
    calc ((n:ℝ) + 1) ^ (-σ) = ((n:ℝ) * (1 + 1/(n:ℝ))) ^ (-σ) := by
          congr 1; field_simp
      _ = (n:ℝ) ^ (-σ) * (1 + 1/(n:ℝ)) ^ (-σ) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ (n:ℝ) ^ (-σ) * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
          (Real.rpow_nonneg (by positivity) _)
      _ = (n:ℝ) ^ (-σ) := by ring
  by_cases hcase : T0 ≤ N
  · -- empty block
    have hempty : Finset.Ioc N T0 = ∅ := by
      rw [Finset.Ioc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty, norm_zero]
    have h2jpos : (0:ℝ) < (2:ℝ)^J := by positivity
    have hexp : 0 ≤ C * Real.exp ((1-σ) * (J:ℝ) * Real.log 2
        - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by positivity
    have hrp : 0 ≤ ((2:ℝ)^J)^(-σ) := Real.rpow_nonneg h2jpos.le _
    linarith
  · have habel := zps_abel (fun n => ((n:ℂ) ^ (-(Complex.I * (T:ℂ))))) (fun n => (n:ℝ)^(-σ))
      N T0 B (by omega) hBnn
      (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hwmono hpartial
    have hsum_eq : ∑ n ∈ Finset.Ioc N T0, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (T : ℂ)))
        = ∑ n ∈ Finset.Ioc N T0, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hnp : (0 : ℝ) < n := by
        have : N ≤ n := le_of_lt (Finset.mem_Ioc.mp hn).1
        exact lt_of_lt_of_le hNpos (by exact_mod_cast this)
      have hnne : (n : ℂ) ≠ 0 := by
        intro h0
        have h1 : (n:ℝ) = 0 := by exact_mod_cast h0
        exact (ne_of_gt hnp) h1
      rw [Complex.ofReal_cpow hnp.le (-σ), Complex.ofReal_natCast, Complex.ofReal_neg,
        ← Complex.cpow_add _ _ hnne]
      congr 1
      ring
    rw [hsum_eq] at habel
    have hcast : (N : ℝ) = (2:ℝ)^J := by rw [hNdef, Nat.cast_pow, Nat.cast_ofNat]
    have hBcast : B = 1 + C * ((2:ℝ)^J) ^ (1 - 1/(D*(Real.log T/Real.log ((2:ℝ)^J))^2)) := by
      rw [hBdef, hcast]
    have hw : (((N + 1 : ℕ)) : ℝ) ^ (-σ) ≤ ((2:ℝ)^J) ^ (-σ) := by
      have h2jpos : (0:ℝ) < (2:ℝ)^J := by positivity
      have h1 : ((2:ℝ)^J) ≤ (((N + 1 : ℕ)) : ℝ) := by
        rw [← hcast]; push_cast; linarith
      exact rpow_neg_anti σ hσ h2jpos h1
    calc ‖∑ n ∈ Finset.Ioc N T0, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖
        ≤ B * (((N + 1 : ℕ)) : ℝ) ^ (-σ) := habel
      _ ≤ B * ((2:ℝ)^J) ^ (-σ) := mul_le_mul_of_nonneg_left hw hBnn
      _ = (1 + C * ((2:ℝ)^J) ^ (1 - 1/(D*(Real.log T/Real.log ((2:ℝ)^J))^2)))
            * ((2:ℝ)^J) ^ (-σ) := by rw [hBcast]
      _ = ((2:ℝ)^J) ^ (-σ)
            + C * Real.exp ((1-σ) * (J:ℝ) * Real.log 2
                - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) :=
          block_glue C D T σ hD hT J hJ1

/-! ## Summing the exponentials -/

/-- `(1 - r) * ∑_{j<K} r^j = 1 - r^K`. -/
private lemma geom_range_mul_eq (r : ℝ) (K : ℕ) :
    (1 - r) * ∑ j ∈ Finset.range K, r^j = 1 - r^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

private lemma geom_range_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 3/4) (K : ℕ) :
    ∑ j ∈ Finset.range K, r^j ≤ 4 := by
  have hident : (1 - r) * ∑ j ∈ Finset.range K, r^j = 1 - r^K := geom_range_mul_eq r K
  have hrK : 0 ≤ r^K := pow_nonneg hr0 K
  have h14 : (1:ℝ)/4 ≤ 1 - r := by linarith
  have hkey : (1/4) * ∑ j ∈ Finset.range K, r^j ≤ 1 := by
    calc (1/4) * ∑ j ∈ Finset.range K, r^j
        ≤ (1 - r) * ∑ j ∈ Finset.range K, r^j :=
          mul_le_mul_of_nonneg_right h14 (Finset.sum_nonneg (fun j _ => pow_nonneg hr0 j))
      _ = 1 - r^K := hident
      _ ≤ 1 := by linarith
  linarith

private lemma two_rpow_neg_half_le : (2:ℝ)^(-(1/2:ℝ)) ≤ 3/4 := by
  have hsq : ((2:ℝ)^(-(1/2:ℝ)))^2 = 1/2 := by
    rw [sq, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      show (-(1/2:ℝ)) + (-(1/2:ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hr0 : (0:ℝ) ≤ (2:ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg (by norm_num) _
  nlinarith [hsq, hr0]

/-- The geometric part of the dyadic sum: `∑_{1 ≤ j ≤ J-1} (2^j)^{-σ} ≤ 4` for `σ ≥ 1/2`. -/
private lemma dyadic_inv_pow_sum (σ : ℝ) (hσ : 1/2 ≤ σ) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 (J-1), ((2:ℝ)^j)^(-σ) ≤ 4 := by
  set r : ℝ := (2:ℝ)^(-(1/2:ℝ)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r ≤ 3/4 := by rw [hr]; exact two_rpow_neg_half_le
  have hpt : ∀ j : ℕ, ((2:ℝ)^j)^(-σ) ≤ r^j := by
    intro j
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hL : ((2:ℝ)^j)^(-σ) = (2:ℝ)^((j:ℝ) * (-σ)) := by
      rw [← Real.rpow_natCast (x := (2:ℝ)) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hR : r^j = (2:ℝ)^((-(1/2:ℝ)) * (j:ℝ)) := by
      rw [hr, ← Real.rpow_natCast (x := (2:ℝ)^(-(1/2:ℝ))) j,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    rw [hL, hR]
    exact (Real.rpow_le_rpow_left_iff (x := 2) (by norm_num)).mpr (by nlinarith)
  calc ∑ j ∈ Finset.Icc 1 (J-1), ((2:ℝ)^j)^(-σ)
      ≤ ∑ j ∈ Finset.range J, ((2:ℝ)^j)^(-σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => by simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega)
          (fun x _ _ => Real.rpow_nonneg (by positivity) _)
    _ ≤ ∑ j ∈ Finset.range J, r^j := Finset.sum_le_sum (fun j _ => hpt j)
    _ ≤ 4 := geom_range_le r hr0 hr1 J

/-- The dyadic exponential sum bound: for `D > 0` there is `A > 0` with
`∑_{j<K} exp(η j log 2 - (j log 2)^3/(D L^2)) ≤ A L^{2/3} exp((2/9)√(3D) η^{3/2} L)`
for all `η ≥ 0`, `L ≥ 1` and `K`. -/
private lemma dyadic_exp_bound (D : ℝ) (hD : 0 < D) :
    ∃ A : ℝ, 0 < A ∧ ∀ η L : ℝ, 0 ≤ η → 1 ≤ L → ∀ K : ℕ,
      ∑ j ∈ Finset.range K,
          Real.exp (η * (j:ℝ) * Real.log 2 - ((j:ℝ) * Real.log 2)^3/(D*L^2))
        ≤ A * L ^ (2/3:ℝ) * Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L) := by
  refine ⟨1 + (8 / Real.log 2) * D ^ (1/3:ℝ), ?_, ?_⟩
  · have hln2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro η L hη hL1 K
    have hL : 0 < L := lt_of_lt_of_le one_pos hL1
    have hln2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 := sum_exp_le_integral_add_max D L η hD hL hη K
    have h2 := int_exp_cube_le D L η hD hL hη
    have hL23 : (1:ℝ) ≤ L ^ (2/3:ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hc : (0:ℝ) ≤ (8 / Real.log 2) * D ^ (1/3:ℝ) := by positivity
    have hE : (0:ℝ) < Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L) := Real.exp_pos _
    calc ∑ j ∈ Finset.range K,
          Real.exp (η * (j:ℝ) * Real.log 2 - ((j:ℝ) * Real.log 2)^3/(D*L^2))
        ≤ Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L)
            + 2 * ∫ x in Set.Ioi (0:ℝ),
                Real.exp (η * x * Real.log 2 - (x * Real.log 2)^3/(D*L^2)) := h1
      _ ≤ Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L)
            + 2 * ((4/Real.log 2)*D^(1/3:ℝ)*L^(2/3:ℝ)
                * Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L)) := by
          linarith [mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2)]
      _ = (1 + (8/Real.log 2)*D^(1/3:ℝ)*L^(2/3:ℝ))
            * Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L) := by ring
      _ ≤ (1 + (8/Real.log 2)*D^(1/3:ℝ)) * L^(2/3:ℝ)
            * Real.exp ((2/9)*Real.sqrt (3*D)*η^(3/2:ℝ)*L) := by
          have hle : 1 + (8/Real.log 2)*D^(1/3:ℝ)*L^(2/3:ℝ)
              ≤ (1 + (8/Real.log 2)*D^(1/3:ℝ)) * L^(2/3:ℝ) := by nlinarith [hL23, hc]
          exact mul_le_mul_of_nonneg_right hle hE.le

/-! ## The positive-height case -/

private lemma zeta_partial_sum_bound_pos (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : VKExpSum C D) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ⌊T⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I)))‖ ≤
        A * T ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ))
          * (Real.log T) ^ (2 / 3 : ℝ) := by
  obtain ⟨A₁, hA₁pos, hA₁⟩ := dyadic_exp_bound D hD
  refine ⟨8 + 4 * (C * A₁), by positivity, ?_⟩
  intro σ T hσ1 hσ2 hT3
  have hTpos : (0:ℝ) < T := by linarith
  have hLpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    linarith [show Real.exp 1 < 3 by exact Real.exp_one_lt_three, (Real.exp_pos 1).le]
  have hσ0 : 0 ≤ σ := by linarith
  have hη0 : 0 ≤ 1 - σ := by linarith
  have h2T : 2 ≤ T := by linarith
  set T0 : ℕ := ⌊T⌋₊ with hT0
  set J : ℕ := Nat.log 2 T0 with hJ
  have hT0ge2 : 2 ≤ T0 := by
    rw [hT0]
    have h : (((2:ℕ) : ℝ)) ≤ T := by
      have h2 : (((2:ℕ) : ℝ)) = 2 := by norm_num
      rw [h2]; linarith
    exact Nat.le_floor h
  have hJpos : 0 < J := by
    rw [hJ]; exact Nat.log_pos_iff.mpr ⟨hT0ge2, by norm_num⟩
  have hJ1 : 1 ≤ J := hJpos
  have h2J : 2^J ≤ T0 := by rw [hJ]; exact Nat.pow_log_le_self 2 (by omega)
  have hT0lt : T0 < 2^(J+1) := by
    rw [hJ]; exact Nat.lt_pow_succ_log_self (by norm_num) T0
  have hNT : (((2:ℕ)^J : ℕ) : ℝ) ≤ T := by
    have h1 : (((2:ℕ)^J : ℕ) : ℝ) ≤ (T0 : ℝ) := by exact_mod_cast h2J
    have h2 : (T0 : ℝ) ≤ T := Nat.floor_le (by linarith)
    linarith
  have hMlast : T0 ≤ 2 * 2^J := by
    have h : T0 < 2^J * 2 := by simpa [pow_succ] using hT0lt
    omega
  set f : ℕ → ℂ := fun n => ((n : ℂ) ^ (-((σ : ℂ) + (T : ℂ) * Complex.I))) with hf
  have hfn : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ 1 := by
    intro n hn
    have hn0 : 0 < n := hn
    rw [hf]; dsimp only
    rw [norm_nat_cpow n _ hn0]
    have hre : (-((σ : ℂ) + (T : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have hnorm := dyadic_norm_bound f T0 J hJ1 h2J (hfn 1 (by norm_num)) (hfn 2 (by norm_num))
  have hblock := vk_block_bound_dyadic C D hC hD hVK T σ h2T hσ0 J hJ1 hNT
  have hlast := vk_block_bound_last C D hC hD hVK T σ h2T hσ0 T0 J hJ1 hNT hMlast
  have hsum_block : ∑ j ∈ Finset.Icc 1 (J-1), ‖∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n‖
      ≤ ∑ j ∈ Finset.Icc 1 (J-1),
          ((((2:ℝ)^j)^(-σ)) + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2
            - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))) :=
    Finset.sum_le_sum (fun j hj => hblock j hj)
  have hfin : ‖∑ n ∈ Finset.Icc 1 T0, f n‖ ≤
      2 + (∑ j ∈ Finset.Icc 1 (J-1),
          ((((2:ℝ)^j)^(-σ)) + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2
            - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))))
        + ((((2:ℝ)^J)^(-σ)) + C * Real.exp ((1-σ) * (J:ℝ) * Real.log 2
            - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))) := by
    linarith [hnorm, hsum_block, hlast]
  have hsplit : ∑ j ∈ Finset.Icc 1 (J-1),
        ((((2:ℝ)^j)^(-σ)) + C * Real.exp ((1-σ) * (j:ℝ) * Real.log 2
            - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)))
      = (∑ j ∈ Finset.Icc 1 (J-1), ((2:ℝ)^j)^(-σ))
        + C * ∑ j ∈ Finset.Icc 1 (J-1), Real.exp ((1-σ) * (j:ℝ) * Real.log 2
            - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hs1 : ∑ j ∈ Finset.Icc 1 (J-1), ((2:ℝ)^j)^(-σ) ≤ 4 := dyadic_inv_pow_sum σ hσ1 J
  have hs2 : ∑ j ∈ Finset.Icc 1 (J-1), Real.exp ((1-σ) * (j:ℝ) * Real.log 2
        - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))
      ≤ A₁ * Real.log T ^ (2/3:ℝ)
        * Real.exp ((2/9)*Real.sqrt (3*D)*(1-σ)^(3/2:ℝ)*Real.log T) := by
    refine le_trans ?_ (hA₁ (1-σ) (Real.log T) hη0 hL1 J)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
    · intro x _ _; exact (Real.exp_pos _).le
  have hl1 : ((2:ℝ)^J)^(-σ) ≤ 1 := by
    rw [rpow_two_pow_neg σ J]
    have hle : -σ * ((J:ℝ)*Real.log 2) ≤ 0 := by
      have : 0 ≤ (J:ℝ)*Real.log 2 := by positivity
      nlinarith
    simpa using Real.exp_le_exp.mpr hle
  have hl2 : Real.exp ((1-σ) * (J:ℝ) * Real.log 2 - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))
      ≤ A₁ * Real.log T ^ (2/3:ℝ)
        * Real.exp ((2/9)*Real.sqrt (3*D)*(1-σ)^(3/2:ℝ)*Real.log T) := by
    refine le_trans ?_ (hA₁ (1-σ) (Real.log T) hη0 hL1 (J+1))
    have hsingle : Real.exp ((1-σ) * (J:ℝ) * Real.log 2
          - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))
        = ∑ j ∈ ({J} : Finset ℕ), Real.exp ((1-σ) * (j:ℝ) * Real.log 2
            - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) := by
      rw [Finset.sum_singleton]
    rw [hsingle]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_range.mpr (Nat.lt_succ_self J)
    · intro x _ _; exact (Real.exp_pos _).le
  set Z : ℝ := Real.log T ^ (2/3:ℝ)
      * Real.exp ((2/9)*Real.sqrt (3*D)*(1-σ)^(3/2:ℝ)*Real.log T) with hZ
  have hZ1 : 1 ≤ Z := by
    rw [hZ]
    have ha : 1 ≤ Real.log T ^ (2/3:ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hb : 1 ≤ Real.exp ((2/9)*Real.sqrt (3*D)*(1-σ)^(3/2:ℝ)*Real.log T) := by
      have := Real.exp_le_exp.mpr (show (0:ℝ) ≤ (2/9)*Real.sqrt (3*D)*(1-σ)^(3/2:ℝ)*Real.log T by
        positivity)
      simpa using this
    nlinarith
  have hs2' : ∑ j ∈ Finset.Icc 1 (J-1), Real.exp ((1-σ) * (j:ℝ) * Real.log 2
        - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) ≤ A₁ * Z := by
    rw [hZ]; linarith [hs2]
  have hl2' : Real.exp ((1-σ) * (J:ℝ) * Real.log 2 - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2))
      ≤ A₁ * Z := by
    rw [hZ]; linarith [hl2]
  have hCA1 : 0 ≤ C * A₁ := mul_nonneg hC.le hA₁pos.le
  have hCA1Z : 0 ≤ (C * A₁) * Z := mul_nonneg hCA1 (by linarith)
  have hstep : 2 + (4 + C * (A₁ * Z)) + (1 + C * (A₁ * Z)) ≤ (8 + 4 * (C * A₁)) * Z := by
    nlinarith [hZ1, hCA1Z, hCA1]
  have hmain : ‖∑ n ∈ Finset.Icc 1 T0, f n‖ ≤ (8 + 4 * (C * A₁)) * Z := by
    have e1 : C * ∑ j ∈ Finset.Icc 1 (J-1), Real.exp ((1-σ) * (j:ℝ) * Real.log 2
          - ((j:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) ≤ C * (A₁ * Z) :=
      mul_le_mul_of_nonneg_left hs2' hC.le
    have e2 : C * Real.exp ((1-σ) * (J:ℝ) * Real.log 2
          - ((J:ℝ)*Real.log 2)^3/(D*(Real.log T)^2)) ≤ C * (A₁ * Z) :=
      mul_le_mul_of_nonneg_left hl2' hC.le
    rw [hsplit] at hfin
    linarith [hfin, hs1, e1, e2, hl1, hstep]
  calc ‖∑ n ∈ Finset.Icc 1 T0, f n‖
      ≤ (8 + 4 * (C * A₁)) * Z := hmain
    _ = (8 + 4 * (C * A₁)) * T ^ ((2/9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ))
          * (Real.log T) ^ (2 / 3 : ℝ) := by
        rw [hZ, Real.rpow_def_of_pos hTpos, mul_comm (Real.log T)]
        ring

/-! ## Reducing the general case to the positive one -/

private lemma sum_cpow_conj (σ t : ℝ) (T0 : ℕ) :
    (∑ n ∈ Finset.Icc 1 T0, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
      = (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 T0,
          ((n : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)))) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have h0 : ((n : ℂ)).arg = 0 := by
      rw [← Complex.ofReal_natCast (n := n)]
      exact Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)
    rw [h0]
    exact fun h => Real.pi_ne_zero h.symm
  have hconj : (starRingEnd ℂ) ((n : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)))
      = (n : ℂ) ^ ((starRingEnd ℂ) (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))) := by
    have h := Complex.cpow_conj ((n : ℂ)) (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) harg
    rw [Complex.conj_natCast] at h
    exact h.symm
  rw [hconj]
  congr 1
  simp only [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

theorem zeta_partial_sum_bound (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hVK : VKExpSum C D) :
    ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤
        A * |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
          (Real.log |t|) ^ (2 / 3 : ℝ) := by
  obtain ⟨A, hA, hAb⟩ := zeta_partial_sum_bound_pos C D hC hD hVK
  refine ⟨A, hA, ?_⟩
  intro σ t hσ1 hσ2 ht
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht ⊢
    exact hAb σ t hσ1 hσ2 ht
  · rw [abs_of_neg ht0] at ht ⊢
    have hpos := hAb σ (-t) hσ1 hσ2 (by linarith)
    rw [sum_cpow_conj σ t ⌊-t⌋₊, Complex.norm_conj]
    exact hpos

end

end Work.BMF
