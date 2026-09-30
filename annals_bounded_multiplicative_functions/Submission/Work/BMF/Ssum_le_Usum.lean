import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.Ssum.norm_ab_sum_sub_Usum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.Ssum_le_Usum`

Ford's *Vinogradov's integral and bounds for the Riemann zeta function* (Proc. LMS 85 (2002)),
Lemma 5.1, step (5.2): the block sum `S(N,t) = ∑_{N<n≤R} (n+u)^{-it}` is bounded by the
smoothed exponential sum `U = ∑_{a≤M₁}∑_{b≤M₂} e(∑_j γ_j (ab)^j)` (with Ford's
`γ_j = (-1)^j t/(2π j z^j)`) evaluated at some `z ∈ (N,2N]`, plus an explicit Taylor error.

The proof follows Ford: average `S` over the `M₁M₂` shifts `n ↦ n+ab`, compare the shifted range
with the fixed range `(N, R-1]`, and Taylor-expand `log (1 + ab/z)`.
-/

namespace Work.BMF

open Finset

noncomputable section

/-! ## Elementary bounds for the additive character `eZ` and complex powers -/

private lemma eZ_add (a b : ℝ) : eZ (a + b) = eZ a * eZ b := by
  unfold eZ
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eZ_norm (x : ℝ) : ‖eZ x‖ = 1 := by
  unfold eZ
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
      = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma norm_eZ_sub_one_le (z : ℝ) : ‖eZ z - 1‖ ≤ 2 * Real.pi * |z| := by
  have h : eZ z = Complex.exp (Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ)) := by
    unfold eZ
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))
        = Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ) by push_cast; ring]
  rw [h]
  calc ‖Complex.exp (Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ)) - 1‖
      ≤ ‖(2 * Real.pi * z : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |z| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

private lemma norm_eZ_sub_le (a b : ℝ) : ‖eZ a - eZ b‖ ≤ 2 * Real.pi * |a - b| := by
  have h : eZ a - eZ b = eZ b * (eZ (a - b) - 1) := by
    rw [mul_sub, mul_one, ← eZ_add, show b + (a - b) = a from by ring]
  rw [h, norm_mul, eZ_norm, one_mul]
  exact norm_eZ_sub_one_le (a - b)

/-- The complex power `c^{-it}` of a positive real has modulus `1`. -/
private lemma norm_cpow_neg_I_mul_eq_one (c t : ℝ) (hc : 0 < c) :
    ‖(((c : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')]
  rw [← Complex.ofReal_log hc.le, Complex.norm_exp]
  have hre : ((Real.log c : ℂ) * (-(Complex.I * (t : ℂ)))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  norm_num

/-! ## The sharp Taylor remainder for `log (1 + y)` -/

/-- The degree-`k` Taylor polynomial `∑_{j=1}^{k} (-1)^{j-1} y^j / j` of `log (1 + y)`. -/
private def tayLog (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * y ^ j / (j : ℝ)

private lemma tayLog_zero (k : ℕ) : tayLog k 0 = 0 := by
  rw [tayLog]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp [zero_pow hj1]

private lemma tayLog_eq_range (k : ℕ) :
    tayLog k
      = fun y : ℝ => ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ i / ((i : ℝ) + 1)) * y ^ (i + 1) := by
  funext y
  simp only [tayLog]
  rw [← Finset.Ico_succ_right_eq_Icc 1 k, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 : 1 + i - 1 = i := by omega
  have h2 : ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  rw [h1, h2, Nat.add_comm 1 i]
  ring

private lemma hasDerivAt_tayLog (k : ℕ) (y : ℝ) :
    HasDerivAt (tayLog k) (∑ i ∈ Finset.range k, (-y) ^ i) y := by
  rw [tayLog_eq_range]
  have h : HasDerivAt
      (fun z : ℝ => ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ i / ((i : ℝ) + 1)) * z ^ (i + 1))
      (∑ i ∈ Finset.range k, ((-1 : ℝ) ^ i / ((i : ℝ) + 1)) * (((i : ℝ) + 1) * y ^ i)) y := by
    refine HasDerivAt.fun_sum fun i hi => ?_
    have h1 : HasDerivAt (fun z : ℝ => z ^ (i + 1)) (((i : ℝ) + 1) * y ^ i) y := by
      simpa using hasDerivAt_pow (i + 1) y
    have h2 := (hasDerivAt_const y (((-1 : ℝ) ^ i / ((i : ℝ) + 1)))).mul h1
    convert h2 using 1
    ring
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  have hneg : (-y) ^ i = (-1 : ℝ) ^ i * y ^ i := by
    rw [← neg_one_mul, mul_pow]
  rw [hneg]
  field_simp

/-- The derivative of `log (1 + y) - tayLog k y` is `(-1)^k y^k / (1+y)`. -/
private lemma hasDerivAt_log_sub_tayLog (k : ℕ) (y : ℝ) (hy : y ≠ -1) :
    HasDerivAt (fun z : ℝ => Real.log (1 + z) - tayLog k z)
      ((-1 : ℝ) ^ k * y ^ k / (1 + y)) y := by
  have hne : (1 : ℝ) + y ≠ 0 := by intro h; exact hy (by linarith)
  have hlog : HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 y := by
      simpa using (hasDerivAt_id y).const_add 1
    have h2 := h1.log hne
    simpa using h2
  refine ((hlog.sub (hasDerivAt_tayLog k y))).congr_deriv ?_
  have hyn : (-y) ≠ 1 := by intro h; exact hy (by linarith)
  have hgeom : (∑ i ∈ Finset.range k, (-y) ^ i) = (1 - (-y) ^ k) / (1 + y) := by
    have h := geom_sum_eq hyn k
    rw [h]
    field_simp
    ring_nf
  rw [hgeom]
  rw [show (1 : ℝ) - (-y) ^ k = 1 - (-1) ^ k * y ^ k from by rw [← neg_one_mul, mul_pow]]
  field_simp
  ring_nf

/-- **Sharp Taylor remainder bound for `log (1 + x)`** (Ford's (5.1) with sharp constant):
for `0 ≤ x ≤ 1` the degree-`k` Taylor polynomial of `log (1+x)` differs from it by at most
`x^{k+1}/(k+1)`. -/
private lemma log_tay_remainder (k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.log (1 + x) - tayLog k x| ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
  set F : ℝ → ℝ := fun y => (-1 : ℝ) ^ k * (Real.log (1 + y) - tayLog k y) with hF
  set G : ℝ → ℝ := fun y => F y - y ^ (k + 1) / ((k : ℝ) + 1) with hG
  have hFderiv : ∀ y : ℝ, y ≠ -1 → HasDerivAt F (y ^ k / (1 + y)) y := by
    intro y hy
    have h := (hasDerivAt_log_sub_tayLog k y hy).const_mul ((-1 : ℝ) ^ k)
    refine h.congr_deriv ?_
    have hk : ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) = 1 := by
      rw [← mul_pow, show (-1 : ℝ) * (-1) = 1 by norm_num, one_pow]
    calc (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * y ^ k / (1 + y))
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * y ^ k / (1 + y) := by ring
      _ = y ^ k / (1 + y) := by rw [hk, one_mul]
  have hGderiv : ∀ y : ℝ, y ≠ -1 → HasDerivAt G (-(y ^ (k + 1) / (1 + y))) y := by
    intro y hy
    have hne : (1 : ℝ) + y ≠ 0 := by intro h; exact hy (by linarith)
    have h1 := hFderiv y hy
    have h2 : HasDerivAt (fun z : ℝ => z ^ (k + 1) / ((k : ℝ) + 1)) (y ^ k) y := by
      have h3 : HasDerivAt (fun z : ℝ => z ^ (k + 1)) (((k : ℝ) + 1) * y ^ k) y := by
        simpa using hasDerivAt_pow (k + 1) y
      have h4 := h3.div_const ((k : ℝ) + 1)
      rwa [mul_div_cancel_left₀ _ (by positivity : ((k : ℝ) + 1) ≠ 0)] at h4
    have h5 := h1.sub h2
    refine h5.congr_deriv ?_
    field_simp
    ring
  have hFmono : MonotoneOn F (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (D := Set.Icc 0 1)
      (f' := fun y : ℝ => y ^ k / (1 + y)) (convex_Icc 0 1) ?_ ?_ ?_
    · intro y hy
      exact ((hFderiv y (by have := hy.1; linarith)).continuousAt).continuousWithinAt
    · intro y hy
      exact (hFderiv y (by have h := (interior_subset hy).1; linarith)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hy
      have hy0 : 0 < y := hy'.1
      positivity
  have hGanti : AntitoneOn G (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Icc 0 1)
      (f' := fun y : ℝ => -(y ^ (k + 1) / (1 + y))) (convex_Icc 0 1) ?_ ?_ ?_
    · intro y hy
      exact ((hGderiv y (by have := hy.1; linarith)).continuousAt).continuousWithinAt
    · intro y hy
      exact (hGderiv y (by have h := (interior_subset hy).1; linarith)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hy
      have hy0 : 0 < y := hy'.1
      have hpos : 0 ≤ y ^ (k + 1) / (1 + y) := by positivity
      linarith
  have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hF0 : F 0 = 0 := by
    simp [hF, tayLog_zero]
  have hFge : 0 ≤ F x := by
    have h := hFmono hzero hxmem hx0
    rwa [hF0] at h
  have hGx : G x ≤ 0 := by
    have h := hGanti hzero hxmem hx0
    have h0 : G 0 = 0 := by
      simp [hG, hF0]
    rwa [h0] at h
  have hbound : F x ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [hG] at hGx
    linarith
  have habs : |F x| ≤ x ^ (k + 1) / ((k : ℝ) + 1) := by
    rw [abs_of_nonneg hFge]
    exact hbound
  have hval : F x = (-1 : ℝ) ^ k * (Real.log (1 + x) - tayLog k x) := rfl
  have : |Real.log (1 + x) - tayLog k x| = |F x| := by
    rw [hval, abs_mul, show |(-1 : ℝ) ^ k| = 1 by
      rw [abs_pow, show |(-1 : ℝ)| = 1 by norm_num, one_pow], one_mul]
  rw [this]
  exact habs

/-! ## Elementary finite-interval lemmas -/

/-- Reindexing a `Finset.Ioc` sum by a shift: the map `n ↦ n + c` is a bijection
`Ioc (K-c) (L-c) → Ioc K L` when `c ≤ K`. -/
theorem sum_Ioc_shift (K L c : ℕ) (f : ℕ → ℂ) (hc : c ≤ K) :
    ∑ n ∈ Finset.Ioc (K - c) (L - c), f (n + c) = ∑ m ∈ Finset.Ioc K L, f m := by
  refine Finset.sum_bij (fun n _ => n + c) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  · intro n₁ h₁ n₂ h₂ heq
    simp only [Finset.mem_Ioc] at h₁ h₂
    omega
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    exact ⟨m - c, by simp only [Finset.mem_Ioc]; omega, by omega⟩
  · intro n hn
    rfl

/-- Shifting the upper end of the interval `Ioc K (L-1)` down by `c` changes the sum by at most
`2c` in norm, when the summand has norm at most `1` everywhere. -/
theorem ioc_sdiff_bound (K L c : ℕ) (f : ℕ → ℂ) (hc : 1 ≤ c) (hcK : c ≤ K)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Ioc (K - c) (L - c), f n) - ∑ n ∈ Finset.Ioc K (L - 1), f n‖
      ≤ 2 * (c : ℝ) := by
  set A : Finset ℕ := Finset.Ioc (K - c) (L - c) with hA
  set B : Finset ℕ := Finset.Ioc K (L - 1) with hB
  have hsplit : (∑ n ∈ A, f n) - ∑ n ∈ B, f n
      = (∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n := by
    have h1 : (∑ n ∈ A, f n) = (∑ n ∈ A \ B, f n) + ∑ n ∈ A ∩ B, f n := by
      rw [← Finset.sum_sdiff (Finset.inter_subset_left (s₁ := A) (s₂ := B)),
        Finset.sdiff_inter_self_left A B]
    have h2 : (∑ n ∈ B, f n) = (∑ n ∈ B \ A, f n) + ∑ n ∈ A ∩ B, f n := by
      rw [← Finset.sum_sdiff (Finset.inter_subset_right (s₁ := A) (s₂ := B)),
        Finset.sdiff_inter_self_right B A, Finset.inter_comm]
    rw [h1, h2]
    ring
  have hcardA : ((A \ B).card : ℝ) ≤ (c : ℝ) := by
    have hsub : A \ B ⊆ Finset.Ioc (K - c) K := by
      intro n hn
      rw [Finset.mem_sdiff] at hn
      obtain ⟨hnA, hnB⟩ := hn
      rw [hA, Finset.mem_Ioc] at hnA
      rw [hB, Finset.mem_Ioc] at hnB
      rw [Finset.mem_Ioc]
      refine ⟨hnA.1, ?_⟩
      by_contra hcon
      have hL : L - 1 < n := by
        by_contra hL'
        exact hnB ⟨not_le.mp hcon, not_lt.mp hL'⟩
      omega
    calc ((A \ B).card : ℝ) ≤ ((Finset.Ioc (K - c) K).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = (c : ℝ) := by
          have h : (Finset.Ioc (K - c) K).card = c := by
            rw [Nat.card_Ioc]
            omega
          rw [h]
  have hcardB : ((B \ A).card : ℝ) ≤ (c : ℝ) := by
    have hsub : B \ A ⊆ Finset.Ioc (L - c) (L - 1) := by
      intro n hn
      rw [Finset.mem_sdiff] at hn
      obtain ⟨hnB, hnA⟩ := hn
      rw [hB, Finset.mem_Ioc] at hnB
      rw [hA, Finset.mem_Ioc] at hnA
      rw [Finset.mem_Ioc]
      refine ⟨?_, hnB.2⟩
      by_contra hcon
      have hK : n ≤ K - c := by
        by_contra hK'
        exact hnA ⟨not_le.mp hK', not_lt.mp hcon⟩
      omega
    calc ((B \ A).card : ℝ) ≤ ((Finset.Ioc (L - c) (L - 1)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ (c : ℝ) := by
          exact Nat.cast_le.mpr (by rw [Nat.card_Ioc]; omega)
  calc ‖(∑ n ∈ A, f n) - ∑ n ∈ B, f n‖
      = ‖(∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n‖ := by rw [hsplit]
    _ ≤ ‖∑ n ∈ A \ B, f n‖ + ‖∑ n ∈ B \ A, f n‖ := norm_sub_le _ _
    _ ≤ ((A \ B).card : ℝ) + ((B \ A).card : ℝ) := by
        have h1 : ‖∑ n ∈ A \ B, f n‖ ≤ ((A \ B).card : ℝ) := by
          calc ‖∑ n ∈ A \ B, f n‖ ≤ ∑ n ∈ A \ B, ‖f n‖ := norm_sum_le _ _
            _ ≤ ∑ _n ∈ A \ B, (1 : ℝ) := Finset.sum_le_sum fun n _ => hf n
            _ = ((A \ B).card : ℝ) := by simp
        have h2 : ‖∑ n ∈ B \ A, f n‖ ≤ ((B \ A).card : ℝ) := by
          calc ‖∑ n ∈ B \ A, f n‖ ≤ ∑ n ∈ B \ A, ‖f n‖ := norm_sum_le _ _
            _ ≤ ∑ _n ∈ B \ A, (1 : ℝ) := Finset.sum_le_sum fun n _ => hf n
            _ = ((B \ A).card : ℝ) := by simp
        linarith
    _ ≤ 2 * (c : ℝ) := by linarith

theorem Ssum_le_Usum (k : ℕ) (hk : 1 ≤ k) (N t u R : ℝ) (M₁ M₂ : ℕ)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hMprod : (M₁ : ℝ) * (M₂ : ℝ) ≤ N) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u ≤ 1) (hN : 1 ≤ N) (hR : N < R) (hR2 : R ≤ 2 * N) :
    ∃ z : ℝ, N < z ∧ z ≤ 2 * N ∧
      ‖Ssum N u t R‖
        ≤ 2 * ((M₁ : ℝ) * (M₂ : ℝ))
          + t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k)
          + (N / ((M₁ : ℝ) * (M₂ : ℝ)))
              * ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t z)‖ := by
  set M : ℝ := (M₁ : ℝ) * (M₂ : ℝ) with hMdef
  have hM1 : (1 : ℝ) ≤ (M₁ : ℝ) := Nat.one_le_cast.mpr hM₁
  have hM2 : (1 : ℝ) ≤ (M₂ : ℝ) := Nat.one_le_cast.mpr hM₂
  have hMpos : 0 < M := by rw [hMdef]; nlinarith
  have hMge1 : 1 ≤ M := by rw [hMdef]; nlinarith
  set F0 : ℕ → ℂ := fun m => ((((m : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) with hF0def
  have hSsum : Ssum N u t R = ∑ m ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, F0 m := by rw [hF0def]; rfl
  -- floor facts
  have hNr : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hRr : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hNlt : N < ((⌊N⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one N
  have hMle : M₁ * M₂ ≤ ⌊N⌋₊ := by
    have h1 : ((M₁ * M₂ : ℕ) : ℝ) ≤ N := by
      have h2 : ((M₁ * M₂ : ℕ) : ℝ) = (M₁ : ℝ) * (M₂ : ℝ) := by push_cast; ring
      rw [h2]; exact hMprod
    exact Nat.le_floor h1
  -- the maximum function and the error constant
  set Phi : ℕ → ℝ :=
    fun n => ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((n : ℝ) + u))‖ with hPhidef
  have hPhieq : ∀ n : ℕ, Phi n =
      ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((n : ℝ) + u))‖ := by
    intro n; rw [hPhidef]
  set E : ℝ := t * M ^ (k + 2) / (((k : ℝ) + 1) * N ^ (k + 1)) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  -- the cardinality bound on the fixed interval
  have hFixCard : ((Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1)).card : ℝ) ≤ N := by
    rw [Nat.card_Ioc]
    have hb : N - 1 < ((⌊N⌋₊ : ℕ) : ℝ) := by linarith [hNlt]
    rcases le_or_gt (⌊N⌋₊ + 1) ⌊R⌋₊ with h | h
    · have hsub : ⌊R⌋₊ - 1 - ⌊N⌋₊ = ⌊R⌋₊ - (⌊N⌋₊ + 1) := by omega
      rw [hsub, Nat.cast_sub h]
      push_cast
      linarith
    · have hzero : ⌊R⌋₊ - 1 - ⌊N⌋₊ = 0 := by omega
      rw [hzero]
      push_cast
      linarith
  -- the main estimate with an arbitrary "extra" constant `b`
  have hmain : ∀ b : ℝ, 0 ≤ b →
      (∀ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), Phi n + E ≤ b) →
      ‖Ssum N u t R‖ ≤ 2 * M + (N / M) * b := by
    intro b hb0 hb
    -- the per-`(a,b')` shift identity
    have hshift : ∀ a ∈ Finset.Icc 1 M₁, ∀ b' ∈ Finset.Icc 1 M₂,
        (∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
          = Ssum N u t R := by
      intro a ha b' hb'
      have hab : a * b' ≤ ⌊N⌋₊ := by
        have h1 : a ≤ M₁ := (Finset.mem_Icc.mp ha).2
        have h2 : b' ≤ M₂ := (Finset.mem_Icc.mp hb').2
        exact le_trans (Nat.mul_le_mul h1 h2) hMle
      rw [sum_Ioc_shift ⌊N⌋₊ ⌊R⌋₊ (a * b') F0 hab]
      exact hSsum.symm
    -- the boundary error
    have hsdiff : ∀ a ∈ Finset.Icc 1 M₁, ∀ b' ∈ Finset.Icc 1 M₂,
        ‖(∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
          - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')‖ ≤ 2 * ((a * b' : ℕ) : ℝ) := by
      intro a ha b' hb'
      have h1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have h2 : 1 ≤ b' := (Finset.mem_Icc.mp hb').1
      have hab1 : 1 ≤ a * b' := by
        rw [Nat.one_le_iff_ne_zero]
        exact Nat.mul_ne_zero (by omega) (by omega)
      have hab : a * b' ≤ ⌊N⌋₊ := by
        have h1' : a ≤ M₁ := (Finset.mem_Icc.mp ha).2
        have h2' : b' ≤ M₂ := (Finset.mem_Icc.mp hb').2
        exact le_trans (Nat.mul_le_mul h1' h2') hMle
      refine ioc_sdiff_bound ⌊N⌋₊ ⌊R⌋₊ (a * b') (fun n => F0 (n + a * b')) hab1 hab ?_
      intro n
      rw [hF0def, norm_cpow_neg_I_mul_eq_one _ t (by positivity)]
    -- the per-`n` bound
    have hnb : ∀ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1),
        ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b')‖ ≤ Phi n + E := by
      intro n hn
      have hnN : ⌊N⌋₊ < n := (Finset.mem_Ioc.mp hn).1
      have hMn : M₁ * M₂ ≤ n := le_trans hMle (by omega)
      have hMz : (M₁ : ℝ) * (M₂ : ℝ) ≤ (n : ℝ) + u := by
        have h1 : ((M₁ * M₂ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hMn
        have h2 : ((M₁ * M₂ : ℕ) : ℝ) = (M₁ : ℝ) * (M₂ : ℝ) := by push_cast; ring
        rw [h2] at h1
        linarith [hu.le]
      have hkey := Work.BMF.Ssum.norm_ab_sum_sub_Usum_le k hk t u n M₁ M₂ ht.le hu.le hM₁ hM₂ hMz
      have hsum_eq : (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b'))
          = (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ((((n : ℝ) + (a : ℝ) * (b' : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
        refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b' hb' => ?_
        rw [hF0def]
        push_cast
        ring_nf
      rw [hsum_eq, hPhieq n]
      refine le_trans hkey ?_
      -- bound the Taylor error by `E`
      have herr : t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 2)
            / (((k : ℝ) + 1) * ((n : ℝ) + u) ^ (k + 1)) ≤ E := by
        have hzN : N ≤ (n : ℝ) + u := by
          have h3 : ((⌊N⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
            have h4 : ⌊N⌋₊ + 1 ≤ n := hnN
            calc ((⌊N⌋₊ : ℕ) : ℝ) + 1 = ((⌊N⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ (n : ℝ) := Nat.cast_le.mpr h4
          linarith [hNlt, h3, hu.le]
        have hpow : N ^ (k + 1) ≤ ((n : ℝ) + u) ^ (k + 1) :=
          pow_le_pow_left₀ (by linarith) hzN (k + 1)
        have hD : ((k : ℝ) + 1) * N ^ (k + 1) ≤ ((k : ℝ) + 1) * ((n : ℝ) + u) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        have hdiv := div_le_div_of_nonneg_left
          (show (0 : ℝ) ≤ t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 2) by positivity)
          (show (0 : ℝ) < ((k : ℝ) + 1) * N ^ (k + 1) by positivity) hD
        rw [hEdef, hMdef]
        exact hdiv
      linarith [herr]
    -- the double sum of `(a,b')` copies of `Ssum`
    have hcard : (∑ _a ∈ Finset.Icc 1 M₁, ∑ _b' ∈ Finset.Icc 1 M₂, (1 : ℂ)) = (M : ℂ) := by
      have hinner : ∀ a : ℕ, (∑ _b' ∈ Finset.Icc 1 M₂, (1 : ℂ)) = (M₂ : ℂ) := by
        intro a
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl (fun a _ => hinner a)]
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [hMdef]
      push_cast
      ring
    have hMS : (M : ℂ) * Ssum N u t R
        = ∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, Ssum N u t R := by
      rw [← hcard, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_mul]
      simp
    have hsplit : (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, Ssum N u t R)
        = (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))
          + (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
                - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))) := by
      have hp : ∀ a ∈ Finset.Icc 1 M₁, ∀ b' ∈ Finset.Icc 1 M₂,
          Ssum N u t R = (∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))
            + ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
                - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')) := by
        intro a ha b' hb'
        rw [← hshift a ha b' hb']
        ring
      calc (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, Ssum N u t R)
          = (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ((∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))
                + ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
                    - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')))) :=
            Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b' hb' => hp a ha b' hb'
        _ = _ := by simp only [Finset.sum_add_distrib]
    -- the two pieces
    have hX : ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
          ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')‖ ≤ N * b := by
      have hswap : (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
            ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))
          = ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), ∑ a ∈ Finset.Icc 1 M₁,
              ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b') := by
        calc (∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))
            = ∑ a ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1),
                ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b') :=
              Finset.sum_congr rfl fun a ha => Finset.sum_comm
          _ = ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), ∑ a ∈ Finset.Icc 1 M₁,
                ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b') := Finset.sum_comm
      calc ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')‖
          = ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), ∑ a ∈ Finset.Icc 1 M₁,
              ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b')‖ := by rw [hswap]
        _ ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1),
              ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, F0 (n + a * b')‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), b :=
            Finset.sum_le_sum (fun n hn => le_trans (hnb n hn) (hb n hn))
        _ = ((Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1)).card : ℝ) * b := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * b := mul_le_mul_of_nonneg_right hFixCard hb0
    have hY : ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
          ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
            - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))‖ ≤ 2 * M * M := by
      calc ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
            ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
              - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))‖
          ≤ ∑ a ∈ Finset.Icc 1 M₁, ‖∑ b' ∈ Finset.Icc 1 M₂,
              ((∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
                - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b'))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂,
              ‖(∑ n ∈ Finset.Ioc (⌊N⌋₊ - a * b') (⌊R⌋₊ - a * b'), F0 (n + a * b'))
                - ∑ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), F0 (n + a * b')‖ :=
            Finset.sum_le_sum fun a ha => norm_sum_le _ _
        _ ≤ ∑ a ∈ Finset.Icc 1 M₁, ∑ b' ∈ Finset.Icc 1 M₂, 2 * ((a * b' : ℕ) : ℝ) :=
            Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b' hb' => hsdiff a ha b' hb'
        _ ≤ ∑ _a ∈ Finset.Icc 1 M₁, ∑ _b' ∈ Finset.Icc 1 M₂, 2 * (M₁ : ℝ) * (M₂ : ℝ) := by
            refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b' hb' => ?_
            have h1 : (a : ℝ) ≤ (M₁ : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp ha).2
            have h2 : (b' : ℝ) ≤ (M₂ : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hb').2
            have h3 : ((a * b' : ℕ) : ℝ) = (a : ℝ) * (b' : ℝ) := by push_cast; ring
            have h4 : (0 : ℝ) ≤ (a : ℝ) := by positivity
            rw [h3]
            nlinarith
        _ = 2 * M * M := by
            rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Nat.card_Icc,
              Nat.add_sub_cancel, Nat.add_sub_cancel, nsmul_eq_mul, nsmul_eq_mul]
            rw [hMdef]
            ring
    -- combine
    have hbnd : ‖Ssum N u t R‖ * M ≤ N * b + 2 * M * M := by
      have h1 : ‖(M : ℂ) * Ssum N u t R‖ ≤ N * b + 2 * M * M := by
        rw [hMS, hsplit]
        exact le_trans (norm_add_le _ _) (add_le_add hX hY)
      have hMnorm : ‖(M : ℂ)‖ = M := RCLike.norm_of_nonneg (K := ℂ) hMpos.le
      rw [norm_mul, hMnorm] at h1
      linarith
    have h2 : ‖Ssum N u t R‖ ≤ (N * b + 2 * (M * M)) / M := by
      rw [le_div_iff₀ hMpos]
      linarith
    calc ‖Ssum N u t R‖ ≤ (N * b + 2 * (M * M)) / M := h2
      _ = 2 * M + (N / M) * b := by
          rw [show N * b + 2 * (M * M) = (2 * M + (N / M) * b) * M by
            field_simp
            ring]
          rw [mul_div_cancel_right₀ _ hMpos.ne']
  -- conclude
  by_cases hne : (Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1)).Nonempty
  · obtain ⟨nstar, hnstarmem, hmax⟩ := Finset.exists_max_image (Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1)) Phi
      hne
    have hb0 : 0 ≤ Phi nstar + E := by
      have := norm_nonneg (Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((nstar : ℝ) + u)))
      rw [hPhieq nstar]
      linarith
    have hb : ∀ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), Phi n + E ≤ Phi nstar + E :=
      fun n hn => by linarith [hmax n hn]
    have hmain' := hmain (Phi nstar + E) hb0 hb
    have hnN : ⌊N⌋₊ < nstar := (Finset.mem_Ioc.mp hnstarmem).1
    have hnR : nstar ≤ ⌊R⌋₊ - 1 := (Finset.mem_Ioc.mp hnstarmem).2
    refine ⟨(nstar : ℝ) + u, ?_, ?_, ?_⟩
    · have h1 : ((⌊N⌋₊ : ℕ) : ℝ) + 1 ≤ (nstar : ℝ) := by
        have h4 : ⌊N⌋₊ + 1 ≤ nstar := hnN
        calc ((⌊N⌋₊ : ℕ) : ℝ) + 1 = ((⌊N⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (nstar : ℝ) := Nat.cast_le.mpr h4
      linarith [hNlt, h1, hu]
    · rcases Nat.eq_zero_or_pos ⌊R⌋₊ with hR0 | hRpos
      · have hz : nstar = 0 := by omega
        subst hz
        push_cast
        linarith [hu1, hN]
      · have h2 : ((nstar : ℕ) : ℝ) ≤ (⌊R⌋₊ : ℝ) - 1 := by
          have hsub : ((⌊R⌋₊ - 1 : ℕ) : ℝ) = (⌊R⌋₊ : ℝ) - 1 := by
            rw [Nat.cast_sub hRpos, Nat.cast_one]
          rw [← hsub]
          exact Nat.cast_le.mpr hnR
        linarith [h2, hRr, hu1, hR2]
    · have hEbound : (N / M) * E ≤ t * M ^ (k + 1) / ((k : ℝ) * N ^ k) := by
          rw [hEdef]
          have hid : (N / M) * (t * M ^ (k + 2) / (((k : ℝ) + 1) * N ^ (k + 1)))
              = t * M ^ (k + 1) / (((k : ℝ) + 1) * N ^ k) := by
            rw [show k + 2 = k + 1 + 1 from by ring, pow_succ, pow_succ]
            field_simp
            ring
          rw [hid]
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
          have hNk : 0 ≤ N ^ k := by positivity
          nlinarith
      have hdist : (N / M) * (Phi nstar + E) = (N / M) * Phi nstar + (N / M) * E := by ring
      rw [hdist, hPhieq nstar] at hmain'
      rw [hMdef] at hmain' hEbound
      linarith
  · refine ⟨(N + R) / 2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · have hb : ∀ n ∈ Finset.Ioc ⌊N⌋₊ (⌊R⌋₊ - 1), Phi n + E ≤ 0 :=
        fun n hn => absurd ⟨n, hn⟩ hne
      have hmain' := hmain 0 le_rfl hb
      have h1 : 0 ≤ t * ((M₁ : ℝ) * (M₂ : ℝ)) ^ (k + 1) / ((k : ℝ) * N ^ k) := by positivity
      have h2 : 0 ≤ (N / ((M₁ : ℝ) * (M₂ : ℝ)))
          * ‖Usum k M₁ M₂ (fun j : Fin k => gam ((j : ℕ) + 1) t ((N + R) / 2))‖ := by positivity
      rw [hMdef] at hmain'
      linarith

end

end Work.BMF
