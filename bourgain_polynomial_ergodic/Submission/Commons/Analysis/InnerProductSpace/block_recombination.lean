import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Commons.Analysis.InnerProductSpace.norm_sum_sq_of_orthogonal

open Finset

namespace Commons.Analysis.InnerProductSpace

/-- For `n ≥ 2`, the upper half `⌈n/2⌉` has `clog 2` at most `clog 2 n - 1`. -/
private lemma clog2_half_succ_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 ((n + 1) / 2) ≤ Nat.clog 2 n - 1 := by
  set k := Nat.clog 2 n with hk
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hn)
  have hle : n ≤ 2 ^ k := by rw [hk]; exact Nat.le_pow_clog (by norm_num) n
  have h2 : (n + 1) / 2 ≤ 2 ^ (k - 1) := by
    have h1 : (n + 1) / 2 ≤ (2 ^ k + 1) / 2 := Nat.div_le_div_right (by omega)
    have h3 : (2 ^ k + 1) / 2 = 2 ^ (k - 1) := by
      have h : 2 ^ k = 2 ^ (k - 1) * 2 := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [pow_succ]
      rw [h]; omega
    omega
  exact Nat.clog_le_of_le_pow h2

/-- For `n ≥ 2`, the lower half `⌊n/2⌋` has `clog 2` at most `clog 2 n - 1`. -/
private lemma clog2_half_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.clog 2 (n / 2) ≤ Nat.clog 2 n - 1 := by
  set k := Nat.clog 2 n with hk
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hn)
  have hle : n ≤ 2 ^ k := by rw [hk]; exact Nat.le_pow_clog (by norm_num) n
  have h2 : n / 2 ≤ 2 ^ (k - 1) := by
    have h1 : n / 2 ≤ 2 ^ k / 2 := Nat.div_le_div_right hle
    have h3 : 2 ^ k / 2 = 2 ^ (k - 1) := by
      have h : 2 ^ k = 2 ^ (k - 1) * 2 := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega]
        rw [pow_succ]
      rw [h, Nat.mul_div_cancel _ (by norm_num)]
    omega
  exact Nat.clog_le_of_le_pow h2

/-- Numerical kernel of the induction: if `p, q ≤ k - 1`, `B ≥ 0`, `k ≥ 1` and the two
energies `SL, SR` are nonnegative, then the recombination quadratic form is bounded by
`(B + k/2)^2 (SL + SR)`. -/
private lemma arith_ineq (B p q k SL SR : ℝ) (hB : 0 ≤ B) (hk : 1 ≤ k)
    (hp : p ≤ k - 1) (hq : q ≤ k - 1) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hSL : 0 ≤ SL) (hSR : 0 ≤ SR) :
    (B + (1/2) * p) ^ 2 * SL + 2 * (B + (1/2) * q) * Real.sqrt SL * Real.sqrt SR
      + (B + (1/2) * q) ^ 2 * SR
    ≤ (B + (1/2) * k) ^ 2 * (SL + SR) := by
  have hu : 0 ≤ Real.sqrt SL := Real.sqrt_nonneg SL
  have hv : 0 ≤ Real.sqrt SR := Real.sqrt_nonneg SR
  have hu2 : Real.sqrt SL ^ 2 = SL := Real.sq_sqrt hSL
  have hv2 : Real.sqrt SR ^ 2 = SR := Real.sq_sqrt hSR
  set d := B + (1/2) * (k - 1) with hd
  have hd0 : 0 ≤ d := by rw [hd]; nlinarith
  have hCp : 0 ≤ B + (1/2) * p := by nlinarith
  have hCq : 0 ≤ B + (1/2) * q := by nlinarith
  have hpd : B + (1/2) * p ≤ d := by rw [hd]; nlinarith
  have hqd : B + (1/2) * q ≤ d := by rw [hd]; nlinarith
  have hp2 : (B + (1/2) * p) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hCp hpd 2
  have hq2 : (B + (1/2) * q) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hCq hqd 2
  have hamgm : 2 * Real.sqrt SL * Real.sqrt SR ≤ SL + SR := by
    nlinarith [sq_nonneg (Real.sqrt SL - Real.sqrt SR), hu2, hv2]
  have hcd : B + (1/2) * k = d + 1 / 2 := by rw [hd]; ring
  have step1 : (B + (1/2) * p) ^ 2 * SL + 2 * (B + (1/2) * q) * Real.sqrt SL * Real.sqrt SR
      + (B + (1/2) * q) ^ 2 * SR
      ≤ d ^ 2 * SL + 2 * d * Real.sqrt SL * Real.sqrt SR + d ^ 2 * SR := by
    have h1 := mul_le_mul_of_nonneg_right hp2 hSL
    have h3 := mul_le_mul_of_nonneg_right hq2 hSR
    have h2 : 2 * (B + (1/2) * q) * Real.sqrt SL * Real.sqrt SR
        ≤ 2 * d * Real.sqrt SL * Real.sqrt SR := by
      have hfac : 0 ≤ Real.sqrt SL * Real.sqrt SR := mul_nonneg hu hv
      nlinarith [hfac, hqd]
    nlinarith [h1, h2, h3]
  have step2 : d ^ 2 * SL + 2 * d * Real.sqrt SL * Real.sqrt SR + d ^ 2 * SR
      ≤ (B + (1/2) * k) ^ 2 * (SL + SR) := by
    have h2 : 2 * d * Real.sqrt SL * Real.sqrt SR ≤ d * (SL + SR) := by
      calc 2 * d * Real.sqrt SL * Real.sqrt SR
          = d * (2 * Real.sqrt SL * Real.sqrt SR) := by ring
        _ ≤ d * (SL + SR) := mul_le_mul_of_nonneg_left hamgm hd0
    have hdd : d ^ 2 + d ≤ (B + (1/2) * k) ^ 2 := by rw [hcd]; nlinarith
    have hSS : 0 ≤ SL + SR := add_nonneg hSL hSR
    calc d ^ 2 * SL + 2 * d * Real.sqrt SL * Real.sqrt SR + d ^ 2 * SR
        ≤ d ^ 2 * SL + d * (SL + SR) + d ^ 2 * SR := by linarith
      _ = (d ^ 2 + d) * (SL + SR) := by ring
      _ ≤ (B + (1/2) * k) ^ 2 * (SL + SR) := mul_le_mul_of_nonneg_right hdd hSS
  linarith [step1, step2]

theorem block_recombination {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : ℝ) (hB : 0 ≤ B) (a b : ℕ) (hab : a ≤ b) (φ f : ℕ → E)
    (hbd : ∀ r ∈ Finset.Ico a b, ‖φ r‖ ≤ B * ‖f r‖)
    (hcollapse : ∀ r ∈ Finset.Ico a b, ∀ s ∈ Finset.Ico a b, r < s →
      inner ℂ (φ r) (φ s) = inner ℂ (f r) (φ s))
    (horth : ∀ r ∈ Finset.Ico a b, ∀ s ∈ Finset.Ico a b, r ≠ s →
      inner ℂ (f r) (f s) = 0) :
    ‖∑ r ∈ Finset.Ico a b, φ r‖ ≤
      (B + (1/2) * (Nat.clog 2 (b - a) : ℝ)) * Real.sqrt (∑ r ∈ Finset.Ico a b, ‖f r‖ ^ 2) := by
  have key : ∀ n : ℕ, ∀ (a : ℕ) (φ f : ℕ → E),
      (∀ r ∈ Finset.Ico a (a + n), ‖φ r‖ ≤ B * ‖f r‖) →
      (∀ r ∈ Finset.Ico a (a + n), ∀ s ∈ Finset.Ico a (a + n), r < s →
        inner ℂ (φ r) (φ s) = inner ℂ (f r) (φ s)) →
      (∀ r ∈ Finset.Ico a (a + n), ∀ s ∈ Finset.Ico a (a + n), r ≠ s →
        inner ℂ (f r) (f s) = 0) →
      ‖∑ r ∈ Finset.Ico a (a + n), φ r‖ ≤
        (B + (1/2) * (Nat.clog 2 n : ℝ)) * Real.sqrt (∑ r ∈ Finset.Ico a (a + n), ‖f r‖ ^ 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a φ f hbd hcol horth
      rcases Nat.lt_or_ge n 2 with hnlt | hnge
      · -- n = 0 or n = 1
        interval_cases n
        · -- n = 0
          have hcl : Nat.clog 2 0 = 0 := by decide
          simp [hcl]
        · -- n = 1
          have hcl : Nat.clog 2 1 = 0 := by decide
          have hIco : Finset.Ico a (a + 1) = {a} := by
            ext r; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [hcl, hIco]
          simp only [Finset.sum_singleton, Nat.cast_zero, mul_zero, add_zero]
          rw [Real.sqrt_sq (norm_nonneg (f a))]
          exact hbd a (Finset.mem_Ico.mpr ⟨le_refl a, Nat.lt_succ_self a⟩)
      · -- n ≥ 2
        set m := (n + 1) / 2 with hm
        set t := n / 2 with ht
        have hmt : m + t = n := by omega
        have hm_lt : m < n := by omega
        have ht_lt : t < n := by omega
        have hk1 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hnge)
        have hcm : Nat.clog 2 m ≤ Nat.clog 2 n - 1 := by rw [hm]; exact clog2_half_succ_le n hnge
        have hct : Nat.clog 2 t ≤ Nat.clog 2 n - 1 := by rw [ht]; exact clog2_half_le n hnge
        have hcmR : (Nat.clog 2 m : ℝ) ≤ (Nat.clog 2 n : ℝ) - 1 := by
          have h' : (Nat.clog 2 m : ℝ) ≤ ((Nat.clog 2 n - 1 : ℕ) : ℝ) := by exact_mod_cast hcm
          rw [Nat.cast_sub hk1] at h'
          simpa using h'
        have hctR : (Nat.clog 2 t : ℝ) ≤ (Nat.clog 2 n : ℝ) - 1 := by
          have h' : (Nat.clog 2 t : ℝ) ≤ ((Nat.clog 2 n - 1 : ℕ) : ℝ) := by exact_mod_cast hct
          rw [Nat.cast_sub hk1] at h'
          simpa using h'
        -- sub-hypotheses
        have hsubL : Finset.Ico a (a + m) ⊆ Finset.Ico a (a + n) := by
          intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
        have hsubR : Finset.Ico (a + m) ((a + m) + t) ⊆ Finset.Ico a (a + n) := by
          intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
        have hL := ih m hm_lt a φ f
          (fun r hr => hbd r (hsubL hr))
          (fun r hr s hs hrs => hcol r (hsubL hr) s (hsubL hs) hrs)
          (fun r hr s hs hne => horth r (hsubL hr) s (hsubL hs) hne)
        have hR := ih t ht_lt (a + m) φ f
          (fun r hr => hbd r (hsubR hr))
          (fun r hr s hs hrs => hcol r (hsubR hr) s (hsubR hs) hrs)
          (fun r hr s hs hne => horth r (hsubR hr) s (hsubR hs) hne)
        have hamt : (a + m) + t = a + n := by omega
        rw [hamt] at hR
        -- set up abbreviations
        set ΦL : E := ∑ r ∈ Finset.Ico a (a + m), φ r with hΦL
        set ΦR : E := ∑ r ∈ Finset.Ico (a + m) (a + n), φ r with hΦR
        set fL : E := ∑ r ∈ Finset.Ico a (a + m), f r with hfL
        set SL : ℝ := ∑ r ∈ Finset.Ico a (a + m), ‖f r‖ ^ 2 with hSLdef
        set SR : ℝ := ∑ r ∈ Finset.Ico (a + m) (a + n), ‖f r‖ ^ 2 with hSRdef
        have hSLnn : 0 ≤ SL := by rw [hSLdef]; exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
        have hSRnn : 0 ≤ SR := by rw [hSRdef]; exact Finset.sum_nonneg (fun r _ => sq_nonneg _)
        -- cross term identity
        have hcross : inner ℂ ΦL ΦR = inner ℂ fL ΦR := by
          rw [hΦL, sum_inner, hfL, sum_inner]
          apply Finset.sum_congr rfl
          intro r hr
          rw [hΦR, inner_sum, inner_sum]
          apply Finset.sum_congr rfl
          intro s hs
          exact hcol r (hsubL hr) s (hsubR (by rw [hamt]; exact hs)) (by
            have hr2 := (Finset.mem_Ico.mp hr).2
            have hs1 := (Finset.mem_Ico.mp hs).1
            omega)
        have hre : RCLike.re (inner ℂ ΦL ΦR) ≤ ‖fL‖ * ‖ΦR‖ := by
          rw [hcross]
          calc RCLike.re (inner ℂ fL ΦR) ≤ ‖inner ℂ fL ΦR‖ := RCLike.re_le_norm _
            _ ≤ ‖fL‖ * ‖ΦR‖ := norm_inner_le_norm _ _
        have horthL2 : ∀ r ∈ Finset.Ico a (a + m), ∀ s ∈ Finset.Ico a (a + m), r ≠ s →
            inner ℂ (f r) (f s) = 0 :=
          fun r hr s hs hne => horth r (hsubL hr) s (hsubL hs) hne
        have hfLsq : ‖fL‖ ^ 2 = SL := by
          rw [hfL, hSLdef]
          exact Commons.Analysis.InnerProductSpace.norm_sum_sq_of_orthogonal _ _ horthL2
        have hfLnorm : ‖fL‖ = Real.sqrt SL := by
          rw [← hfLsq, Real.sqrt_sq (norm_nonneg fL)]
        -- squared bounds for the two blocks
        have hXL : ‖ΦL‖ ^ 2 ≤ (B + (1/2) * (Nat.clog 2 m : ℝ)) ^ 2 * SL := by
          have h0 : 0 ≤ B + (1/2) * (Nat.clog 2 m : ℝ) := by positivity
          have hsq : Real.sqrt SL ^ 2 = SL := Real.sq_sqrt hSLnn
          have hmul := mul_self_le_mul_self (norm_nonneg ΦL) hL
          nlinarith [hmul, hsq]
        have hXR : ‖ΦR‖ ^ 2 ≤ (B + (1/2) * (Nat.clog 2 t : ℝ)) ^ 2 * SR := by
          have h0 : 0 ≤ B + (1/2) * (Nat.clog 2 t : ℝ) := by positivity
          have hsq : Real.sqrt SR ^ 2 = SR := Real.sq_sqrt hSRnn
          have hmul := mul_self_le_mul_self (norm_nonneg ΦR) hR
          nlinarith [hmul, hsq]
        have hCn : 0 ≤ B + (1/2) * (Nat.clog 2 n : ℝ) := by positivity
        have hk1R : (1:ℝ) ≤ (Nat.clog 2 n : ℝ) := by exact_mod_cast hk1
        have harith := arith_ineq B (Nat.clog 2 m : ℝ) (Nat.clog 2 t : ℝ)
          (Nat.clog 2 n : ℝ) SL SR hB hk1R hcmR hctR
          (by positivity) (by positivity) hSLnn hSRnn
        have hnorm : ‖ΦL + ΦR‖ ^ 2
            = ‖ΦL‖ ^ 2 + 2 * RCLike.re (inner ℂ ΦL ΦR) + ‖ΦR‖ ^ 2 := norm_add_sq ΦL ΦR
        have hsum2 : ‖ΦL + ΦR‖ ^ 2 ≤ (B + (1/2) * (Nat.clog 2 n : ℝ)) ^ 2 * (SL + SR) := by
          have hcrossbd : 2 * RCLike.re (inner ℂ ΦL ΦR)
              ≤ 2 * ((B + (1/2) * (Nat.clog 2 t : ℝ)) * Real.sqrt SL * Real.sqrt SR) := by
            have h1 : RCLike.re (inner ℂ ΦL ΦR) ≤ Real.sqrt SL * ‖ΦR‖ := by
              rw [← hfLnorm]; exact hre
            have h2 : ‖ΦR‖ ≤ (B + (1/2) * (Nat.clog 2 t : ℝ)) * Real.sqrt SR := hR
            have h3 : 0 ≤ Real.sqrt SL := Real.sqrt_nonneg SL
            have h4 : 0 ≤ B + (1/2) * (Nat.clog 2 t : ℝ) := by positivity
            have h5 : 0 ≤ Real.sqrt SR := Real.sqrt_nonneg SR
            nlinarith [h1, h2, h3, h4, h5]
          rw [hnorm]
          linarith [hXL, hXR, hcrossbd, harith]
        -- conclude by taking square roots
        have hgoal : ‖ΦL + ΦR‖ ≤ (B + (1/2) * (Nat.clog 2 n : ℝ)) * Real.sqrt (SL + SR) := by
          have hSS : 0 ≤ SL + SR := add_nonneg hSLnn hSRnn
          calc ‖ΦL + ΦR‖ = Real.sqrt (‖ΦL + ΦR‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
            _ ≤ Real.sqrt ((B + (1/2) * (Nat.clog 2 n : ℝ)) ^ 2 * (SL + SR)) :=
                Real.sqrt_le_sqrt hsum2
            _ = (B + (1/2) * (Nat.clog 2 n : ℝ)) * Real.sqrt (SL + SR) := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCn]
        have hsumφ : (∑ r ∈ Finset.Ico a (a + n), φ r) = ΦL + ΦR := by
          rw [hΦL, hΦR]
          rw [← Finset.Ico_union_Ico_eq_Ico (by omega : a ≤ a + m) (by omega : a + m ≤ a + n)]
          exact Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a (a + m) (a + n))
        have hsumf : (∑ r ∈ Finset.Ico a (a + n), ‖f r‖ ^ 2) = SL + SR := by
          rw [hSLdef, hSRdef]
          rw [← Finset.Ico_union_Ico_eq_Ico (by omega : a ≤ a + m) (by omega : a + m ≤ a + n)]
          exact Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a (a + m) (a + n))
        rw [hsumφ, hsumf]
        exact hgoal
  have hb : a + (b - a) = b := Nat.add_sub_of_le hab
  have hres := key (b - a) a φ f
    (by rw [hb]; exact hbd)
    (by rw [hb]; exact hcollapse)
    (by rw [hb]; exact horth)
  rw [hb] at hres
  exact hres

end Commons.Analysis.InnerProductSpace