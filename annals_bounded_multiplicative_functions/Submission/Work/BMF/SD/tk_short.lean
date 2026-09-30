import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.MSD.basic
import Submission.Work.BMF.MSD.natIcc_mul
import Submission.Work.BMF.MSD.dirichlet_kernel
import Submission.Work.BMF.MSD.kern_sum_sep
import Submission.Work.BMF.MSD.frac_sep
import Submission.Work.BMF.MSD.kern_le_filter_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.SD.tk_short`

Second-moment bound for the discrepancy of `f` on arithmetic progressions of prime moduli
over a short interval: with `2 ≤ P ≤ Q`, `Q ^ 3 ≤ H`, `1 ≤ H`, `H ≤ x` and `‖f n‖ ≤ 1`,

`Σ_{p ∈ primesIn P Q} p * ‖Σ_{m ∈ [x/p, (x+H)/p]} f (p*m) - (1/p) * Σ_{n ∈ [x, x+H]} f n‖ ^ 2 ≤ C H^2`.

The proof is an elementary additive large sieve:
* `ℓ_p := Σ_{n ∈ [x,x+H], p ∣ n} f n - (1/p) Σ_{n ∈ [x,x+H]} f n = (1/p) Σ_{1 ≤ a ≤ p-1} F (a/p)`
  where `F θ = Σ_{n ∈ [x,x+H]} f n * eC (n θ)`, by the orthogonality of the additive characters
  mod `p`;
* Cauchy--Schwarz in `a` turns `p ‖ℓ_p‖^2` into `Σ_a ‖F (a/p)‖^2`, so the problem is a
  second-moment bound for `F` at the `δ`-separated points `a/p` (`δ = 1/Q^2`);
* that second moment is bounded by duality (the analytic large sieve with a logarithmic loss),
  which suffices since `Q^2 log Q ≪ H` when `Q^3 ≤ H`.
-/

namespace Work.BMF.SD

open Finset Real Complex
open scoped ComplexConjugate
open Work.BMF
open Work.BMF.MSD

/-! ## Elementary facts about `eC` -/

lemma eC_add' (a b : ℝ) : eC (a + b) = eC a * eC b := by
  rw [eC, eC, eC, ← Complex.exp_add]; congr 1; push_cast; ring

lemma eC_int (k : ℤ) : eC (k : ℝ) = 1 := by
  rw [eC, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

lemma eC_mul_nat (t : ℝ) (n : ℕ) : eC (n * t) = (eC t) ^ n := by
  induction n with
  | zero => simp [eC]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, eC_add', ih, pow_succ]

lemma norm_eC' (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_eC (t : ℝ) : starRingEnd ℂ (eC t) = eC (-t) := by
  rw [eC, eC, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-! ## The geometric bound for exponential sums -/

lemma norm_eC_sub_one (t : ℝ) : ‖eC t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hexp : eC t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [eC]; congr 1; push_cast; ring
  have hre0 : (eC t).re = Real.cos (2 * Real.pi * t) := by
    rw [hexp]; exact Complex.exp_ofReal_mul_I_re _
  have him0 : (eC t).im = Real.sin (2 * Real.pi * t) := by
    rw [hexp]; exact Complex.exp_ofReal_mul_I_im _
  have hsq : ‖eC t - 1‖ ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hre0, him0,
      Complex.one_re, Complex.one_im]
    have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * t)
      rw [show 2 * (Real.pi * t) = 2 * Real.pi * t by ring] at h
      have h2 : Real.cos (Real.pi * t) ^ 2 = 1 - Real.sin (Real.pi * t)^2 := by
        linarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
      rw [h, h2]; ring
    have hsin2 : Real.sin (2 * Real.pi * t)
        = 2 * Real.sin (Real.pi * t) * Real.cos (Real.pi * t) := by
      rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.sin_two_mul]
    rw [hcos, hsin2]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  have hsq2 : ‖eC t - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [hsq, mul_pow, sq_abs]; ring
  have h := (sq_eq_sq_iff_abs_eq_abs ‖eC t - 1‖ (2 * |Real.sin (Real.pi * t)|)).mp hsq2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h

theorem geom_sum_eC (N : ℕ) (t : ℝ) (m : ℤ) (hm : |t - m| ≤ 1 / 2) (hm' : t ≠ (m : ℝ)) :
    ‖∑ j ∈ Finset.range N, eC (j * t)‖ ≤ 1 / (2 * |t - m|) := by
  have hnorm := norm_eC_sub_one t
  have hsin : 2 * |t - (m:ℝ)| ≤ |Real.sin (Real.pi * t)| := by
    have h1 : Real.sin (Real.pi * t) = (-1 : ℝ) ^ m * Real.sin (Real.pi * (t - m)) := by
      have h := Real.sin_add_int_mul_pi (Real.pi * (t - m)) m
      rw [← h]; congr 1; push_cast; ring
    have h2 : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t - (m:ℝ)|) := by
      rw [h1, abs_mul, abs_zpow]
      simp only [abs_neg, abs_one, one_zpow, one_mul]
      rw [abs_sin_eq_sin_abs_of_abs_le_pi]
      · congr 1; rw [abs_mul, abs_of_pos Real.pi_pos]
      · rw [abs_mul, abs_of_pos Real.pi_pos]
        have hh := mul_le_mul_of_nonneg_left hm (le_of_lt Real.pi_pos)
        linarith [Real.pi_pos, hh]
    rw [h2]
    have h3 : 0 ≤ Real.pi * |t - (m:ℝ)| := by positivity
    have h4 : Real.pi * |t - (m:ℝ)| ≤ Real.pi / 2 := by
      have hh := mul_le_mul_of_nonneg_left hm (le_of_lt Real.pi_pos)
      linarith
    have h5 := Real.mul_le_sin h3 h4
    have h6 : 2 / Real.pi * (Real.pi * |t - (m:ℝ)|) = 2 * |t - (m:ℝ)| := by field_simp
    rwa [h6] at h5
  have hpos : 0 < ‖eC t - 1‖ := by
    rw [hnorm]
    have h0 : 0 < |t - (m:ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hm')
    nlinarith [hsin]
  have hz1 : eC t ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  have hsum : (∑ j ∈ Finset.range N, eC (j * t)) = ∑ j ∈ Finset.range N, (eC t) ^ j :=
    Finset.sum_congr rfl fun j _ => eC_mul_nat t j
  rw [hsum, geom_sum_eq hz1, norm_div]
  have hnum : ‖(eC t) ^ N - 1‖ ≤ 2 := by
    calc ‖(eC t) ^ N - 1‖ ≤ ‖(eC t) ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_eC', one_pow, norm_one]; norm_num
  rw [div_le_iff₀ hpos]
  calc ‖(eC t) ^ N - 1‖ ≤ 2 := hnum
    _ = (1 / (2 * |t - (m:ℝ)|)) * (4 * |t - (m:ℝ)|) := by field_simp; ring
    _ ≤ (1 / (2 * |t - (m:ℝ)|)) * ‖eC t - 1‖ := by
        gcongr
        rw [hnorm]; linarith [hsin]

/-! ## Counting separated points in an interval -/

theorem sep_card_le (S : Finset ℝ) (δ a b : ℝ) (hδ : 0 < δ) (hab' : a ≤ b)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ |s - t|)
    (hab : ∀ s ∈ S, a ≤ s ∧ s ≤ b) :
    (S.card : ℝ) ≤ (b - a) / δ + 1 := by
  have key : ∀ S : Finset ℝ, (∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ |s - t|) →
      ∀ lo hi : ℝ, (∀ s ∈ S, lo ≤ s ∧ s ≤ hi) → 0 ≤ hi - lo + δ →
      (S.card : ℝ) * δ ≤ (hi - lo) + δ := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro _ lo hi _ h0; simpa using h0
    | insert c s hlt ih =>
        intro hseps lo hi hmem h0
        have hc : lo ≤ c ∧ c ≤ hi := hmem c (Finset.mem_insert_self c s)
        have hs : ∀ x ∈ s, lo ≤ x ∧ x ≤ hi := fun x hx => hmem x (Finset.mem_insert_of_mem hx)
        have hseps' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| :=
          fun x hx y hy hxy =>
            hseps x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
        have hnew : ∀ x ∈ s, lo ≤ x ∧ x ≤ c - δ := by
          intro x hx
          obtain ⟨h1, _⟩ := hs x hx
          refine ⟨h1, ?_⟩
          have hxlt : x < c := hlt x hx
          have hmemx : δ ≤ |c - x| :=
            hseps c (Finset.mem_insert_self c s) x (Finset.mem_insert_of_mem hx) (ne_of_gt hxlt)
          rw [abs_of_pos (by linarith)] at hmemx
          linarith
        have h0' : 0 ≤ (c - δ) - lo + δ := by linarith [hc.1]
        have ih' := ih hseps' lo (c - δ) hnew h0'
        have hnotmem : c ∉ s := fun hx => absurd (hlt c hx) (lt_irrefl _)
        have hcard : ((insert c s).card : ℝ) = (s.card : ℝ) + 1 := by
          rw [Finset.card_insert_of_notMem hnotmem]; push_cast; ring
        rw [hcard, add_mul, one_mul]
        have hle : (c - δ) - lo + δ ≤ hi - lo + δ := by linarith [hc.2]
        linarith [ih', hle]
  have h := key S hsep a b hab (by linarith)
  have hgoal : (S.card : ℝ) ≤ ((b - a) + δ) / δ := (le_div_iff₀ hδ).mpr h
  have heq : ((b - a) + δ) / δ = (b - a) / δ + 1 := by
    rw [add_div, div_self (ne_of_gt hδ), add_comm]
  rwa [heq] at hgoal

/-! ## Orthogonality of the additive characters modulo a prime -/

lemma eC_eq_one_iff_int (t : ℝ) : eC t = 1 ↔ ∃ k : ℤ, t = k := by
  constructor
  · intro h
    rw [eC, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hne : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
            = (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) from rfl, hk]
      ring
    exact Complex.ofReal_inj.mp (mul_left_cancel₀ hne h3)
  · rintro ⟨k, rfl⟩
    exact eC_int k

lemma eC_div_prime_eq_one_iff (p n : ℕ) (hp : p.Prime) :
    eC ((n : ℝ) / (p : ℝ)) = 1 ↔ p ∣ n := by
  rw [eC_eq_one_iff_int]
  constructor
  · rintro ⟨k, hk⟩
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
    have h1 : (n : ℝ) = (k : ℝ) * (p : ℝ) := (div_eq_iff (ne_of_gt hp0)).mp hk
    have hk0 : 0 ≤ k := by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have : (0:ℝ) ≤ (k:ℝ) := by nlinarith [h1, hp0, hn]
      exact_mod_cast this
    refine ⟨k.toNat, ?_⟩
    have hknn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      have h : ((k.toNat : ℤ) : ℝ) = (k : ℝ) := by rw [Int.toNat_of_nonneg hk0]
      exact_mod_cast h
    have h2 : (n : ℝ) = ((p * k.toNat : ℕ) : ℝ) := by
      rw [h1, ← hknn]
      simp only [Nat.cast_mul]
      ring
    exact_mod_cast h2
  · rintro ⟨m, rfl⟩
    refine ⟨(m : ℤ), ?_⟩
    have hp0 : ((p:ℝ)) ≠ 0 := by
      have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
      linarith
    have key : ((p * m : ℕ) : ℝ) = ((m : ℤ) : ℝ) * (p : ℝ) := by push_cast; ring
    exact (div_eq_iff hp0).mpr key

theorem sum_range_eC_div_prime (p n : ℕ) (hp : p.Prime) :
    ∑ a ∈ Finset.range p, eC ((a : ℝ) * (n : ℝ) / (p : ℝ))
      = if p ∣ n then (p : ℂ) else 0 := by
  have hp0 : 0 < p := hp.pos
  have hζ : (eC ((n:ℝ) / (p:ℝ))) ^ p = 1 := by
    rw [← eC_mul_nat]
    have h : (p:ℝ) * ((n:ℝ) / (p:ℝ)) = (n:ℝ) := by
      field_simp
    rw [h]
    exact eC_int n
  have hterm : ∀ a : ℕ, eC ((a:ℝ) * (n:ℝ) / (p:ℝ)) = (eC ((n:ℝ)/(p:ℝ))) ^ a := by
    intro a
    rw [← eC_mul_nat]
    congr 1
    ring
  rw [show (∑ a ∈ Finset.range p, eC ((a : ℝ) * (n : ℝ) / (p : ℝ)))
      = ∑ a ∈ Finset.range p, (eC ((n:ℝ)/(p:ℝ)))^a from Finset.sum_congr rfl (fun a _ => hterm a)]
  by_cases h : p ∣ n
  · rw [if_pos h]
    have h1 : eC ((n:ℝ)/(p:ℝ)) = 1 := (eC_div_prime_eq_one_iff p n hp).mpr h
    rw [h1]
    simp
  · rw [if_neg h]
    have hne : eC ((n:ℝ)/(p:ℝ)) ≠ 1 := fun hc => h ((eC_div_prime_eq_one_iff p n hp).mp hc)
    rw [geom_sum_eq hne, hζ]
    simp

theorem sum_eC_div_prime (p n : ℕ) (hp : p.Prime) :
    ∑ a ∈ Finset.Icc 1 (p - 1), eC ((a : ℝ) * (n : ℝ) / (p : ℝ))
      = (if p ∣ n then (p : ℂ) else 0) - 1 := by
  have hp1 : 1 ≤ p := hp.one_le
  have hIcc : Finset.Icc 1 (p - 1) = (Finset.range p).erase 0 := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hIcc, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hp.pos), sum_range_eC_div_prime p n hp]
  norm_num [eC]


/-! ## The Schur test for symmetric nonnegative kernels -/

/-- Quadratic-form bound for a symmetric nonnegative kernel with bounded rows. -/
lemma schur_bound {ι : Type*} [DecidableEq ι] (T : Finset ι) (B : ι → ι → ℝ) (x : ι → ℝ)
    (M : ℝ) (hBnn : ∀ r ∈ T, ∀ s ∈ T, 0 ≤ B r s)
    (hBsym : ∀ r ∈ T, ∀ s ∈ T, B r s = B s r)
    (hrow : ∀ r ∈ T, ∑ s ∈ T, B r s ≤ M) (hxnn : ∀ r, 0 ≤ x r) :
    ∑ r ∈ T, ∑ s ∈ T, x r * x s * B r s ≤ M * ∑ r ∈ T, x r ^ 2 := by
  have hstep : ∑ r ∈ T, ∑ s ∈ T, x r * x s * B r s
      ≤ ∑ r ∈ T, ∑ s ∈ T, ((x r ^ 2 + x s ^ 2) / 2) * B r s := by
    apply Finset.sum_le_sum; intro r hr
    apply Finset.sum_le_sum; intro s hs
    have hB := hBnn r hr s hs
    nlinarith [sq_nonneg (x r - x s)]
  have hrow1 : ∀ r ∈ T, ∑ s ∈ T, ((x r ^ 2 + x s ^ 2) / 2) * B r s
      ≤ (M / 2) * x r ^ 2 + (1 / 2) * (∑ s ∈ T, x s ^ 2 * B r s) := by
    intro r hr
    have hsplit : ∑ s ∈ T, ((x r ^ 2 + x s ^ 2) / 2) * B r s
        = (x r ^ 2 / 2) * (∑ s ∈ T, B r s)
          + (1 / 2) * (∑ s ∈ T, x s ^ 2 * B r s) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s hs; ring
    rw [hsplit]
    have h1 : (x r ^ 2 / 2) * (∑ s ∈ T, B r s) ≤ (x r ^ 2 / 2) * M :=
      mul_le_mul_of_nonneg_left (hrow r hr) (by positivity)
    have h2 : (x r ^ 2 / 2) * M = (M / 2) * x r ^ 2 := by ring
    linarith [h1, h2]
  calc ∑ r ∈ T, ∑ s ∈ T, x r * x s * B r s
      ≤ ∑ r ∈ T, ∑ s ∈ T, ((x r ^ 2 + x s ^ 2) / 2) * B r s := hstep
    _ ≤ ∑ r ∈ T, ((M / 2) * x r ^ 2 + (1 / 2) * (∑ s ∈ T, x s ^ 2 * B r s)) :=
        Finset.sum_le_sum hrow1
    _ = (M / 2) * (∑ r ∈ T, x r ^ 2)
          + (1 / 2) * (∑ r ∈ T, ∑ s ∈ T, x s ^ 2 * B r s) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (M / 2) * (∑ r ∈ T, x r ^ 2)
          + (1 / 2) * (∑ s ∈ T, ∑ r ∈ T, x s ^ 2 * B r s) := by
        rw [Finset.sum_comm]
    _ = (M / 2) * (∑ r ∈ T, x r ^ 2)
          + (1 / 2) * (∑ s ∈ T, x s ^ 2 * (∑ r ∈ T, B r s)) := by
        have h : (∑ s ∈ T, ∑ r ∈ T, x s ^ 2 * B r s)
            = ∑ s ∈ T, x s ^ 2 * (∑ r ∈ T, B r s) := by
          apply Finset.sum_congr rfl; intro s _
          rw [Finset.mul_sum]
        rw [h]
    _ = (M / 2) * (∑ r ∈ T, x r ^ 2)
          + (1 / 2) * (∑ s ∈ T, x s ^ 2 * (∑ r ∈ T, B s r)) := by
        have h : (∑ s ∈ T, x s ^ 2 * (∑ r ∈ T, B r s))
            = ∑ s ∈ T, x s ^ 2 * (∑ r ∈ T, B s r) := by
          apply Finset.sum_congr rfl; intro s hs
          rw [Finset.sum_congr rfl (fun r hr => hBsym r hr s hs)]
        rw [h]
    _ ≤ (M / 2) * (∑ r ∈ T, x r ^ 2) + (1 / 2) * (∑ s ∈ T, x s ^ 2 * M) := by
        gcongr with s hs
        exact hrow s hs
    _ = (M / 2) * (∑ r ∈ T, x r ^ 2) + (1 / 2) * (M * ∑ s ∈ T, x s ^ 2) := by
        have h : (∑ s ∈ T, x s ^ 2 * M) = M * ∑ s ∈ T, x s ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro s _; ring
        rw [h]
    _ = M * ∑ r ∈ T, x r ^ 2 := by ring

/-! ## The additive large sieve, dual form -/

/-- The exponential sum `Σ_{n ∈ Ico a (a+N)} eC (n Δ)` is bounded by the Dirichlet-kernel
majorant `kern N Δ` and, by conjugation, by `kern N (-Δ)`. -/
lemma eC_sum_le_kern (a N : ℕ) (Δ : ℝ) :
    ‖∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * Δ)‖ ≤ min (kern N Δ) (kern N (-Δ)) := by
  refine le_min (dirichlet_kernel a N Δ) ?_
  have hconj : (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (-Δ)))
      = conj (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * Δ)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [conj_eC]
    congr 1
    ring
  rw [← norm_conj (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * Δ)), ← hconj]
  exact dirichlet_kernel a N (-Δ)

/-- **Additive large sieve, dual (second-moment) form.** -/
theorem large_sieve_kernel_bound {ι : Type*} [DecidableEq ι] (T : Finset ι) (θ : ι → ℝ)
    (N : ℕ) (a : ℕ) (c : ι → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → δ ≤ circDist (θ r - θ s)) :
    ∑ n ∈ Finset.Ico a (a + N), ‖∑ r ∈ T, c r * eC ((n:ℝ) * θ r)‖ ^ 2
      ≤ (2 * (N:ℝ) + (8/δ) * (2 + Real.log (2 * (N:ℝ) + 2))) * ∑ r ∈ T, ‖c r‖ ^ 2 := by
  set M : ℝ := 2 * (N:ℝ) + (8 / δ) * (2 + Real.log (2 * (N:ℝ) + 2)) with hMdef
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 < 8 / δ := by positivity
    have h2 : 0 ≤ Real.log (2 * (N:ℝ) + 2) := Real.log_nonneg (by linarith)
    nlinarith
  set B : ι → ι → ℝ := fun r s => min (kern N (θ r - θ s)) (kern N (-(θ r - θ s))) with hBdef
  have hBnn : ∀ r ∈ T, ∀ s ∈ T, 0 ≤ B r s :=
    fun r _ s _ => le_min (kern_nonneg _ _) (kern_nonneg _ _)
  have hBsym : ∀ r ∈ T, ∀ s ∈ T, B r s = B s r := by
    intro r hr s hs
    simp only [hBdef]
    rw [show -(θ r - θ s) = θ s - θ r by ring, show -(θ s - θ r) = θ r - θ s by ring, min_comm]
  have hrow : ∀ r ∈ T, ∑ s ∈ T, B r s ≤ M := by
    intro r _
    calc ∑ s ∈ T, B r s ≤ ∑ s ∈ T, kern N (θ r - θ s) :=
          Finset.sum_le_sum (fun s _ => min_le_left _ _)
      _ ≤ M := by rw [hMdef]; exact kern_sum_sep ι T θ δ hδ hδ1 hsep N r
  have hquad := schur_bound T B (fun r => ‖c r‖) M hBnn hBsym hrow (fun r => norm_nonneg _)
  have hBkern : ∀ r ∈ T, ∀ s ∈ T,
      ‖∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s))‖ ≤ B r s := by
    intro r _ s _
    exact eC_sum_le_kern a N (θ r - θ s)
  have hconjre : ∀ z : ℂ, (z * conj z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hlin : ∀ n : ℕ, (∑ r ∈ T, c r * eC ((n:ℝ) * θ r))
      * conj (∑ r ∈ T, c r * eC ((n:ℝ) * θ r))
      = ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s)) := by
    intro n
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    rw [map_mul, conj_eC]
    have hkey : eC ((n:ℝ) * θ r) * eC (-((n:ℝ) * θ s)) = eC ((n:ℝ) * (θ r - θ s)) := by
      rw [← eC_add']
      congr 1
      ring
    calc c r * eC ((n:ℝ) * θ r) * (conj (c s) * eC (-((n:ℝ) * θ s)))
        = c r * conj (c s) * (eC ((n:ℝ) * θ r) * eC (-((n:ℝ) * θ s))) := by ring
      _ = c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s)) := by rw [hkey]
  have hLHS : ∑ n ∈ Finset.Ico a (a + N), ‖∑ r ∈ T, c r * eC ((n:ℝ) * θ r)‖ ^ 2
      = (∑ n ∈ Finset.Ico a (a + N),
          ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s))).re := by
    have h1 : ∑ n ∈ Finset.Ico a (a + N), ‖∑ r ∈ T, c r * eC ((n:ℝ) * θ r)‖ ^ 2
        = ∑ n ∈ Finset.Ico a (a + N),
            (((∑ r ∈ T, c r * eC ((n:ℝ) * θ r))
              * conj (∑ r ∈ T, c r * eC ((n:ℝ) * θ r))).re) := by
      apply Finset.sum_congr rfl; intro n _
      exact (hconjre _).symm
    rw [h1, Complex.re_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [hlin n]
  have hswap : (∑ n ∈ Finset.Ico a (a + N),
        ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s)))
      = ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s)
          * (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.mul_sum]
  have hbound : (∑ n ∈ Finset.Ico a (a + N),
        ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s))).re
      ≤ ∑ r ∈ T, ∑ s ∈ T, ‖c r‖ * ‖c s‖ * B r s := by
    calc (∑ n ∈ Finset.Ico a (a + N),
          ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s))).re
        ≤ ‖∑ n ∈ Finset.Ico a (a + N),
            ∑ r ∈ T, ∑ s ∈ T, c r * conj (c s) * eC ((n:ℝ) * (θ r - θ s))‖ :=
          Complex.re_le_norm _
      _ = ‖∑ r ∈ T, ∑ s ∈ T, c r * conj (c s)
            * (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s)))‖ := by rw [hswap]
      _ ≤ ∑ r ∈ T, ‖∑ s ∈ T, c r * conj (c s)
            * (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s)))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ T, ∑ s ∈ T, ‖c r * conj (c s)
            * (∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s)))‖ :=
          Finset.sum_le_sum (fun r _ => norm_sum_le _ _)
      _ = ∑ r ∈ T, ∑ s ∈ T, ‖c r‖ * ‖c s‖
            * ‖∑ n ∈ Finset.Ico a (a + N), eC ((n:ℝ) * (θ r - θ s))‖ := by
          apply Finset.sum_congr rfl; intro r _
          apply Finset.sum_congr rfl; intro s _
          rw [norm_mul, norm_mul, norm_conj]
      _ ≤ ∑ r ∈ T, ∑ s ∈ T, ‖c r‖ * ‖c s‖ * B r s := by
          apply Finset.sum_le_sum; intro r hr
          apply Finset.sum_le_sum; intro s hs
          exact mul_le_mul_of_nonneg_left (hBkern r hr s hs)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [hLHS]
  exact hbound.trans hquad

/-- **Additive large sieve, primal form**, by duality from the dual form. -/
theorem large_sieve_primal {ι : Type*} [DecidableEq ι] (T : Finset ι) (θ : ι → ℝ)
    (N : ℕ) (a : ℕ) (g : ℕ → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → δ ≤ circDist (θ r - θ s)) :
    ∑ r ∈ T, ‖∑ n ∈ Finset.Ico a (a + N), g n * eC ((n:ℝ) * θ r)‖ ^ 2
      ≤ (2 * (N:ℝ) + (8/δ) * (2 + Real.log (2 * (N:ℝ) + 2)))
          * ∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2 := by
  set M : ℝ := 2 * (N:ℝ) + (8/δ) * (2 + Real.log (2 * (N:ℝ) + 2)) with hMdef
  set F : ι → ℂ := fun r => ∑ n ∈ Finset.Ico a (a + N), g n * eC ((n:ℝ) * θ r) with hFdef
  set Tr : ℝ := ∑ r ∈ T, ‖F r‖ ^ 2 with hTrdef
  set D : ℕ → ℂ := fun n => ∑ r ∈ T, F r * eC (-((n:ℝ) * θ r)) with hDdef
  have hTrnn : 0 ≤ Tr := by rw [hTrdef]; positivity
  have hSnn : 0 ≤ ∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 < 8 / δ := by positivity
    have h2 : 0 ≤ Real.log (2 * (N:ℝ) + 2) := Real.log_nonneg (by linarith)
    nlinarith
  -- the dual sums conjugate to the primal ones
  have hDnorm : ∀ n : ℕ, ‖D n‖ = ‖∑ r ∈ T, conj (F r) * eC ((n:ℝ) * θ r)‖ := by
    intro n
    have h : D n = conj (∑ r ∈ T, conj (F r) * eC ((n:ℝ) * θ r)) := by
      rw [hDdef, map_sum]
      apply Finset.sum_congr rfl; intro r _
      rw [map_mul, conj_eC]
      simp only [starRingEnd_self_apply]
    rw [h, norm_conj]
  -- `conj (F r)` is the sampling of `conj g` at `-θ r`
  have hkey : ∀ r ∈ T, conj (F r) = ∑ n ∈ Finset.Ico a (a + N), conj (g n) * eC (-((n:ℝ) * θ r)) := by
    intro r _
    rw [hFdef, map_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [map_mul, conj_eC]
  -- `Tr` is the pairing of `g` with `D`
  have hTr : ((Tr : ℝ) : ℂ) = ∑ n ∈ Finset.Ico a (a + N), conj (g n) * D n := by
    have h1 : ((Tr : ℝ) : ℂ) = ∑ r ∈ T, F r * conj (F r) := by
      rw [hTrdef]; push_cast
      apply Finset.sum_congr rfl; intro r _
      rw [Complex.mul_conj']
    have h2 : (∑ n ∈ Finset.Ico a (a + N), conj (g n) * D n)
        = ∑ n ∈ Finset.Ico a (a + N),
            ∑ r ∈ T, conj (g n) * (F r * eC (-((n:ℝ) * θ r))) := by
      apply Finset.sum_congr rfl; intro n _
      rw [hDdef, Finset.mul_sum]
    rw [h1, h2, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    rw [hkey r hr, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    ring
  -- the dual bound applied to `conj ∘ F`
  have hdual : ∑ n ∈ Finset.Ico a (a + N), ‖D n‖ ^ 2 ≤ M * Tr := by
    have h1 := large_sieve_kernel_bound T θ N a (fun r => conj (F r)) δ hδ hδ1 hsep
    calc ∑ n ∈ Finset.Ico a (a + N), ‖D n‖ ^ 2
        = ∑ n ∈ Finset.Ico a (a + N),
            ‖∑ r ∈ T, conj (F r) * eC ((n:ℝ) * θ r)‖ ^ 2 := by
          apply Finset.sum_congr rfl; intro n _; rw [hDnorm n]
      _ ≤ M * ∑ r ∈ T, ‖conj (F r)‖ ^ 2 := h1
      _ = M * Tr := by
          rw [hTrdef]
          congr 1
          apply Finset.sum_congr rfl; intro r _; rw [norm_conj]
  -- Cauchy--Schwarz
  have hCS : Tr ≤ Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
      * Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖D n‖ ^ 2) := by
    have hnormTr : ‖((Tr : ℝ) : ℂ)‖ = Tr := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTrnn]
    calc Tr = ‖((Tr : ℝ) : ℂ)‖ := hnormTr.symm
      _ = ‖∑ n ∈ Finset.Ico a (a + N), conj (g n) * D n‖ := by rw [hTr]
      _ ≤ ∑ n ∈ Finset.Ico a (a + N), ‖conj (g n) * D n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Ico a (a + N), ‖g n‖ * ‖D n‖ := by
          apply Finset.sum_congr rfl; intro n _
          rw [norm_mul, norm_conj]
      _ ≤ Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
            * Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖D n‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ (fun n => ‖g n‖) (fun n => ‖D n‖)
  -- conclude
  rcases eq_or_lt_of_le hTrnn with h0 | hpos
  · rw [← h0]; exact mul_nonneg hMnn hSnn
  · have hsqrt : Real.sqrt Tr
        ≤ Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M := by
      refine le_of_mul_le_mul_right ?_ (Real.sqrt_pos.mpr hpos)
      calc Real.sqrt Tr * Real.sqrt Tr = Tr := by rw [← pow_two, Real.sq_sqrt hTrnn]
        _ ≤ Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
              * Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖D n‖ ^ 2) := hCS
        _ ≤ Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt (M * Tr) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdual) (Real.sqrt_nonneg _)
        _ = (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M)
              * Real.sqrt Tr := by
            rw [Real.sqrt_mul hMnn]; ring
    calc Tr = Real.sqrt Tr * Real.sqrt Tr := by rw [← pow_two, Real.sq_sqrt hTrnn]
      _ ≤ (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M)
            * (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M) :=
          mul_le_mul hsqrt hsqrt (Real.sqrt_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * M := by
          have hs1 : Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
              * Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
              = ∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2 := by
            rw [← pow_two, Real.sq_sqrt hSnn]
          have hs2 : Real.sqrt M * Real.sqrt M = M := by rw [← pow_two, Real.sq_sqrt hMnn]
          calc (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M)
                * (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * Real.sqrt M)
              = (Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2)
                  * Real.sqrt (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2))
                * (Real.sqrt M * Real.sqrt M) := by ring
            _ = (∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2) * M := by rw [hs1, hs2]
      _ = M * ∑ n ∈ Finset.Ico a (a + N), ‖g n‖ ^ 2 := by ring

/-! ## The per-prime reduction -/

/-- For a prime `p`, the discrepancy of the sum over multiples of `p` against `1/p` times the
full sum is a mean of the Fourier coefficients of `f` at the frequencies `a/p`. -/
theorem per_prime (x H : ℝ) (f : ℕ → ℂ) (p : ℕ) (hp : p.Prime) :
    (∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
        - (1 / (p : ℂ)) * (∑ n ∈ natIcc x (x + H), f n)
      = (1 / (p : ℂ)) * ∑ a ∈ Finset.Icc 1 (p - 1),
          ∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hpC : (p:ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact hp.ne_zero
  have hnat := natIcc_mul x H p hp1 f
  have horth : ∀ n : ℕ,
      (1 / (p : ℂ)) * (∑ a ∈ Finset.Icc 1 (p - 1), eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))))
        = (if p ∣ n then (1 : ℂ) else 0) - 1 / (p : ℂ) := by
    intro n
    rw [show (∑ a ∈ Finset.Icc 1 (p - 1), eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))))
        = ∑ a ∈ Finset.Icc 1 (p - 1), eC ((a : ℝ) * (n : ℝ) / (p : ℝ)) from by
          apply Finset.sum_congr rfl; intro a _; congr 1; ring]
    rw [sum_eC_div_prime p n hp]
    by_cases h : p ∣ n
    · rw [if_pos h, if_pos h]
      field_simp
    · rw [if_neg h, if_neg h]
      ring
  rw [hnat, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hA : ∀ n ∈ natIcc x (x + H), ((if p ∣ n then f n else 0) - 1 / (p : ℂ) * f n)
      = f n * ((1 / (p : ℂ)) * (∑ a ∈ Finset.Icc 1 (p - 1),
          eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))))) := by
    intro n _
    rw [horth n]
    by_cases hd : p ∣ n
    · rw [if_pos hd, if_pos hd]; ring
    · rw [if_neg hd, if_neg hd]; ring
  rw [Finset.sum_congr rfl hA]
  have hswap : (∑ n ∈ natIcc x (x + H), f n * ((1 / (p : ℂ)) * (∑ a ∈ Finset.Icc 1 (p - 1),
          eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))))
      = (1 / (p : ℂ)) * ∑ a ∈ Finset.Icc 1 (p - 1),
          ∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))) := by
    calc ∑ n ∈ natIcc x (x + H), f n * ((1 / (p : ℂ)) * (∑ a ∈ Finset.Icc 1 (p - 1),
            eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))))
        = ∑ n ∈ natIcc x (x + H), ∑ a ∈ Finset.Icc 1 (p - 1),
            f n * ((1 / (p : ℂ)) * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))) := by
          apply Finset.sum_congr rfl; intro n _
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ a ∈ Finset.Icc 1 (p - 1), ∑ n ∈ natIcc x (x + H),
            f n * ((1 / (p : ℂ)) * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))) := Finset.sum_comm
      _ = (1 / (p : ℂ)) * ∑ a ∈ Finset.Icc 1 (p - 1),
            ∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _; ring
  exact hswap

/-- Per-prime second-moment bound: `p` times the squared discrepancy is at most the sum of the
squared Fourier coefficients at the frequencies `a/p`. -/
theorem per_prime_sq (x H : ℝ) (f : ℕ → ℂ) (p : ℕ) (hp : p.Prime) :
    (p : ℝ) * ‖(∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
        - (1 / (p : ℂ)) * (∑ n ∈ natIcc x (x + H), f n)‖ ^ 2
      ≤ ∑ a ∈ Finset.Icc 1 (p - 1),
          ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))‖ ^ 2 := by
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.one_le
  rw [per_prime x H f p hp]
  set S : ℂ := ∑ a ∈ Finset.Icc 1 (p - 1),
      ∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))) with hSdef
  set Z : ℕ → ℂ := fun a => ∑ n ∈ natIcc x (x + H),
      f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ))) with hZdef
  have hS : S = ∑ a ∈ Finset.Icc 1 (p - 1), Z a := rfl
  have hcard1 : ((Finset.Icc 1 (p - 1)).card : ℝ) = (p:ℝ) - 1 := by
    rw [Nat.card_Icc]
    have h : (p - 1 + 1 - 1 : ℕ) = p - 1 := by omega
    rw [h, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hnorm2 : ‖(1 / (p : ℂ)) * S‖ ^ 2 = ‖(1 / (p : ℂ))‖ ^ 2 * ‖S‖ ^ 2 := by
    rw [norm_mul]; ring
  have hcn : ‖(1 / (p : ℂ))‖ = 1 / (p:ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hCS : ‖S‖ ^ 2 ≤ ((p:ℝ) - 1) * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 := by
    have h1 : ‖∑ a ∈ Finset.Icc 1 (p - 1), Z a‖ ≤ ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ :=
      norm_sum_le _ _
    have h2 : (∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖) ^ 2
        ≤ ((p:ℝ) - 1) * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 := by
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Icc 1 (p - 1))
        (fun a => ‖Z a‖) (fun _ => (1:ℝ))
      simp only [mul_one, one_pow, Finset.sum_const, hcard1, nsmul_eq_mul] at hcs
      have h3 : (0:ℝ) ≤ ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 :=
        Finset.sum_nonneg (fun a _ => sq_nonneg _)
      have h4 : (0:ℝ) ≤ (p:ℝ) - 1 := by linarith
      have hsq : (∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖) ^ 2
          ≤ (Real.sqrt (∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2) * Real.sqrt ((p:ℝ) - 1)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => norm_nonneg _)) hcs 2
      rw [mul_pow, Real.sq_sqrt h3, Real.sq_sqrt h4, mul_comm] at hsq
      exact hsq
    calc ‖S‖ ^ 2 = ‖∑ a ∈ Finset.Icc 1 (p - 1), Z a‖ ^ 2 := by rw [hS]
      _ ≤ (∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ((p:ℝ) - 1) * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 := h2
  have hfac : (p:ℝ) * (1 / (p:ℝ)) ^ 2 = 1 / (p:ℝ) := by
    field_simp
  calc (p : ℝ) * ‖(1 / (p : ℂ)) * S‖ ^ 2
      = (p:ℝ) * ((1 / (p:ℝ)) ^ 2 * ‖S‖ ^ 2) := by rw [hnorm2, hcn]
    _ = (1 / (p:ℝ)) * ‖S‖ ^ 2 := by rw [← mul_assoc, hfac]
    _ ≤ (1 / (p:ℝ)) * (((p:ℝ) - 1) * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = (((p:ℝ) - 1) / (p:ℝ)) * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 := by ring
    _ ≤ 1 * ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (div_le_one_of_le₀ (by linarith) (by positivity))
          (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    _ = ∑ a ∈ Finset.Icc 1 (p - 1), ‖Z a‖ ^ 2 := one_mul _

/-! ## Assembly: the two reductions -/

/-- Summation over primes and residues, rewritten as a sum over the filtered product of
primes with `{1, …, ⌊Q⌋₊}`. -/
theorem per_prime_sum_le (P Q x H : ℝ) (f : ℕ → ℂ) :
    ∑ p ∈ primesIn P Q, (p : ℝ) * ‖(∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
        - (1 / p) * (∑ n ∈ natIcc x (x + H), f n)‖ ^ 2
      ≤ ∑ u ∈ ((primesIn P Q).product (Finset.range (⌊Q⌋₊ + 1))).filter
            (fun u => u.2 ∈ Finset.Ico 1 u.1),
          ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((u.2 : ℝ) / (u.1 : ℝ)))‖ ^ 2 := by
  set G : ℕ → ℕ → ℝ := fun p a =>
      ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((a : ℝ) / (p : ℝ)))‖ ^ 2 with hGdef
  have hprime : ∀ p ∈ primesIn P Q, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hle : ∀ p ∈ primesIn P Q, p ≤ ⌊Q⌋₊ := by
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).1
    rw [natIcc, Finset.mem_Icc] at hmem
    exact hmem.2
  have hstep1 : ∑ p ∈ primesIn P Q, (p : ℝ) * ‖(∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
        - (1 / p) * (∑ n ∈ natIcc x (x + H), f n)‖ ^ 2
      ≤ ∑ p ∈ primesIn P Q, ∑ a ∈ Finset.Icc 1 (p - 1), G p a := by
    apply Finset.sum_le_sum; intro p hp
    have hpP := hprime p hp
    have hcast : (∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
          - (1 / p) * (∑ n ∈ natIcc x (x + H), f n)
        = (∑ m ∈ natIcc (x / p) ((x + H) / p), f (p * m))
          - (1 / (p : ℂ)) * (∑ n ∈ natIcc x (x + H), f n) := by
      congr 1
      try push_cast
      try ring
    rw [hcast]
    exact per_prime_sq x H f p hpP
  refine hstep1.trans ?_
  have hIcc : ∀ p : ℕ, Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
    intro p; ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [Finset.sum_congr rfl (fun p _ => by rw [hIcc p])]
  rw [Finset.sum_filter]
  rw [show (∑ u ∈ (primesIn P Q).product (Finset.range (⌊Q⌋₊ + 1)),
        (if u.2 ∈ Finset.Ico 1 u.1 then G u.1 u.2 else 0))
      = ∑ p ∈ primesIn P Q, ∑ a ∈ Finset.range (⌊Q⌋₊ + 1),
          (if a ∈ Finset.Ico 1 p then G p a else 0) from
    Finset.sum_product (primesIn P Q) (Finset.range (⌊Q⌋₊ + 1))
      (fun u : ℕ × ℕ => if u.2 ∈ Finset.Ico 1 u.1 then G u.1 u.2 else 0)]
  apply Finset.sum_le_sum; intro p hp
  have hpQ : p ≤ ⌊Q⌋₊ := hle p hp
  have hfil : (Finset.range (⌊Q⌋₊ + 1)).filter (fun a => a ∈ Finset.Ico 1 p)
      = Finset.Ico 1 p := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h; exact ⟨by omega, h⟩
  refine le_of_eq ?_
  rw [← Finset.sum_filter, hfil]

/-- The large sieve applied to the frequencies `a/p`. -/
theorem pair_large_sieve (P Q x H : ℝ) (f : ℕ → ℂ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ u ∈ ((primesIn P Q).product (Finset.range (⌊Q⌋₊ + 1))).filter
          (fun u => u.2 ∈ Finset.Ico 1 u.1),
        ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * ((u.2 : ℝ) / (u.1 : ℝ)))‖ ^ 2
      ≤ (2 * ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ)
          + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) + 2)))
        * ∑ n ∈ natIcc x (x + H), ‖f n‖ ^ 2 := by
  set TT : Finset (ℕ × ℕ) := ((primesIn P Q).product (Finset.range (⌊Q⌋₊ + 1))).filter
      (fun u => u.2 ∈ Finset.Ico 1 u.1) with hTTdef
  set θ : ℕ × ℕ → ℝ := fun u => (u.2 : ℝ) / (u.1 : ℝ) with hθdef
  set W : ℕ × ℕ → ℝ := fun u =>
      ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * θ u)‖ ^ 2 with hWdef
  have hQ2 : (2:ℝ) ≤ Q := le_trans hP hPQ
  have hδ : 0 < 1 / Q ^ 2 := by positivity
  have hδ1 : 1 / Q ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hsep : ∀ r ∈ TT, ∀ s ∈ TT, r ≠ s → 1 / Q ^ 2 ≤ circDist (θ r - θ s) := by
    intro r hr s hs hne
    have hrmem : r.1 ∈ primesIn P Q ∧ r.2 ∈ Finset.Ico 1 r.1 := by
      rw [hTTdef] at hr
      have h := Finset.mem_filter.mp hr
      exact ⟨(Finset.mem_product.mp h.1).1, h.2⟩
    have hsmem : s.1 ∈ primesIn P Q ∧ s.2 ∈ Finset.Ico 1 s.1 := by
      rw [hTTdef] at hs
      have h := Finset.mem_filter.mp hs
      exact ⟨(Finset.mem_product.mp h.1).1, h.2⟩
    have hne' : (r.1, r.2) ≠ (s.1, s.2) := fun h => hne h
    have hres := frac_sep P Q hP hPQ hrmem.1 hsmem.1 hrmem.2 hsmem.2 hne'
    rw [hθdef]
    exact hres
  have hIco : Finset.Ico ⌈x⌉₊ (⌈x⌉₊ + (⌊x + H⌋₊ + 1 - ⌈x⌉₊)) = natIcc x (x + H) := by
    rw [natIcc]
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hmain := large_sieve_primal TT θ (⌊x + H⌋₊ + 1 - ⌈x⌉₊) ⌈x⌉₊ f (1 / Q ^ 2) hδ hδ1 hsep
  rw [hIco] at hmain
  have hgoal : (∑ u ∈ TT, W u) ≤ (2 * ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ)
        + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) + 2)))
      * ∑ n ∈ natIcc x (x + H), ‖f n‖ ^ 2 := by
    have hWeq : (∑ u ∈ TT, ‖∑ n ∈ natIcc x (x + H), f n * eC ((n : ℝ) * θ u)‖ ^ 2)
        = ∑ u ∈ TT, W u := by
      apply Finset.sum_congr rfl; intro u _
      rw [hWdef]
    rw [← hWeq]
    exact hmain
  exact hgoal

/-- Arithmetic facts used to finish the estimate. -/
theorem log_le_three_rpow (H : ℝ) (hH : 1 ≤ H) :
    Real.log H ≤ 3 * H ^ (1/3 : ℝ) := by
  have hHpos : (0:ℝ) < H := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < H ^ (1/3:ℝ) by positivity)
  rw [Real.log_rpow hHpos] at h
  have hpos : 0 < H ^ (1/3:ℝ) := Real.rpow_pos_of_pos hHpos _
  linarith

/-- The square of a real number at most `H ^ (1/3)` is at most `H ^ (2/3)`. -/
theorem sq_le_rpow_two_thirds {Q H : ℝ} (hQ : 0 ≤ Q) (hH : 0 < H) (h : Q ≤ H ^ (1/3 : ℝ)) :
    Q ^ 2 ≤ H ^ (2/3 : ℝ) := by
  have h1 : Q ^ 2 ≤ (H ^ (1/3 : ℝ)) ^ 2 := pow_le_pow_left₀ hQ h 2
  have h2 : (H ^ (1/3 : ℝ)) ^ 2 = H ^ (2/3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hH)]
    norm_num
  rwa [h2] at h1

theorem tk_short :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q x H : ℝ) (f : ℕ → ℂ),
      2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → 1 ≤ H → H ≤ x → (∀ n, ‖f n‖ ≤ 1) →
      (∑ p ∈ Work.BMF.primesIn P Q, (p : ℝ) *
        ‖(∑ m ∈ Work.BMF.natIcc (x / p) ((x + H) / p), f (p * m))
            - (1 / p) * (∑ n ∈ Work.BMF.natIcc x (x + H), f n)‖ ^ 2)
        ≤ C * H ^ 2 := by
  refine ⟨200, by norm_num, ?_⟩
  intro P Q x H f hP hPQ hQ3 hH1 hHx hf
  have hQpos : 0 < Q := by linarith
  have hHpos : 0 < H := by linarith
  -- the two reductions
  refine (per_prime_sum_le P Q x H f).trans ?_
  refine (pair_large_sieve P Q x H f hP hPQ).trans ?_
  -- arithmetic
  set N : ℕ := ⌊x + H⌋₊ + 1 - ⌈x⌉₊ with hNdef
  have hSnn : 0 ≤ ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hN1 : ((N : ℕ) : ℝ) ≤ H + 1 := by
    rw [hNdef]
    rcases le_or_gt ⌈x⌉₊ (⌊x + H⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      have hfl : ((⌊x + H⌋₊ : ℕ) : ℝ) ≤ x + H :=
        Nat.floor_le (by linarith)
      have hce : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
      push_cast
      linarith
    · have h0 : ⌊x + H⌋₊ + 1 - ⌈x⌉₊ = 0 := by omega
      rw [h0]; simp; linarith
  have hcard : (∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2) ≤ (N : ℝ) := by
    have hterm : ∀ n, ‖f n‖ ^ 2 ≤ (1:ℝ) := by
      intro n; nlinarith [hf n, norm_nonneg (f n)]
    calc ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2
        ≤ ∑ n ∈ Work.BMF.natIcc x (x + H), (1:ℝ) := Finset.sum_le_sum (fun n _ => hterm n)
      _ = ((Work.BMF.natIcc x (x + H)).card : ℝ) := by simp
      _ = (N : ℝ) := by
          rw [hNdef, Work.BMF.natIcc, Nat.card_Icc]
  have hS1 : (∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2) ≤ H + 1 := hcard.trans hN1
  -- bounds on the prefactor
  have hN2 : 2 * (N : ℝ) + 2 ≤ 6 * H := by linarith [hN1, hH1]
  have hlog : 2 + Real.log (2 * (N : ℝ) + 2) ≤ 10 * H ^ (1/3 : ℝ) := by
    have h1 : Real.log (2 * (N : ℝ) + 2) ≤ Real.log (6 * H) :=
      Real.log_le_log (by positivity) hN2
    have h2 : Real.log (6 * H) = Real.log 6 + Real.log H :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6 by norm_num); linarith
    have h4 : Real.log H ≤ 3 * H ^ (1/3 : ℝ) := log_le_three_rpow H hH1
    have h5 : (1:ℝ) ≤ H ^ (1/3 : ℝ) := by
      have := Real.rpow_le_rpow (show (0:ℝ) ≤ 1 by norm_num) hH1
        (show (0:ℝ) ≤ (1/3 : ℝ) by norm_num)
      rwa [Real.one_rpow] at this
    linarith
  have hQle : Q ≤ H ^ (1/3 : ℝ) := by
    have h1 : (Q ^ 3 : ℝ) ^ (1/3 : ℝ) ≤ H ^ (1/3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hQ3 (by norm_num)
    have hpow : (Q ^ 3 : ℝ) ^ (1/3 : ℝ) = Q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hQpos)]
      rw [show (((3:ℕ):ℝ) * (1/3 : ℝ)) = 1 by norm_num, Real.rpow_one]
    rwa [hpow] at h1
  have hQ23 : Q ^ 2 ≤ H ^ (2/3 : ℝ) := sq_le_rpow_two_thirds (le_of_lt hQpos) hHpos hQle
  have hdelta : 8 / (1 / Q ^ 2) = 8 * Q ^ 2 := by
    field_simp
  have hb : (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2)) ≤ 80 * H := by
    rw [hdelta]
    calc 8 * Q ^ 2 * (2 + Real.log (2 * (N : ℝ) + 2))
        ≤ 8 * Q ^ 2 * (10 * H ^ (1/3 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hlog
          positivity
      _ = 80 * (Q ^ 2 * H ^ (1/3 : ℝ)) := by ring
      _ ≤ 80 * (H ^ (2/3 : ℝ) * H ^ (1/3 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hQ23 (Real.rpow_nonneg (le_of_lt hHpos) _)
      _ = 80 * H := by
          rw [← Real.rpow_add hHpos, show (2/3:ℝ) + 1/3 = 1 by norm_num, Real.rpow_one]
  have hM : 2 * (N : ℝ) + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2))
      ≤ 84 * H := by linarith [hN1, hb]
  calc (2 * (N : ℝ) + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2)))
        * ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2
      ≤ (84 * H) * (H + 1) := by
        apply mul_le_mul hM hS1 hSnn (by positivity)
    _ = 84 * H * (H + 1) := by ring
    _ ≤ 168 * H ^ 2 := by nlinarith
    _ ≤ 200 * H ^ 2 := by nlinarith

end Work.BMF.SD
