/-
# `Work.FITop4.Red5.sum_Zint_annM_prim_le` — the sharp annulus count against a primitive `z`

The outer lattice count of the §5.2 sieve step in its **primitive** form.  For a primitive
Gaussian integer `z` (`(z, z̄) = 1`, the paper's (5.7)–(5.8) setting) with `N = |z|² ≥ 1` and
`M ≥ 1`, the annulus sum

  `Σ_{M < |w|² ≤ 2M} Z(Re w z)`

is `≪ M^{3/4} N^{-1/4} + (M N)^{1/4}`.

## Why this is sharper than `sum_Zint_annulus_le`

`sum_Zint_annulus_le` bounds the same sum by `≪ M^{3/4} N^{1/4}`, using only that each `c`-fibre
of the annulus (`Re(wz) = c²`) is contained in a line inside the disk of radius `√(2M)` and is
`√N`-separated, which gives at most `2√(2M) + 1` points per fibre.  That is lossy by a factor
`√N`.  The sharp count uses the *arithmetic* of the fibre: for `(r,s) = 1` the solutions of
`Re(wz) = v` form a coset `w = w₀ + λ(s,r)`, and the companion coordinate
`Im(wz) = ψ(z,w) = w.re·z.im + w.im·z.re` is *constant along the fibre modulo* `|z|² = N`, so the
admissible `λ` (equivalently the `ψ`-values) form a set of integers in `[-√(2MN), √(2MN)]` that is
a single class modulo `N`: at most `2√(2MN)/N + 1 = 2√(2M/N) + 1` values.  This is
`Work.FIArea1.per_c_gen_bound`, restated here with `N = |z|²` itself rather than with the
parameter `Pa.N`.

The number of `c` with `c⁴ = Re(wz)² ≤ |w|²|z|² ≤ 2MN` is `2(2MN)^{1/4} + 3 ≤ 6(MN)^{1/4}`, and
the product `6(MN)^{1/4}·(2√(2M/N) + 1)` is `12√2 M^{3/4}N^{-1/4} + 6(MN)^{1/4}`, whence the
constant `64`.

The two ingredients are proved here: `per_c_gen_bound_prim` (the fibre bound with the exact
normalisation `N = |z|²`) and `arith_bound` (the elementary real inequality).  The final assembly
is `sum_Zint_annM_prim_le`.
-/
import Mathlib
import Submission.Work.FIArea1.count_annulus
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-! ## 0. Two metric helpers and the double count, local to this module

They also appear in the `piecesSetup`-based modules of this directory (`Work.FITop4.Red5.Zint_sum_eq_fiber_sum`,
`Work.FITop4.Red5.gnorm_mul_real`, `Work.FITop4.Red5.gnorm_eq_coords_real`); they are re-proved here, under
module-local names, so that this module depends only on the `FIArea1` lattice lemmas and the `FIArea2`
square-indicator count. -/

/-- `|wz|² = |w|²|z|²`, over `ℝ`. -/
lemma annM_prim_gnorm_mul_real (w z : GaussianInt) :
    (Work.FIPlan.gnorm (w * z) : ℝ)
      = (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
  rw [Work.FIArea1.gnorm_mul]; push_cast; ring

/-- `|z|² = re² + im²`, over `ℝ`. -/
lemma annM_prim_gnorm_eq_coords (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  have h := congrArg (fun t : ℤ => (t : ℝ)) (Work.FIArea1.gnorm_int z)
  push_cast at h
  exact h

/-- **Double counting of the square indicator** over the outer annulus: summing `Z(Re wz)` and
re-organising by the integer root `c` of `c² = Re(wz)` gives the sum over `c ∈ [-K,K]` of the
number of `w` in the annulus with `c² = Re(wz)`.  The hypothesis says that the truncation to
`[-K,K]` loses no root. -/
lemma annM_sum_eq_fiber_sum (Pa : Work.FITop.Params) (z : GaussianInt) (K : ℕ)
    (hroot : ∀ w ∈ Work.FITop3.annM Pa, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
    (∑ w ∈ Work.FITop3.annM Pa, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (((Work.FITop3.annM Pa).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℝ) := by
  classical
  have h1 : ∀ w ∈ Work.FITop3.annM Pa,
      (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
        = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (if c ^ 2 = Work.FIPlan.cForm w z then (1 : ℝ) else 0) :=
    fun w hw => Work.FIArea2.Zint_eq_Cnt K (Work.FIPlan.cForm w z) (hroot w hw)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_boole _ _

/-! ## 1. The per-`c` fibre bound with the exact normalisation `N = |z|²`

This is `Work.FIArea1.per_c_gen_bound` with `Pa.N` replaced by `|z|²`, which is what the sharp
count needs.  The proof is the same: `w ↦ ψ(z,w)` is injective on the fibre
(`psi_eq_of_cForm_eq`), its values are congruent modulo `N` (`nz_dvd_psi_sub`) and are bounded by
`√(2MN)` in absolute value (`psi_sq_le`), so `card_int_le_shifted_ap` applies. -/
lemma per_c_gen_bound_prim {Pa : Work.FITop.Params} {z : GaussianInt}
    {T : Finset GaussianInt} {v : ℤ}
    (hcop : IsCoprime z.re z.im) (hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0)
    (hMpos : 0 < Pa.M)
    (hT : ∀ w ∈ T, w ∈ Work.FITop3.annM Pa ∧ Work.FIPlan.cForm w z = v) :
    (T.card : ℝ) ≤ 2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1 := by
  have hnz0 : Work.FIPlan.gnorm z ≠ 0 := by
    intro h0
    exact hnz (by rw [h0]; norm_num)
  have hnzR : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hnz0
  by_cases hne : T.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hne
    set B : Finset ℤ := T.image (Work.FIArea1.psi z) with hB
    have hinj : Set.InjOn (Work.FIArea1.psi z) (T : Set GaussianInt) := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      exact Work.FIArea1.psi_eq_of_cForm_eq hcop hnz (by rw [(hT a ha).2, (hT b hb).2]) hab
    have hBcard : B.card = T.card := by rw [hB]; exact Finset.card_image_of_injOn hinj
    set R : ℝ := Real.sqrt (2 * Pa.M * (Work.FIPlan.gnorm z : ℝ)) with hR
    have hRnn : 0 ≤ R := Real.sqrt_nonneg _
    have hdiv : ∀ t ∈ B, ((Work.FIPlan.gnorm z) : ℤ) ∣ (t - Work.FIArea1.psi z w₀) := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hcw : Work.FIPlan.cForm w z = Work.FIPlan.cForm w₀ z := by
        rw [(hT w hw).2, (hT w₀ hw₀).2]
      exact Work.FIArea1.nz_dvd_psi_sub hcop hcw
    have hint : ∀ t ∈ B, |(t : ℝ)| ≤ R := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hgt : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M :=
        (Work.FITop3.mem_annM.mp (hT w hw).1).2.2
      have hgz0 : (0 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := le_of_lt hnzR
      have hsq : (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
          ≤ 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ) := by
        have h1 := Work.FIArea1.psi_sq_le w z
        have h2 : (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
            ≤ (((Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        calc (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
              ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := h2
          _ ≤ (2 * Pa.M) * (Work.FIPlan.gnorm z : ℝ) :=
              mul_le_mul_of_nonneg_right hgt hgz0
      rw [hR]
      exact Real.abs_le_sqrt hsq
    have hmain := Work.FIArea1.card_int_le_shifted_ap (U := B)
        (t0 := Work.FIArea1.psi z w₀) (m := Work.FIPlan.gnorm z)
        (Nat.pos_of_ne_zero hnz0) hRnn hdiv hint
    rw [hBcard] at hmain
    have hstep : 2 * R / (Work.FIPlan.gnorm z : ℝ)
        ≤ 2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) := by
      have hsqeq : (R / (Work.FIPlan.gnorm z : ℝ)) ^ 2
          = 2 * Pa.M / (Work.FIPlan.gnorm z : ℝ) := by
        rw [hR, div_pow, Real.sq_sqrt (by positivity)]
        field_simp
      have hnn : 0 ≤ R / (Work.FIPlan.gnorm z : ℝ) := by positivity
      have heq : R / (Work.FIPlan.gnorm z : ℝ)
          = Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) := by
        rw [← Real.sqrt_sq hnn, hsqeq]
      rw [show 2 * R / (Work.FIPlan.gnorm z : ℝ)
            = 2 * (R / (Work.FIPlan.gnorm z : ℝ)) by ring, heq]
    linarith [hmain, hstep]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ 2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) := by positivity
    linarith

/-! ## 2. The closing real inequality -/

/-- **The arithmetic step.**  With `M, N ≥ 1` and `K ≤ (2MN)^{1/4} + 1`,

  `(2K+1)(2√(2M/N) + 1) ≤ 64 (M^{3/4} N^{-1/4} + (MN)^{1/4})`.

The two factors are `2K + 1 ≤ 6(MN)^{1/4}` (the `c`-range) and `2√(2M/N) + 1` (the fibre
bound); their product is `12√2·M^{3/4}N^{-1/4} + 6(MN)^{1/4}`. -/
lemma arith_bound {M N K : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hK : K ≤ (2 * M * N) ^ ((1 : ℝ) / 4) + 1) :
    (2 * K + 1) * (2 * Real.sqrt (2 * M / N) + 1)
      ≤ 64 * (M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4) + (M * N) ^ ((1 : ℝ) / 4)) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hMN0 : (0 : ℝ) ≤ M * N := by positivity
  set A : ℝ := (M * N) ^ ((1 : ℝ) / 4) with hA
  have hA1 : 1 ≤ A := by
    rw [hA]; exact Real.one_le_rpow (by nlinarith) (by norm_num)
  have hAnn : 0 ≤ A := le_trans zero_le_one hA1
  have h2A : (2 * M * N) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 4) * A := by
    rw [hA, show (2 : ℝ) * M * N = 2 * (M * N) by ring,
      Real.mul_rpow (by norm_num) hMN0]
  -- `2^{1/4} ≤ 3/2`
  have hr2 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 3 / 2 := by
    have h4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h4' : ((3 : ℝ) / 2) ^ 4 = 81 / 16 := by norm_num
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (4 : ℕ) ≠ 0)]
    rw [h4, h4']
    norm_num
  -- `2K + 1 ≤ 6A`
  have hK2 : 2 * K + 1 ≤ 6 * A := by
    have h1 : 2 * K + 1 ≤ 2 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * A + 1) + 1 := by
      linarith [hK, h2A]
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) * A ≤ (3 / 2) * A :=
      mul_le_mul_of_nonneg_right hr2 hAnn
    linarith [h1, h2, hA1]
  -- `√(2M/N) = √2·√(M/N)` and `√(M/N)·A = M^{3/4}N^{-1/4}`
  have hsqrt : Real.sqrt (2 * M / N) = Real.sqrt 2 * Real.sqrt (M / N) := by
    rw [show 2 * M / N = 2 * (M / N) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hSA : Real.sqrt (M / N) * A = M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4) := by
    have h1 : Real.sqrt (M / N) = M ^ ((1 : ℝ) / 2) / N ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow (le_of_lt hM0) (le_of_lt hN0)]
    have h2 : A = M ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4) := by
      rw [hA, Real.mul_rpow (le_of_lt hM0) (le_of_lt hN0)]
    rw [h1, h2]
    calc M ^ ((1 : ℝ) / 2) / N ^ ((1 : ℝ) / 2) * (M ^ ((1 : ℝ) / 4) * N ^ ((1 : ℝ) / 4))
        = (M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 4)) * (N ^ ((1 : ℝ) / 4) / N ^ ((1 : ℝ) / 2)) := by
          ring
      _ = M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4) := by
          rw [← Real.rpow_add hM0, ← Real.rpow_sub hN0]
          norm_num
  have hterm1 : 12 * Real.sqrt 2 * (Real.sqrt (M / N) * A)
      ≤ 64 * (M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4)) := by
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hpos : 0 ≤ M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4) := by positivity
    have hc : 12 * Real.sqrt 2 ≤ 64 := by nlinarith [hs2]
    rw [hSA]
    exact mul_le_mul_of_nonneg_right hc hpos
  have hterm2 : 6 * A ≤ 64 * A := by linarith [hAnn]
  calc (2 * K + 1) * (2 * Real.sqrt (2 * M / N) + 1)
      ≤ (6 * A) * (2 * (Real.sqrt 2 * Real.sqrt (M / N)) + 1) := by
        have : 2 * Real.sqrt (2 * M / N) + 1 = 2 * (Real.sqrt 2 * Real.sqrt (M / N)) + 1 := by
          rw [hsqrt]
        rw [this]
        exact mul_le_mul_of_nonneg_right hK2 (by positivity)
    _ = 12 * Real.sqrt 2 * (Real.sqrt (M / N) * A) + 6 * A := by ring
    _ ≤ 64 * (M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4)) + 64 * A := add_le_add hterm1 hterm2
    _ = 64 * (M ^ ((3 : ℝ) / 4) * N ^ (-(1 : ℝ) / 4) + (M * N) ^ ((1 : ℝ) / 4)) := by
        rw [hA]; ring

/-! ## 3. The target -/

theorem sum_Zint_annM_prim_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (z : GaussianInt),
      1 ≤ Pa.M → Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z →
      (∑ w ∈ Work.FITop3.annM Pa, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ c * (Pa.M ^ ((3 : ℝ) / 4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4)
            + (Pa.M * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := by
  refine ⟨64, by norm_num, ?_⟩
  intro Pa z hM1 hprim hz1
  classical
  have hMpos : (0 : ℝ) < Pa.M := by linarith
  have hN1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hz1
  have hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0 := by
    have h : Work.FIPlan.gnorm z ≠ 0 := Nat.one_le_iff_ne_zero.mp hz1
    exact_mod_cast h
  have hcop : IsCoprime z.re z.im := Work.FIArea2.isCoprime_re_im_of_isCoprime_star hprim
  set B : ℝ := (2 * Pa.M * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) with hBdef
  set K : ℕ := ⌈B⌉₊ with hKdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hKle : (K : ℝ) ≤ B + 1 := by
    rw [hKdef]; exact le_of_lt (Nat.ceil_lt_add_one hBnn)
  -- every integer root `c` of `Re(wz) = c²` lies in `[-K,K]`
  have hroot : ∀ w ∈ Work.FITop3.annM Pa, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro w hw c hc
    obtain ⟨-, hlt, hle⟩ := Work.FITop3.mem_annM.mp hw
    have hgnw : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M := hle
    have hprod : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
        = ((w * z).re : ℝ) ^ 2 + ((w * z).im : ℝ) ^ 2 := by
      rw [← annM_prim_gnorm_mul_real w z, annM_prim_gnorm_eq_coords]
    have hre : ((w * z).re : ℝ) = (c : ℝ) ^ 2 := by
      have h : ((Work.FIPlan.cForm w z : ℤ) : ℝ) = (c : ℝ) ^ 2 := by
        rw [← hc]; push_cast; ring
      simpa only [Work.FIPlan.cForm] using h
    have hc4 : ((c : ℝ)) ^ 4 ≤ 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ) := by
      have hstep : ((c : ℝ) ^ 2) ^ 2
          ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        rw [← hre, hprod]
        nlinarith [sq_nonneg ((w * z).im : ℝ)]
      have hstep2 : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ≤ (2 * Pa.M) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_le_mul_of_nonneg_right hgnw (by positivity)
      calc ((c : ℝ)) ^ 4 = ((c : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hstep
        _ ≤ (2 * Pa.M) * (Work.FIPlan.gnorm z : ℝ) := hstep2
        _ = 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ) := by ring
    have hB4 : B ^ 4 = 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ) := by
      rw [hBdef,
        ← Real.rpow_natCast ((2 * Pa.M * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ))]
      norm_num
    have hcabs : |(c : ℝ)| ≤ B := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hBnn ?_
      rw [hB4]
      calc |(c : ℝ)| ^ 4 = ((c : ℝ)) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ 2 * Pa.M * (Work.FIPlan.gnorm z : ℝ) := hc4
    have hcK : |(c : ℝ)| ≤ (K : ℝ) := le_trans hcabs (by rw [hKdef]; exact Nat.le_ceil B)
    rw [Finset.mem_Icc]
    constructor
    · have h := (abs_le.mp hcK).1
      have h' : ((-(K : ℤ)) : ℝ) ≤ (c : ℝ) := by push_cast; linarith
      exact_mod_cast h'
    · have h := (abs_le.mp hcK).2
      have h' : (c : ℝ) ≤ ((K : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
  rw [annM_sum_eq_fiber_sum Pa z K hroot]
  -- each `c`-fibre has at most `2√(2M/N) + 1` points
  have hfib : ∀ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ((((Work.FITop3.annM Pa).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ)
        ≤ 2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1 := by
    intro c _
    refine per_c_gen_bound_prim (Pa := Pa) (z := z)
      (T := (Work.FITop3.annM Pa).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z))
      (v := c ^ 2) hcop hnz hMpos ?_
    intro w hw
    rw [Finset.mem_filter] at hw
    exact ⟨hw.1, hw.2.symm⟩
  have hcardI : (((Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ) = 2 * (K : ℝ) + 1 := by
    rw [Int.card_Icc]
    have htoNat : ((K : ℤ) + 1 - (-(K : ℤ))).toNat = 2 * K + 1 := by
      have h : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    rw [htoNat]
    push_cast
    ring
  have h1 : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ((((Work.FITop3.annM Pa).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ))
      ≤ (2 * (K : ℝ) + 1)
          * (2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
    calc _ ≤ ∑ _c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1) :=
          Finset.sum_le_sum hfib
      _ = (((Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ)
            * (2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (K : ℝ) + 1)
            * (2 * Real.sqrt (2 * Pa.M / (Work.FIPlan.gnorm z : ℝ)) + 1) := by rw [hcardI]
  have hKle' : (K : ℝ) ≤ (2 * Pa.M * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) + 1 := by
    rw [← hBdef]; exact hKle
  exact h1.trans (arith_bound (M := Pa.M) (N := (Work.FIPlan.gnorm z : ℝ)) (K := (K : ℝ))
    hM1 hN1 hKle')

end

end Work.FITop4.Red5
