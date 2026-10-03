/-
# `Work.FITop4.Red5.window_sharp_count_sqfree`

The sharp dyadic window count under the *squarefree* support hypothesis `Squarefree (|z|²)` of the
paper's coefficient `β_z`, rather than Gaussian primitivity `(z, z̄) = 1`.

The two hypotheses differ only when `|z|²` is even: squarefreeness of `|z|² = a² + b²` still forces
`gcd(a, b) = 1` (a common divisor `g > 1` would give `g² ∣ |z|²`), and *that* is all the lattice
count `winAnn_per_c_bound` uses.  (For even `|z|²` the ramified prime `1 + i` divides both `z` and
`z̄`, so `z` need not be primitive, but its coordinates remain coprime.)

Hence `window_sharp_count_coprime` restates `window_sharp_count` with the hypothesis
`IsCoprime z.re z.im` in place of `IsPrimitive z`; the requested statement follows through
`isCoprime_re_im_of_squarefree_gnorm`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.window_sharp_count

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **A squarefree norm forces coprime coordinates.**  If `|z|² = a² + b²` is squarefree then
`gcd(a, b) = 1`, i.e. `IsCoprime z.re z.im`.  (A common divisor `g > 1` of `a` and `b` would give
`g² ∣ a² + b²`, against squarefreeness.) -/
lemma isCoprime_re_im_of_squarefree_gnorm {z : GaussianInt}
    (h : Squarefree (Work.FIPlan.gnorm z)) : IsCoprime z.re z.im := by
  have hgn : Work.FIPlan.gnorm z = z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs :=
    GaussianInt.natAbs_norm_eq z
  have hdvd : z.re.natAbs.gcd z.im.natAbs * z.re.natAbs.gcd z.im.natAbs ∣
      Work.FIPlan.gnorm z := by
    rw [hgn]
    exact dvd_add (mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      (mul_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
  have hg : z.re.natAbs.gcd z.im.natAbs = 1 := Nat.isUnit_iff.mp (h _ hdvd)
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, hg]

/-- **The sharp dyadic window count with coprime coordinates.**  For `M = Mn` and `N = |z|²`
(`IsCoprime z.re z.im`, `N ≥ 1`),

  `Σ_{M < |w|² ≤ 2M} Z(Re w z) ≤ 64 (M^{3/4} N^{-1/4} + (M N)^{1/4})`.

This is `window_sharp_count` with the primitive hypothesis weakened to the coordinate coprimality
that the lattice count actually uses. -/
lemma window_sharp_count_coprime :
    ∃ c : ℝ, 0 < c ∧ ∀ (Mn : ℕ) (z : GaussianInt), 1 ≤ Mn →
    IsCoprime z.re z.im → 1 ≤ Work.FIPlan.gnorm z →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ c * ((Mn : ℝ) ^ ((3:ℝ)/4) * ((Work.FIPlan.gnorm z : ℝ)) ^ (-(1:ℝ)/4)
          + ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)) := by
  refine ⟨64, by norm_num, ?_⟩
  intro Mn z hMn hcop hz1
  rw [← window_eq_winAnn (A := Mn) (fun w => (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))]
  have hN1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hz1
  have hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0 := by
    have h : Work.FIPlan.gnorm z ≠ 0 := Nat.one_le_iff_ne_zero.mp hz1
    exact_mod_cast h
  set B : ℝ := (2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) with hBdef
  set K : ℕ := ⌈B⌉₊ with hKdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hKle : (K : ℝ) ≤ B + 1 := by rw [hKdef]; exact le_of_lt (Nat.ceil_lt_add_one hBnn)
  -- every integer root `c` of `Re(wz) = c²` lies in `[-K,K]`
  have hroot : ∀ w ∈ winAnn Mn, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro w hw c hc
    obtain ⟨-, -, hle⟩ := mem_winAnn.mp hw
    have hgnw : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * (Mn : ℝ) := by exact_mod_cast hle
    have hprod : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
        = ((w * z).re : ℝ) ^ 2 + ((w * z).im : ℝ) ^ 2 := by
      rw [← annM_prim_gnorm_mul_real w z, annM_prim_gnorm_eq_coords]
    have hre : ((w * z).re : ℝ) = (c : ℝ) ^ 2 := by
      have h : ((Work.FIPlan.cForm w z : ℤ) : ℝ) = (c : ℝ) ^ 2 := by
        rw [← hc]; push_cast; ring
      simpa only [Work.FIPlan.cForm] using h
    have hc4 : ((c : ℝ)) ^ 4 ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
      have hstep : ((c : ℝ) ^ 2) ^ 2
          ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        rw [← hre, hprod]
        nlinarith [sq_nonneg ((w * z).im : ℝ)]
      have hstep2 : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ≤ (2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_le_mul_of_nonneg_right hgnw (by positivity)
      calc ((c : ℝ)) ^ 4 = ((c : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hstep
        _ ≤ (2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ) := hstep2
        _ = 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by ring
    have hB4 : B ^ 4 = 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
      rw [hBdef,
        ← Real.rpow_natCast ((2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ))]
      norm_num
    have hcabs : |(c : ℝ)| ≤ B := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hBnn ?_
      rw [hB4]
      calc |(c : ℝ)| ^ 4 = ((c : ℝ)) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hc4
    have hcK : |(c : ℝ)| ≤ (K : ℝ) := le_trans hcabs (by rw [hKdef]; exact Nat.le_ceil B)
    rw [Finset.mem_Icc]
    constructor
    · have h := (abs_le.mp hcK).1
      have h' : ((-(K : ℤ)) : ℝ) ≤ (c : ℝ) := by push_cast; linarith
      exact_mod_cast h'
    · have h := (abs_le.mp hcK).2
      have h' : (c : ℝ) ≤ ((K : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
  rw [winAnn_sum_eq_fiber_sum Mn z K hroot]
  have hfib : ∀ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ((((winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ)
        ≤ 2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1 := by
    intro c _
    refine winAnn_per_c_bound (A := Mn) (z := z)
      (T := (winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z))
      (v := c ^ 2) hcop hnz ?_
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
        ((((winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ))
      ≤ (2 * (K : ℝ) + 1)
          * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
    calc _ ≤ ∑ _c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) :=
          Finset.sum_le_sum hfib
      _ = (((Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ)
            * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (K : ℝ) + 1)
            * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by rw [hcardI]
  have hKle' : (K : ℝ) ≤ (2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) + 1 := by
    rw [← hBdef]; exact hKle
  exact h1.trans (arith_bound (M := (Mn : ℝ)) (N := (Work.FIPlan.gnorm z : ℝ)) (K := (K : ℝ))
    (by exact_mod_cast hMn) hN1 hKle')

theorem window_sharp_count_sqfree :
    ∃ c : ℝ, 0 < c ∧ ∀ (Mn : ℕ) (z : GaussianInt), 1 ≤ Mn → z ≠ 0 →
    Squarefree (Work.FIPlan.gnorm z) → 1 ≤ Work.FIPlan.gnorm z →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ c * ((Mn : ℝ) ^ ((3:ℝ)/4) * ((Work.FIPlan.gnorm z : ℝ)) ^ (-(1:ℝ)/4)
          + ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)) := by
  obtain ⟨c, hc, hbound⟩ := window_sharp_count_coprime
  exact ⟨c, hc, fun Mn z hMn _ hsf hz1 =>
    hbound Mn z hMn (isCoprime_re_im_of_squarefree_gnorm hsf) hz1⟩

end

end Work.FITop4.Red5
