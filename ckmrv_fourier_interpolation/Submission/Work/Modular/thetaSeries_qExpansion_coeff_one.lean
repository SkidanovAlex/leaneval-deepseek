import Mathlib
import Submission.Work.Modular.Lattice

namespace Work.Modular

open Work.Modular
open scoped Manifold
open UpperHalfPlane
open MeasureTheory

/-- The point `u + i` of the upper half plane, as a function of the real variable `u`. -/
private def iLine (u : ℝ) : ℍ := ⟨(u : ℂ) + Complex.I, by simp [Complex.add_im]⟩

@[simp]
private lemma coe_iLine (u : ℝ) : ((iLine u : ℍ) : ℂ) = (u : ℂ) + Complex.I := rfl

@[simp]
private lemma iLine_im (u : ℝ) : (iLine u).im = 1 := by simp [iLine]

/-- The modulus of the summand `thetaTerm τ x = exp (π i τ ‖x‖²)` of the theta series. -/
private lemma norm_thetaTerm {n : ℕ} (τ : ℍ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖thetaTerm τ x‖ = Real.exp (-Real.pi * τ.im * ‖x‖ ^ 2) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, UpperHalfPlane.coe_im]
  ring

/-- **Gaussian decay on a discrete lattice.**  For a discrete `ℤ`-submodule `L` of `ℝⁿ` and any
`c > 0`, the sum `∑_{x ∈ L} exp (-c ‖x‖²)` converges.

Since `2N > finrank ℤ L` for `N = finrank ℤ L + 1`, the series `∑_{x ∈ L} ‖x‖^{-2N}` converges
(`ZLattice.summable_norm_pow_inv`).  On the other hand, for `r > 0` the Taylor bound
`(c r²/2)^N / N! ≤ exp (c r²/2)` gives
`exp (-c r²) ≤ exp (-c r²/2) ≤ N! 2^N c^{-N} r^{-2N}`, so the Gaussian is dominated by a multiple
of `‖x‖^{-2N}` away from `x = 0`.  (The same statement is available as
`Work.Modular.summable_exp_neg_norm_sq`; a local copy keeps this file's imports minimal.) -/
private lemma summable_lattice_gaussian {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable (fun z : L => Real.exp (-c * ‖(z : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
  set N : ℕ := Module.finrank ℤ L + 1 with hN
  have hfin_lt : Module.finrank ℤ L < 2 * N := by omega
  have hpoly : Summable (fun z : L => (‖z‖⁻¹) ^ (2 * N)) :=
    ZLattice.summable_norm_pow_inv L (2 * N) hfin_lt
  have hkey : ∀ r : ℝ, 0 < r → Real.exp (-c * r ^ 2) ≤
      ((N.factorial : ℝ) * (2 / c) ^ N) * (r⁻¹) ^ (2 * N) := by
    intro r hr
    have hcr : 0 < c * r ^ 2 / 2 := by positivity
    have h2 : Real.exp (-(c * r ^ 2 / 2)) = (Real.exp (c * r ^ 2 / 2))⁻¹ := Real.exp_neg _
    have h3 : (Real.exp (c * r ^ 2 / 2))⁻¹ ≤ ((c * r ^ 2 / 2) ^ N / (N.factorial : ℝ))⁻¹ := by
      have hp : 0 < (c * r ^ 2 / 2) ^ N / (N.factorial : ℝ) := by positivity
      simpa only [one_div] using
        one_div_le_one_div_of_le hp (Real.pow_div_factorial_le_exp (c * r ^ 2 / 2) hcr.le N)
    have h4 : ((c * r ^ 2 / 2) ^ N / (N.factorial : ℝ))⁻¹ =
        ((N.factorial : ℝ) * (2 / c) ^ N) * (r⁻¹) ^ (2 * N) := by
      have hpow : (c * r ^ 2 / 2) ^ N = (c / 2) ^ N * r ^ (2 * N) := by
        rw [show c * r ^ 2 / 2 = (c / 2) * r ^ 2 by ring, mul_pow, pow_mul]
      rw [hpow, inv_div, div_eq_mul_inv, mul_inv, ← inv_pow, ← inv_pow, inv_div]
      ring
    calc Real.exp (-c * r ^ 2) ≤ Real.exp (-(c * r ^ 2 / 2)) :=
          Real.exp_le_exp.mpr (by nlinarith [sq_nonneg r])
      _ = (Real.exp (c * r ^ 2 / 2))⁻¹ := h2
      _ ≤ ((c * r ^ 2 / 2) ^ N / (N.factorial : ℝ))⁻¹ := h3
      _ = ((N.factorial : ℝ) * (2 / c) ^ N) * (r⁻¹) ^ (2 * N) := h4
  refine Summable.of_norm_bounded_eventually
    (hpoly.mul_left ((N.factorial : ℝ) * (2 / c) ^ N)) ?_
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : L))] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Submodule.norm_coe]
  exact hkey _ (norm_pos_iff.mpr hz)

/-- The integrand of the interval-integral formula for the first `q`-expansion coefficient of a
theta series, evaluated along the horizontal line `Im = 1`: it is
`exp (-2 π i (u + i)) · Θ( u + i )`, written with `exp (-2 π i z) = q^{-1}`. -/
private noncomputable def thetaLineIntegrand {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (u : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((iLine u : ℍ) : ℂ))) * thetaTerm (iLine u) x

private lemma continuous_thetaLineIntegrand {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (thetaLineIntegrand x) := by
  refine Continuous.mul ?_ ?_
  · rw [show (fun u : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((iLine u : ℍ) : ℂ)))) =
        (fun u : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ((u : ℂ) + Complex.I)))) by
      funext u; rw [coe_iLine]]
    fun_prop
  · rw [show (fun u : ℝ => thetaTerm (iLine u) x) =
        (fun u : ℝ => Complex.exp (Real.pi * Complex.I * ((u : ℂ) + Complex.I) *
          ((‖x‖ ^ 2 : ℝ) : ℂ))) by
      funext u; simp only [thetaTerm, coe_iLine]]
    fun_prop

private lemma norm_exp_neg_two_pi_I_iLine (u : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ((iLine u : ℍ) : ℂ)))‖ = Real.exp (2 * Real.pi) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, coe_iLine, Complex.add_re, Complex.add_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

private lemma norm_thetaLineIntegrand {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (u : ℝ) :
    ‖thetaLineIntegrand x u‖ = Real.exp (2 * Real.pi) * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  rw [thetaLineIntegrand, norm_mul, norm_exp_neg_two_pi_I_iLine, norm_thetaTerm, iLine_im]
  congr 1
  ring_nf

/-- The integral of the integrand over one period vanishes unless `‖x‖² = 2`. -/
private lemma integral_thetaLineIntegrand {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hk : ‖x‖ ^ 2 = 2 * (k : ℝ)) (hk1 : k ≠ 1) :
    ∫ u in (0 : ℝ)..1, thetaLineIntegrand x u = 0 := by
  have hk1' : ((k : ℤ) - 1) ≠ 0 := by
    intro h
    exact hk1 (by omega)
  have hortho : ∫ u in (0 : ℝ)..1,
      Complex.exp (2 * Real.pi * Complex.I * (((k : ℤ) - 1 : ℤ) : ℂ) * (u : ℂ)) = 0 := by
    rw [show (2 * Real.pi * Complex.I * (((k : ℤ) - 1 : ℤ) : ℂ)) =
        (((k : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
    rw [integral_exp_mul_complex]
    · rw [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]
    · refine mul_ne_zero (Int.cast_ne_zero.mpr hk1') (mul_ne_zero ?_ Complex.I_ne_zero)
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpt : Set.EqOn (thetaLineIntegrand x)
      (fun u : ℝ => Complex.exp (2 * Real.pi * (1 - (k : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * (((k : ℤ) - 1 : ℤ) : ℂ) * (u : ℂ)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro u _
    rw [thetaLineIntegrand]
    simp only [thetaTerm]
    rw [coe_iLine, hk, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, hortho, mul_zero]

/-- The first `q`-coefficient of the theta series of an even lattice with no vectors of squared
length `2` vanishes.  By Mathlib's `UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral` the
coefficient is `∫_{0}^{1} q^{-1} Θ_L (u + t i) du`; expanding `Θ_L` as its defining sum and
swapping sum and integral, the `x`-th term is `exp (2 π t) exp (-2 π k t) exp (2 π i (k - 1) u)`
with `‖x‖² = 2 k`, whose integral over `[0, 1]` is `1` if `k = 1` and `0` otherwise.  Hence the
coefficient equals the (finite) number of vectors of squared length `2`, which is zero. -/
theorem thetaSeries_qExpansion_coeff_one {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L]
    (hper : Function.Periodic ((thetaSeries L) ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDiff (thetaSeries L)) (hbdd : UpperHalfPlane.IsBoundedAtImInfty (thetaSeries L))
    (heven : IsEvenSubmodule L) (hmin : ∀ x ∈ L, ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≠ 2) :
    (UpperHalfPlane.qExpansion 1 (thetaSeries L)).coeff 1 = 0 := by
  have : Countable L := Finsupp.Countable.of_moduleFinite (R := ℤ) (M := L)
  rw [UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral (h := 1) one_pos hper hhol hbdd 1
    (t := 1) one_pos]
  simp only [one_div, inv_one, one_mul, pow_one, Complex.ofReal_one]
  trans ∫ u in (0 : ℝ)..1, ∑' x : L, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u
  · apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [show (⟨(u : ℂ) + (UpperHalfPlane.I : ℂ), _⟩ : ℍ) = iLine u from by
      rw [UpperHalfPlane.ext_iff]
      simp only [iLine, UpperHalfPlane.I]]
    rw [show (Function.Periodic.qParam 1 ((u : ℂ) + (UpperHalfPlane.I : ℂ)))⁻¹ =
        Complex.exp (-(2 * Real.pi * Complex.I * ((iLine u : ℍ) : ℂ))) from by
      rw [coe_iLine]
      simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      rw [← Complex.exp_neg]
      rfl]
    simp only [thetaSeries, thetaLineIntegrand, coe_iLine]
    rw [← tsum_mul_left]
  · have hInt : ∀ x : L, Integrable
        (fun u : ℝ => thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro x
      exact ((continuous_thetaLineIntegrand _).continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hint_norm : ∀ x : L, ∫ u, ‖thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
        Real.exp (2 * Real.pi) * Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      intro x
      rw [show (fun u : ℝ => ‖thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u‖) =
          (fun _ : ℝ => Real.exp (2 * Real.pi) *
            Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) from
        funext (fun u => norm_thetaLineIntegrand _ u)]
      rw [show ∫ u, Real.exp (2 * Real.pi) *
            Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
          ∫ u in (0 : ℝ)..1, Real.exp (2 * Real.pi) *
            Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) from by
        rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]]
      rw [intervalIntegral.integral_const]
      simp
    have hsum : Summable (fun x : L => ∫ u,
        ‖thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      have hbase : Summable (fun x : L =>
          Real.exp (2 * Real.pi) * Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :=
        (summable_lattice_gaussian L Real.pi_pos).mul_left _
      exact hbase.congr (fun x => (hint_norm x).symm)
    have hsingle : ∀ x : L, ∫ u, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := by
      intro x
      obtain ⟨k, hk⟩ := heven (x : EuclideanSpace ℝ (Fin n)) x.2
      have hk1 : k ≠ 1 := by
        intro h
        exact hmin (x : EuclideanSpace ℝ (Fin n)) x.2 (by rw [hk, h]; norm_num)
      rw [show ∫ u, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
          ∫ u in (0 : ℝ)..1, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u from by
        rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]]
      exact integral_thetaLineIntegrand _ k hk hk1
    have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (F := fun x : L => fun u : ℝ => thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u)
      hInt hsum
    rw [show ∫ u in (0 : ℝ)..1,
          (∑' x : L, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u) =
        ∫ u, (∑' x : L, thetaLineIntegrand (x : EuclideanSpace ℝ (Fin n)) u)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) from by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]]
    rw [← hswap]
    simp only [hsingle, tsum_zero]

end Work.Modular
