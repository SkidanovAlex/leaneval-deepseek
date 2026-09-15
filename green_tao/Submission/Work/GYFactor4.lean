import Submission.Work.GYFactor3
import Submission.Commons.Analysis.Measure.Fubini.measurePreserving_prodPiCurry
import Submission.Commons.Analysis.Series.summable_prod_mul_nonneg
import Submission.Commons.Analysis.Series.summable_pi_prod_max_rpow
import Submission.Commons.MeasureTheory.integrable_tsum_of_summable_integral_norm
import Submission.Commons.Analysis.Complex.perron_log_identity

/-!
# The Perron + Fubini + Euler-product identity (Green–Tao §10, (10.2) = (10.5) = (10.7))

`Submission/Work/GYAvg.lean` reduces Green–Tao Proposition 9.5 to the divisor-sum main term
`mainSum R W A b = ∑_{d,e ∈ [1,R]^m} (∏_i μ(d_i)μ(e_i) log(R/d_i) log(R/e_i)) · ρ(d,e)`.

This file performs the contour-integral rewriting of `mainSum` (Green–Tao (10.2) = (10.5)):
`log(R/d) = (1/2π)∫_t (R/d)^{c+it}/(c+it)² dt` for every `c > 0`, so for `c > 1` (where the
Dirichlet series converges absolutely, making the interchange legitimate)

`mainSum = (2πi)^{-2m} ∫_{Γ_c^{2m}} F(z,z') ∏_j R^{z_j+z'_j}/(z_j²z'_j²)`,

with `F(z,z') = ∑_{d,e} ∏_i μ(d_i)μ(e_i) d_i^{-z_i}e_i^{-z'_i}·ρ(d,e)` the §10 Dirichlet series,
which the Euler-product identity of `GYFactor3` identifies with `∏_p E_p` in `Re > 1`.
-/

open Finset MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

/-- The point of the vertical line `Re = c`: `sline c t = c + i t`. -/
noncomputable def sline (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma sline_re (c t : ℝ) : (sline c t).re = c := by
  simp [sline]

@[simp] lemma sline_im (c t : ℝ) : (sline c t).im = t := by
  simp [sline]

lemma continuous_sline (c : ℝ) : Continuous (sline c) := by
  unfold sline; fun_prop

lemma sline_ne_zero {c t : ℝ} (hc : 0 < c) : sline c t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [sline] at this
  linarith

/-- The one-variable Perron kernel `x^s / s²`. -/
noncomputable def Pker (c x : ℝ) (t : ℝ) : ℂ := (x : ℂ) ^ (sline c t) / (sline c t) ^ 2

/-- **The Perron identity** in the form used below (Green–Tao §10). -/
lemma perron_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, Pker c x t
      = if 1 < x then (Real.log x : ℂ) else 0 := by
  have h := Commons.Analysis.Complex.perron_log_identity (c := c) (x := x) hc hx
  simpa [Pker, sline, mul_add, mul_comm, mul_left_comm, mul_assoc] using h

/-- The Perron kernel is integrable: `‖x^{c+it}/(c+it)²‖ ≤ x^c·(1+c²)/c²·(1+t²)⁻¹`. -/
lemma integrable_Pker {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun t : ℝ => Pker c x t) := by
  have hx0 : (0 : ℝ) < x := hx
  have hnum : Continuous (fun t : ℝ => (x : ℂ) ^ (sline c t)) := by
    have he : (fun t : ℝ => (x:ℂ) ^ (sline c t))
        = fun t => Complex.exp (Complex.log (x:ℂ) * (sline c t)) := by
      funext t
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx)]
    rw [he]
    exact Complex.continuous_exp.comp (continuous_const.mul (continuous_sline c))
  have hcont : Continuous (fun t : ℝ => Pker c x t) := by
    refine Continuous.div hnum ((continuous_sline c).pow 2) (fun t => ?_)
    exact pow_ne_zero 2 (sline_ne_zero hc)
  have hb : ∀ t : ℝ, ‖Pker c x t‖
      ≤ (x ^ c * (1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ := by
    intro t
    have h1 : ‖(x : ℂ) ^ (sline c t)‖ = x ^ c := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp [sline]
    have h2 : ‖(sline c t) ^ 2‖ = (sline c t).re ^ 2 + (sline c t).im ^ 2 := by
      rw [Complex.norm_pow, Complex.sq_norm, Complex.normSq_apply]
      ring
    have h4 : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
    have hge : (1 : ℝ) ≤ ((1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ * (c ^ 2 + t ^ 2) := by
      have h2 : ((1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ * (c ^ 2 + t ^ 2)
          = (1 + c ^ 2) * (c ^ 2 + t ^ 2) / (c ^ 2 * (1 + t ^ 2)) := by
        field_simp
      rw [h2, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg c, sq_nonneg t]
    have hxc : (0 : ℝ) < x ^ c := Real.rpow_pos_of_pos hx c
    rw [Pker, norm_div, h1, h2, sline_re, sline_im]
    rw [div_le_iff₀ h4]
    calc (x : ℝ) ^ c = x ^ c * 1 := by ring
      _ ≤ x ^ c * (((1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ * (c ^ 2 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left hge hxc.le
      _ = (x ^ c * (1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹ * (c ^ 2 + t ^ 2) := by ring
  refine Integrable.mono' (g := fun t : ℝ => (x ^ c * (1 + c ^ 2) / c ^ 2) * (1 + t ^ 2)⁻¹)
    ?_ hcont.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  exact (integrable_inv_one_add_sq.const_mul _)


/-! ## The Green–Tao kernel and the §10 Dirichlet-series summand -/

/-- The Green–Tao kernel `∏_j R^{z_j+z'_j}/(z_j²z'_j²)`, written in the factorised form (equivalent
to the shape used by `zeta_bound_m_strip`, see `Ker_eq`). -/
noncomputable def Ker (R : ℕ) (z z' : Fin m → ℂ) : ℂ :=
  ∏ i, ((R : ℂ) ^ (z i) * (R : ℂ) ^ (z' i) * ((z i) ^ 2 * (z' i) ^ 2)⁻¹)

/-- The §10 Dirichlet-series summand, with `ρ` in place of the local weight (they agree whenever
the Möbius factors do not vanish). -/
noncomputable def Dsm (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ)
    (z z' : Fin m → ℂ) : ℂ :=
  (∏ i, ((ArithmeticFunction.moebius (d i) : ℂ) * (ArithmeticFunction.moebius (e i) : ℂ)
      * ((d i : ℂ) ^ (-(z i))) * ((e i : ℂ) ^ (-(z' i))))) * ((rho W A b d e : ℝ) : ℂ)

/-- The `(z, z')`-dependent factor of the *contour* integrand of one pair `(d, e)`: the map
`(t, t') ↦ ∏_i Pker c (R/d_i) (t i) Pker c (R/e_i) (t' i)`. -/
noncomputable def Ppr (c : ℝ) (R : ℕ) (d e : Fin m → ℕ) (p : Fin m → ℝ × ℝ) : ℂ :=
  ∏ i, (Pker c ((R : ℝ) / (d i : ℝ)) (p i).1 * Pker c ((R : ℝ) / (e i : ℝ)) (p i).2)

/-- The double contour integral of one pair `(d, e)`, written over `Fin m → ℝ × ℝ` so that
Fubini in the product structure is available directly. -/
noncomputable def Ip (c : ℝ) (R : ℕ) (d e : Fin m → ℕ) : ℂ :=
  ∫ p : Fin m → ℝ × ℝ, Ppr c R d e p

/-- **The product-structure Fubini for `Ip`**: the `m`-fold integral factorises over the indices. -/
lemma Ip_factor (c : ℝ) (R : ℕ) (d e : Fin m → ℕ) :
    Ip c R d e = ∏ i, (∫ s : ℝ, Pker c ((R : ℝ) / (d i : ℝ)) s)
      * (∫ s : ℝ, Pker c ((R : ℝ) / (e i : ℝ)) s) := by
  unfold Ip Ppr
  refine (MeasureTheory.integral_fin_nat_prod_volume_eq_prod
    (fun i (x : ℝ × ℝ) => Pker c ((R : ℝ) / (d i : ℝ)) x.1
      * Pker c ((R : ℝ) / (e i : ℝ)) x.2)).trans ?_
  refine Finset.prod_congr rfl (fun i _ => MeasureTheory.integral_prod_mul _ _)

/-- The one-variable Perron integral in closed form, valid for `x ≥ 0`. -/
lemma integral_Pker {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    ∫ t : ℝ, Pker c x t = (2 * (Real.pi : ℂ)) * ((max (Real.log x) 0 : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst hx0
    have hz : (fun t : ℝ => Pker c 0 t) = fun _ => 0 := by
      funext t
      rw [Pker, show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero,
        Complex.zero_cpow (sline_ne_zero hc), zero_div]
    rw [Real.log_zero, max_eq_left le_rfl, Complex.ofReal_zero, mul_zero, hz, integral_zero]
  · have h := perron_one (c := c) (x := x) hc hx0
    have h2 : (∫ t : ℝ, Pker c x t)
        = (2 * (Real.pi : ℂ)) * ((if 1 < x then (Real.log x : ℂ) else 0)) := by
      have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      have h3 := congrArg (fun w : ℂ => (2 * (Real.pi : ℂ)) * w) h
      rw [← mul_assoc, mul_one_div_cancel hpi, one_mul] at h3
      exact h3
    rw [h2]
    congr 1
    by_cases h1 : 1 < x
    · rw [if_pos h1, max_eq_left (Real.log_pos h1).le]
    · rw [if_neg h1, max_eq_right (Real.log_nonpos hx0.le (le_of_not_gt h1))]
      norm_num

/-- **`Ip` in closed form** (Perron + the product-structure Fubini): for `c > 0`,
`Ip c R d e = (2π)^{2m} ∏_i (log(R/d_i))_+ (log(R/e_i))_+`. -/
lemma Ip_closed {c : ℝ} (hc : 0 < c) (R : ℕ) (d e : Fin m → ℕ) :
    Ip c R d e = (2 * (Real.pi : ℂ)) ^ (2 * m)
      * ∏ i, (((max (Real.log ((R : ℝ) / (d i : ℝ))) 0 : ℝ) : ℂ)
          * ((max (Real.log ((R : ℝ) / (e i : ℝ))) 0 : ℝ) : ℂ)) := by
  rw [Ip_factor, Finset.prod_mul_distrib]
  have key : ∀ f : Fin m → ℕ,
      (∏ i : Fin m, ∫ s : ℝ, Pker c ((R : ℝ) / (f i : ℝ)) s)
        = (2 * (Real.pi : ℂ)) ^ m
          * ∏ i, ((max (Real.log ((R : ℝ) / (f i : ℝ))) 0 : ℝ) : ℂ) := by
    intro f
    rw [show (∏ i : Fin m, ∫ s : ℝ, Pker c ((R : ℝ) / (f i : ℝ)) s)
          = ∏ i : Fin m,
              ((2 * (Real.pi : ℂ)) * ((max (Real.log ((R : ℝ) / (f i : ℝ))) 0 : ℝ) : ℂ))
        from Finset.prod_congr rfl
          (fun i _ => integral_Pker hc (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg (f i))))]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [key d, key e]
  rw [show (∏ i : Fin m, (((max (Real.log ((R : ℝ) / (d i : ℝ))) 0 : ℝ) : ℂ)
        * ((max (Real.log ((R : ℝ) / (e i : ℝ))) 0 : ℝ) : ℂ)))
      = (∏ i, ((max (Real.log ((R : ℝ) / (d i : ℝ))) 0 : ℝ) : ℂ))
        * (∏ i, ((max (Real.log ((R : ℝ) / (e i : ℝ))) 0 : ℝ) : ℂ))
    from Finset.prod_mul_distrib]
  have hp : (2 * (Real.pi : ℂ)) ^ (2 * m)
      = (2 * (Real.pi : ℂ)) ^ m * (2 * (Real.pi : ℂ)) ^ m := by
    rw [← pow_add]
    ring_nf
  rw [hp]
  ring


/-! ## Rewriting `mainSum` as a (finite) sum of contour integrals -/

/-- On the truncation range `1 ≤ d ≤ R` the two logarithms `log (R/d)` and `(log (R/d))_+`
coincide. -/
lemma log_eq_max_log {R d : ℕ} (hd1 : 1 ≤ d) (hdR : d ≤ R) :
    (Real.log ((R : ℝ) / (d : ℝ)) : ℂ)
      = ((max (Real.log ((R : ℝ) / (d : ℝ))) 0 : ℝ) : ℂ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hx : (1 : ℝ) ≤ (R : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd0, one_mul]
    exact_mod_cast hdR
  rw [max_eq_left (Real.log_nonneg hx)]

/-- **The Perron rewriting of `mainSum`** (Green–Tao (10.2) = the finite sum of (10.5)-integrands):
each term of the divisor sum is `(2π)^{-2m}` times the corresponding `Ip`. -/
lemma mainSum_eq_Ip_sum {c : ℝ} (hc : 0 < c) (R W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) :
    (mainSum (m := m) (t := t) R W A b : ℂ) = ((2 * (Real.pi : ℂ)) ^ (2 * m))⁻¹ *
      ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
        ((∏ i, ((ArithmeticFunction.moebius (d i) : ℂ)
            * (ArithmeticFunction.moebius (e i) : ℂ))) * ((rho W A b d e : ℝ) : ℂ))
          * Ip c R d e := by
  classical
  have hmain : (mainSum (m := m) (t := t) R W A b : ℂ) =
      ∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
        (((coef R d e * rho W A b d e : ℝ)) : ℂ) := by
    rw [mainSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Complex.ofReal_sum]
  rw [hmain, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  simp only [P, Fintype.mem_piFinset] at hd he
  have hd1 : ∀ i, 1 ≤ d i := fun i => (Finset.mem_Icc.mp (hd i)).1
  have hdR : ∀ i, d i ≤ R := fun i => (Finset.mem_Icc.mp (hd i)).2
  have he1 : ∀ i, 1 ≤ e i := fun i => (Finset.mem_Icc.mp (he i)).1
  have heR : ∀ i, e i ≤ R := fun i => (Finset.mem_Icc.mp (he i)).2
  have hcoef : ((coef R d e : ℝ) : ℂ)
      = (∏ i, (ArithmeticFunction.moebius (d i) : ℂ))
        * (∏ i, (ArithmeticFunction.moebius (e i) : ℂ))
        * (∏ i, ((Real.log ((R : ℝ) / (d i : ℝ)) : ℝ) : ℂ))
        * (∏ i, ((Real.log ((R : ℝ) / (e i : ℝ)) : ℝ) : ℂ)) := by
    rw [coef, Complex.ofReal_prod]
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hL1 : (∏ i, ((Real.log ((R : ℝ) / (d i : ℝ)) : ℝ) : ℂ))
      = ∏ i, ((max (Real.log ((R : ℝ) / (d i : ℝ))) 0 : ℝ) : ℂ) :=
    Finset.prod_congr rfl (fun i _ => log_eq_max_log (hd1 i) (hdR i))
  have hL2 : (∏ i, ((Real.log ((R : ℝ) / (e i : ℝ)) : ℝ) : ℂ))
      = ∏ i, ((max (Real.log ((R : ℝ) / (e i : ℝ))) 0 : ℝ) : ℂ) :=
    Finset.prod_congr rfl (fun i _ => log_eq_max_log (he1 i) (heR i))
  have hgoal : (2 * (Real.pi : ℂ)) ^ (2 * m) * (((coef R d e * rho W A b d e : ℝ)) : ℂ)
      = ((∏ i, ((ArithmeticFunction.moebius (d i) : ℂ)
            * (ArithmeticFunction.moebius (e i) : ℂ))) * ((rho W A b d e : ℝ) : ℂ))
          * Ip c R d e := by
    rw [Complex.ofReal_mul, hcoef, hL1, hL2, Ip_closed hc R d e]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  rw [← hgoal]
  have hpi : ((2 * (Real.pi : ℂ)) ^ (2 * m)) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
  rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]


/-- `R ^ (∑_{i∈s} f i) = ∏_{i∈s} R ^ (f i)` for `R ≠ 0`. -/
lemma cpow_finset_sum {ι : Type*} {R : ℂ} (hR : R ≠ 0) (s : Finset ι) (f : ι → ℂ) :
    R ^ (s.sum f) = s.prod (fun i => R ^ f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Complex.cpow_add _ _ hR, ih]

/-- The kernel in the shape used by the contour-integration lemma `zeta_bound_m_strip`. -/
lemma Ker_eq {R : ℕ} (hR : (R : ℂ) ≠ 0) (z z' : Fin m → ℂ) :
    Ker R z z' = (R : ℂ) ^ (∑ i, (z i + z' i)) * ∏ i, ((z i) ^ 2 * (z' i) ^ 2)⁻¹ := by
  rw [Ker, cpow_finset_sum hR Finset.univ (fun i => z i + z' i)]
  rw [Finset.prod_congr rfl (fun i _ => Complex.cpow_add (z i) (z' i) hR)]
  rw [Finset.prod_mul_distrib]

/-- `((a/b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w * ((b : ℂ) ^ (-w))` for `a, b ≥ 0`. -/
lemma div_cpow_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w * ((b : ℂ) ^ (-w)) := by
  rw [← Commons.Analysis.Complex.div_cpow_ofReal_div a b ha hb w, div_eq_mul_inv, Complex.cpow_neg]

/-- The per-index product identity relating the Perron kernel to the `Dsm`-summand factors. -/
lemma perKer {c : ℝ} (R d e : ℕ) (s s' : ℝ) :
    Pker c ((R : ℝ) / (d : ℝ)) s * Pker c ((R : ℝ) / (e : ℝ)) s'
      = (R : ℂ) ^ (sline c s) * (R : ℂ) ^ (sline c s')
        * ((d : ℂ) ^ (-(sline c s))) * ((e : ℂ) ^ (-(sline c s')))
        * ((sline c s) ^ 2 * (sline c s') ^ 2)⁻¹ := by
  rw [Pker, Pker, div_cpow_eq (Nat.cast_nonneg R) (Nat.cast_nonneg d) (sline c s),
    div_cpow_eq (Nat.cast_nonneg R) (Nat.cast_nonneg e) (sline c s')]
  simp only [Complex.ofReal_natCast]
  field_simp

/-- **The pointwise identity between the pair-`(d,e)` contour integrand and `Dsm · Ker`.** -/
lemma integrand_eq {c : ℝ} (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (d e : Fin m → ℕ) (p : Fin m → ℝ × ℝ) :
    (∏ i, ((ArithmeticFunction.moebius (d i) : ℂ) * (ArithmeticFunction.moebius (e i) : ℂ)))
        * ((rho W A b d e : ℝ) : ℂ) * Ppr c R d e p
      = Dsm (m := m) (t := t) W A b d e (fun i => sline c ((p i).1))
          (fun i => sline c ((p i).2))
        * Ker (m := m) R (fun i => sline c ((p i).1)) (fun i => sline c ((p i).2)) := by
  have hper : ∀ i : Fin m,
      Pker c ((R : ℝ) / (d i : ℝ)) ((p i).1) * Pker c ((R : ℝ) / (e i : ℝ)) ((p i).2)
        = (R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
          * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))
          * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹ :=
    fun i => perKer R (d i) (e i) ((p i).1) ((p i).2)
  have hX : (∏ i : Fin m, (Pker c ((R : ℝ) / (d i : ℝ)) ((p i).1)
          * Pker c ((R : ℝ) / (e i : ℝ)) ((p i).2)))
      = ∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
          * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))
          * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹) :=
    Finset.prod_congr rfl (fun i _ => hper i)
  have hfin : (∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
          * (ArithmeticFunction.moebius (e i) : ℂ)))
        * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
            * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))
            * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹))
      = (∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
              * (ArithmeticFunction.moebius (e i) : ℂ)
              * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))))
          * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
              * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    ring_nf
  simp only [Ppr, Dsm, Ker]
  rw [hX]
  calc (∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
          * (ArithmeticFunction.moebius (e i) : ℂ)))
        * ((rho W A b d e : ℝ) : ℂ)
        * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
            * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))
            * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹))
      = ((∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
              * (ArithmeticFunction.moebius (e i) : ℂ)))
          * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
              * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))
              * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹)))
        * ((rho W A b d e : ℝ) : ℂ) := by ring
    _ = ((∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
              * (ArithmeticFunction.moebius (e i) : ℂ)
              * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))))
          * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
              * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹)))
        * ((rho W A b d e : ℝ) : ℂ) := by rw [hfin]
    _ = (∏ i : Fin m, ((ArithmeticFunction.moebius (d i) : ℂ)
              * (ArithmeticFunction.moebius (e i) : ℂ)
              * ((d i : ℂ) ^ (-(sline c ((p i).1)))) * ((e i : ℂ) ^ (-(sline c ((p i).2))))))
          * ((rho W A b d e : ℝ) : ℂ)
          * (∏ i : Fin m, ((R : ℂ) ^ (sline c ((p i).1)) * (R : ℂ) ^ (sline c ((p i).2))
              * ((sline c ((p i).1)) ^ 2 * (sline c ((p i).2)) ^ 2)⁻¹)) := by ring


/-! ## The bridge to the iterated `(t, t')`-integral, and the Euler-product step -/

/-- **Currying the two `m`-fold contour integrals.**  The `2m`-fold integral over
`Fin m → ℝ × ℝ` equals the iterated integral over `(Fin m → ℝ) × (Fin m → ℝ)`. -/
lemma integral_curry_pi {m : ℕ} (G : (Fin m → ℝ × ℝ) → ℂ)
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ × ℝ))) :
    (∫ p : Fin m → ℝ × ℝ, G p)
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ, G (fun i => (t i, t' i)) := by
  have h : MeasureTheory.MeasurePreserving
      (⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ × ℝ)) :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm
  rw [← h.integral_comp' G]
  rw [MeasureTheory.integral_prod
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
    (f := fun x : (Fin m → ℝ) × (Fin m → ℝ) =>
      G ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm x))
    (h.integrable_comp hG.aestronglyMeasurable |>.mpr hG)]
  rfl

/-- The summands of the §10 Dirichlet series agree with those written with `ρ`. -/
lemma Dsm_eq_localWeight (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (de : (Fin m → ℕ) × (Fin m → ℕ)) (z z' : Fin m → ℂ) :
    (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
        * (ArithmeticFunction.moebius (de.2 i) : ℂ)
        * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))))
      * localWeight m (vSys W A b) de.1 de.2
      = Dsm (m := m) (t := t) W A b de.1 de.2 z z' := by
  by_cases hsq : ∀ i, Squarefree (de.1 i) ∧ Squarefree (de.2 i)
  · have hpos : ∀ i, 0 < Nat.lcm (de.1 i) (de.2 i) :=
      fun i => Nat.lcm_pos (Nat.pos_of_ne_zero (hsq i).1.ne_zero)
        (Nat.pos_of_ne_zero (hsq i).2.ne_zero)
    have h := rho_eq_localWeight W A b de.1 de.2 (fun i => (hsq i).1) (fun i => (hsq i).2) hpos
    rw [show localWeight m (vSys W A b) de.1 de.2 = ((rho W A b de.1 de.2 : ℝ) : ℂ) from h.symm]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.mp hsq
    rw [not_and_or] at hi
    have hfac : ((ArithmeticFunction.moebius (de.1 i) : ℂ)
        * (ArithmeticFunction.moebius (de.2 i) : ℂ)
        * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))) = 0 := by
      rcases hi with h | h
      · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    have hzero : (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
        * (ArithmeticFunction.moebius (de.2 i) : ℂ)
        * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i))))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfac
    rw [hzero, zero_mul]
    simp only [Dsm, hzero, zero_mul]



/-! ## The main Perron + Fubini + Euler-product identity -/

/-- The summand of the double divisor sum, as a function of `p : Fin m → ℝ × ℝ`. -/
noncomputable def Fsum (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (de : (Fin m → ℕ) × (Fin m → ℕ)) (p : Fin m → ℝ × ℝ) : ℂ :=
  ((∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
      * (ArithmeticFunction.moebius (de.2 i) : ℂ))) * ((rho W A b de.1 de.2 : ℝ) : ℂ))
    * Ppr c R de.1 de.2 p

/-- `Ip` is the integral of `Ppr`. -/
lemma Ip_eq_integral (c : ℝ) (R : ℕ) (d e : Fin m → ℕ) :
    Ip c R d e = ∫ p : Fin m → ℝ × ℝ, Ppr c R d e p := rfl

/-- The per-pair term of the divisor sum as an integral. -/
lemma Ip_term_eq_integral (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (d e : Fin m → ℕ) :
    ((∏ i, ((ArithmeticFunction.moebius (d i) : ℂ)
        * (ArithmeticFunction.moebius (e i) : ℂ))) * ((rho W A b d e : ℝ) : ℂ)) * Ip c R d e
      = ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b (d, e) p :=
  (MeasureTheory.integral_const_mul _ _).symm

/-- The pointwise value of the `tsum` over all divisor pairs: the Euler product times the kernel. -/
lemma tsum_Fsum {c : ℝ} (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (hc : 1 < c) (ht : 1 ≤ t) {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    (hne : ∀ i, ∃ j, A i j ≠ 0) (hW0 : 0 < W) (p : Fin m → ℝ × ℝ) :
    (∑' de : (Fin m → ℕ) × (Fin m → ℕ), Fsum (t := t) c R W A b de p)
      = (∏' q : ℕ, eulerFactor m (vSys W A b) (fun i => sline c ((p i).1))
            (fun i => sline c ((p i).2)) q)
          * Ker (m := m) R (fun i => sline c ((p i).1)) (fun i => sline c ((p i).2)) := by
  set z : Fin m → ℂ := fun i => sline c ((p i).1) with hz
  set z' : Fin m → ℂ := fun i => sline c ((p i).2) with hz'
  have hzre : ∀ i, 1 ≤ (z i).re := by
    intro i; rw [hz]; simp [sline_re]; linarith
  have hz're : ∀ i, 1 ≤ (z' i).re := by
    intro i; rw [hz']; simp [sline_re]; linarith
  have hsum := hasSum_eulerProduct_vSys (m := m) (t := t) W A b ht hA hne hW0 z z' hzre hz're
  have hfun : (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
        (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)
            * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))))
          * localWeight m (vSys W A b) de.1 de.2)
      = (fun de : (Fin m → ℕ) × (Fin m → ℕ) => Dsm (m := m) (t := t) W A b de.1 de.2 z z') :=
    funext (fun de => Dsm_eq_localWeight W A b de z z')
  rw [hfun] at hsum
  have hF : (fun de : (Fin m → ℕ) × (Fin m → ℕ) => Fsum (t := t) c R W A b de p)
      = (fun de : (Fin m → ℕ) × (Fin m → ℕ) => Dsm (m := m) (t := t) W A b de.1 de.2 z z'
          * Ker (m := m) R z z') :=
    funext (fun de => integrand_eq (t := t) R W A b de.1 de.2 p)
  rw [hF, tsum_mul_right, hsum.tsum_eq, hz, hz']


/-! ## Integrability and summability of the pair integrands -/

/-- `Pker c x` is integrable for `x ≥ 0` (`x = 0` included, where the kernel vanishes). -/
lemma integrable_Pker' {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => Pker c x t) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [show (fun t : ℝ => Pker c 0 t) = fun _ => 0 from funext (fun t => by
      rw [Pker, show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero,
        Complex.zero_cpow (sline_ne_zero hc), zero_div])]
    exact integrable_zero _ _ _
  · exact integrable_Pker hc h

/-- The two-variable factor `Pker c a x.1 · Pker c b x.2` is integrable. -/
lemma integrable_Pker_pair {c : ℝ} (hc : 0 < c) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun x : ℝ × ℝ => Pker c a x.1 * Pker c b x.2) :=
  Integrable.mul_prod (integrable_Pker' hc ha) (integrable_Pker' hc hb)

/-- `Ppr` is integrable on `Fin m → ℝ × ℝ`. -/
lemma integrable_Ppr {c : ℝ} (hc : 0 < c) (R : ℕ) (d e : Fin m → ℕ) :
    Integrable (fun p : Fin m → ℝ × ℝ => Ppr c R d e p) := by
  unfold Ppr
  exact Integrable.fin_nat_prod (fun i => integrable_Pker_pair hc
    (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg (d i)))
    (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg (e i))))

/-- The integrand `Fsum` of a single pair is integrable. -/
lemma integrable_Fsum {c : ℝ} (hc : 0 < c) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (de : (Fin m → ℕ) × (Fin m → ℕ)) :
    Integrable (fun p : Fin m → ℝ × ℝ => Fsum (t := t) c R W A b de p) :=
  (integrable_Ppr (m := m) hc R de.1 de.2).const_mul _

/-- The constant of the modulus bound, `K = R^c (1+c²)/c² π`. -/
noncomputable def Kmod (c : ℝ) (R : ℕ) : ℝ := (R : ℝ) ^ c * (1 + c ^ 2) / c ^ 2 * Real.pi

lemma Kmod_nonneg {c : ℝ} (hc : 0 < c) (R : ℕ) : 0 ≤ Kmod c R := by
  rw [Kmod]; positivity

/-- Modulus bound for the one-dimensional Perron integral along `Re = c`. -/
lemma integral_norm_Pker_le {c : ℝ} (hc : 0 < c) (R d : ℕ) :
    ∫ s : ℝ, ‖Pker c ((R : ℝ) / (d : ℝ)) s‖ ≤ Kmod c R * max (d : ℝ) 1 ^ (-c) := by
  rcases eq_or_lt_of_le (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg d) :
      (0 : ℝ) ≤ (R : ℝ) / (d : ℝ)) with h0 | hpos
  · have hz : ∀ s : ℝ, ‖Pker c ((R : ℝ) / (d : ℝ)) s‖ = 0 := by
      intro s
      rw [← h0, norm_eq_zero, Pker, show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero,
        Complex.zero_cpow (sline_ne_zero hc), zero_div]
    rw [funext hz, integral_zero]
    exact mul_nonneg (Kmod_nonneg hc R)
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_right (d : ℝ) 1)) _)
  · have hxd : (0 : ℝ) < (d : ℝ) := by
      by_contra h
      rw [not_lt] at h
      have := div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg R) h
      linarith
    have hd0 : d ≠ 0 := by
      intro h; rw [h] at hxd; simp at hxd
    have hd1n : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1n
    have hb : ∀ s : ℝ, ‖Pker c ((R : ℝ) / (d : ℝ)) s‖
        ≤ (((R : ℝ) / (d : ℝ)) ^ c * (1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹ := by
      intro s
      have h1 : ‖(((R : ℝ) / (d : ℝ) : ℝ) : ℂ) ^ (sline c s)‖ = ((R : ℝ) / (d : ℝ)) ^ c := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]; simp [sline]
      have h2 : ‖(sline c s) ^ 2‖ = (sline c s).re ^ 2 + (sline c s).im ^ 2 := by
        rw [Complex.norm_pow, Complex.sq_norm, Complex.normSq_apply]; ring
      have h4 : (0 : ℝ) < c ^ 2 + s ^ 2 := by positivity
      have hge : (1 : ℝ) ≤ ((1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹ * (c ^ 2 + s ^ 2) := by
        have h3 : ((1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹ * (c ^ 2 + s ^ 2)
            = (1 + c ^ 2) * (c ^ 2 + s ^ 2) / (c ^ 2 * (1 + s ^ 2)) := by field_simp
        rw [h3, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg c, sq_nonneg s]
      have hxc : (0 : ℝ) < ((R : ℝ) / (d : ℝ)) ^ c := Real.rpow_pos_of_pos hpos c
      rw [Pker, norm_div, h1, h2, sline_re, sline_im]
      rw [div_le_iff₀ h4]
      calc ((R : ℝ) / (d : ℝ)) ^ c
          = ((R : ℝ) / (d : ℝ)) ^ c * 1 := by ring
        _ ≤ ((R : ℝ) / (d : ℝ)) ^ c
              * (((1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹ * (c ^ 2 + s ^ 2)) :=
            mul_le_mul_of_nonneg_left hge hxc.le
        _ = (((R : ℝ) / (d : ℝ)) ^ c * (1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹ * (c ^ 2 + s ^ 2) := by
            ring
    have hint : Integrable (fun s : ℝ =>
        (((R : ℝ) / (d : ℝ)) ^ c * (1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun s => norm_nonneg _)) hint
      (Filter.Eventually.of_forall hb)
    have hval : ∫ s : ℝ, ((((R : ℝ) / (d : ℝ)) ^ c * (1 + c ^ 2) / c ^ 2) * (1 + s ^ 2)⁻¹)
        = ((R : ℝ) / (d : ℝ)) ^ c * (1 + c ^ 2) / c ^ 2 * Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    rw [hval] at hmono
    refine le_trans hmono ?_
    rw [Kmod, max_eq_left hd1]
    rw [Real.div_rpow (Nat.cast_nonneg R) (le_of_lt hxd) c]
    have hdp : (0 : ℝ) < (d : ℝ) ^ c := Real.rpow_pos_of_pos hxd c
    have hdneg : ((d : ℝ)) ^ (-c) = ((d : ℝ) ^ c)⁻¹ := by
      rw [Real.rpow_neg (Nat.cast_nonneg d)]
    rw [hdneg]
    field_simp
    linarith [le_refl ((R : ℝ) ^ c)]


/-- `ρ` is non-negative (for arbitrary `d, e`). -/
lemma rho_nonneg_gen (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ) :
    0 ≤ rho W A b d e := by
  rw [rho]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)

/-- `ρ ≤ 1` for arbitrary `d, e` (the sharp version `rho_le_one` assumes positive entries). -/
lemma rho_le_one_gen (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (d e : Fin m → ℕ) :
    rho W A b d e ≤ 1 := by
  have hcard : ((Sfin W A b d e).card : ℝ) ≤ ((Ddd d e : ℝ)) ^ t := by
    have h1 : (Sfin W A b d e).card ≤ (Ddd d e) ^ t := by
      calc (Sfin W A b d e).card ≤ Fintype.card (Fin t → Fin (Ddd d e)) := by
            rw [← Finset.card_univ]
            exact Finset.card_le_card (Finset.subset_univ _)
        _ = (Ddd d e) ^ t := by simp [Fintype.card_fun]
    exact_mod_cast h1
  rw [rho]
  by_cases hp : ((Ddd d e : ℝ)) ^ t = 0
  · rw [hp, inv_zero, zero_mul]
    norm_num
  · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hp))]
    simpa using hcard

/-- `‖μ n‖ ≤ 1` for every `n`. -/
lemma norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  have := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast this

/-- The constant `‖∏ μ μ · ρ‖` is at most one. -/
lemma norm_Fconst_le_one (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (de : (Fin m → ℕ) × (Fin m → ℕ)) :
    ‖(∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
        * (ArithmeticFunction.moebius (de.2 i) : ℂ))) * ((rho W A b de.1 de.2 : ℝ) : ℂ)‖ ≤ 1 := by
  have h1 : ‖∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
      * (ArithmeticFunction.moebius (de.2 i) : ℂ))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [norm_mul]
    calc ‖((ArithmeticFunction.moebius (de.1 i) : ℤ) : ℂ)‖
          * ‖((ArithmeticFunction.moebius (de.2 i) : ℤ) : ℂ)‖
        ≤ 1 * 1 := mul_le_mul (norm_moebius_le_one _) (norm_moebius_le_one _)
            (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have h2 : ‖((rho W A b de.1 de.2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg_gen W A b de.1 de.2)]
    exact rho_le_one_gen W A b de.1 de.2
  calc ‖(∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
        * (ArithmeticFunction.moebius (de.2 i) : ℂ))) * ((rho W A b de.1 de.2 : ℝ) : ℂ)‖
      = ‖∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
          * (ArithmeticFunction.moebius (de.2 i) : ℂ))‖
        * ‖((rho W A b de.1 de.2 : ℝ) : ℂ)‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-- The `L¹`-norm of a single pair integrand is bounded by the product of the one-dimensional
bounds. -/
lemma integral_norm_Fsum_le {c : ℝ} (hc : 0 < c) (R W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) (de : (Fin m → ℕ) × (Fin m → ℕ)) :
    ∫ p : Fin m → ℝ × ℝ, ‖Fsum (t := t) c R W A b de p‖
      ≤ Kmod c R ^ (2 * m)
        * ((∏ i, max (de.1 i : ℝ) 1 ^ (-c)) * (∏ i, max (de.2 i : ℝ) 1 ^ (-c))) := by
  have hstep1 : ∀ p : Fin m → ℝ × ℝ, ‖Fsum (t := t) c R W A b de p‖ ≤ ‖Ppr c R de.1 de.2 p‖ := by
    intro p
    rw [Fsum, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_Fconst_le_one W A b de)
  calc ∫ p : Fin m → ℝ × ℝ, ‖Fsum (t := t) c R W A b de p‖
      ≤ ∫ p : Fin m → ℝ × ℝ, ‖Ppr c R de.1 de.2 p‖ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun p => norm_nonneg _))
          (integrable_Ppr hc R de.1 de.2).norm
          (Filter.Eventually.of_forall hstep1)
    _ = ∏ i, (∫ s : ℝ, ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) s‖)
          * (∫ s : ℝ, ‖Pker c ((R : ℝ) / (de.2 i : ℝ)) s‖) := by
        unfold Ppr
        simp only [norm_prod]
        rw [MeasureTheory.integral_fin_nat_prod_volume_eq_prod
          (fun i (x : ℝ × ℝ) => ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) x.1
            * Pker c ((R : ℝ) / (de.2 i : ℝ)) x.2‖)]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [show (∫ x : ℝ × ℝ, ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) x.1
              * Pker c ((R : ℝ) / (de.2 i : ℝ)) x.2‖)
            = ∫ x : ℝ × ℝ, ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) x.1‖
              * ‖Pker c ((R : ℝ) / (de.2 i : ℝ)) x.2‖
          from MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun x => norm_mul _ _))]
        exact MeasureTheory.integral_prod_mul
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (f := fun s : ℝ => ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) s‖)
          (g := fun s : ℝ => ‖Pker c ((R : ℝ) / (de.2 i : ℝ)) s‖)
    _ ≤ ∏ i, (Kmod c R * max (de.1 i : ℝ) 1 ^ (-c))
          * (Kmod c R * max (de.2 i : ℝ) 1 ^ (-c)) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · exact mul_nonneg (integral_nonneg (fun s => norm_nonneg _))
            (integral_nonneg (fun s => norm_nonneg _))
        · have h1 : (∫ s : ℝ, ‖Pker c ((R : ℝ) / (de.1 i : ℝ)) s‖)
              ≤ Kmod c R * max (de.1 i : ℝ) 1 ^ (-c) := integral_norm_Pker_le hc R (de.1 i)
          have h2 : (∫ s : ℝ, ‖Pker c ((R : ℝ) / (de.2 i : ℝ)) s‖)
              ≤ Kmod c R * max (de.2 i : ℝ) 1 ^ (-c) := integral_norm_Pker_le hc R (de.2 i)
          have h3 : (0 : ℝ) ≤ ∫ s : ℝ, ‖Pker c ((R : ℝ) / (de.2 i : ℝ)) s‖ :=
            integral_nonneg (fun s => norm_nonneg _)
          have h4 : (0 : ℝ) ≤ Kmod c R * max (de.1 i : ℝ) 1 ^ (-c) :=
            mul_nonneg (Kmod_nonneg hc R) (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ 1)) _)
          exact mul_le_mul h1 h2 h3 h4
    _ = Kmod c R ^ (2 * m)
          * ((∏ i, max (de.1 i : ℝ) 1 ^ (-c)) * (∏ i, max (de.2 i : ℝ) 1 ^ (-c))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- **Summability of the `L¹`-norms of the pair integrands.** -/
lemma summable_integral_norm_Fsum {c : ℝ} (hcm : (m : ℝ) < c) (R W : ℕ)
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) :
    Summable (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
      ∫ p : Fin m → ℝ × ℝ, ‖Fsum (t := t) c R W A b de p‖) := by
  have hc : (0 : ℝ) < c := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hf := Commons.Analysis.Series.summable_pi_prod_max_rpow (m := m) hcm
  have hfn : ∀ d : Fin m → ℕ, 0 ≤ ∏ i, max (d i : ℝ) 1 ^ (-c) :=
    fun d => Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ 1)) _)
  have hmaj := Commons.Analysis.Series.summable_prod_mul_nonneg hf hf hfn hfn
  refine Summable.of_nonneg_of_le (fun de => integral_nonneg (fun p => norm_nonneg _))
    (fun de => integral_norm_Fsum_le hc R W A b de) (Summable.mul_left _ hmaj)


/-! ## The main Perron + Fubini + Euler-product identity -/

/-- `Ip` vanishes when one of the two tuples has an entry outside `[1,R]`. -/
lemma Ip_eq_zero_of_not_mem {c : ℝ} (hc : 0 < c) {R : ℕ} {d e : Fin m → ℕ}
    (h : d ∉ P (m := m) R ∨ e ∉ P (m := m) R) : Ip c R d e = 0 := by
  have key : ∀ f : Fin m → ℕ, f ∉ P (m := m) R →
      (∏ i, ((max (Real.log ((R : ℝ) / (f i : ℝ))) 0 : ℝ) : ℂ)) = 0 := by
    intro f hf
    simp only [P, Fintype.mem_piFinset] at hf
    push_neg at hf
    obtain ⟨i, hi⟩ := hf
    rw [Finset.mem_Icc, not_and_or] at hi
    have hmax : max (Real.log ((R : ℝ) / (f i : ℝ))) 0 = 0 := by
      rcases hi with hi | hi
      · have hd0 : f i = 0 := by omega
        rw [hd0, Nat.cast_zero, div_zero, Real.log_zero]
        exact max_self 0
      · have hlt : (R : ℝ) / (f i : ℝ) < 1 := by
          rw [div_lt_one (by exact_mod_cast (by omega : 0 < f i))]
          exact_mod_cast (not_le.mp hi)
        exact max_eq_right
          (Real.log_nonpos (div_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg _)) hlt.le)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [hmax, Complex.ofReal_zero]
  rw [Ip_closed hc R d e, Finset.prod_mul_distrib]
  rcases h with h | h
  · simp only [key d h, zero_mul, mul_zero]
  · simp only [key e h, mul_zero]

/-- Bookkeeping of the complex constants in the contour identity. -/
lemma const_book (Cp I : ℂ) (m : ℕ) (hCp : Cp ≠ 0) (hI : I ≠ 0) (Y : ℂ) :
    ((Cp * I)⁻¹) ^ (2 * m) * (Y * (I ^ m * I ^ m)) = (Cp ^ (2 * m))⁻¹ * Y := by
  have hI2 : I ^ m * I ^ m = I ^ (2 * m) := by rw [← pow_add]; ring_nf
  rw [hI2]
  have hthis : ((Cp * I)⁻¹) ^ (2 * m) = (Cp ^ (2 * m))⁻¹ * ((I ^ (2 * m))⁻¹) := by
    rw [mul_inv, mul_pow, inv_pow, inv_pow]
  rw [hthis]
  have hIp : I ^ (2 * m) ≠ 0 := pow_ne_zero _ hI
  calc (Cp ^ (2 * m))⁻¹ * (I ^ (2 * m))⁻¹ * (Y * I ^ (2 * m))
      = (Cp ^ (2 * m))⁻¹ * (((I ^ (2 * m))⁻¹ * I ^ (2 * m)) * Y) := by ring
    _ = (Cp ^ (2 * m))⁻¹ * (1 * Y) := by rw [inv_mul_cancel₀ hIp]
    _ = (Cp ^ (2 * m))⁻¹ * Y := by ring



/-! ## The final assembly: Green–Tao (10.2) = (10.5) = (10.7)

The two `noncomputable def`s `Ftsum`/`Eker`/`ContourInt` below are *abbreviations only*: they
exist so that the final `calc` works with small terms (writing the Euler product and the `2m`-fold
contour integral inline makes `rw`/`trans` unification blow the heartbeat budget). -/

/-- The `de`-sum of the pair integrands at a fixed point `p` of the contour. -/
noncomputable def Ftsum (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (p : Fin m → ℝ × ℝ) : ℂ :=
  ∑' de : (Fin m → ℕ) × (Fin m → ℕ), Fsum (t := t) c R W A b de p

/-- The pointwise limit of the pair integrands: the Euler product times the kernel. -/
noncomputable def Eker (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (p : Fin m → ℝ × ℝ) : ℂ :=
  (∏' q : ℕ, eulerFactor m (vSys W A b) (fun i => sline c ((p i).1))
      (fun i => sline c ((p i).2)) q)
    * Ker (m := m) R (fun i => sline c ((p i).1)) (fun i => sline c ((p i).2))

/-- The `2m`-fold contour integral of Green–Tao §10, in its `(t,t')`-iterated form. -/
noncomputable def ContourInt (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) : ℂ :=
  ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
    Eker (t := t) c R W A b (fun i => (t_ i, t_' i)) * Complex.I ^ m * Complex.I ^ m

/-- The pointwise Euler-product identity, as an equality of functions. -/
lemma Ftsum_eq_Eker {c : ℝ} (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (hc : 1 < c) (ht : 1 ≤ t) {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    (hne : ∀ i, ∃ j, A i j ≠ 0) (hW0 : 0 < W) :
    Ftsum (t := t) c R W A b = Eker (t := t) c R W A b :=
  funext (fun p => tsum_Fsum (c := c) R W A b hc ht hA hne hW0 p)

/-- Pulling the two `Complex.I ^ m` factors out of the iterated contour integral. -/
lemma ContourInt_eq (c : ℝ) (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) :
    ContourInt (t := t) c R W A b
      = (∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
            Eker (t := t) c R W A b (fun i => (t_ i, t_' i)))
          * (Complex.I ^ m * Complex.I ^ m) := by
  have hinner : ∀ t_ : Fin m → ℝ,
      (∫ t_' : Fin m → ℝ, Eker (t := t) c R W A b (fun i => (t_ i, t_' i))
          * Complex.I ^ m * Complex.I ^ m)
        = (∫ t_' : Fin m → ℝ, Eker (t := t) c R W A b (fun i => (t_ i, t_' i)))
            * (Complex.I ^ m * Complex.I ^ m) := by
    intro t_
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
    ring
  rw [ContourInt]
  simp only [hinner]
  rw [MeasureTheory.integral_mul_const]

/-- **The Perron + Fubini + Euler-product identity** (Green–Tao (10.2) = (10.5) = (10.7)).  The
main term of the box average is the `2m`-fold contour integral over `Re = c` of the Euler product
`∏_p E_p` times the kernel `∏_j R^{z_j+z'_j}/(z_j²z'_j²)`. -/
theorem mainSum_eq_contour {c : ℝ} (hm : 1 ≤ m) (hcm : (m : ℝ) < c) {Amax : ℕ}
    (R W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hW0 : 0 < W) :
    (mainSum (m := m) (t := t) R W A b : ℂ) =
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) * ContourInt (t := t) c R W A b := by
  have hc : (0 : ℝ) < c := lt_of_le_of_lt (Nat.cast_nonneg m) hcm
  have hc1 : (1 : ℝ) < c :=
    lt_of_le_of_lt (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) hcm
  have hCp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hCp2m : ((2 * (Real.pi : ℂ)) ^ (2 * m))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hCp)
  have hFsum_int : ∀ de : (Fin m → ℕ) × (Fin m → ℕ),
      Integrable (fun p : Fin m → ℝ × ℝ => Fsum (t := t) c R W A b de p) :=
    fun de => integrable_Fsum hc R W A b de
  have hsumm : Summable (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
      ∫ p : Fin m → ℝ × ℝ, ‖Fsum (t := t) c R W A b de p‖) :=
    summable_integral_norm_Fsum hcm R W A b
  have hIntT : Integrable (fun p : Fin m → ℝ × ℝ => Ftsum (t := t) c R W A b p) :=
    Commons.MeasureTheory.integrable_tsum_of_summable_integral_norm hFsum_int hsumm
  have hfun : Ftsum (t := t) c R W A b = Eker (t := t) c R W A b :=
    Ftsum_eq_Eker R W A b hc1 ht hA hne hW0
  have hIntE : Integrable (Eker (t := t) c R W A b) := by
    rwa [hfun] at hIntT
  -- Step 1: the double sum over `P` as a sum over `P.product P` of pair integrands
  have h1a : (∑ d ∈ P (m := m) R, ∑ e ∈ P (m := m) R,
      ((∏ i, ((ArithmeticFunction.moebius (d i) : ℂ)
          * (ArithmeticFunction.moebius (e i) : ℂ))) * ((rho W A b d e : ℝ) : ℂ))
        * Ip c R d e)
      = ∑ de ∈ (P (m := m) R).product (P (m := m) R),
          ((∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
              * (ArithmeticFunction.moebius (de.2 i) : ℂ)))
            * ((rho W A b de.1 de.2 : ℝ) : ℂ)) * Ip c R de.1 de.2 :=
    (Finset.sum_product (P (m := m) R) (P (m := m) R)
      (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
        ((∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)))
          * ((rho W A b de.1 de.2 : ℝ) : ℂ)) * Ip c R de.1 de.2)).symm
  have h1b : (∑ de ∈ (P (m := m) R).product (P (m := m) R),
          ((∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
              * (ArithmeticFunction.moebius (de.2 i) : ℂ)))
            * ((rho W A b de.1 de.2 : ℝ) : ℂ)) * Ip c R de.1 de.2)
      = ∑ de ∈ (P (m := m) R).product (P (m := m) R),
          ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p :=
    Finset.sum_congr rfl (fun de _ => Ip_term_eq_integral c R W A b de.1 de.2)
  have h1 := h1a.trans h1b
  -- Step 2: the sum over `P ×ˢ P` extends to the full `tsum` (the terms off `P` have vanishing
  -- integral)
  have h2 : (∑ de ∈ (P (m := m) R).product (P (m := m) R),
          ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p)
      = ∑' de : (Fin m → ℕ) × (Fin m → ℕ),
          ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p := by
    refine (tsum_eq_sum (f := fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
        ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p)
      (s := (P (m := m) R).product (P (m := m) R)) ?_).symm
    intro de hde
    have hd : de.1 ∉ P (m := m) R ∨ de.2 ∉ P (m := m) R := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      exact hde (Finset.mem_product.mpr hcon)
    rw [show (∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p)
        = ((∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)))
              * ((rho W A b de.1 de.2 : ℝ) : ℂ)) * Ip c R de.1 de.2
        from (Ip_term_eq_integral c R W A b de.1 de.2).symm]
    rw [Ip_eq_zero_of_not_mem hc hd, mul_zero]
  -- Step 3: Fubini (the series of integrals is the integral of the series)
  have h3 : (∑' de : (Fin m → ℕ) × (Fin m → ℕ),
          ∫ p : Fin m → ℝ × ℝ, Fsum (t := t) c R W A b de p)
      = ∫ p : Fin m → ℝ × ℝ, Ftsum (t := t) c R W A b p :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm hFsum_int hsumm).tsum_eq
  have h4 : (∫ p : Fin m → ℝ × ℝ, Ftsum (t := t) c R W A b p)
      = ∫ p : Fin m → ℝ × ℝ, Eker (t := t) c R W A b p := by rw [hfun]
  have h5 : (∫ p : Fin m → ℝ × ℝ, Eker (t := t) c R W A b p)
      = ∫ t_ : Fin m → ℝ, ∫ t_' : Fin m → ℝ,
          Eker (t := t) c R W A b (fun i => (t_ i, t_' i)) :=
    integral_curry_pi _ hIntE
  have hCInt : ContourInt (t := t) c R W A b
      = (∫ p : Fin m → ℝ × ℝ, Eker (t := t) c R W A b p)
        * (Complex.I ^ m * Complex.I ^ m) := by
    rw [ContourInt_eq, ← h5]
  rw [mainSum_eq_Ip_sum hc R W A b]
  rw [hCInt]
  rw [const_book (2 * (Real.pi : ℂ)) Complex.I m hCp Complex.I_ne_zero]
  refine mul_left_cancel₀ hCp2m ?_
  rw [h1, h2, h3, h4]

end BoxAvg
end GYMaj
