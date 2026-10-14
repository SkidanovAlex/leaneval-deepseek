import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The odd Gegenbauer polynomials vanish at the origin -/

/-- `gC (2m+1) 0 = 0`: the odd-indexed Gegenbauer polynomials vanish at the origin.  This is
what makes the boundary term of the integration by parts at `x = 0` disappear. -/
lemma gC_odd_zero (m : ℕ) : gC (2 * m + 1) 0 = 0 := by
  induction m with
  | zero => rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]; norm_num
  | succ m ih =>
    have h := gC_rec (2 * m + 1) 0
    have h1 : (2 * m + 1) + 2 = 2 * (m + 1) + 1 := by omega
    rw [h1] at h
    have h3 : (((2 * m + 1 : ℕ) : ℝ) + 3) * gC (2 * m + 1) 0 = 0 := by rw [ih]; ring
    simp only [mul_zero, zero_mul] at h
    rw [h3, sub_zero] at h
    have hne : (((2 * m + 1 : ℕ) : ℝ) + 2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hne

/-! ## The self-adjoint form of the Gegenbauer equation -/

/-- The derivative of the "self-adjoint weight times the Gegenbauer derivative",

  `d/dx [(1-x²)² · q'(x)] = -n(n+3) · (1-x²) q(x)`,   `q = gC n`

(the self-adjoint form of `gC_ode`). -/
lemma hasDerivAt_gC_weight (n : ℕ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => (1 - u ^ 2) ^ 2 * deriv (gC n) u)
      (-(((n : ℝ) * ((n : ℝ) + 3)) * ((1 - x ^ 2) * gC n x))) x := by
  have hw : HasDerivAt (fun u : ℝ => (1 - u ^ 2) ^ 2) (-(4 * x * (1 - x ^ 2))) x := by
    have h1 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    have h2 : HasDerivAt (fun u : ℝ => (1 - u ^ 2) ^ 2) (2 * (1 - x ^ 2) * (-(2 * x))) x := by
      convert h1.pow 2 using 1
      ring
    convert h2 using 1
    ring
  have hd : HasDerivAt (fun u : ℝ => deriv (gC n) u) (deriv (deriv (gC n)) x) x := by
    have h2 : ContDiff ℝ 2 (deriv (gC n)) := (contDiff_gC n).deriv'
    exact ((h2.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hm := hw.mul hd
  have hm' : HasDerivAt (fun u : ℝ => (1 - u ^ 2) ^ 2 * deriv (gC n) u)
      (-(4 * x * (1 - x ^ 2)) * deriv (gC n) x + (1 - x ^ 2) ^ 2 * deriv (deriv (gC n)) x) x :=
    hm
  convert hm' using 1
  have hode := (gC_ode n).2 x
  linear_combination (-(1 - x ^ 2)) * hode

/-! ## The integration by parts identity -/

/-- Integration by parts against `gC (2p+1)`, using the self-adjoint form of the Gegenbauer
equation for `gC (2q+1)` and the vanishing of `gC (2p+1)` at `0`:

  `(2q+1)(2q+4) ∫_0^1 (1-u²) q_p q_q = ∫_0^1 (1-u²)² q_p' q_q'`. -/
lemma ibp_gC_odd (p q : ℕ) :
    (((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 3)) *
        (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC (2 * p + 1) u * gC (2 * q + 1) u)
      = ∫ u in (0 : ℝ)..1,
          deriv (gC (2 * p + 1)) u * ((1 - u ^ 2) ^ 2 * deriv (gC (2 * q + 1)) u) := by
  have hc : Continuous (fun u : ℝ => (1 - u ^ 2) * gC (2 * q + 1) u) :=
    (continuous_const.sub (continuous_id.pow 2)).mul (contDiff_gC (2 * q + 1)).continuous
  have hcont : Continuous (fun u : ℝ =>
      -((((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 3)) *
        ((1 - u ^ 2) * gC (2 * q + 1) u))) :=
    (continuous_const.mul hc).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => gC (2 * p + 1) u) (u' := fun u : ℝ => deriv (gC (2 * p + 1)) u)
    (v := fun u : ℝ => (1 - u ^ 2) ^ 2 * deriv (gC (2 * q + 1)) u)
    (v' := fun u : ℝ =>
      -((((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 3)) *
        ((1 - u ^ 2) * gC (2 * q + 1) u)))
    (a := 0) (b := 1)
    (fun x _ => ((contDiff_gC (2 * p + 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt)
    (fun x _ => hasDerivAt_gC_weight (2 * q + 1) x)
    (((contDiff_gC (2 * p + 1)).continuous_deriv (by norm_num)).intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)
  have h1 : (1 - ((1 : ℝ)) ^ 2) ^ 2 * deriv (gC (2 * q + 1)) 1 = 0 := by norm_num
  have h0 : (1 - ((0 : ℝ)) ^ 2) ^ 2 * deriv (gC (2 * q + 1)) 0
      = deriv (gC (2 * q + 1)) 0 := by norm_num
  rw [h1, h0, gC_odd_zero p] at h
  simp only [mul_zero] at h
  have hL : (∫ x in (0 : ℝ)..1, gC (2 * p + 1) x *
        (-((((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 3)) *
          ((1 - x ^ 2) * gC (2 * q + 1) x))))
      = -((((2 * q + 1 : ℕ) : ℝ) * (((2 * q + 1 : ℕ) : ℝ) + 3))) *
        ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC (2 * p + 1) u * gC (2 * q + 1) u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hL] at h
  linarith [h]

/-! ## The eigenvalues are distinct -/

/-- `k ↦ (2k+1)(2k+4)` is strictly increasing, so the eigenvalues
`(2m+1)(2m+4) = 4 + lam m` of `eFam` are distinct for distinct indices. -/
lemma odd_shift_ne {m n : ℕ} (hmn : m ≠ n) :
    ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)
      ≠ ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 3) := by
  have hstep : ∀ k : ℕ, ((2 * k + 1 : ℕ) : ℝ) * (((2 * k + 1 : ℕ) : ℝ) + 3)
      < ((2 * (k + 1) + 1 : ℕ) : ℝ) * (((2 * (k + 1) + 1 : ℕ) : ℝ) + 3) := by
    intro k
    have hd : ((2 * (k + 1) + 1 : ℕ) : ℝ) * (((2 * (k + 1) + 1 : ℕ) : ℝ) + 3)
        - ((2 * k + 1 : ℕ) : ℝ) * (((2 * k + 1 : ℕ) : ℝ) + 3) = 8 * (k : ℝ) + 14 := by
      push_cast
      ring
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact fun h => hmn ((strictMono_nat_of_lt_succ hstep).injective h)

/-! ## The target -/

theorem eFam_orthogonal (m n : ℕ) (hmn : m ≠ n) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
  -- substitute `u = sin θ`
  have hsub : (∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ * eFam n θ * Real.cos θ)
      = ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC (2 * m + 1) u * gC (2 * n + 1) u := by
    set G : ℝ → ℝ := fun u => (1 - u ^ 2) * gC (2 * m + 1) u * gC (2 * n + 1) u with hG
    have hGcont : Continuous G := by
      rw [hG]
      exact ((continuous_const.sub (continuous_id.pow 2)).mul
        (contDiff_gC (2 * m + 1)).continuous).mul (contDiff_gC (2 * n + 1)).continuous
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := G)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hGcont
    rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
    have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ * eFam n θ * Real.cos θ)
        = ∫ θ in (0 : ℝ)..(Real.pi / 2), (G ∘ Real.sin) θ * Real.cos θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [Function.comp_apply, hG, eFam]
      rw [← Real.cos_sq']
      ring
    rw [hcongr, hsub, hG]
  rw [hsub]
  -- the two integration-by-parts identities
  set I : ℝ := ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC (2 * m + 1) u * gC (2 * n + 1) u with hIdef
  set J : ℝ := ∫ u in (0 : ℝ)..1,
    deriv (gC (2 * m + 1)) u * ((1 - u ^ 2) ^ 2 * deriv (gC (2 * n + 1)) u) with hJdef
  have hIs : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC (2 * n + 1) u * gC (2 * m + 1) u) = I := by
    rw [hIdef]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hJs : (∫ u in (0 : ℝ)..1,
        deriv (gC (2 * n + 1)) u * ((1 - u ^ 2) ^ 2 * deriv (gC (2 * m + 1)) u)) = J := by
    rw [hJdef]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hl : (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 3)) * I = J := by
    rw [hIdef, hJdef]
    exact ibp_gC_odd m n
  have hk : (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * I = J := by
    rw [← hIs, ← hJs]
    exact ibp_gC_odd n m
  have hA := odd_shift_ne hmn
  have hkey : ((((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3))
        - (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) + 3))) * I = 0 := by
    rw [sub_mul, hk, hl, sub_self]
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h (sub_ne_zero.mpr hA)
  · exact h

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.psiAngDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open Filter

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer
  (eFam gC gC_rec gC_ode contDiff_gC deriv_cos_comp_sin deriv2_cos_comp_sin
    deriv_tan_cos_comp_sin)

/-- `N m = (2m+2)(2m+3)`: the constant of the statement. -/
def Npsi (m : ℕ) : ℝ := (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)

/-- `u_m(x) = (1-x^2)·C^{(3/2)}_{2m+1}(x)`. -/
def ug (m : ℕ) : ℝ → ℝ := fun x => (1 - x ^ 2) * gC (2 * m + 1) x

/-- The energy `(u')^2 + (N/(1-x^2))u^2`, written as a sum of two functions. -/
def ene (m : ℕ) : ℝ → ℝ :=
  (fun x => (deriv (ug m) x) ^ 2) +
    (fun x => Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2))

/-! ## Elementary facts about `Npsi` -/

lemma Npsi_pos (m : ℕ) : 0 < Npsi m := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  simp only [Npsi]
  positivity

lemma Npsi_eq (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) + 1) * (((2 * m + 1 : ℕ) : ℝ) + 2) := by
  simp only [Npsi]; push_cast; ring

lemma Npsi_eq_two (m : ℕ) :
    Npsi m = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 := by
  rw [Npsi_eq]; ring

lemma Npsi_ge_one (m : ℕ) : 1 ≤ Npsi m := by
  have h0 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Npsi_eq m]
  nlinarith

/-- The value of `C^{(3/2)}_k` at `1`. -/
lemma gC_one (k : ℕ) : gC k 1 = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more n ih1 ih2 =>
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : ((n : ℝ) + 2) * gC (n + 2) 1
        = ((n : ℝ) + 2) * (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    push_cast
    exact hh

/-- A triangle-type inequality used below. -/
lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor
  · have h1 := neg_abs_le a; have h2 := le_abs_self b; linarith
  · have h1 := le_abs_self a; have h2 := neg_abs_le b; linarith

/-! ## Differentiability of `gC` and of `ug` -/

lemma differentiable_gC (k : ℕ) : Differentiable ℝ (gC k) :=
  (contDiff_gC k).differentiable (by norm_num)

lemma differentiable_deriv_gC (k : ℕ) : Differentiable ℝ (deriv (gC k)) :=
  ((contDiff_gC k).deriv' (n := 2)).differentiable (by norm_num)

lemma hasDerivAt_one_sub_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2) (0 - 2 * x) x := by
  have h0 := (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
  convert h0 using 1
  simp

/-! ## The first and second derivatives of `ug` -/

lemma deriv_ug (m : ℕ) (x : ℝ) :
    deriv (ug m) x
      = -2 * x * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
  have h1 := hasDerivAt_one_sub_sq x
  have h2 : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) x) x :=
    (differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y)
      ((0 - 2 * x) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x) x :=
    h1.mul h2
  have h4 : deriv (ug m) x
      = (0 - 2 * x) * gC (2 * m + 1) x + (1 - x ^ 2) * deriv (gC (2 * m + 1)) x := by
    rw [show ug m = fun y : ℝ => (1 - y ^ 2) * gC (2 * m + 1) y from rfl]
    exact h3.deriv
  rw [h4]; ring

lemma differentiable_deriv_ug (m : ℕ) : Differentiable ℝ (deriv (ug m)) := by
  rw [funext (deriv_ug m)]
  have h1 : Differentiable ℝ (fun y : ℝ => (-2 : ℝ) * y) :=
    (differentiable_const (-2 : ℝ)).mul differentiable_id
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  exact (h1.mul (differentiable_gC (2 * m + 1))).add
    (h2.mul (differentiable_deriv_gC (2 * m + 1)))

lemma deriv2_ug (m : ℕ) (x : ℝ) :
    deriv (deriv (ug m)) x
      = -2 * gC (2 * m + 1) x - 4 * x * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x := by
  have hfun : deriv (ug m)
      = fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y :=
    funext (deriv_ug m)
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * gC (2 * m + 1) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x) x := by
    have hlin : HasDerivAt (fun y : ℝ => (-2 : ℝ) * y) (-2) x := hasDerivAt_const_mul (-2)
    exact hlin.mul ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((0 - 2 * x) * deriv (gC (2 * m + 1)) x
        + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x) x :=
    (hasDerivAt_one_sub_sq x).mul
      ((differentiable_deriv_gC (2 * m + 1)).differentiableAt.hasDerivAt)
  have h3 : HasDerivAt
      (fun y : ℝ => -2 * y * gC (2 * m + 1) y + (1 - y ^ 2) * deriv (gC (2 * m + 1)) y)
      ((-2) * gC (2 * m + 1) x + (-2 * x) * deriv (gC (2 * m + 1)) x
        + ((0 - 2 * x) * deriv (gC (2 * m + 1)) x
          + (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x)) x :=
    h1.add h2
  rw [h3.deriv]
  ring


/-! ## The energy -/

lemma differentiable_ene (m : ℕ) : Differentiable ℝ (ene m) := by
  have h1 : Differentiable ℝ (fun x : ℝ => (deriv (ug m) x) ^ 2) :=
    (differentiable_deriv_ug m).pow 2
  have h2 : Differentiable ℝ (fun y : ℝ => (1 : ℝ) - y ^ 2) :=
    (differentiable_const (1 : ℝ)).sub (differentiable_id.pow 2)
  have h3 : Differentiable ℝ (fun x : ℝ => (gC (2 * m + 1) x) ^ 2) :=
    (differentiable_gC (2 * m + 1)).pow 2
  have h4 : Differentiable ℝ
      (fun x : ℝ => Npsi m * (((1 : ℝ) - x ^ 2) * (gC (2 * m + 1) x) ^ 2)) :=
    (differentiable_const (Npsi m)).mul (h2.mul h3)
  exact h1.add h4

lemma continuous_ene (m : ℕ) : Continuous (ene m) := (differentiable_ene m).continuous

lemma ene_eq (m : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    ene m x = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 := by
  show (deriv (ug m) x) ^ 2 + Npsi m * ((1 - x ^ 2) * (gC (2 * m + 1) x) ^ 2)
      = (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
  rw [show ug m x = (1 - x ^ 2) * gC (2 * m + 1) x from rfl]
  field_simp
  try ring

/-- `E'(x) = 2xN·q(x)^2`. -/
lemma deriv_ene (m : ℕ) (x : ℝ) :
    deriv (ene m) x = 2 * x * Npsi m * (gC (2 * m + 1) x) ^ 2 := by
  have hdu : HasDerivAt (deriv (ug m)) (deriv (deriv (ug m)) x) x :=
    (differentiable_deriv_ug m).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (deriv (ug m) y) ^ 2)
      ((2 : ℝ) * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x) x := hdu.pow 2
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2)
      ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x)) x := by
    have hg : HasDerivAt (fun y : ℝ => (gC (2 * m + 1) y) ^ 2)
        ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1) * deriv (gC (2 * m + 1)) x) x :=
      ((differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt).pow 2
    exact (hasDerivAt_one_sub_sq x).mul hg
  have h3 : HasDerivAt
      (fun y : ℝ => Npsi m * (((1 : ℝ) - y ^ 2) * (gC (2 * m + 1) y) ^ 2))
      (Npsi m * ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
        + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
            * deriv (gC (2 * m + 1)) x))) x :=
    h2.const_mul (Npsi m)
  have h4 : HasDerivAt (ene m)
      ((2 : ℝ) * (deriv (ug m) x) ^ (2 - 1) * deriv (deriv (ug m)) x
        + Npsi m * ((0 - 2 * x) * (gC (2 * m + 1) x) ^ 2
          + (1 - x ^ 2) * ((2 : ℝ) * (gC (2 * m + 1) x) ^ (2 - 1)
              * deriv (gC (2 * m + 1)) x))) x :=
    h1.add h3
  rw [h4.deriv]
  rw [deriv2_ug m x]
  have hode := (gC_ode (2 * m + 1)).2 x
  have hkey : (1 - x ^ 2) * deriv (deriv (gC (2 * m + 1))) x
      = 4 * x * deriv (gC (2 * m + 1)) x
        - (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) * gC (2 * m + 1) x := by
    linarith [hode]
  have hN : (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) + 2 = Npsi m :=
    (Npsi_eq_two m).symm
  rw [hkey, ← hN, deriv_ug m x]
  ring

/-- `u'(1) = -N`. -/
lemma deriv_ug_one (m : ℕ) : deriv (ug m) 1 = -Npsi m := by
  rw [deriv_ug m 1]
  have hg := gC_one (2 * m + 1)
  have hN := Npsi_eq m
  rw [hg, hN]
  ring_nf

/-- `E(1) = N^2`. -/
lemma ene_one (m : ℕ) : ene m 1 = Npsi m ^ 2 := by
  show (deriv (ug m) 1) ^ 2 + Npsi m * ((1 - (1 : ℝ) ^ 2) * (gC (2 * m + 1) 1) ^ 2)
      = Npsi m ^ 2
  rw [deriv_ug_one m]
  ring_nf

/-- `E ≤ E(1) = N^2` on `[0,1]`. -/
lemma ene_le (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : ene m x ≤ Npsi m ^ 2 := by
  have hmono : MonotoneOn (ene m) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_ene m).continuousOn
      (differentiable_ene m).differentiableOn ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    rw [deriv_ene m y]
    exact mul_nonneg (mul_nonneg (by linarith) (le_of_lt (Npsi_pos m))) (sq_nonneg _)
  have h1 : ene m x ≤ ene m 1 := hmono hx ⟨by norm_num, le_rfl⟩ hx.2
  rwa [ene_one m] at h1

/-! ## The two bounds on `u` -/

lemma ug_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (ug m x) ^ 2 ≤ Npsi m * (1 - x ^ 2) := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]; exact ene_le m hx
    have h3 : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 ≤ Npsi m ^ 2 := by
      linarith [hE, sq_nonneg (deriv (ug m) x)]
    rw [div_mul_eq_mul_div₀, div_le_iff₀ hc] at h3
    have h4 : Npsi m ^ 2 * (1 - x ^ 2) / Npsi m = Npsi m * (1 - x ^ 2) := by
      rw [sq, mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt (Npsi_pos m))]
    have h5 : (ug m x) ^ 2 ≤ Npsi m ^ 2 * (1 - x ^ 2) / Npsi m :=
      (le_div_iff₀ (Npsi_pos m)).mpr (by linarith [h3])
    rwa [h4] at h5
  · subst heq
    rw [show ug m 1 = 0 from by simp [ug]]
    simp

lemma du_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (deriv (ug m) x) ^ 2 ≤ Npsi m ^ 2 := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hc : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hlt, sq_nonneg x]
    have hE : (deriv (ug m) x) ^ 2 + (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
        ≤ Npsi m ^ 2 := by
      rw [← ene_eq m hne]; exact ene_le m hx
    have h3 : 0 ≤ (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 :=
      mul_nonneg (div_nonneg (le_of_lt (Npsi_pos m)) (le_of_lt hc)) (sq_nonneg _)
    linarith [hE, h3]
  · subst heq
    rw [deriv_ug_one m, neg_sq]

/-! ## Arithmetic helpers -/

lemma arith2 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r ^ 2 + 3 * r / c ≤ 100 * r ^ 2 / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hr : 0 < r := by linarith
  have hL : (r ^ 2 + 3 * r / c) * c ^ 2 = r ^ 2 * c ^ 2 + 3 * r * c := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hA : r ^ 2 * c ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc2le (sq_nonneg r)
    simpa using this
  have hB : 3 * r * c ≤ 99 * r ^ 2 := by
    have hstep : 3 * r * c ≤ 3 * r := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * r)
      simpa using this
    have hstep2 : 3 * r ≤ 99 * r ^ 2 := by
      have h3 : (3 : ℝ) ≤ 99 * r := by linarith
      have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
      calc 3 * r = 3 * r := rfl
        _ ≤ (99 * r) * r := this
        _ = 99 * r ^ 2 := by ring
    linarith
  rw [le_div_iff₀ hc2, hL]
  linarith [hA, hB, sq_nonneg r]

lemma arith3 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r ^ 2 / c + 2 * r / c ^ 2 + (r ^ 2 - 1) * r ≤ 1000 * r ^ 2 * r / c ^ 4 := by
  have hc4 : 0 < c ^ 4 := by positivity
  have hr : 0 < r := by linarith
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hL : (r ^ 2 / c + 2 * r / c ^ 2 + (r ^ 2 - 1) * r) * c ^ 4
      = r ^ 2 * c ^ 3 + 2 * r * c ^ 2 + (r ^ 2 - 1) * r * c ^ 4 := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hc3le : c ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 3
    simpa using this
  have hc4le : c ^ 4 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 4
    simpa using this
  have hrn1 : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hA : r ^ 2 * c ^ 3 ≤ r ^ 2 * r := by
    have h1' : r ^ 2 * c ^ 3 ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hc3le hr2
    have h2' : r ^ 2 * 1 ≤ r ^ 2 * r := by
      have := mul_le_mul_of_nonneg_left h2 hr2
      simpa using this
    linarith
  have hB : 2 * r * c ^ 2 ≤ 2 * (r ^ 2 * r) := by
    have h1' : 2 * r * c ^ 2 ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hc2le (by positivity : (0 : ℝ) ≤ 2 * r)
      simpa using this
    have h2' : 2 * r ≤ 2 * (r ^ 2 * r) := by
      have h3 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
      have h4 : r ≤ r ^ 2 * r := by
        have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
        simpa using this
      exact mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hC : (r ^ 2 - 1) * r * c ^ 4 ≤ r ^ 2 * r := by
    have h1' : (r ^ 2 - 1) * r * c ^ 4 ≤ (r ^ 2 - 1) * r * 1 :=
      mul_le_mul_of_nonneg_left hc4le (mul_nonneg hrn1 (le_of_lt hr))
    have h2' : (r ^ 2 - 1) * r * 1 ≤ r ^ 2 * r := by
      have h3 : r ^ 2 - 1 ≤ r ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_right h3 (le_of_lt hr)
      simpa using this
    linarith
  have hr2r : 0 ≤ r ^ 2 * r := by positivity
  rw [le_div_iff₀ hc4, hL]
  linarith [hA, hB, hC, hr2r]

lemma arith4 {c r : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) (h2 : 1 ≤ r) :
    r + r ^ 2 / c + 2 * r / c ^ 2 ≤ 1000 * r ^ 2 / c ^ 3 := by
  have hc3 : 0 < c ^ 3 := by positivity
  have hr : 0 < r := by linarith
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hL : (r + r ^ 2 / c + 2 * r / c ^ 2) * c ^ 3
      = r * c ^ 3 + r ^ 2 * c ^ 2 + 2 * r * c := by
    field_simp
    try ring
  have hc2le : c ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 2
    simpa using this
  have hc3le : c ^ 3 ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h0) h1 3
    simpa using this
  have hrle : r ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (le_of_lt hr)
    simpa [sq] using this
  have hA : r * c ^ 3 ≤ r ^ 2 := by
    have h1' : r * c ^ 3 ≤ r * 1 := mul_le_mul_of_nonneg_left hc3le (le_of_lt hr)
    linarith [h1', hrle]
  have hB : r ^ 2 * c ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hc2le hr2
    simpa using this
  have hC : 2 * r * c ≤ 2 * r ^ 2 := by
    have h1' : 2 * r * c ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * r)
      simpa using this
    linarith [h1', hrle]
  rw [le_div_iff₀ hc3, hL]
  linarith [hA, hB, hC, hr2]

/-! ## Reduction to `θ`-bounds -/

lemma sin_cos_facts {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ ∧ Real.cos θ ≤ 1 ∧ 0 ≤ Real.sin θ ∧ Real.sin θ ≤ 1 ∧
      1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
  obtain ⟨h0, h1⟩ := hθ
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt h0, by linarith [Real.pi_pos]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ; linarith
  exact ⟨hc, hc1, hs0, hs1, hsq⟩

lemma gC_div_ug (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    gC (2 * m + 1) (Real.sin θ) = ug m (Real.sin θ) / (Real.cos θ) ^ 2 := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  show gC (2 * m + 1) (Real.sin θ)
    = (1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ) / (Real.cos θ) ^ 2
  rw [hsq]
  field_simp

lemma ug_sin_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |ug m (Real.sin θ)| ≤ Real.sqrt (Npsi m) * Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hb := ug_bound m ⟨hs0, hs1⟩
  rw [hsq] at hb
  have h1 : (ug m (Real.sin θ)) ^ 2 ≤ (Real.sqrt (Npsi m) * Real.cos θ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt (Npsi_pos m))]
    exact hb
  have h2 := sq_le_sq.mp h1
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt (Npsi m) * Real.cos θ)] at h2

lemma c_mul_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ * |gC (2 * m + 1) (Real.sin θ)| ≤ Real.sqrt (Npsi m) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have h := ug_sin_bound m hθ
  rw [gC_div_ug m hθ, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (Real.cos θ) ^ 2)]
  have hgoal : Real.cos θ * (|ug m (Real.sin θ)| / (Real.cos θ) ^ 2)
      = |ug m (Real.sin θ)| / Real.cos θ := by
    field_simp
  rw [hgoal, div_le_iff₀ hc]
  exact h

lemma gC_abs_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |gC (2 * m + 1) (Real.sin θ)| ≤ Real.sqrt (Npsi m) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [le_div_iff₀ hc]
  simpa [mul_comm] using c_mul_gC_bound m hθ

lemma deriv_ug_abs_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (ug m) (Real.sin θ)| ≤ Npsi m := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have h := Real.sqrt_le_sqrt (du_bound m ⟨hs0, hs1⟩)
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (le_of_lt (Npsi_pos m))] at h

lemma two_sin_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
      ≤ 2 * (Real.sqrt (Npsi m) / Real.cos θ) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hsabs : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, hs1⟩
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |Real.sin θ| * |gC (2 * m + 1) (Real.sin θ)|
      ≤ 2 * 1 * (Real.sqrt (Npsi m) / Real.cos θ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsabs (by norm_num)) (gC_abs_bound m hθ)
          (abs_nonneg _) (by norm_num)
    _ = 2 * (Real.sqrt (Npsi m) / Real.cos θ) := by ring

lemma deriv_gC_mul_eq (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)
      = deriv (ug m) (Real.sin θ)
        + 2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ) := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [deriv_ug m (Real.sin θ), hsq]
  ring

lemma c2_mul_deriv_gC_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|
      ≤ Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  rw [show (Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|
      = |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| from by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.cos θ) ^ 2)]]
  rw [deriv_gC_mul_eq m hθ]
  calc |deriv (ug m) (Real.sin θ) + 2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
      ≤ |deriv (ug m) (Real.sin θ)| + |2 * Real.sin θ * gC (2 * m + 1) (Real.sin θ)| :=
        abs_add_le _ _
    _ ≤ Npsi m + 2 * (Real.sqrt (Npsi m) / Real.cos θ) :=
        add_le_add (deriv_ug_abs_bound m hθ) (two_sin_gC_bound m hθ)
    _ = Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by ring

lemma scq_bound (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
      ≤ (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ := by
  obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
  have hsabs : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, hs1⟩
  have hq' := c2_mul_deriv_gC_bound m hθ
  rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hc)]
  rw [le_div_iff₀ hc]
  calc |Real.sin θ| * Real.cos θ * |deriv (gC (2 * m + 1)) (Real.sin θ)| * Real.cos θ
      = |Real.sin θ| * ((Real.cos θ) ^ 2 * |deriv (gC (2 * m + 1)) (Real.sin θ)|) := by ring
    _ ≤ 1 * (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) :=
        mul_le_mul hsabs hq' (by positivity) (by norm_num)
    _ = Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ := by ring

/-! ## The derivative formulas for `eFam` -/

lemma deriv_eFam (m : ℕ) (θ : ℝ) :
    deriv (eFam m) θ
      = -Real.sin θ * gC (2 * m + 1) (Real.sin θ)
        + (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ) := by
  have h := congrFun (deriv_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1))) θ
  rw [show deriv (eFam m) θ
      = deriv (fun θ' : ℝ => Real.cos θ' * gC (2 * m + 1) (Real.sin θ')) θ from rfl]
  exact h

lemma deriv2_eFam (m : ℕ) (θ : ℝ) :
    deriv (deriv (eFam m)) θ
      = -Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        - 3 * Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
        + (Real.cos θ) ^ 3 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ) := by
  have h := deriv2_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) θ
  rw [show deriv (deriv (eFam m))
      = deriv (deriv (fun θ' : ℝ => Real.cos θ' * gC (2 * m + 1) (Real.sin θ'))) from rfl]
  exact h

lemma deriv_tan_eFam (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.tan θ' * eFam m θ') θ
      = Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        + Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ) := by
  have h := deriv_tan_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) θ hθ
  rw [show (fun θ' : ℝ => Real.tan θ' * eFam m θ')
      = (fun θ' : ℝ => Real.tan θ' * (Real.cos θ' * gC (2 * m + 1) (Real.sin θ'))) from rfl]
  exact h

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

theorem acoeff_zero_of_fstar (α : ℝ) (F : ℝ → ℝ → ℝ)
    (h : ∀ t, 0 < t → Work.Elliptic.Fstar F t = 0) :
    ∀ z, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := by
  intro z hz
  have hcm : ∀ t, 0 < t → Work.FTS.PhiStar.Series.cmode 0 F t = 0 :=
    fun t ht => Work.FTS.PhiStar.Series.eFam_zero_moment F (h t ht)
  rw [Work.FTS.PhiStar.Series.acoeff, Work.FTS.PhiStar.Radial.radGreen]
  -- the integral `∫_0^z` lives on `Ioc 0 z ⊆ Ioi 0`
  have h1 : (∫ t in (0 : ℝ)..z,
      Work.FTS.PhiStar.Series.cmode 0 F t
        * t ^ ((2 * ((0 : ℕ) : ℝ) + 5) / α - 1)) = 0 := by
    rw [intervalIntegral.integral_of_le hz.le]
    trans ∫ t in Set.Ioc (0 : ℝ) z, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only [hcm t ht.1, zero_mul]
    · simp
  -- the integral `∫_{Ioi z}` lives on `Ioi z ⊆ Ioi 0`
  have h2 : (∫ t in Set.Ioi z,
      Work.FTS.PhiStar.Series.cmode 0 F t * t ^ (-(2 * ((0 : ℕ) : ℝ) / α) - 1)) = 0 := by
    trans ∫ t in Set.Ioi z, (0 : ℝ)
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [hcm t (lt_trans hz ht), zero_mul]
    · simp
  rw [h1, h2]
  simp

end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.ak_hasDerivAt_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

/-! ## Bounding the `z`-derivative of `AK`

`AK α z θ = (Γ(θ)/c)(2z²/(1+z)³)` is the correction profile of the modulation
(`Work.Construction.AK`).  Its `z`-derivative is
`(Γ(θ)/c)·2z(2-z)/(1+z)⁴`, and the two factors are bounded by `10` (`0 ≤ Γ ≤ 1` and
`1/10 ≤ c ≤ 10`) and by `2` respectively. -/

/-- The radial factor `2z(2-z)/(1+z)⁴` of `∂_z AK` is bounded by `2` on `(0,∞)`. -/
theorem abs_akPsi_deriv_le_two {z : ℝ} (hz : 0 < z) :
    |2 * z * (2 - z) / (1 + z) ^ 4| ≤ 2 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have hden : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ h1z
  have hpos : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  rcases le_or_gt z 2 with hz2 | hz2
  · have hnum : (0 : ℝ) ≤ 2 * z * (2 - z) := by nlinarith
    rw [abs_of_nonneg (div_nonneg hnum hpos.le), div_le_iff₀ hpos]
    have h2 : 2 * z * (2 - z) ≤ 2 := by nlinarith [sq_nonneg (z - 1)]
    nlinarith [h2, hden]
  · have hnum : 2 * z * (2 - z) ≤ 0 := by nlinarith
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hpos.le), ← neg_div,
      div_le_iff₀ hpos]
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hsq : z ^ 2 ≤ (1 + z) ^ 4 :=
      le_trans (pow_le_pow_right₀ hz1 (by norm_num : 2 ≤ 4))
        (pow_le_pow_left₀ hz.le (by linarith) 4)
    have h1 : -(2 * z * (2 - z)) ≤ 2 * z ^ 2 := by nlinarith
    have h2 : 2 * z ^ 2 ≤ 2 * (1 + z) ^ 4 := by linarith
    linarith

/-- The coefficient `Γ(θ)/c` of `AK` is bounded by `10` in absolute value on `Iθ`. -/
theorem abs_gam_div_c_le_ten (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Gam a θ / Work.Spaces.c a| ≤ 10 := by
  have hG := Work.Spaces.Gam_bounds a θ ha hθ
  have hc := Work.Spaces.c_bounds a ha ha1
  have hcpos : (0 : ℝ) < Work.Spaces.c a := by linarith [hc.1]
  rw [abs_div, abs_of_nonneg hG.1, abs_of_pos hcpos, div_le_iff₀ hcpos]
  linarith [hG.2, hc.1]

theorem ak_hasDerivAt_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {θ z : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.AK a z' θ) d z ∧ |d| ≤ 20 := by
  have hz1 : z ≠ -1 := by intro h; linarith
  refine ⟨(Work.Spaces.Gam a θ / Work.Spaces.c a) * (2 * z * (2 - z) / (1 + z) ^ 4),
    ?_, ?_⟩
  · have hd : HasDerivAt
        (fun z' : ℝ => (Work.Spaces.Gam a θ / Work.Spaces.c a)
          * (2 * z' ^ 2 / (1 + z') ^ 3))
        ((Work.Spaces.Gam a θ / Work.Spaces.c a)
          * (2 * z * (2 - z) / (1 + z) ^ 4)) z :=
      (Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_akPsi hz1).const_mul _
    convert hd using 1
    funext z'
    rw [Work.Construction.AK]
  · rw [abs_mul]
    calc |Work.Spaces.Gam a θ / Work.Spaces.c a| * |2 * z * (2 - z) / (1 + z) ^ 4|
        ≤ 10 * 2 :=
          mul_le_mul (abs_gam_div_c_le_ten a ha ha1 hθ) (abs_akPsi_deriv_le_two hz)
            (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
/-! ## The traces from the two weighted `L²`-bounds -/

/-- **The boundary traces from the weighted `L²`-bounds.**  For `v` differentiable on
`(0,∞)` with `∫ w² v² < ∞` and `∫ w² (D_z v)² < ∞` on both `(0,1)` and `(1,∞)`
(`w² = (1+z)⁴/z⁴`), the trace `z w(z)² v(z)²` vanishes at `0⁺` and at `+∞`. -/
theorem trace_of_weights {v : ℝ → ℝ}
    (hv : ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ v z)
    (h1 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * v z ^ 2) (Set.Ioo (0 : ℝ) 1))
    (h2 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioo (0 : ℝ) 1))
    (h3 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * v z ^ 2) (Set.Ioi (1 : ℝ)))
    (h4 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioi (1 : ℝ))) :
    Tendsto (fun z => z * (v z * Work.Spaces.w z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun z => z * (v z * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
  set ψ : ℝ → ℝ := fun z => v z ^ 2 / z ^ 3 with hψ
  set χ : ℝ → ℝ := fun z => z * v z ^ 2 with hχ
  -- `ψ` and its derivative bound on `(0,1)`
  have hψderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt ψ ((2 * v z * (z * deriv v z) - 3 * v z ^ 2) / z ^ 4) z := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hnum : HasDerivAt (fun z : ℝ => v z ^ 2) (2 * v z ^ (2 - 1) * deriv v z) z :=
      (hv z hz0).hasDerivAt.pow 2
    have hden : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ (3 - 1)) z := hasDerivAt_pow 3 z
    have h4 := hnum.div hden (by positivity)
    rw [hψ]
    convert h4 using 1
    field_simp
    ring
  have hψbound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖deriv ψ z‖ ≤ 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
        + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hd : deriv ψ z = (2 * v z * (z * deriv v z) - 3 * v z ^ 2) / z ^ 4 :=
      (hψderiv z hz).deriv
    have hw : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := one_div_zpow_four_le_w_sq hz0
    have hb : |2 * v z * (z * deriv v z) - 3 * v z ^ 2| ≤ 4 * v z ^ 2 + (z * deriv v z) ^ 2 := by
      have h1 : |2 * v z * (z * deriv v z)| ≤ v z ^ 2 + (z * deriv v z) ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := two_mul_le_add_sq (|v z|) (|z * deriv v z|)
        rw [sq_abs (v z), sq_abs (z * deriv v z)] at this
        linarith [this]
      have h2 : |3 * v z ^ 2| = 3 * v z ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg (sq_nonneg _)]
      have h3 : |2 * v z * (z * deriv v z) - 3 * v z ^ 2|
          ≤ |2 * v z * (z * deriv v z)| + |3 * v z ^ 2| := by
        have h := abs_sub_le (2 * v z * (z * deriv v z)) 0 (3 * v z ^ 2)
        simpa only [sub_zero, zero_sub, abs_neg] using h
      linarith [h3, h1, h2.le, h2.ge]
    rw [Real.norm_eq_abs, hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < z ^ 4)]
    have hw4 : v z ^ 2 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      calc v z ^ 2 / z ^ 4 = (1 / z ^ 4) * v z ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    have hw5 : (z * deriv v z) ^ 2 / z ^ 4
        ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
      calc (z * deriv v z) ^ 2 / z ^ 4 = (1 / z ^ 4) * (z * deriv v z) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    calc |2 * v z * (z * deriv v z) - 3 * v z ^ 2| / z ^ 4
        ≤ (4 * v z ^ 2 + (z * deriv v z) ^ 2) / z ^ 4 := by
          rw [div_le_div_iff_of_pos_right (by positivity)]
          exact hb
      _ = 4 * (v z ^ 2 / z ^ 4) + (z * deriv v z) ^ 2 / z ^ 4 := by ring
      _ ≤ 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
            + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by linarith [hw4, hw5]
  have hψcont : ContinuousOn (fun z : ℝ => v z ^ 2 / z ^ 3 / z) (Set.Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun z hz => ne_of_gt hz.1)
    refine ContinuousOn.div ?_ (continuousOn_id.pow 3) (fun z hz => ne_of_gt (pow_pos hz.1 3))
    have hvcont : ContinuousOn (fun z : ℝ => v z) (Set.Ioo (0 : ℝ) 1) := by
      intro z hz
      exact (hv z hz.1).continuousAt.continuousWithinAt
    exact hvcont.pow 2
  have hψdiv : IntegrableOn (fun z => ψ z / z) (Set.Ioo (0 : ℝ) 1) := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ‖ψ z / z‖ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hz0 : 0 < z := hz.1
      have hw : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := one_div_zpow_four_le_w_sq hz0
      have h : ψ z / z = (1 / z ^ 4) * v z ^ 2 := by
        rw [hψ]; field_simp
      rw [Real.norm_eq_abs, h, abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    refine Integrable.mono' h1 ?_ hpt
    refine (hψcont.aestronglyMeasurable measurableSet_Ioo).congr ?_
    filter_upwards with z
    rw [hψ]
  have hψder : IntegrableOn (deriv ψ) (Set.Ioo (0 : ℝ) 1) := by
    have hint : IntegrableOn
        (fun z => 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
          + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioo (0 : ℝ) 1) :=
      Integrable.add (Integrable.const_mul h1 4) h2
    refine Integrable.mono' hint (measurable_deriv ψ).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hψbound z hz
  have hψdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ ψ z :=
    fun z hz => (hψderiv z hz).differentiableAt
  have hψnn : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ ψ z := by
    intro z hz
    rw [hψ]
    exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hz.1) 3)
  have hψ0 : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_of_integrableOn_deriv_left hψdiff hψnn hψdiv hψder
  -- `χ` and its derivative bound on `(1,∞)`
  have hχderiv : ∀ z ∈ Set.Ioi (1 : ℝ),
      HasDerivAt χ (v z ^ 2 + 2 * v z * (z * deriv v z)) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hvz : HasDerivAt v (deriv v z) z := (hv z hz0).hasDerivAt
    have hmul := (hasDerivAt_id z).mul (hvz.pow 2)
    have hfun : (id * v ^ 2 : ℝ → ℝ) = χ := by
      rw [hχ]; funext y; rfl
    rw [hfun] at hmul
    convert hmul using 1
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    simp only [Pi.pow_apply, id_eq, one_mul, h21, pow_one]
    ring
  have hχbound : ∀ z ∈ Set.Ioi (1 : ℝ),
      ‖deriv χ z‖ ≤ 2 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
        + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hd : deriv χ z = v z ^ 2 + 2 * v z * (z * deriv v z) := (hχderiv z hz).deriv
    have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz0
    have hb : |v z ^ 2 + 2 * v z * (z * deriv v z)| ≤ 2 * v z ^ 2 + (z * deriv v z) ^ 2 := by
      have h1 : |2 * v z * (z * deriv v z)| ≤ v z ^ 2 + (z * deriv v z) ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := two_mul_le_add_sq (|v z|) (|z * deriv v z|)
        rw [sq_abs (v z), sq_abs (z * deriv v z)] at this
        linarith [this]
      have h2 : |v z ^ 2| = v z ^ 2 := abs_of_nonneg (sq_nonneg _)
      have h3 : |v z ^ 2 + 2 * v z * (z * deriv v z)|
          ≤ |v z ^ 2| + |2 * v z * (z * deriv v z)| := abs_add_le _ _
      linarith [h3, h1, h2.le, h2.ge]
    rw [Real.norm_eq_abs, hd]
    have h6 : v z ^ 2 ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      nlinarith [hw, sq_nonneg (v z)]
    have h7 : (z * deriv v z) ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
      nlinarith [hw, sq_nonneg (z * deriv v z)]
    linarith [hb, h6, h7]
  have hχcont : ContinuousOn (fun z : ℝ => z * v z ^ 2 / z) (Set.Ioi (1 : ℝ)) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun z hz => ne_of_gt (lt_trans zero_lt_one hz))
    have hvcont : ContinuousOn (fun z : ℝ => v z) (Set.Ioi (1 : ℝ)) := by
      intro z hz
      exact (hv z (lt_trans (zero_lt_one : (0 : ℝ) < 1) hz)).continuousAt.continuousWithinAt
    exact continuousOn_id.mul (hvcont.pow 2)
  have hχdiv : IntegrableOn (fun z => χ z / z) (Set.Ioi (1 : ℝ)) := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖χ z / z‖ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq (lt_trans zero_lt_one hz)
      have hz0 : z ≠ 0 := ne_of_gt (lt_trans (zero_lt_one : (0 : ℝ) < 1) hz)
      have h : χ z / z = v z ^ 2 := by
        change z * v z ^ 2 / z = v z ^ 2
        field_simp
      rw [Real.norm_eq_abs, h, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hw, sq_nonneg (v z)]
    refine Integrable.mono' h3 ?_ hpt
    refine (hχcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards with z
    rw [hχ]
  have hχder : IntegrableOn (deriv χ) (Set.Ioi (1 : ℝ)) := by
    have hint : IntegrableOn
        (fun z => 2 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
          + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioi (1 : ℝ)) :=
      Integrable.add (Integrable.const_mul h3 2) h4
    refine Integrable.mono' hint (measurable_deriv χ).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact hχbound z hz
  have hχdiff : ∀ z ∈ Set.Ioi (1 : ℝ), DifferentiableAt ℝ χ z :=
    fun z hz => (hχderiv z hz).differentiableAt
  have hχnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ χ z := by
    intro z hz
    rw [hχ]
    exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hz)) (sq_nonneg _)
  have hχ0 : Tendsto χ atTop (𝓝 0) :=
    tendsto_zero_of_integrableOn_deriv_atTop hχdiff hχnn hχdiv hχder
  constructor
  · -- left end: `z (v w)² = (1+z)⁴ ψ`
    have hlim1 : Tendsto (fun z : ℝ => (1 + z) ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h : ContinuousAt (fun z : ℝ => (1 + z) ^ 4) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    have h := hlim1.mul hψ0
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (z_mul_w_sq_mul z (v z) (ne_of_gt hz)).symm
  · -- right end: `z (v w)² = w² χ`
    have hlim1 : Tendsto (fun z : ℝ => (Work.Spaces.w z) ^ 2) atTop (𝓝 1) := by
      have h1 : Tendsto (fun z : ℝ => (1 + z) / z) atTop (𝓝 1) := by
        have heq : ∀ᶠ z : ℝ in atTop, 1 / z + 1 = (1 + z) / z := by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
          field_simp
        have hinv : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have h2 : Tendsto (fun z : ℝ => 1 / z + 1) atTop (𝓝 1) := by
          simpa [one_div, add_comm] using hinv.const_add 1
        exact h2.congr' heq
      have h2 : Tendsto (fun z : ℝ => (((1 + z) / z) ^ 2) ^ 2) atTop (𝓝 1) := by
        simpa using (h1.pow 2).pow 2
      refine h2.congr' (Filter.Eventually.of_forall (fun z => ?_))
      have hq : (((1 + z) / z) ^ 2) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [← pow_mul, div_pow, show (2 : ℕ) * 2 = 4 from by norm_num]
      rw [hq]
      exact (w_sq_eq z).symm
    have h := hlim1.mul hχ0
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards with z
    exact (z_mul_w_sq_mul' z (v z)).symm

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SixZeroAux.IbpCutoffNonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option linter.unusedVariables false

/-- **The cut-off angular integration by parts, for `0 ≤ q`.**

For `χ` of class `C^∞` vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`) and `hf`, `hv` of class `C¹`
on the open interval `(0, π/2)`,

`∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
    = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf) + (1/2) sin(2θ) χ' hf)·hv²`

with both sides integrable.  This is `Work.H2.T1Q.IbpCutoff` with the hypothesis `0 < q`
weakened to `0 ≤ q` (its proof never uses it). -/
theorem ibpCutoff_nonneg {q : ℝ} (hq : 0 ≤ q) {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
          * (Real.sin (2 * θ) * deriv hv θ) * hv θ) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
            * (Real.sin (2 * θ) * deriv hv θ) * hv θ
        = -∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
                + (1 - q) * Real.cos (2 * θ) * hf θ)
              + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
            * (hv θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  obtain ⟨hIntG, hIntK⟩ := Work.H2.T1Q.ibpCutoff_integrable (q := q) hχ hδ hδ4 hχ0 hχ2 hf' hv'
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (Work.H2.T1Q.IbpPrim q χ hf hv)
        (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) θ := by
    intro θ hθ
    exact Work.H2.T1Q.ibpCutoff_deriv hθ (hχ.contDiffAt.differentiableAt (by simp))
      ((hf'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
      ((hv'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
  have hint : IntervalIntegrable
      (fun θ => Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le]
    exact hIntG.add hIntK
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2),
      (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hint
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_right hδ hχ0)
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_left hδ hχ2)
    simpa using h
  have hsplit : ∫ θ in Work.Spaces.Iθ,
      (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      = (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
        + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ :=
    MeasureTheory.integral_add hIntG hIntK
  have hsum : (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
      + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ = 0 := by
    rw [← hsplit, hIcc, hFTC]
  change MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ
  exact ⟨hIntG, by linarith⟩

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.CompCLM.Base =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.Top.Rescale

/-- **The `C¹` block.**  Precomposition with a continuous linear map `Φ` (mapping `s` into `t`) and
postcomposition with a continuous linear map `A` preserve `C¹` on the strip. -/
theorem contDiffOn_comp_clm {s t : Set (Work.FTS.Top.R3 × ℝ)}
    {g : Work.FTS.Top.R3 × ℝ → Work.FTS.Top.R3}
    (A : Work.FTS.Top.R3 →L[ℝ] Work.FTS.Top.R3)
    (Φ : (Work.FTS.Top.R3 × ℝ) →L[ℝ] (Work.FTS.Top.R3 × ℝ))
    (hΦ : MapsTo Φ s t) (hg : ContDiffOn ℝ 1 g t) :
    ContDiffOn ℝ 1 (fun z => A (g (Φ z))) s := by
  have h1 : ContDiffOn ℝ 1 (g ∘ Φ) s :=
    hg.comp (Φ.contDiff.contDiffOn (𝕜 := ℝ) (s := s)) hΦ
  have h2 : ContDiffOn ℝ 1 (⇑A) Set.univ := A.contDiff.contDiffOn
  have h3 := h2.comp h1 (fun _ _ => trivial)
  convert h3 using 1
  ext z
  rfl

/-- **The within-derivative formula.**  On a set `s` which is uniquely differentiable within at
each of its points, the within-derivative of `z ↦ A (g (Φ z))` is the composite of the
within-derivative of `g` at `Φ z` with the two fixed linear maps `A` and `Φ`.

This is the within chain rule (`HasFDerivWithinAt.comp`, twice) together with
`HasFDerivWithinAt.fderivWithin`; the hypothesis `huniq` is what pins the within-derivative down. -/
theorem fderivWithin_comp_clm {s t : Set (Work.FTS.Top.R3 × ℝ)}
    {g : Work.FTS.Top.R3 × ℝ → Work.FTS.Top.R3}
    (A : Work.FTS.Top.R3 →L[ℝ] Work.FTS.Top.R3)
    (Φ : (Work.FTS.Top.R3 × ℝ) →L[ℝ] (Work.FTS.Top.R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t) :
    ∀ z ∈ s, fderivWithin ℝ (fun z => A (g (Φ z))) s z
      = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ) := by
  intro z hz
  have hz_t : Φ z ∈ t := hΦ hz
  have hg' : HasFDerivWithinAt g (fderivWithin ℝ g t (Φ z)) t (Φ z) :=
    (hg (Φ z) hz_t).hasFDerivWithinAt
  have hΦ' : HasFDerivWithinAt Φ Φ s z := Φ.hasFDerivAt.hasFDerivWithinAt
  have hcomp1 : HasFDerivWithinAt (g ∘ Φ) (fderivWithin ℝ g t (Φ z) ∘L Φ) s z :=
    HasFDerivWithinAt.comp z hg' hΦ' hΦ
  have hA : HasFDerivWithinAt (⇑A) A Set.univ ((g ∘ Φ) z) :=
    A.hasFDerivAt.hasFDerivWithinAt
  have hcomp2 : HasFDerivWithinAt (⇑A ∘ (g ∘ Φ))
      (A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)) s z :=
    HasFDerivWithinAt.comp z hA hcomp1 (fun _ _ => trivial)
  have := hcomp2.fderivWithin (huniq z hz)
  change fderivWithin ℝ (⇑A ∘ (g ∘ Φ)) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)
  exact this

/-- **The norm form of `HolderOnWith`.**  `HolderOnWith` is stated in `edist` coordinates; every
estimate below is in norm coordinates. -/
theorem norm_le_of_holderOnWith {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X} (h : HolderOnWith C r f s) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ) := by
  intro x hx y hy
  have h1 := h.edist_le hx hy
  rw [edist_dist, edist_dist, dist_eq_norm] at h1
  have hC : ((C : ℝ≥0∞)) = ENNReal.ofReal (C : ℝ) := ENNReal.coe_nnreal_eq _
  rw [hC] at h1
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity)] at h1
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

end Work.FTS.Top.Rescale
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.spaceGrad_timeScaleP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Gradient
open scoped Gradient

namespace Work.FTS.Top

/-- **The gradient of a scalar multiple of a scalar-valued function**:
`∇ (fun y => a * g y) x = a • ∇ g x`.

This is unconditional — in particular it also holds at points where `g` is not differentiable:
when `a ≠ 0` the function `a * g` is then non-differentiable as well (divide by `a`), so both
sides are `0`; and when `a = 0` the left-hand side is the gradient of the zero function. -/
theorem gradient_const_mul (a : ℝ) (g : R3 → ℝ) (x : R3) :
    ∇ (fun y => a * g y) x = a • ∇ g x := by
  by_cases ha : a = 0
  · subst ha
    simp
  · by_cases hg : DifferentiableAt ℝ g x
    · -- differentiable case: compare Fréchet derivatives through `toDual`
      have hfd : fderiv ℝ (fun y => a * g y) x = a • fderiv ℝ g x := by
        have h1 : (fun y => a * g y) = (fun y => a • g y) := by
          funext y; rw [smul_eq_mul]
        rw [h1]
        rw [← Pi.smul_apply]
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) a) x
      rw [gradient, gradient, hfd]
      rw [map_smul]
    · -- non-differentiable case: `a * g` is non-differentiable too, both gradients vanish
      have hna : ¬ DifferentiableAt ℝ (fun y => a * g y) x := by
        intro h
        apply hg
        have hfun : (fun y => a⁻¹ * (a * g y)) = g := by
          funext y
          rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        rw [← hfun]
        exact h.const_smul a⁻¹
      rw [gradient_eq_zero_of_not_differentiableAt hna,
        gradient_eq_zero_of_not_differentiableAt hg, smul_zero]

end Work.FTS.Top

namespace Work.FTS.Top.Rescale

/-
The gradient of the time-rescaled pressure.

`Work.FTS.Top.timeScaleP c p x t = c ^ 2 * p x (c * t)`, and the *space* variable is not rescaled,
so the gradient picks up exactly the factor `c ^ 2`.  The statement is unconditional: it holds for
`c = 0` too (`timeScaleP 0 p = 0` and `0 * ∇ = 0`).

Route: prove first the auxiliary fact `∇ (fun y => a * g y) x = a • ∇ g x` (unconditional in
Mathlib: in the differentiable case use `HasGradientAt.unique` with
`hasGradientAt_iff_hasFDerivAt`, `fderiv_const_smul_field` and `toDual_gradient`; in the
non-differentiable case `gradient_eq_zero_of_not_differentiableAt`, noting that `a • g` is
non-differentiable too when `a ≠ 0`, and that `a = 0` makes both sides `0`).
Then apply with `g = fun y => p y (c * t)` and `a = c ^ 2`, using `c ^ 2 * p y (c*t) = c^2 • p y (c*t)`.
Everything in namespace `Work.FTS.Top`.
-/
theorem spaceGrad_timeScaleP (c : ℝ) (p : Work.FTS.Top.R3 → ℝ → ℝ) (x : Work.FTS.Top.R3) (t : ℝ) :
    FiniteTimeSingularity.spaceGrad (Work.FTS.Top.timeScaleP c p) x t
      = (c * c) • FiniteTimeSingularity.spaceGrad p x (c * t) := by
  show ∇ (fun y => c ^ 2 * p y (c * t)) x = (c * c) • ∇ (fun y => p y (c * t)) x
  rw [pow_two]
  exact gradient_const_mul (c * c) (fun y => p y (c * t)) x

end Work.FTS.Top.Rescale
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.vortLInf_timeScale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Top.Rescale

/-
The `L^∞` norm of the vorticity, `Work.LWP.vortLInf u t = ⨆ x, ‖vorticity (u · t) x‖`, scales by
`c` under the time rescaling; the space variable is *not* rescaled, so there is no `c²` factor:

  `vortLInf (timeScale c u) t = c * vortLInf u (c * t)`   for `c ≥ 0`.

Route: `Work.FTS.Top.vorticity_timeScale` gives
`vorticity (timeScale c u · t) = fun x => c • vorticity (u · (c*t)) x`, and `‖c • w‖ = c * ‖w‖`
for `c ≥ 0`, so with `f x = ‖vorticity (u · (c*t)) x‖ ≥ 0` the claim is the real identity

  `(⨆ x, c * f x) = c * (⨆ x, f x)`   for `c ≥ 0`.

That identity is unconditional: for `c = 0` both sides are `0`; for `c > 0` the range of `c * f ·`
is bounded above exactly when the range of `f` is, so the junk value `sSup ∅ = 0` is on both sides
simultaneously.  It is Mathlib's `Real.mul_iSup_of_nonneg` (`Real.sSup_smul_of_nonneg` for a
positive scaling, `Real.sSup_of_not_bddAbove` otherwise), so no case split is needed here.
Namespace `Work.FTS.Top`.
-/
/-- The pointwise norm of the rescaled vorticity slice, `c ≥ 0`: `‖c • w‖ = c * ‖w‖`. -/
theorem norm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (w : Work.FTS.Top.R3) :
    ‖c • w‖ = c * ‖w‖ := by
  rw [norm_smul, Real.norm_of_nonneg hc]

theorem vortLInf_timeScale (c : ℝ) (hc : 0 ≤ c) (u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3)
    (t : ℝ) :
    Work.LWP.vortLInf (Work.FTS.Top.timeScale c u) t = c * Work.LWP.vortLInf u (c * t) := by
  -- `vortLInf` is the `iSup` of the pointwise norms of the vorticity slice.
  unfold Work.LWP.vortLInf
  -- The rescaled slice's vorticity is `c •` the original slice's vorticity, and `‖c • w‖ = c ‖w‖`
  -- when `c ≥ 0`; so the two `iSup`s are taken of `x ↦ c * f x` and `f`, with `f ≥ 0`.
  have hv : (fun x => ‖FiniteTimeSingularity.vorticity (Work.FTS.Top.timeScale c u · t) x‖)
      = fun x => c * ‖FiniteTimeSingularity.vorticity (u · (c * t)) x‖ := by
    rw [Work.FTS.Top.vorticity_timeScale]
    funext x
    exact norm_smul_of_nonneg hc _
  rw [hv]
  -- Pull the factor `c` out of the `iSup`.  `Real.mul_iSup_of_nonneg` is unconditional in `ℝ`:
  -- both sides are the junk value `0` when the range is unbounded above, and `0` for `c = 0`.
  exact (Real.mul_iSup_of_nonneg hc
    (fun x => ‖FiniteTimeSingularity.vorticity (u · (c * t)) x‖)).symm

end Work.FTS.Top.Rescale
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality, without any decay hypothesis

`Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay`: for `v : ℝ → ℝ` differentiable on `(0,∞)`
with `(v w)²` and `(x v' w)²` integrable on `[0,∞)`, and `z > 0`,

  `(v z)² w(z)² z ≤ 4 ∫_{z}^{∞} (v w)² + ∫_{z}^{∞} (x v' w)²`.

This is the statement of `Work.FTS_RegExport.RXA1w.agmonZ_weight` with the hypothesis that
`x (v x w x)² → 0` at `+∞` removed.  That hypothesis is *not* needed: writing
`F x = x (v x w x)²`, the fundamental theorem of calculus on `[z, X]` gives

  `F z ≤ F X + ∫_{z}^{∞} |F'|`   for every `X ≥ z`,

and integrability of `(v w)²` alone forces `F` to take arbitrarily small values at
arbitrarily large points (`agmon_small_value` below, via the divergence of `∫ dx/x`), so
`inf_{X ≥ z} F X = 0` and `F z ≤ ∫_{z}^{∞} |F'|`.  The pointwise bound
`|F'| ≤ 4 (v w)² + (x v' w)²` on `[0,∞)` finishes the argument.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

/-- If `u²` is integrable on `(z,∞)` (with `z > 0`), then `x * u x ^ 2` is arbitrarily small
at arbitrarily large points.  (No continuity of `u` is required: the pointwise lower bound
`u x² > ε/x` on the whole half-line `(z,∞)` forces `∫_{z}^{N} u² ≥ ε log(N/z) → ∞`.) -/
private lemma agmon_small_value {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun x => u x ^ 2) (Set.Ioi z)) :
    ∀ ε > 0, ∃ R : ℝ, z < R ∧ R * (u R) ^ 2 ≤ ε := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ N : ℝ, z < N →
      ε * Real.log (N / z) ≤ ∫ x in Set.Ioi z, u x ^ 2 := by
    intro N hzN
    have hNz : z ≤ N := le_of_lt hzN
    have hInt1 : IntervalIntegrable (fun x : ℝ => ε / x) volume z N := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hNz]
      exact ContinuousOn.div continuousOn_const continuousOn_id
        (fun x hx => ne_of_gt (lt_of_lt_of_le hz hx.1))
    have hInt2 : IntervalIntegrable (fun x : ℝ => u x ^ 2) volume z N := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hNz]
      exact hint.mono_set (fun x hx => hx.1)
    have hcmp : ∫ x in z..N, ε / x ≤ ∫ x in z..N, u x ^ 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo hNz hInt1 hInt2 (fun x hx => by
        have hx0 : 0 < x := lt_trans hz hx.1
        rw [div_le_iff₀ hx0]
        linarith [hcon x hx.1])
    have h2 : ∫ x in z..N, u x ^ 2 ≤ ∫ x in Set.Ioi z, u x ^ 2 := by
      rw [intervalIntegral.integral_of_le hNz]
      exact MeasureTheory.setIntegral_mono_set hint
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : ∫ x in z..N, ε / x = ε * Real.log (N / z) := by
      have hdiv : (fun x : ℝ => ε / x) = fun x : ℝ => ε * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [hdiv, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hz (lt_trans hz hzN)]
    linarith
  set N : ℝ := z * Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) with hN
  have hcpos : 0 < |(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1 := by
    have h1 : 0 ≤ |(∫ x in Set.Ioi z, u x ^ 2)| / ε :=
      div_nonneg (abs_nonneg _) (le_of_lt hε)
    linarith
  have hzN : z < N := by
    rw [hN]
    have h : z * 1 < z * Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) :=
      mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.mpr hcpos) hz
    simpa using h
  have hlog : ε * Real.log (N / z) = |(∫ x in Set.Ioi z, u x ^ 2)| + ε := by
    have hNz' : N / z = Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) := by
      rw [hN, mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hNz', Real.log_exp]
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp
  have hcontra := hstep N hzN
  rw [hlog] at hcontra
  have habs : (∫ x in Set.Ioi z, u x ^ 2) ≤ |(∫ x in Set.Ioi z, u x ^ 2)| :=
    le_abs_self _
  linarith

/-- The pointwise bound `|(x (v x w x)²)'| ≤ 4 (v w)² + (x v' w)²` on `[0,∞)`. -/
private lemma agmon_deriv_bound (v v' : ℝ → ℝ) (x : ℝ) (hx : x ∈ Work.Spaces.Iz) :
    |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
      ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
  have hx0 : 0 ≤ x := hx
  have hb : |(x - 3) / (1 + x)| ≤ 3 := by
    have h1x : (0 : ℝ) < 1 + x := by linarith
    rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
    by_cases h : x ≤ 3
    · rw [abs_of_nonpos (by linarith)]; nlinarith
    · push_neg at h
      rw [abs_of_pos (by linarith)]; nlinarith
  have hkey : Work.FTS_RegExport.RXT.agmonFderiv v v' x
      = 2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)
        + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)) := by
    rw [Work.FTS_RegExport.RXT.agmonFderiv]; ring
  have hAB : 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)|
      ≤ (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
    nlinarith [sq_nonneg (|v x * Work.Spaces.w x| - |x * v' x * Work.Spaces.w x|),
      sq_abs (v x * Work.Spaces.w x), sq_abs (x * v' x * Work.Spaces.w x)]
  have hE1 : |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)|
      = 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hE2 : |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
      = (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  rw [hkey]
  calc |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)
          + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
      ≤ |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)|
          + |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))| := abs_add_le _ _
    _ = 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)|
          + (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by rw [hE1, hE2]
    _ ≤ (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2
          + (v x * Work.Spaces.w x) ^ 2 * 3 := by
        refine add_le_add hAB ?_
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by ring

theorem v2_agmonZ_noDecay {v v' : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x)
    (hint1 : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := by
  -- `(z, ∞) ⊆ [0, ∞)`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hderiv x hx).differentiableAt.continuousAt.continuousWithinAt
  -- arbitrarily small values of `agmonF v` at arbitrarily large points
  have hsmall : ∀ ε > 0, ∃ R : ℝ, z ≤ R ∧ Work.FTS_RegExport.RXT.agmonF v R ≤ ε := by
    intro ε hε
    obtain ⟨R, hzR, hR⟩ :=
      agmon_small_value hz (hint1.mono_set hsub) ε hε
    exact ⟨R, le_of_lt hzR, hR⟩
  -- the pointwise derivative of `agmonF v`
  have hFderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
        (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x :=
    Work.FTS_RegExport.RXT.AgmonND.hasDerivAt_agmonF hderiv
  -- the pointwise bound for that derivative
  have hF'bound : ∀ x ∈ Work.Spaces.Iz,
      |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
        ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 :=
    fun x hx => agmon_deriv_bound v v' x hx
  -- integrability of the dominating function
  have hgint : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := (hint1.const_mul 4).add hint2
  have hIz_eq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]
  -- `v'` agrees a.e. with `deriv v` on `(0,∞)`, hence is a.e. strongly measurable there
  have hv'meas : AEStronglyMeasurable v' (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (aestronglyMeasurable_deriv v volume).restrict.congr
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (hderiv x hx).deriv))
  have haesm : AEStronglyMeasurable (Work.FTS_RegExport.RXT.agmonFderiv v v')
      (volume.restrict Work.Spaces.Iz) := by
    rw [hIz_eq]
    have hvc : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hvcont.aestronglyMeasurable measurableSet_Ioi
    have hwc : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS_RegExport.RXT.continuousOn_w_Ioi.aestronglyMeasurable measurableSet_Ioi
    have hc3 : AEStronglyMeasurable (fun x : ℝ => (x - 3) / (1 + x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h2 : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi (0 : ℝ)) :=
        continuousOn_const.add continuousOn_id
      exact ((continuousOn_id.sub continuousOn_const).div h2
        (fun x hx => by have hx0 : 0 < x := hx; exact ne_of_gt (by linarith))).aestronglyMeasurable
        measurableSet_Ioi
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => 2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.const_mul 2).mul (aestronglyMeasurable_id.mul hv'meas)).mul (hwc.pow 2))
    have h2 : AEStronglyMeasurable
        (fun x : ℝ => (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.pow 2).mul (hwc.pow 2)).mul hc3)
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [Work.FTS_RegExport.RXT.agmonFderiv, Pi.add_apply])
  have hF'int : MeasureTheory.IntegrableOn (Work.FTS_RegExport.RXT.agmonFderiv v v')
      Work.Spaces.Iz :=
    hgint.mono' haesm (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
      rw [Real.norm_eq_abs]; exact hF'bound x hx)
  have hAbsOn : MeasureTheory.IntegrableOn
      (fun x => |Work.FTS_RegExport.RXT.agmonFderiv v v' x|) Work.Spaces.Iz := hF'int.abs
  have hAbsOnz : MeasureTheory.IntegrableOn
      (fun x => |Work.FTS_RegExport.RXT.agmonFderiv v v' x|) (Set.Ioi z) :=
    hAbsOn.mono_set hsub
  have hgintz : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      (Set.Ioi z) := hgint.mono_set hsub
  -- the fundamental theorem of calculus on `[z, X]`
  have htail : ∀ X : ℝ, z ≤ X → Work.FTS_RegExport.RXT.agmonF v z
      ≤ Work.FTS_RegExport.RXT.agmonF v X
        + ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
    intro X hzX
    have hFcont : ContinuousOn (Work.FTS_RegExport.RXT.agmonF v) (Set.Icc z X) := by
      have hv : ContinuousOn v (Set.Icc z X) := hvcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hw : ContinuousOn Work.Spaces.w (Set.Icc z X) :=
        Work.FTS_RegExport.RXT.continuousOn_w_Ioi.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have h := ((hv.pow 2).mul (hw.pow 2)).mul continuousOn_id
      refine h.congr (fun y _ => ?_)
      simp only [Work.FTS_RegExport.RXT.agmonF, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    have hd : ∀ x ∈ Set.Ioo z X,
        HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
          (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x :=
      fun x hx => hFderiv x (lt_trans hz hx.1)
    have hintv : IntervalIntegrable (Work.FTS_RegExport.RXT.agmonFderiv v v') volume z X := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hzX]
      exact hF'int.mono_set (fun x hx => le_of_lt (lt_trans hz hx.1))
    have hFTC : ∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x
        = Work.FTS_RegExport.RXT.agmonF v X - Work.FTS_RegExport.RXT.agmonF v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzX hFcont hd hintv
    have h3abs : |∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x|
        ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
      rw [intervalIntegral.integral_of_le hzX]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
      exact MeasureTheory.setIntegral_mono_set hAbsOnz
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : -(∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x)
        ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| :=
      le_trans (neg_le_abs _) h3abs
    linarith [hFTC, h3]
  -- `inf_{X ≥ z} agmonF v X = 0` gives the boundary term at `+∞` for free
  have hmain : Work.FTS_RegExport.RXT.agmonF v z
      ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨R, hzR, hR⟩ := hsmall ε hε
    have h1 := htail R hzR
    linarith
  have hle : ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
      ≤ ∫ x in Set.Ioi z,
          (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2) := by
    refine integral_mono_ae hAbsOnz hgintz ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => hF'bound x (le_of_lt (lt_trans hz hx)))
  have hsplit : ∫ x in Set.Ioi z,
        (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      = 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := by
    rw [integral_add ((hint1.mono_set hsub).const_mul 4) (hint2.mono_set hsub),
      integral_const_mul]
  calc (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      = Work.FTS_RegExport.RXT.agmonF v z := (Work.FTS_RegExport.RXT.agmonF_eq v z).symm
    _ ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := hmain
    _ ≤ ∫ x in Set.Ioi z,
          (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2) := hle
    _ = 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
          + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := hsplit

end Work.FTS_RegExport.RXT.Slots
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.angular_meanVar_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- The derivative datum `g'` of a function differentiable on the open angular interval is
a.e. strongly measurable for the Lebesgue measure restricted to `Iθ`. -/
lemma aeStronglyMeasurable_deriv_of_hasDerivAt {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ) :
    AEStronglyMeasurable g' (volume.restrict Work.Spaces.Iθ) := by
  have hset : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hm : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ := Measure.restrict_congr_set hset
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      deriv g x = g' x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun x hx => (hg x hx).deriv)
  have hae' : ∀ᵐ x ∂(volume.restrict Work.Spaces.Iθ), deriv g x = g' x := hm.symm ▸ hae
  exact ((measurable_deriv g).aemeasurable.congr hae').aestronglyMeasurable

/-- `sin(2θ)^{γ-2}` is interval integrable on `[0,π/2]` for `γ > 1`. -/
lemma intervalIntegrable_sin_rpow {γ : ℝ} (hγ : 1 < γ) :
    IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) volume 0 (Real.pi / 2) := by
  have hc : (-1 : ℝ) < γ - 2 := by linarith
  have hInt : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Flat.integrableOn_sin_two_rpow_Icc hc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)).2 hInt

/-- Assembly step: from the mean-value point, the FTC on interior subintervals and the weighted
Cauchy–Schwarz bound, the pointwise angular inequality follows. -/
theorem angular_meanVar_le_aux {γ : ℝ} {g g' : ℝ → ℝ}
    (hA : ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      2 * g t ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2))
    (hB : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      ∫ x in a..b, g' x = g b - g a)
    (hC : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      (∫ x in a..b, |g' x|) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  intro θ hθ
  obtain ⟨t, ht, htle⟩ := hA
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2) with hM
  set W : ℝ := ∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) with hW
  have step : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      (∫ x in a..b, g' x) ^ 2 ≤ W * M := by
    intro a b ha hab hb
    have h2 := hC a b ha hab hb
    rw [hM, hW] at h2
    refine le_trans ?_ h2
    have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := g') hab
    calc (∫ x in a..b, g' x) ^ 2 = |∫ x in a..b, g' x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ x in a..b, |g' x|) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg _) habs
  have key : (g θ - g t) ^ 2 ≤ W * M := by
    rcases le_total t θ with h | h
    · have h1 : g θ - g t = ∫ x in t..θ, g' x := (hB t θ ht.1 h hθ.2).symm
      rw [h1]; exact step t θ ht.1 h hθ.2
    · have h1 : g θ - g t = -(∫ x in θ..t, g' x) := by
        rw [hB θ t hθ.1 h ht.2]; ring
      rw [h1, neg_sq]; exact step θ t hθ.1 h ht.2
  have hfin : g θ ^ 2 ≤ 2 * (g θ - g t) ^ 2 + 2 * g t ^ 2 := by
    nlinarith [sq_nonneg ((g θ - g t) - g t)]
  linarith [hfin, key, htle]

theorem angular_meanVar_le {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint1 : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  refine angular_meanVar_le_aux (γ := γ) ?_ ?_ ?_
  · exact Work.FTS_RegExport.RXT.Angular.meanValue hint1
  · intro a b ha hab hb
    exact Work.FTS_RegExport.RXT.Angular.integral_deriv_eq_sub hγ hg hint2 ha hab hb
  · intro a b ha hab hb
    exact Work.FTS_RegExport.RXT.Angular.cs_weighted hγ
      (aeStronglyMeasurable_deriv_of_hasDerivAt hg) hint2 (intervalIntegrable_sin_rpow hγ)
      ha hab hb

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.radial_noDecay_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **Radial pointwise bound with no decay hypothesis.**

For `v : ℝ → ℝ` differentiable on `(0,∞)` with `v'` its derivative, if both weighted energies
`∫ v² w²` and `∫ (z v')² w²` are finite (`w(z) = (1+z)²/z²`), then

  `v(z)² ≤ 20 (min z 1)² (∫ v²w² + ∫ (zv')²w²)`  for every `z > 0`.

Route.  The profile `F(x) = x (v(x) w(x))²` has
`|F'| ≤ 4 (v w)² + (x v' w)²` on `(0,∞)`, so the fundamental theorem of calculus on `[z,x]`
gives `F x ≥ F z - (4 ∫(vw)² + ∫(xv'w)²)` for all `x ≥ z`.  If `F z` exceeded that constant,
`F` would be trapped above a positive constant `c` on `[z,∞)`, whence
`∫_z^X (vw)² = ∫_z^X F(x)/x ≥ c log(X/z) → ∞`, contradicting `∫_z^X (vw)² ≤ ∫ v² w² < ∞`.
So `F z ≤ 4 ∫(vw)² + ∫(xv'w)²`, and since `v(z)² = F(z) z³/(1+z)⁴` and
`z³/(1+z)⁴ ≤ (min z 1)²`, the claim follows. -/
theorem radial_noDecay_le {v v' : ℝ → ℝ}
    (hv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => v z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun z => (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), v z ^ 2 ≤ 20 * (min z 1) ^ 2 *
      ((∫ z in Set.Ioi 0, v z ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi 0, (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  intro z hz
  let I1 : ℝ := ∫ z in Set.Ioi (0 : ℝ), v z ^ 2 * (Work.Spaces.w z) ^ 2
  let I2 : ℝ := ∫ z in Set.Ioi (0 : ℝ), (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2
  set F : ℝ → ℝ := fun y => y * (v y * Work.Spaces.w y) ^ 2 with hF
  set F' : ℝ → ℝ := fun y => 2 * v y * (y * v' y) * (Work.Spaces.w y) ^ 2
          + (v y) ^ 2 * (Work.Spaces.w y) ^ 2 * ((y - 3) / (1 + y)) with hF'
  set G : ℝ → ℝ := fun y => 4 * (v y * Work.Spaces.w y) ^ 2
          + (y * v' y * Work.Spaces.w y) ^ 2 with hG
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hv x hx).continuousAt.continuousWithinAt
  have hwcont : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
    have h : (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) = Work.Spaces.w := by
      funext y; rw [Work.Spaces.w]
    rw [← h]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt hx))
  have hFcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]
    exact continuousOn_id.mul ((hvcont.mul hwcont).pow 2)
  have hderivF : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    exact (noDecayPieces.agmonF_deriv_bnd (v := v) (v' := v') hv x hx).1
  have hmeas : AEStronglyMeasurable F' (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hd : AEStronglyMeasurable (deriv F) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv F volume).restrict
    refine hd.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hderivF x hx).deriv
  have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x := by
    intro x hx
    have h := (noDecayPieces.agmonF_deriv_bnd (v := v) (v' := v') hv x hx).2
    rw [hF', hG]
    exact h
  have hJ1int : IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun hint1 (fun x _ => by ring) measurableSet_Ioi
  have hJ2int : IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun hint2 (fun x _ => by ring) measurableSet_Ioi
  have hG1int : IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    Integrable.const_mul hJ1int 4
  have hG2int : IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) := hJ2int
  have hGint : IntegrableOn G (Set.Ioi 0) := by
    rw [hG]
    exact Integrable.add hG1int hG2int
  have hGnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] G := by
    rw [hG]
    refine Filter.Eventually.of_forall (fun x => ?_)
    show (0 : ℝ) ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2
    nlinarith [sq_nonneg (v x * Work.Spaces.w x), sq_nonneg (x * v' x * Work.Spaces.w x)]
  have hFlower : ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x :=
    noDecayPieces.le_sub_setIntegral_of_deriv_le hFcont hmeas hderivF hbd hGint hGnn hz
  have hFz_le : F z ≤ (∫ t in Set.Ioi 0, G t) := by
    by_contra hcon
    push_neg at hcon
    have hc : 0 < F z - (∫ t in Set.Ioi 0, G t) := by linarith
    refine noDecayPieces.false_of_log_divergence (g := fun x => F x / x)
      (z := z) (c := F z - (∫ t in Set.Ioi 0, G t)) hz hc ?_ ?_ ?_
    · have hEq : Set.EqOn (fun x => v x ^ 2 * (Work.Spaces.w x) ^ 2) (fun x => F x / x)
          (Set.Ioi 0) := by
        intro x hx
        rw [hF]
        rw [eq_div_iff (ne_of_gt hx)]
        ring
      exact MeasureTheory.IntegrableOn.congr_fun hint1 hEq measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      show (0 : ℝ) ≤ F x / x
      rw [hF]
      have h : x * (v x * Work.Spaces.w x) ^ 2 / x = (v x * Work.Spaces.w x) ^ 2 := by
        rw [div_eq_iff (ne_of_gt hx)]
        ring
      rw [h]
      positivity
    · intro x hzx
      have hx0 : 0 < x := lt_of_lt_of_le hz hzx
      exact div_le_div_of_nonneg_right (hFlower x hzx) hx0.le
  have hMrw : (∫ t in Set.Ioi (0 : ℝ), G t)
      = 4 * (∫ t in Set.Ioi (0 : ℝ), (v t * Work.Spaces.w t) ^ 2)
        + (∫ t in Set.Ioi (0 : ℝ), (t * v' t * Work.Spaces.w t) ^ 2) := by
    rw [hG]
    rw [MeasureTheory.integral_add hG1int hG2int, MeasureTheory.integral_const_mul]
  have hJ1 : (∫ t in Set.Ioi (0 : ℝ), (v t * Work.Spaces.w t) ^ 2)
      = (∫ z in Set.Ioi (0 : ℝ), v z ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  have hJ2 : (∫ t in Set.Ioi (0 : ℝ), (t * v' t * Work.Spaces.w t) ^ 2)
      = (∫ z in Set.Ioi (0 : ℝ), (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  have hI1nn : 0 ≤ I1 :=
    MeasureTheory.integral_nonneg (f := fun z => v z ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun x => by positivity)
  have hI2nn : 0 ≤ I2 :=
    MeasureTheory.integral_nonneg (f := fun z => (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun x => by positivity)
  have hprof : z * (v z * Work.Spaces.w z) ^ 2 ≤ 4 * I1 + I2 := by
    have h1 := hFz_le
    rw [hF] at h1
    rw [hMrw, hJ1, hJ2] at h1
    exact h1
  have hK0 : 0 ≤ 4 * I1 + I2 := by linarith [hI1nn, hI2nn]
  have hsq : v z ^ 2 ≤ (4 * I1 + I2) * (min z 1) ^ 2 :=
    noDecayPieces.sq_le_of_profile_le hz hK0 hprof
  have hKle : 4 * I1 + I2 ≤ 20 * (I1 + I2) := by linarith [hI1nn, hI2nn]
  calc v z ^ 2 ≤ (4 * I1 + I2) * (min z 1) ^ 2 := hsq
    _ ≤ (20 * (I1 + I2)) * (min z 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
    _ = 20 * (min z 1) ^ 2 * (I1 + I2) := by ring

end Work.FTS_RegExport.RXT
end
end
