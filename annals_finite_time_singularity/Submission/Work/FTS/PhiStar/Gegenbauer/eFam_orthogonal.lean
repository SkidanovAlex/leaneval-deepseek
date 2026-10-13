/-
# `Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal` — orthogonality of the Dirichlet basis

The Dirichlet eigenfunctions of `Work.Elliptic.Lzero` are

  `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`  (`= cos θ · gC (2m+1) (sin θ)`),

with eigenvalues `lam m = 2m(2m+5)` (`eFam_Lzero`).  This file proves that they are mutually
orthogonal with respect to the self-adjoint weight `cos θ dθ`:

  `∫_0^{π/2} eFam m θ · eFam n θ · cos θ dθ = 0`  for `m ≠ n`.

**The route.**  Substituting `u = sin θ` (`cos θ dθ = du`, `θ ∈ (0, π/2) ↦ u ∈ (0, 1)`) and
using `cos²θ = 1 - sin²θ` turns the integral into the classical Gegenbauer scalar product with
weight `(1-u²)`:

  `∫_0^{π/2} e_m e_n cos θ dθ = ∫_0^1 (1-u²) gC(2m+1)(u) gC(2n+1)(u) du`.

For the latter, the self-adjoint form of the Gegenbauer equation `(1-x²)q'' - 4xq' + n(n+3)q = 0`
(`gC_ode`) is `-((1-x²)² q')' = n(n+3)(1-x²)q`.  Integrating by parts against `gC(2m+1)`
respectively `gC(2n+1)`, whose values at `x = 0` vanish (odd indices, `gC_odd_zero`), gives the
*two* identities

  `(2m+1)(2m+4) · I = J`,   `(2n+1)(2n+4) · I = J`,
  `I = ∫_0^1 (1-u²) gC(2m+1) gC(2n+1)`,  `J = ∫_0^1 (1-u²)² gC(2m+1)' gC(2n+1)'`,

whence `((2m+1)(2m+4) - (2n+1)(2n+4)) · I = 0`.  The eigenvalues differ for `m ≠ n`
(`odd_shift_ne`: `k ↦ (2k+1)(2k+4)` is strictly increasing), so `I = 0`.

The heavy analytic tool is the Mathlib change-of-variables and integration-by-parts API for
interval integrals (`intervalIntegral.integral_comp_mul_deriv`,
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

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
