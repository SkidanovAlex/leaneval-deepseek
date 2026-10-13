/-
# `Work.FTS.PhiStar.Gegenbauer.gC_orthogonal_half` — orthogonality of `gC` on the half interval

`gC n = C^{(3/2)}_n` is the Gegenbauer polynomial of order `3/2` (see `Defs.lean`), which
satisfies the Gegenbauer equation

  `(1-x²) q'' - 4x q' + n(n+3) q = 0`   (`gC_ode`),

whose self-adjoint form is

  `d/dx [(1-x²)² q'] = -n(n+3) (1-x²) q`   (`hasDerivAt_gC_weight`).

**The target.**  For `p ≠ q` of the *same parity* (`Even (p+q)`),

  `∫_0^1 (1-x²) gC p x gC q x dx = 0`.

The parity hypothesis is necessary: for `p = 0`, `q = 1` the integral is `3/4`.

**The route.**  Integrate `gC p · (1-x²)² (gC q)'` by parts on `[0,1]`.  The endpoint `x = 1`
contributes nothing since `(1-x²)² = 0` there; the endpoint `x = 0` contributes the boundary
term `gC p 0 · deriv (gC q) 0`.  Using the self-adjoint form of the equation for `gC q` this
gives the identity

  `q(q+3) · I = J + gC p 0 · deriv (gC q) 0`,
  `I = ∫_0^1 (1-x²) gC p gC q`,  `J = ∫_0^1 (gC p)' (1-x²)² (gC q)'`.

Two observations finish the argument:

* the *boundary terms vanish* in both orders when `p + q` is even: if `n` is odd then
  `gC n 0 = 0` (`gC_odd_zero`), and if `n` is even then `deriv (gC n) 0 = 0`
  (`deriv_gC_even_zero`, from the ladder relation `D_n` at `x = 0` together with
  `gC_odd_zero`).  Hence `p(p+3) I = J` *and* `q(q+3) I = J`, so
  `(p(p+3) - q(q+3)) I = 0`.
* `k ↦ k(k+3)` is strictly increasing (`eig_ne`), so `p ≠ q` forces `p(p+3) ≠ q(q+3)`, and
  therefore `I = 0`.

(This is the half-interval companion of the full-interval orthogonality; the `e_m = cos θ ·
gC (2m+1) (sin θ)` orthogonality of `eFam_orthogonal` is the odd-odd case transported by
`u = sin θ`.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The derivative of `gC n` at the origin -/

/-- The ladder relation `D_n` of `Gegenbauer/gC_ode`, evaluated at `x = 0`:
`deriv (gC n) 0 = (n + 2) · gC (n-1) 0` for `n ≥ 1`. -/
lemma deriv_gC_zero (n : ℕ) (hn : 1 ≤ n) :
    deriv (gC n) 0 = ((n : ℝ) + 2) * gC (n - 1) 0 := by
  have h := Erel_all (n - 1) 0
  have h1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [Erel, h1, Drel] at h
  ring_nf at h
  linarith

/-- For an even index the derivative of `gC` at the origin vanishes: `gC (2m)` is an even
polynomial.  (`n = 2m` is even and `n - 1 = 2(m-1) + 1` is odd, hence `gC (n-1) 0 = 0`.) -/
lemma deriv_gC_even_zero (m : ℕ) : deriv (gC (2 * m)) 0 = 0 := by
  cases m with
  | zero =>
    rw [show gC (2 * 0) = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  | succ k =>
    rw [deriv_gC_zero (2 * (k + 1)) (by omega)]
    have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h3, gC_odd_zero k]
    ring

/-! ## Integration by parts on the half interval -/

/-- Integration by parts for the Gegenbauer self-adjoint form on `[0,1]`, assuming that the
boundary term at the origin vanishes:

  `q(q+3) ∫_0^1 (1-x²) gC p gC q = ∫_0^1 (gC p)' (1-x²)² (gC q)' + gC p 0 · deriv (gC q) 0`,

and with `hbc : gC p 0 · deriv (gC q) 0 = 0` the boundary term is dropped.  The endpoint at
`x = 1` contributes nothing because `(1-x²)²` vanishes there. -/
lemma ibp_gC_half (p q : ℕ) (hbc : gC p 0 * deriv (gC q) 0 = 0) :
    ((q : ℝ) * ((q : ℝ) + 3)) *
        (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u)
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
  have hc : Continuous (fun u : ℝ => (1 - u ^ 2) * gC q u) :=
    (continuous_const.sub (continuous_id.pow 2)).mul (contDiff_gC q).continuous
  have hcont : Continuous (fun u : ℝ =>
      -(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - u ^ 2) * gC q u))) :=
    (continuous_const.mul hc).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => gC p u) (u' := fun u : ℝ => deriv (gC p) u)
    (v := fun u : ℝ => (1 - u ^ 2) ^ 2 * deriv (gC q) u)
    (v' := fun u : ℝ => -(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - u ^ 2) * gC q u)))
    (a := 0) (b := 1)
    (fun x _ => ((contDiff_gC p).differentiable (by norm_num)).differentiableAt.hasDerivAt)
    (fun x _ => hasDerivAt_gC_weight q x)
    (((contDiff_gC p).continuous_deriv (by norm_num)).intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)
  have h1 : (1 - ((1 : ℝ)) ^ 2) ^ 2 * deriv (gC q) 1 = 0 := by norm_num
  have h0 : (1 - ((0 : ℝ)) ^ 2) ^ 2 * deriv (gC q) 0 = deriv (gC q) 0 := by norm_num
  rw [h1, h0, mul_zero, hbc] at h
  have hL : (∫ x in (0 : ℝ)..1, gC p x *
        (-(((q : ℝ) * ((q : ℝ) + 3)) * ((1 - x ^ 2) * gC q x))))
      = -(((q : ℝ) * ((q : ℝ) + 3))) *
        ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hL] at h
  linarith

/-! ## The eigenvalues `k(k+3)` are distinct -/

/-- `k ↦ k(k+3)` is strictly increasing, so `p ≠ q` implies `p(p+3) ≠ q(q+3)`: the eigenvalues
attached to `gC p` and `gC q` differ. -/
lemma eig_ne {p q : ℕ} (hpq : p ≠ q) :
    (p : ℝ) * ((p : ℝ) + 3) ≠ (q : ℝ) * ((q : ℝ) + 3) := by
  have hstep : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) + 3)
      < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 3) := by
    intro k
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  exact fun h => hpq ((strictMono_nat_of_lt_succ hstep).injective h)

/-! ## The target -/

theorem gC_orthogonal_half (p q : ℕ) (hpq : p ≠ q) (hpar : Even (p + q)) :
    ∫ x in (0 : ℝ)..1,
        (1 - x ^ 2) * Work.FTS.PhiStar.Gegenbauer.gC p x
          * Work.FTS.PhiStar.Gegenbauer.gC q x = 0 := by
  -- `p` and `q` have the same parity
  have hsame : Even p ↔ Even q := Nat.even_add.mp hpar
  -- the boundary term of the integration by parts vanishes, in both orders
  have hbc1 : gC p 0 * deriv (gC q) 0 = 0 := by
    rcases Nat.even_or_odd q with hq | hq
    · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp hq
      rw [deriv_gC_even_zero n, mul_zero]
    · by_cases hp : Even p
      · exact absurd (hsame.mp hp) (Nat.not_even_iff_odd.mpr hq)
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hp
        rw [hk, gC_odd_zero k, zero_mul]
  have hbc2 : gC q 0 * deriv (gC p) 0 = 0 := by
    rcases Nat.even_or_odd p with hp | hp
    · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp hp
      rw [deriv_gC_even_zero n, mul_zero]
    · by_cases hq : Even q
      · exact absurd (hsame.mpr hq) (Nat.not_even_iff_odd.mpr hp)
      · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hq
        rw [hk, gC_odd_zero k, zero_mul]
  -- the two integration-by-parts identities
  have h1 := ibp_gC_half p q hbc1
  have h2 := ibp_gC_half q p hbc2
  -- symmetrise the two identities to a common integral
  have hU : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC q u * gC p u)
      = ∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hJ : (∫ u in (0 : ℝ)..1, deriv (gC q) u * ((1 - u ^ 2) ^ 2 * deriv (gC p) u))
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have h2' : ((p : ℝ) * ((p : ℝ) + 3)) *
        (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u)
      = ∫ u in (0 : ℝ)..1, deriv (gC p) u * ((1 - u ^ 2) ^ 2 * deriv (gC q) u) := by
    rw [← hU, ← hJ]
    exact h2
  -- both eigenvalues multiply the same integral, so their difference does too
  have hkey : (((p : ℝ) * ((p : ℝ) + 3)) - ((q : ℝ) * ((q : ℝ) + 3))) *
      (∫ u in (0 : ℝ)..1, (1 - u ^ 2) * gC p u * gC q u) = 0 := by
    rw [sub_mul, h2', h1]
    ring
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd h (sub_ne_zero.mpr (eig_ne hpq))
  · exact h

end Work.FTS.PhiStar.Gegenbauer
