/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment condition `∫ Θ_n sin θ cos²θ = 0` for `n ≥ 2`

`Work.FTS.EllipticEst.LevelOneAsm.eigFun_moment`: for the angular eigenfunctions
`Θ_n(θ) = cos θ · p_n(sin θ)`, `p_n(u) = Σ_{k<n} c_k u^{2k+1}` of `EigBasis`, one has

  `∫_{Iθ} Θ_n(θ) · sin θ cos²θ dθ = 0`  for `n ≥ 2`.

This is the statement that the eigenfunctions other than the kernel mode `n = 1` are
orthogonal to the moment profile `sin θ cos²θ` — the condition that removes the kernel of
`Lzero` from the elliptic problem (see the header of `EigBasis`).

## The proof

Let `v(θ) = p_n(sin θ)`, so that the integrand is `Θ_n · sinθcos²θ = v(θ) · sinθ cos³θ`.
The eigenpolynomial satisfies the *Jacobi* (associated Legendre) equation

  `(1 - u²) p_n''(u) - 4u p_n'(u) + (4 + λ_n) p_n(u) = 0`,   `λ_n = 4(n-1)² + 10(n-1)`,

which is exactly the content of the recurrence `c_{k+1}(2k+3)(2k+2) = c_k(4k² + 10k - λ_n)`
defining `eigCoef`.  In θ-form this reads `-v'' + 3 tan θ · v' - 4v = λ_n v`, i.e. with
`Mv := -v'' + 3 tanθ · v' - 4v` one has `Mv = λ_n v`.

The point is then that `M` is *formally self-adjoint* against the weight
`w(θ) = sin θ cos³θ` with Dirichlet data: for every `v`,

  `∫_0^{π/2} (Mv)(θ) · w(θ) dθ = -v(0)`,

because `(Mv)·w` is the derivative of the explicit primitive

  `P(θ) = -v'(θ)·sinθcos³θ + v(θ)·cos⁴θ`.

(`P' = -v''w + v'(cos⁴ - w') - 4v sinθcos³` and `cos⁴ - w' = 3sin²θcos²θ`, so
`P' = (-v'' + 3tanθ·v' - 4v)·w`.)  Since `v(0) = p_n(0) = 0`, integrating gives
`λ_n ∫_0^{π/2} v·w = 0`, and `λ_n ≠ 0` for `n ≥ 2` (indeed `λ_n ≥ 14`) finishes the proof.

The formal second derivative is written in the *unshifted* form `eigMomD2 n u =
Σ_k c_k (2k+1)(2k) u^{2k-1}`; the identity `eigMom_ode` is then proved by telescoping:
the coefficient of `u^{2k-1}` in `(1-u²)p'' + …` coming from the `k`-th term is exactly
`c_k(2k+1)(2k) = c_{k-1}(4(k-1)² + 10(k-1) - λ_n)`, i.e. it cancels the `u^{2k-1}`-coefficient
of the `(k-1)`-st term, leaving only the boundary monomials `a_0 = 0` and `a_n = 0`.
-/
import Mathlib
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open Finset MeasureTheory Set

noncomputable section

namespace Work.FTS.EllipticEst.LevelOneAsm

/-- `a_k = c_k (2k+1)(2k)`: the coefficient of `u^{2k-1}` in `(eigPoly n)''`, and also the
coefficient of `u^{2k+1}` in `-4u (eigPoly n)' + (4 + λ) (eigPoly n)` combined with the
shifted `u^{2k+1}`-part of `(1-u²)(eigPoly n)''`. -/
private def eigA (n k : ℕ) : ℝ := eigCoef n k * (2*(k:ℝ)+1) * (2*(k:ℝ))

/-- `b_k = c_k (2k+1)`: the coefficient of `u^{2k}` in `(eigPoly n)'`. -/
private def eigB (n k : ℕ) : ℝ := eigCoef n k * (2*(k:ℝ)+1)

/-- The formal first derivative polynomial of `eigPoly n`: `Σ_{k<n} c_k (2k+1) u^{2k}`. -/
def eigMomD (n : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Finset.range n, eigB n k * u ^ (2*k)

/-- The formal second derivative polynomial of `eigPoly n`:
`Σ_{k<n} c_k (2k+1)(2k) u^{2k-1}` (the `k = 0` term is `0`). -/
def eigMomD2 (n : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Finset.range n, eigA n k * u ^ (2*k-1)

/-- The recurrence for the eigencoefficients, in the form used by the telescoping:
`a_{k+1} = a_k + 4 b_k - (4 + λ_n) c_k`. -/
private lemma eigA_shift (n k : ℕ) :
    eigA n (k+1) = eigA n k + 4*eigB n k - (4 + eigLam n) * eigCoef n k := by
  unfold eigA eigB
  push_cast
  rw [show eigCoef n (k+1) = eigCoef n k *
      ((4*(k:ℝ)^2+10*(k:ℝ)-eigLam n)/((2*(k:ℝ)+3)*(2*(k:ℝ)+2))) from by simp [eigCoef]]
  have h : ((2*(k:ℝ)+3)*((2*(k:ℝ)+2))) ≠ 0 := by positivity
  field_simp
  ring

/-- The top coefficient vanishes: `c_m = 0` (the recurrence has the eigenvalue as a root). -/
private lemma eigCoef_self (m : ℕ) (hm : 1 ≤ m) : eigCoef m m = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [show eigCoef (n+1) (n+1) = eigCoef (n+1) n *
      ((4*(n:ℝ)^2+10*(n:ℝ)-eigLam (n+1))/((2*(n:ℝ)+3)*(2*(n:ℝ)+2))) from by simp [eigCoef]]
  rw [show (4*(n:ℝ)^2+10*(n:ℝ)-eigLam (n+1)) = 0 from by
    rw [eigLam, eigLamNat]; push_cast; ring]
  ring

private lemma eigA_zero (n : ℕ) : eigA n 0 = 0 := by simp [eigA]

private lemma eigA_top (n : ℕ) : eigA (n+1) (n+1) = 0 := by
  simp only [eigA]
  rw [eigCoef_self (n+1) (by omega)]
  ring

/-- **The Jacobi equation for the eigenpolynomial**:
`(1-u²) p_n''(u) - 4u p_n'(u) + (4 + λ_n) p_n(u) = 0`. -/
theorem eigMom_ode (n : ℕ) (u : ℝ) :
    (1 - u^2) * eigMomD2 n u - 4*u*eigMomD n u + (4 + eigLam n) * eigPoly n u = 0 := by
  rcases n with _ | n
  · simp [eigMomD2, eigMomD, eigPoly]
  rw [eigMomD2, eigMomD, eigPoly]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [show (∑ k ∈ Finset.range (n+1),
        ((1 - u^2) * (eigA (n+1) k * u ^ (2*k-1)) - 4*u*(eigB (n+1) k * u^(2*k))
          + (4 + eigLam (n+1)) * (eigCoef (n+1) k * u ^ (2*k+1))))
      = ∑ k ∈ Finset.range (n+1),
          (eigA (n+1) k * u^(2*k-1) - eigA (n+1) (k+1) * u^(2*(k+1)-1))
    from Finset.sum_congr rfl (fun k _ => by
      have hp1 : u ^ 2 * (eigA (n+1) k * u ^ (2*k-1)) = eigA (n+1) k * u ^ (2*k+1) := by
        rcases k with _ | k
        · simp [eigA]
        · rw [show 2*(k+1)-1 = 2*k+1 from by omega,
              show 2*(k+1)+1 = 2 + (2*k+1) from by omega, pow_add]
          ring
      have hp2 : (4*u)*(eigB (n+1) k * u ^ (2*k)) = 4*(eigB (n+1) k * u ^ (2*k+1)) := by
        have huu : u * u ^ (2*k) = u ^ (2*k+1) := by rw [← pow_succ']
        calc (4*u)*(eigB (n+1) k * u ^ (2*k))
            = 4*(eigB (n+1) k * (u * u ^ (2*k))) := by ring
          _ = 4*(eigB (n+1) k * u ^ (2*k+1)) := by rw [huu]
      have hp3 : u ^ (2*(k+1)-1) = u ^ (2*k+1) := by congr 1
      rw [hp3, eigA_shift, sub_mul, one_mul, hp1, hp2]
      ring)]
  rw [Finset.sum_range_sub']
  simp [eigA_zero, eigA_top]

/-- `eigMomD n` is the derivative of `eigPoly n`. -/
lemma hasDerivAt_eigMom (n : ℕ) (u : ℝ) : HasDerivAt (eigPoly n) (eigMomD n u) u := by
  unfold eigPoly eigMomD
  have h : ∀ k ∈ Finset.range n,
      HasDerivAt (fun y : ℝ => eigCoef n k * y ^ (2 * k + 1))
        (eigB n k * u ^ (2 * k)) u := by
    intro k _
    have h1 : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
        ((2 * k + 1 : ℕ) * u ^ (2 * k + 1 - 1)) u := hasDerivAt_pow (2*k+1) u
    have h2 := h1.const_mul (eigCoef n k)
    convert h2 using 1
    unfold eigB; push_cast; ring
  have hsum := HasDerivAt.sum h
  have hfun : (∑ i ∈ Finset.range n, fun y : ℝ => eigCoef n i * y ^ (2 * i + 1))
      = fun y : ℝ => ∑ i ∈ Finset.range n, eigCoef n i * y ^ (2 * i + 1) := by
    funext y; rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- `eigMomD2 n` is the derivative of `eigMomD n`. -/
lemma hasDerivAt_eigMomD (n : ℕ) (u : ℝ) : HasDerivAt (eigMomD n) (eigMomD2 n u) u := by
  unfold eigMomD eigMomD2
  have h : ∀ k ∈ Finset.range n,
      HasDerivAt (fun y : ℝ => eigB n k * y ^ (2 * k)) (eigA n k * u ^ (2*k-1)) u := by
    intro k _
    have h1 : HasDerivAt (fun y : ℝ => y ^ (2 * k)) ((2 * k : ℕ) * u ^ (2 * k - 1)) u :=
      hasDerivAt_pow (2*k) u
    have h2 := h1.const_mul (eigB n k)
    convert h2 using 1
    unfold eigA eigB; push_cast; ring
  have hsum := HasDerivAt.sum h
  have hfun : (∑ i ∈ Finset.range n, fun y : ℝ => eigB n i * y ^ (2 * i))
      = fun y : ℝ => ∑ i ∈ Finset.range n, eigB n i * y ^ (2 * i) := by
    funext y; rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The primitive of `λ_n · Θ_n · sinθcos²θ`:
`P(θ) = -v'(θ)·sinθcos³θ + v(θ)·cos⁴θ` with `v = p_n(sin θ)`; its derivative is
`(-v'' + 3 tanθ · v' - 4v)·sinθcos³θ = λ_n · v(θ)·sinθcos³θ = λ_n · Θ_n(θ)·sinθcos²θ`. -/
def eigMomPrim (n : ℕ) (θ : ℝ) : ℝ :=
  -((eigMomD n (Real.sin θ) * Real.cos θ) * (Real.sin θ * Real.cos θ ^ 3))
    + eigPoly n (Real.sin θ) * Real.cos θ ^ 4

/-- **The key identity**: `d/dθ [eigMomPrim n] θ = λ_n · Θ_n(θ) · sinθcos²θ`. -/
lemma hasDerivAt_eigMomPrim (n : ℕ) (θ : ℝ) :
    HasDerivAt (eigMomPrim n) (eigLam n * (eigFun n θ * (Real.sin θ * Real.cos θ ^ 2))) θ := by
  unfold eigMomPrim eigFun
  have hA : HasDerivAt (fun t => eigPoly n (Real.sin t))
      (eigMomD n (Real.sin θ) * Real.cos θ) θ := by
    have h := (hasDerivAt_eigMom n (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)
    simpa [Function.comp_def] using h
  have hB : HasDerivAt (fun t => eigMomD n (Real.sin t) * Real.cos t)
      (eigMomD2 n (Real.sin θ) * Real.cos θ ^ 2 - eigMomD n (Real.sin θ) * Real.sin θ) θ := by
    have h1 : HasDerivAt (fun t => eigMomD n (Real.sin t))
        (eigMomD2 n (Real.sin θ) * Real.cos θ) θ := by
      have h := (hasDerivAt_eigMomD n (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)
      simpa [Function.comp_def] using h
    refine (h1.mul (Real.hasDerivAt_cos θ)).congr_deriv ?_
    ring
  have hw : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 3)
      (Real.cos θ ^ 4 - 3 * Real.sin θ ^ 2 * Real.cos θ ^ 2) θ := by
    have h := (hasDerivAt_pow 3 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
    have hc3 : HasDerivAt (fun t => Real.cos t ^ 3) (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      refine h.congr_deriv ?_
      ring_nf
    refine ((Real.hasDerivAt_sin θ).mul hc3).congr_deriv ?_
    ring
  have hq : HasDerivAt (fun t => Real.cos t ^ 4) (-4 * Real.sin θ * Real.cos θ ^ 3) θ := by
    have h := (hasDerivAt_pow 4 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
    refine h.congr_deriv ?_
    ring_nf
  have hmain := (((hB.mul hw).neg).add (hA.mul hq))
  refine hmain.congr_deriv ?_
  have hode := eigMom_ode n (Real.sin θ)
  have hc2 : (1 - Real.sin θ ^ 2) = Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  rw [hc2] at hode
  linear_combination (-(Real.sin θ * Real.cos θ^3)) * hode

/-- `p_n(0) = 0` (`p_n` is a sum of odd powers). -/
lemma eigMomPoly_zero (n : ℕ) : eigPoly n 0 = 0 := by
  simp only [eigPoly]
  apply Finset.sum_eq_zero
  intro k _
  have : (0:ℝ) ^ (2*k+1) = 0 := by
    apply zero_pow
    omega
  rw [this, mul_zero]

lemma eigMomPrim_zero (n : ℕ) : eigMomPrim n 0 = 0 := by
  simp [eigMomPrim, eigMomPoly_zero]

lemma eigMomPrim_pi2 (n : ℕ) : eigMomPrim n (π/2) = 0 := by
  simp [eigMomPrim]

/-- **The moment condition**: for `n ≥ 2` the eigenfunction `Θ_n = eigFun n` is orthogonal
to the profile `sin θ cos²θ` of the solvability condition. -/
theorem eigFun_moment (n : ℕ) (hn : 2 ≤ n) :
    ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.LevelOneAsm.eigFun n θ *
        (Real.sin θ * Real.cos θ ^ 2) = 0 := by
  have hle : (0:ℝ) ≤ π/2 := by positivity
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (π/2),
      HasDerivAt (eigMomPrim n) (eigLam n * (eigFun n x * (Real.sin x * Real.cos x ^ 2))) x :=
    fun x _ => hasDerivAt_eigMomPrim n x
  have hc1 : Continuous (eigPoly n) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_eigMom n u).continuousAt
  have hce : Continuous (eigFun n) := by
    change Continuous (fun θ : ℝ => Real.cos θ * eigPoly n (Real.sin θ))
    exact Real.continuous_cos.mul (hc1.comp Real.continuous_sin)
  have hcont : Continuous fun x : ℝ => eigLam n * (eigFun n x * (Real.sin x * Real.cos x ^ 2)) :=
    continuous_const.mul (hce.mul (Real.continuous_sin.mul (Real.continuous_cos.pow 2)))
  have hint : IntervalIntegrable
      (fun x : ℝ => eigLam n * (eigFun n x * (Real.sin x * Real.cos x ^ 2))) volume 0 (π/2) :=
    hcont.intervalIntegrable 0 (π/2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [eigMomPrim_pi2, eigMomPrim_zero, sub_zero, intervalIntegral.integral_const_mul] at hFTC
  have hlam : eigLam n ≠ 0 := by
    have : (0:ℝ) < eigLam n := by
      rw [eigLam, eigLamNat]
      have h1 : 1 ≤ n := by omega
      have h2 : (1:ℝ) ≤ (n:ℝ) - 1 := by
        have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      push_cast [Nat.cast_sub h1]
      nlinarith [sq_nonneg ((n:ℝ)-1)]
    exact ne_of_gt this
  have hkey : ∫ θ in (0:ℝ)..π/2, eigFun n θ * (Real.sin θ * Real.cos θ ^ 2) = 0 := by
    rcases mul_eq_zero.mp hFTC with h | h
    · exact absurd h hlam
    · exact h
  rw [← hkey]
  change ∫ θ in Set.Icc (0:ℝ) (π/2), eigFun n θ * (Real.sin θ * Real.cos θ ^ 2)
      = ∫ θ in (0:ℝ)..π/2, eigFun n θ * (Real.sin θ * Real.cos θ ^ 2)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

end Work.FTS.EllipticEst.LevelOneAsm
