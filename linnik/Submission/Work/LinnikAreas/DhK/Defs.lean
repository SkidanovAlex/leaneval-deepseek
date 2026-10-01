import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Commons.NumberTheory.Zeta.xiE_circle_growth
import Submission.Commons.NumberTheory.Zeta.xiE_zeroCount
import Submission.Commons.NumberTheory.Zeta.xiE_noZero_ball

/-!
# `Work.LinnikAreas.DhK.Defs`

Shared vocabulary for the Deuring–Heilbronn repulsion argument carried out by Turán's power-sum
method (Kadiri–Ng–Wong, arXiv:1902.08640, §2) via the quadratic field `K` with
`ζ_K(s) = ζ(s)·L(s, χ₀*)`, where `χ₀*` is the primitive real character inducing a real `χ₀`.

The non-trivial zeros of `ζ_K` are

* the non-trivial zeros of `ζ`, i.e. the zeros of the entire completion
  `Ξ(s) = 1/2 + (1/2)·s(s-1)·Λ₀(s)` (`Xi` below, an entire genus-one function with `Ξ 0 = 1/2`), and
* the non-trivial zeros of `L(·,χ₀*)`, i.e. the zeros of `completedLFunction χ₀*`,

each counted with multiplicity; `kMult` records the sum of the two multiplicities.

NOTE (import hygiene): this file deliberately does **not** import
`Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq` (nor anything importing
`Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect`), because that module and
`Submission.Commons.NumberTheory.Linnik.logDeriv_pf_identity` both declare
`Commons.NumberTheory.Linnik.pfP`; importing both is impossible.  Everything here lives in the
`P3`/`logDeriv_pf_identity` world plus the neutral zeta-growth modules.
-/

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.DhK

/-- The entire completion `Ξ` of the Riemann zeta function,
`Ξ(s) = 1/2 + (1/2)·s(s-1)·Λ₀(s)`.  It is entire, `Ξ 0 = Ξ 1 = 1/2 ≠ 0`, satisfies
`Ξ(1-s) = Ξ(s)`, and its zeros are exactly the non-trivial zeros of `ζ` with multiplicities.
(Definitionally the same function as `Commons.NumberTheory.Zeta.XiPF.xiF`.) -/
def Xi (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

@[simp] lemma Xi_zero : Xi 0 = 1 / 2 := by simp [Xi]

lemma Xi_zero_ne : Xi 0 ≠ 0 := by rw [Xi_zero]; norm_num

/-- `Ξ` has no zeros in the half-plane `Re s > 1`. -/
lemma Xi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : Xi s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h1; rw [h1] at hs; norm_num at hs
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro hz
    exact riemannZeta_ne_zero_of_one_lt_re hs
      (by rw [riemannZeta_def_of_ne_zero hs0, hz, zero_div])
  have hΛ₀ : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [h]; ring
  have hEQ : Xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
    rw [Xi, hΛ₀]
    field_simp
    ring
  have hfac : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
  rw [hEQ] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact hfac h'
  · exact hΛ h'


/-- Every zero of `Ξ` has real part at most `1`. -/
lemma Xi_zero_re_le_one {u : ℂ} (h : Xi u = 0) : u.re ≤ 1 := by
  by_contra hc
  exact Xi_ne_zero_of_one_lt_re (lt_of_not_ge hc) h

/-- The multiplicity of `u` as a non-trivial zero of the Dedekind zeta function `ζ_K` of the
quadratic field attached to a real primitive Dirichlet character `χ` of conductor `N`: the sum of
the vanishing orders of `u` as a zero of `Ξ` and as a zero of `completedLFunction χ`. -/
def kMult {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℂ) : ℕ :=
  analyticOrderNatAt Xi u + analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u

/-- The ball-truncated multiplicity of `u` as a non-trivial zero of `ζ_K`: the sum of the vanishing
orders of `u` as a zero of `Ξ` and of `completedLFunction χ`, restricted to the closed ball of
radius `R` (as a natural number, so that the ball sums below are sums of non-negative terms). -/
def kMultTrunc {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (R : ℝ) (u : ℂ) : ℕ :=
  (MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u).toNat +
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) u).toNat

/-- The complex power `m²/(c+it-u)²` used in Turán's power-sum method for the zeros of `ζ_K`. -/
def zPow (m c t : ℝ) (u : ℂ) : ℂ := ((m : ℂ) ^ 2) / ((c : ℂ) + Complex.I * (t : ℂ) - u) ^ 2


/-- The multiplicity-weighted sum of `Re (1/(s-u)^k)` over the non-trivial zeros `u` of `ζ_K`,
i.e. over the zeros of `Ξ` and of `completedLFunction χ` with multiplicity.  (The family is
summable for `k ≥ 1` since all such zeros have `Re u < 1` and the zero count is `≪ T log(NT)`.) -/
noncomputable def zeroSumRe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (k : ℕ) : ℝ :=
  ∑' u : ℂ, (kMult χ u : ℝ) * ((1 / (s - u)) ^ k).re


/-- The multiplicity of `u` as a non-trivial zero of `ζ_K`, with the point `β₀` (the exceptional
real zero, written as a complex number) excluded. -/
def kMultNe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₀ : ℝ) (u : ℂ) : ℕ :=
  if u = (β₀ : ℂ) then 0 else kMult χ u

/-- The Turán power sum `∑_{u} kMult χ u · [Re (1/(c-u))^{2j} + Re (1/(c+iγ'-u))^{2j}]`, i.e. the
multiplicity-weighted real part of the power sums of `(1/(c-u))²` and `(1/(c+iγ'-u))²` at the
exponent `j`. -/
noncomputable def zeroSumPos {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₀ : ℝ)
    (c γ' : ℝ) (j : ℕ) : ℝ :=
  ∑' u : ℂ, (kMultNe χ β₀ u : ℝ) *
    (((1 / ((c : ℂ) - u)) ^ (2 * j)).re + ((1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u)) ^ (2 * j)).re)


end Work.LinnikAreas.DhK

end
