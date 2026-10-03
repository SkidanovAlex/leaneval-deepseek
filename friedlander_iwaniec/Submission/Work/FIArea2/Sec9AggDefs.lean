/-
# The §9 aggregate: the objects and the plan

*FI* §9 bounds the per-pair error of (9.1) summed over the polar box:

  `D*(M,N) − D₀(M,N) = O(ϑ^{-1}τ²N²(log N)^b)`    (9.10),

and the heart of the section is the estimate of the `h`-weighted lattice sum (9.5)

  `Z(h₁,h₂) = Σ_{(z₁,z₂)=1} |β_{z₁}β_{z₂}|τ(Δ)³(Λ,Δ)|Δ|^{-1}`,  `Λ = z₁h₁² − z₂h₂²`,

together with the weighted `h`-sum (9.7) of the "lacunarity" quantity `L(r₁,r₂)`.

This file names the two objects the aggregate is built from, so that the per-frequency bound
(`Work.FIArea2.Count.sec9_Z_bound`) and the assembly can be stated in one vocabulary:

* `sec9Uwt Pa h` — the (9.2) weight `(1+h₁²H^{-2})^{-1}(1+h₂²H^{-2})^{-1}`, `H = Hscale M N`;
* `sec9Usum Pa z₁ z₂` — the *uniform* `H(z₁,z₂)` of (9.2)/(9.3), the `h ≠ 0` sum of
  `(Λ,Δ)·sec9Uwt`, which dominates `Haver` by `Haver_le_uniform` (up to the factor `64`);
* `IsAxisFree Pa z` — the axis-avoidance of §5, `√(ϑN) < |Re z|, |Im z|` (the paper: "we can
  assume `|φ mod π/2| > πϑ` because the other sectors contribute no more than (4.23) by (5.16)").
  Without it the `(s₁,s₂)`-count `O(1 + ρ|I|/|r₁|)` of §9 loses `ϑ^{-1/2}`; the near-axis sectors
  are a `B`-level statement, not a `D`-level one.

The two inputs the aggregate consumes (both delegated with exact statements):

* `Work.FIArea2.Count.sec9_Z_bound` — the per-frequency bound
  `Σ_{(z,z') ∈ B², axis-free} τ(Δ)³|Δ|^{-1}(Λ,Δ) ≤ C ϑ^{-1/2}(log N)^K Σ_{(u,u') ∈ I²} (u,u')τ₄(uh₁²−u'h₂²)`
  (the paper's chain "group by `(Λ,Δ) = d`" + the `(s₁,s₂)`-count + the divisor sum along `d ∣ Δ`
  + `Σ_{d|Λ}τ(d)³ ≤ τ(Λ)^4`, with the symmetry `r ↔ s` handling `Λ(r₁,r₂) = 0`);
* `Work.FIArea2.Count.Lsum_plus_le` — the companion of `Lsum_le` for the *sum* form
  `τ₄(r₁h₁² + r₂h₂²)`, needed for the mixed-sign ranges of `Σ_{r₁,r₂}`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.Haver_le_uniform

set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **§5 axis-avoidance**: `√(ϑN) < |Re z|` and `√(ϑN) < |Im z|` — the paper's
"`|φ mod π/2| > πϑ`", the reduction that keeps the polar box away from both coordinate axes and
makes the `(s₁,s₂)`-count of §9 uniform in `ϑ^{-1/2}`. -/
def IsAxisFree (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Real.sqrt (Pa.ϑ * Pa.N) < |(z.re : ℝ)| ∧ Real.sqrt (Pa.ϑ * Pa.N) < |(z.im : ℝ)|

/-- The (9.2) weight of one frequency: `(1+h₁²H^{-2})^{-1}(1+h₂²H^{-2})^{-1}` with
`H = Hscale M N`. -/
def sec9Uwt (Pa : Work.FITop.Params) (h1 h2 : ℤ) : ℝ :=
  (1 + (h1 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
    * (1 + (h2 : ℝ) ^ 2 / (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹

/-- **The uniform `H(z₁,z₂)` of (9.2)/(9.3)**: the `h ≠ 0` sum of `(Λ,Δ)` against the *uniform*
weight `(1+h_j²H^{-2})^{-1}`, `H = M^{-1/4}N^{3/4}`.  By `Haver_le_uniform`, the true (9.2) weight
`Haver` (which carries Lemma 7.1's `(1+h_j²secWeight_j)^{-1}`) is at most `64` times this. -/
def sec9Usum (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else
    (gcdDelta z1 z2 h.1 h.2 : ℝ) * sec9Uwt Pa h.1 h.2)

lemma sec9Uwt_nonneg (Pa : Work.FITop.Params) (h1 h2 : ℤ) : 0 ≤ sec9Uwt Pa h1 h2 := by
  unfold sec9Uwt
  have h1' : (0:ℝ) ≤ 1 + (h1 : ℝ)^2 / (Work.FIPlan.Hscale Pa.M Pa.N)^2 := by positivity
  have h2' : (0:ℝ) ≤ 1 + (h2 : ℝ)^2 / (Work.FIPlan.Hscale Pa.M Pa.N)^2 := by positivity
  exact mul_nonneg (inv_nonneg.mpr h1') (inv_nonneg.mpr h2')

lemma sec9Usum_nonneg (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : 0 ≤ sec9Usum Pa z1 z2 :=
  tsum_nonneg fun h => by
    by_cases hh : h = (0,0)
    · simp [hh]
    · rw [if_neg hh]
      exact mul_nonneg (Nat.cast_nonneg _) (sec9Uwt_nonneg Pa h.1 h.2)

/-- The §9 pair weight `τ(Δ)³|Δ|^{−1}`, restricted to the coprime, axis-free pairs of the box:
the indicator-times-weight factor shared by `sec9Psum`, `sec9Psum0` and `sec9Zsum`. -/
def sec9Core (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ IsAxisFree Pa z1 ∧ IsAxisFree Pa z2 then
    (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
      / (Work.FIPlan.absDelta z1 z2 : ℝ))
  else 0

/-- The §9 pair sum of (9.5) without the coefficients: `Σ_{(z₁,z₂)} τ(Δ)³|Δ|^{−1}H(z₁,z₂)`, i.e.
`sec9Psum` with `‖β_{z₁}β_{z₂}‖` replaced by `1`. -/
def sec9Psum0 (Pa : Work.FITop.Params) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    sec9Core Pa z1 z2 * sec9Usum Pa z1 z2

/-- The §9 *pair sum*: the weight `|β_{z₁}β_{z₂}|τ(Δ)³|Δ|^{-1}` against the uniform `h`-sum,
restricted to the coprime, axis-free pairs of the box. -/
def sec9Psum (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    ‖β z1‖ * ‖β z2‖ * sec9Core Pa z1 z2 * sec9Usum Pa z1 z2


/-- **The per-frequency weight sum of *FI* §9 (9.5)** without the coefficients:
`Σ_{axis-free (z₁,z₂) ∈ B²} τ(Δ)³|Δ|^{−1}(Λ,Δ)`, `Λ = z₁h₁² − z₂h₂²`.  This is the left-hand side
of `Work.FIArea2.Count.sec9_Z_bound`; it is packaged as a `def` so that its statement does not
depend on the local `Classical.propDecidable` instance. -/
def sec9Zsum (Pa : Work.FITop.Params) (h1 h2 : ℤ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ IsAxisFree Pa z1 ∧ IsAxisFree Pa z2 then
      (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3
        / (Work.FIPlan.absDelta z1 z2 : ℝ)) * (gcdDelta z1 z2 h1 h2 : ℝ)
    else 0)

/-- The right-hand side of `Work.FIArea2.Count.sec9_Z_bound`: the `(u₁,u₂)`-sum of the coordinates
of the outer box weighted by `(|u₁|,|u₂|)τ₄(u₁h₁²−u₂h₂²)`. -/
def sec9Usumming (Pa : Work.FITop.Params) (h1 h2 : ℤ) : ℝ :=
  ∑ u1 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
   ∑ u2 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
    (Nat.gcd u1.natAbs u2.natAbs : ℝ)
      * (((u1 * h1 ^ 2 - u2 * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)

/-- `sec9Zsum` in the `sec9Core` form (definitional unfolding). -/
theorem sec9Zsum_eq (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    sec9Zsum Pa h1 h2
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          sec9Core Pa z1 z2 * (gcdDelta z1 z2 h1 h2 : ℝ) := by
  unfold sec9Zsum sec9Core
  refine Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  by_cases h : Work.FIPlan.GaussCoprime z1 z2 ∧ IsAxisFree Pa z1 ∧ IsAxisFree Pa z2 <;>
    simp [h]

end

end Work.FIArea2
