import Mathlib

/-!
# The model-ODE computations behind the model-adapted flow

Two independent groups of *elementary* facts about the quadratic models of the Morse charts.  They
are used both by the model-adapted flow (`Work.Drive.N2.exists_modelAdapted_levelFlow`) and by its
consumer (`Work.Drive.N2.levelSeparatingMap_far`), so they live in this low module.

* `Work.Drive.N2.abs_quadForm_le_norm_sq`, `Work.Drive.N2.sqrt_abs_quadForm_le_norm` — the metric
  lemma `|s₁ y₀² + s₂ y₁²| ≤ ‖y‖²`; on the model level `{Q = δ}` the chart radius is `≥ √|δ|`.
* `Work.Drive.N2.saddle_model_orbit_product_const`, `Work.Drive.N2.saddle_model_orbit_norm_mono`,
  `Work.Drive.N2.definite_model_norm_mono` — along a solution of the model ODE the chart radius is
  *strictly increasing* in `|Q|`: in the saddle case the product `u·v` is conserved and the identity
  `(u²+v²)² = Q² + 4(uv)²` does the job; in the definite cases `Q = ±(u²+v²)` pointwise.

* `Work.Drive.N2.level_law_of_deriv` — the bridge from the *field-level* clause `df (X) = 1` to the
  *integral* level law `f (Φ (t, y)) = f y + t` along a flow segment that avoids the region `U` on
  which `df (X) = 1` may fail.

The two model monotonicity lemmas are stated for the *normalised* model field `∇Q/‖∇Q‖²`
(the chart image of an orbit then solves `u' = (2‖u‖²)⁻¹ ∇Q (u)`); a positive scalar multiple of
that field satisfies the same two differential equations *up to a common positive factor*, which
leaves the invariants `u·v` resp. `Q = ±‖u‖²` intact, so the conclusions below hold verbatim for the
field `(dφ)⁻¹ (μ (‖φ·‖) ∇Q (φ·))` used by `Work.Drive.N2.exists_modelAdapted_levelFlow`. -/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function
open MeasureTheory
open scoped Interval

set_option maxHeartbeats 1600000

/-! ## The metric lemma behind the legality of the transports

For the quadratic model `Q y = s₁ y₀² + s₂ y₁²` (`sᵢ = ±1`) one has `|Q y| ≤ ‖y‖²`; hence on each
level `{Q = δ}` the chart-radius is at least `√|δ|`.  This is the *only* metric input of the
"model-adapted field" design (`NOTES_levelSeparatingMap_far_DESIGN.md` §2): the journeys of the
transports end at reference levels that are `> r²` away from the critical values, so they end outside
the model balls, and the monotonicity of the chart-radius along orbits (for an orbit whose field is
the model field `∇Q/‖∇Q‖²` in the chart) then keeps them outside all along. -/

/-- `|s₁ y₀² + s₂ y₁²| ≤ ‖y‖²` for `sᵢ = ±1`. -/
theorem abs_quadForm_le_norm_sq {s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    |s₁ * y 0 ^ 2 + s₂ * y 1 ^ 2| ≤ ‖y‖ ^ 2 := by
  have h1 : |s₁| = 1 := by rcases hs₁ with h | h <;> simp [h]
  have h2 : |s₂| = 1 := by rcases hs₂ with h | h <;> simp [h]
  have hmain : |s₁ * y 0 ^ 2 + s₂ * y 1 ^ 2| ≤ y 0 ^ 2 + y 1 ^ 2 :=
    calc |s₁ * y 0 ^ 2 + s₂ * y 1 ^ 2| ≤ |s₁ * y 0 ^ 2| + |s₂ * y 1 ^ 2| := abs_add_le _ _
      _ = y 0 ^ 2 + y 1 ^ 2 := by
          rw [abs_mul, abs_mul, h1, h2, one_mul, one_mul,
            abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  have hnorm : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  exact hmain

/-- Consequence: every point of the level `{Q = δ}` has chart-radius `≥ √|δ|`. -/
theorem sqrt_abs_quadForm_le_norm {s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    Real.sqrt |s₁ * y 0 ^ 2 + s₂ * y 1 ^ 2| ≤ ‖y‖ :=
  Real.sqrt_le_iff.mpr ⟨norm_nonneg y, abs_quadForm_le_norm_sq hs₁ hs₂ y⟩


/-! ## The chart computation behind the model monotonicity

`NOTES_levelSeparatingMap_far_DESIGN.md` §3 requires the model-adapted flow to satisfy: along an
orbit whose chart coordinates solve the model ODE `u' = (2‖(u,v)‖²)⁻¹ s₁u`, `v' = (2‖(u,v)‖²)⁻¹ s₂v`,
the chart-radius is a *strictly increasing function of `|Q|`*, `Q = s₁u² + s₂v²`.

Here is the computation, stated for an arbitrary solution of the ODE (no manifolds, no flow):

* in the **saddle** case (`s₁ = -s₂`, the only case where the estimate is not vacuous) the product
  `u·v` is conserved, and the algebraic identity `(u²+v²)² = Q² + 4(uv)²` turns that into the
  monotonicity;
* in the **definite** cases (`s₁ = s₂`) one has `Q = ±(u²+v²)` pointwise, so the monotonicity is a
  tautology. -/

/-- Saddle model ODE: the product of the coordinates is conserved. -/
theorem saddle_model_orbit_product_const {u v : ℝ → ℝ} {s₁ s₂ : ℝ} (hs : s₁ + s₂ = 0)
    (hu : ∀ t, HasDerivAt u ((2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₁ * u t)) t)
    (hv : ∀ t, HasDerivAt v ((2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₂ * v t)) t)
    (hne : ∀ t, u t ^ 2 + v t ^ 2 ≠ 0) :
    ∀ t, u t * v t = u 0 * v 0 := by
  have hderiv : ∀ t, HasDerivAt (fun s => u s * v s) 0 t := by
    intro t
    have h := (hu t).mul (hv t)
    have hρ : (2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₁ * u t) * v t
        + u t * ((2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₂ * v t)) = 0 := by
      have h2 : (2 * (u t ^ 2 + v t ^ 2)) ≠ 0 := by
        have := hne t; positivity
      field_simp
      ring_nf
      linear_combination (u t * v t * (u t ^ 2 + v t ^ 2)⁻¹) * hs
    exact h.congr_deriv hρ
  have h' : ∀ t, deriv (fun s => u s * v s) t = 0 := fun t => (hderiv t).deriv
  exact fun t => is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt) h' t 0

/-- Saddle model ODE: the chart-radius is strictly increasing in `|Q|`. -/
theorem saddle_model_orbit_norm_mono {u v : ℝ → ℝ} {s₁ s₂ : ℝ}
    (h1 : s₁ = 1 ∨ s₁ = -1) (h2 : s₂ = 1 ∨ s₂ = -1) (hs : s₁ + s₂ = 0)
    (hu : ∀ t, HasDerivAt u ((2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₁ * u t)) t)
    (hv : ∀ t, HasDerivAt v ((2 * (u t ^ 2 + v t ^ 2))⁻¹ * (s₂ * v t)) t)
    (hne : ∀ t, u t ^ 2 + v t ^ 2 ≠ 0) :
    ∀ t₁ t₂, |s₁ * u t₁ ^ 2 + s₂ * v t₁ ^ 2| < |s₁ * u t₂ ^ 2 + s₂ * v t₂ ^ 2| →
      Real.sqrt (u t₁ ^ 2 + v t₁ ^ 2) < Real.sqrt (u t₂ ^ 2 + v t₂ ^ 2) := by
  intro t₁ t₂ h
  have hprod := saddle_model_orbit_product_const hs hu hv hne
  have hs2 : s₂ ^ 2 = 1 := by rcases h2 with hh | hh <;> rw [hh] <;> norm_num
  have hs' : s₁ = -s₂ := by linarith
  -- the algebraic identity `(u²+v²)² = Q² + 4(uv)²` in the saddle case
  have hid : ∀ (a b : ℝ), (a ^ 2 + b ^ 2) ^ 2 = (s₁ * a ^ 2 + s₂ * b ^ 2) ^ 2 + 4 * (a * b) ^ 2 := by
    intro a b
    have h3 : (-s₂ * a ^ 2 + s₂ * b ^ 2) = s₂ * (b ^ 2 - a ^ 2) := by ring
    rw [hs', h3, mul_pow, hs2, one_mul]
    ring
  have hP : ∀ t, (u t ^ 2 + v t ^ 2) ^ 2
      = (s₁ * u t ^ 2 + s₂ * v t ^ 2) ^ 2 + 4 * (u 0 * v 0) ^ 2 := by
    intro t
    rw [hid, hprod t]
  have hQ : (s₁ * u t₁ ^ 2 + s₂ * v t₁ ^ 2) ^ 2 < (s₁ * u t₂ ^ 2 + s₂ * v t₂ ^ 2) ^ 2 := by
    rw [sq_lt_sq]
    exact h
  have hlt : (u t₁ ^ 2 + v t₁ ^ 2) ^ 2 < (u t₂ ^ 2 + v t₂ ^ 2) ^ 2 := by
    rw [hP t₁, hP t₂]
    linarith
  have hsq : u t₁ ^ 2 + v t₁ ^ 2 < u t₂ ^ 2 + v t₂ ^ 2 := by
    nlinarith [hlt, sq_nonneg (u t₁), sq_nonneg (v t₁), sq_nonneg (u t₂), sq_nonneg (v t₂)]
  exact Real.sqrt_lt_sqrt (by positivity) hsq

/-- Definite model case (`s₁ = s₂ = ±1`): `Q = ±(u²+v²)` *pointwise*, so the monotonicity of the
chart-radius in `|Q|` is immediate (no ODE needed). -/
theorem definite_model_norm_mono {u v : ℝ → ℝ} {s₁ s₂ : ℝ} (hs : s₁ = s₂)
    (h1 : s₁ = 1 ∨ s₁ = -1) :
    ∀ t₁ t₂, |s₁ * u t₁ ^ 2 + s₂ * v t₁ ^ 2| < |s₁ * u t₂ ^ 2 + s₂ * v t₂ ^ 2| →
      Real.sqrt (u t₁ ^ 2 + v t₁ ^ 2) < Real.sqrt (u t₂ ^ 2 + v t₂ ^ 2) := by
  have e : ∀ t, |s₁ * u t ^ 2 + s₂ * v t ^ 2| = u t ^ 2 + v t ^ 2 := by
    intro t
    have hpos : (0 : ℝ) ≤ u t ^ 2 + v t ^ 2 := by
      nlinarith [sq_nonneg (u t), sq_nonneg (v t)]
    rw [← hs]
    rcases h1 with hh | hh
    · rw [hh]; simp [abs_of_nonneg hpos]
    · rw [hh]
      rw [show (-1) * u t ^ 2 + (-1) * v t ^ 2 = -(u t ^ 2 + v t ^ 2) from by ring, abs_neg,
        abs_of_nonneg hpos]
  intro t₁ t₂ h
  rw [e t₁, e t₂] at h
  exact Real.sqrt_lt_sqrt (by positivity) h


/-- **The level law from the derivative.**  If the flow `Φ` is the flow of a field with `df (X) = 1`
off `U`, and a flow segment starting at `y` avoids `U`, then `f` increases at unit speed along it:
`f (Φ (t, y)) = f y + t`.  (The `hzero` clause is needed for `t = 0`.) -/
theorem level_law_of_deriv {M : Type*} [TopologicalSpace M] {Φ : ℝ × M → M} {f : M → ℝ}
    {U : Set M} {y : M} {t : ℝ}
    (hf : Continuous f)
    (horb : Continuous fun s : ℝ => Φ (s, y))
    (hzero : ∀ z : M, Φ (0, z) = z)
    (hsemi : ∀ a b : ℝ, Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hderiv : ∀ z : M, z ∉ U → HasDerivAt (fun s : ℝ => f (Φ (s, z))) 1 0)
    (hav : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∉ U) :
    f (Φ (t, y)) = f y + t := by
  have hderivAt : ∀ x ∈ Set.uIcc 0 t, HasDerivAt (fun s : ℝ => f (Φ (s, y))) 1 x := by
    intro x hx
    have hxU : Φ (x, y) ∉ U := hav x hx
    have H : HasDerivAt (fun s : ℝ => f (Φ (s, Φ (x, y)))) 1 0 := hderiv (Φ (x, y)) hxU
    have heq : (fun s : ℝ => f (Φ (s, Φ (x, y)))) = fun s : ℝ => f (Φ (s + x, y)) := by
      funext s
      rw [hsemi s x]
    rw [heq] at H
    have H' : HasDerivAt (fun s : ℝ => f (Φ (s + x, y))) 1 (x - x) := by simpa using H
    have hinner : HasDerivAt (fun r : ℝ => r - x) 1 x := (hasDerivAt_id x).sub_const x
    have hcomp := HasDerivAt.comp (h := fun r : ℝ => r - x) (x := x) H' hinner
    have hfun : ((fun s : ℝ => f (Φ (s + x, y))) ∘ fun r : ℝ => r - x)
        = fun s : ℝ => f (Φ (s, y)) := by
      funext s
      simp only [Function.comp_apply, sub_add_cancel]
    rw [hfun] at hcomp
    simpa using hcomp
  have hint : ∫ (s : ℝ) in (0)..t, (1 : ℝ) = f (Φ (t, y)) - f (Φ (0, y)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivAt intervalIntegrable_const
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hint
  rw [hzero y] at hint
  linarith

end Work.Drive.N2
