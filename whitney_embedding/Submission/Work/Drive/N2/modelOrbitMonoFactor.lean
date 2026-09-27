import Mathlib
import Submission.Work.Drive.N2.modelOrbitMono

/-!
# Model monotonicity with an arbitrary time factor

Along a solution of the model equations `u' = lam * (s₁ * u)`, `v' = lam * (s₂ * v)` the chart
radius `√(u² + v²)` is a strictly increasing function of `|Q|`, `Q = s₁ u² + s₂ v²`, for an
*arbitrary* factor `lam` (no positivity, no normalisation): in the definite case (`s₁ = s₂`) the
relation is pointwise (`Q = ±(u² + v²)`), in the saddle case `u·v` is conserved along the interval
and `(u² + v²)² = Q² + 4 (u v)²`.
-/

open scoped Manifold ContDiff Topology
open Set

namespace Work.Drive.N2

/-- The algebraic identity behind the saddle case: for `s₁, s₂ ∈ {±1}` with `s₁ + s₂ = 0`,
`(u² + v²)² = (s₁ u² + s₂ v²)² + 4 (u v)²`. -/
lemma sq_add_sq_eq_quadForm_saddle {a b s₁ s₂ : ℝ} (h1 : s₁ = 1 ∨ s₁ = -1)
    (h2 : s₂ = 1 ∨ s₂ = -1) (hs : s₁ + s₂ = 0) :
    (a ^ 2 + b ^ 2) ^ 2 = (s₁ * a ^ 2 + s₂ * b ^ 2) ^ 2 + 4 * (a * b) ^ 2 := by
  rcases h1 with h | h <;> rcases h2 with h' | h' <;> rw [h, h'] at hs ⊢ <;>
    (try norm_num at hs) <;> ring

/-- Model monotonicity with an arbitrary time factor `lam`: if `(u, v)` solves the model equations
`u' = lam * (s₁ * u)`, `v' = lam * (s₂ * v)` on the interval between `t₁` and `t₂`, then the chart
radius `√(u ^ 2 + v ^ 2)` is a strictly increasing function of `|Q|`, `Q = s₁ u ^ 2 + s₂ v ^ 2`. -/
theorem model_orbit_norm_mono_of_factor {u v lam : ℝ → ℝ} {s₁ s₂ t₁ t₂ : ℝ}
    (h1 : s₁ = 1 ∨ s₁ = -1) (h2 : s₂ = 1 ∨ s₂ = -1)
    (hu : ∀ t ∈ Set.Icc (min t₁ t₂) (max t₁ t₂), HasDerivAt u (lam t * (s₁ * u t)) t)
    (hv : ∀ t ∈ Set.Icc (min t₁ t₂) (max t₁ t₂), HasDerivAt v (lam t * (s₂ * v t)) t) :
    |s₁ * u t₁ ^ 2 + s₂ * v t₁ ^ 2| < |s₁ * u t₂ ^ 2 + s₂ * v t₂ ^ 2| →
      Real.sqrt (u t₁ ^ 2 + v t₁ ^ 2) < Real.sqrt (u t₂ ^ 2 + v t₂ ^ 2) := by
  intro h
  have hQ : (s₁ * u t₁ ^ 2 + s₂ * v t₁ ^ 2) ^ 2 < (s₁ * u t₂ ^ 2 + s₂ * v t₂ ^ 2) ^ 2 :=
    sq_lt_sq.mpr h
  have hs₁2 : s₁ ^ 2 = 1 := by rcases h1 with h | h <;> rw [h] <;> norm_num
  -- the square of the chart radius is strictly increasing in the square of `Q`
  have hsq : (u t₁ ^ 2 + v t₁ ^ 2) ^ 2 < (u t₂ ^ 2 + v t₂ ^ 2) ^ 2 := by
    by_cases hsame : s₁ = s₂
    · have he : ∀ t, s₁ * u t ^ 2 + s₂ * v t ^ 2 = s₁ * (u t ^ 2 + v t ^ 2) := by
        intro t; rw [hsame]; ring
      have h2' : (s₁ * (u t₁ ^ 2 + v t₁ ^ 2)) ^ 2 < (s₁ * (u t₂ ^ 2 + v t₂ ^ 2)) ^ 2 := by
        rw [← he t₁, ← he t₂]; exact hQ
      rwa [mul_pow, mul_pow, hs₁2, one_mul, one_mul] at h2'
    · have hsaddle : s₁ + s₂ = 0 := by
        rcases h1 with h | h <;> rcases h2 with h' | h' <;> rw [h, h'] at hsame ⊢ <;>
          first | exact absurd rfl hsame | norm_num
      have hid : ∀ t, (u t ^ 2 + v t ^ 2) ^ 2
          = (s₁ * u t ^ 2 + s₂ * v t ^ 2) ^ 2 + 4 * (u t * v t) ^ 2 :=
        fun t => sq_add_sq_eq_quadForm_saddle (a := u t) (b := v t) h1 h2 hsaddle
      have hconst : u t₁ * v t₁ = u t₂ * v t₂ := by
        have hderiv : ∀ t ∈ Set.uIcc t₁ t₂, HasDerivAt (fun s => u s * v s) 0 t := by
          intro t ht
          have ht' : t ∈ Set.Icc (min t₁ t₂) (max t₁ t₂) := ht
          have hprod := (hu t ht').mul (hv t ht')
          have hzero : lam t * (s₁ * u t) * v t + u t * (lam t * (s₂ * v t)) = 0 := by
            have : lam t * (s₁ * u t) * v t + u t * (lam t * (s₂ * v t))
                = lam t * (u t * v t) * (s₁ + s₂) := by ring
            rw [this, hsaddle, mul_zero]
          exact hprod.congr_deriv hzero
        have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          intervalIntegrable_const
        rw [intervalIntegral.integral_zero] at hint
        linarith
      rw [hid t₁, hid t₂, hconst]
      linarith [hQ]
  -- conclude from the squares
  have hlt : u t₁ ^ 2 + v t₁ ^ 2 < u t₂ ^ 2 + v t₂ ^ 2 := by
    have := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at this
  exact Real.sqrt_lt_sqrt (by positivity) hlt

end Work.Drive.N2
