import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bound `|D_θ^j (c2m)| ≤ 1000 · sin(2θ)²`, `1 ≤ j ≤ 4`

`Work.Construction.c2m θ = cos(2θ) - sin²θ = (3cos(2θ) - 1)/2` is the angular
coefficient multiplying the transport term of the linearised equation, and
`Work.Spaces.dthU = sin(2θ)·∂_θ` is the one-variable angular derivation `D_θ`.

Since `c2m` is a trigonometric polynomial of degree two, every iterate `D_θ^j c2m`
with `j ≥ 1` is `sin(2θ)²` times a polynomial in `cos(2θ)`, hence `O(sin(2θ)²)`.
For the four orders `1 ≤ j ≤ 4` needed here the closed forms are completely
explicit: writing `u = sin(2θ)`, `v = cos(2θ)`,

* `D_θ c2m = -3u²`,
* `D_θ² c2m = -12u²v`,
* `D_θ³ c2m = 24u⁴ - 48u²v²`,
* `D_θ⁴ c2m = 384u⁴v - 192u²v³`,

and each is bounded by `1000·u²` using only `u² + v² = 1` (the crude bounds are
`3`, `12`, `72` and `576`).

The closed forms are obtained by explicit differentiation: `c2m'(θ) = -3 sin(2θ)`,
and each subsequent step differentiates a polynomial in `u` and `v` with
`u' = 2v`, `v' = -2u`, so that `D_θ f = u·f'`.
-/

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Real

/-! ## The derivative of `c2m` -/

/-- `c2m'(θ) = -3·sin(2θ)`, where `c2m θ = cos(2θ) - sin²θ`. -/
lemma dthU_c2m_deriv (θ : ℝ) : deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) := by
  have hsub : HasDerivAt (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2)
      (-3 * Real.sin (2 * θ)) θ := by
    have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    have hfin : HasDerivAt (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2)
        (-Real.sin (2 * θ) * 2 - 2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) θ := hc.sub hs
    rw [show (-3 * Real.sin (2 * θ))
        = (-Real.sin (2 * θ) * 2 - 2 * (Real.sin θ) ^ (2 - 1) * Real.cos θ) from by
      rw [Real.sin_two_mul]; ring]
    exact hfin
  exact hsub.deriv

/-- The first iterate: `D_θ c2m = -3 sin(2θ)²`. -/
lemma dthU_c2m_eq : Work.Spaces.dthU Work.Construction.c2m
    = fun θ => -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_deriv θ]
  ring

/-! ## The derivatives of the successive closed forms -/

/-- `(θ ↦ -3 sin(2θ)²)'(θ) = -12 sin(2θ)cos(2θ)`. -/
lemma dthU_c2m_f1_deriv (θ : ℝ) :
    deriv (fun t : ℝ => -(3 : ℝ) * (Real.sin (2 * t)) ^ 2) θ
      = -12 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hp : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc : HasDerivAt (fun t : ℝ => -(3 : ℝ) * (Real.sin (2 * t)) ^ 2)
      (-(3 : ℝ) * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hp.const_mul (-3)
  rw [hc.deriv]
  ring

/-- The second iterate: `D_θ² c2m = -12 sin(2θ)²cos(2θ)`. -/
lemma dthU_c2m_f1_eq : Work.Spaces.dthU (fun θ => -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2)
    = fun θ => -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f1_deriv θ]
  ring

/-- `(θ ↦ -12 sin(2θ)²cos(2θ))'(θ) = -48 sin(2θ)cos(2θ)² + 24 sin(2θ)³`. -/
lemma dthU_c2m_f2_deriv (θ : ℝ) :
    deriv (fun t : ℝ => -(12 : ℝ) * (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t)) θ
      = -48 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 2 + 24 * (Real.sin (2 * θ)) ^ 3 := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
  have hp : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hm : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))
      ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ))
        + (Real.sin (2 * θ)) ^ 2 * (-Real.sin (2 * θ) * 2)) θ := hp.mul hc
  have hfin : HasDerivAt (fun t : ℝ => -(12 : ℝ) * ((Real.sin (2 * t)) ^ 2 * Real.cos (2 * t)))
      (-(12 : ℝ) * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ))
        + (Real.sin (2 * θ)) ^ 2 * (-Real.sin (2 * θ) * 2))) θ := hm.const_mul (-12)
  rw [show (fun t : ℝ => -(12 : ℝ) * (Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))
      = (fun t : ℝ => -(12 : ℝ) * ((Real.sin (2 * t)) ^ 2 * Real.cos (2 * t))) from by
        ext t; ring,
    hfin.deriv]
  ring

/-- The third iterate: `D_θ³ c2m = 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²`. -/
lemma dthU_c2m_f2_eq :
    Work.Spaces.dthU (fun θ => -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      = fun θ => (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
          - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f2_deriv θ]
  ring

/-- `(θ ↦ 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²)'(θ) = 384 sin(2θ)³cos(2θ) - 192 sin(2θ)cos(2θ)³`. -/
lemma dthU_c2m_f3_deriv (θ : ℝ) :
    deriv (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2) θ
      = 384 * (Real.sin (2 * θ)) ^ 3 * Real.cos (2 * θ)
        - 192 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 3 := by
  have h : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h.cos
  have hp4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hp2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hq2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hA : HasDerivAt (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4)
      (24 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hp4.const_mul 24
  have hB : HasDerivAt (fun t : ℝ => (48 : ℝ) * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2))
      (48 * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ)) ^ 2
        + (Real.sin (2 * θ)) ^ 2 * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)))) θ :=
    (hp2.mul hq2).const_mul 48
  have hfin : HasDerivAt (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2))
      (24 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))
        - 48 * ((2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) * (Real.cos (2 * θ)) ^ 2
          + (Real.sin (2 * θ)) ^ 2 * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)))) θ :=
    hA.sub hB
  rw [show (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2)
      = (fun t : ℝ => (24 : ℝ) * (Real.sin (2 * t)) ^ 4
        - 48 * ((Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 2)) from by ext t; ring,
    hfin.deriv]
  ring

/-- The fourth iterate: `D_θ⁴ c2m = 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³`. -/
lemma dthU_c2m_f3_eq :
    Work.Spaces.dthU (fun θ => (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
        - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
      = fun θ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
          - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3 := by
  funext θ
  rw [Work.Spaces.dthU_apply, dthU_c2m_f3_deriv θ]
  ring

/-! ## The four iterates, as values -/

/-- `D_θ c2m θ = -3 sin(2θ)²`. -/
lemma dthU_c2m_iter_one (θ : ℝ) :
    (Work.Spaces.dthU^[1]) Work.Construction.c2m θ = -(3 : ℝ) * (Real.sin (2 * θ)) ^ 2 := by
  rw [Function.iterate_one, dthU_c2m_eq]

/-- `D_θ² c2m θ = -12 sin(2θ)²cos(2θ)`. -/
lemma dthU_c2m_iter_two (θ : ℝ) :
    (Work.Spaces.dthU^[2]) Work.Construction.c2m θ
      = -(12 : ℝ) * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq]

/-- `D_θ³ c2m θ = 24 sin(2θ)⁴ - 48 sin(2θ)²cos(2θ)²`. -/
lemma dthU_c2m_iter_three (θ : ℝ) :
    (Work.Spaces.dthU^[3]) Work.Construction.c2m θ
      = (24 : ℝ) * (Real.sin (2 * θ)) ^ 4
        - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq, dthU_c2m_f2_eq]

/-- `D_θ⁴ c2m θ = 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³`. -/
lemma dthU_c2m_iter_four (θ : ℝ) :
    (Work.Spaces.dthU^[4]) Work.Construction.c2m θ
      = (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
    dthU_c2m_eq, dthU_c2m_f1_eq, dthU_c2m_f2_eq, dthU_c2m_f3_eq]

/-! ## The four pointwise bounds -/

/-- `|D_θ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_one_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[1]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_one]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have h3 : |(-(3 : ℝ))| = 3 := by norm_num
  rw [h3]
  nlinarith [sq_nonneg (Real.sin (2 * θ))]

/-- `|D_θ² c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_two_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[2]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_two]
  have hv : |Real.cos (2 * θ)| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have h12 : |(-(12 : ℝ))| = 12 := by norm_num
  rw [h12]
  nlinarith [sq_nonneg (Real.sin (2 * θ)), hv, abs_nonneg (Real.cos (2 * θ))]

/-- `|D_θ³ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_three_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[3]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_three]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hkey : (24 : ℝ) * (Real.sin (2 * θ)) ^ 4 - 48 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2
      = (Real.sin (2 * θ)) ^ 2 * (24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hX : |24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2| ≤ 1000 := by
    rw [abs_le]
    constructor <;> nlinarith
  calc (Real.sin (2 * θ)) ^ 2
        * |24 * (Real.sin (2 * θ)) ^ 2 - 48 * (Real.cos (2 * θ)) ^ 2|
      ≤ (Real.sin (2 * θ)) ^ 2 * 1000 := mul_le_mul_of_nonneg_left hX (sq_nonneg _)
    _ = 1000 * (Real.sin (2 * θ)) ^ 2 := by ring

/-- `|D_θ⁴ c2m θ| ≤ 1000 sin(2θ)²`. -/
lemma dthU_c2m_iter_four_bound (θ : ℝ) :
    |(Work.Spaces.dthU^[4]) Work.Construction.c2m θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_four]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hkey : (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      = (Real.sin (2 * θ)) ^ 2
        * (384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hv : |Real.cos (2 * θ)| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [sq_nonneg (Real.sin (2 * θ)), Real.sin_sq_add_cos_sq (2 * θ)]
  have hA : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)| ≤ 384 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
    have h384 : |(384 : ℝ)| = 384 := by norm_num
    rw [h384]
    have hm : (Real.sin (2 * θ)) ^ 2 * |Real.cos (2 * θ)| ≤ 1 := by
      nlinarith [hu2, hv, sq_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]
    nlinarith [hm, sq_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]
  have hB : |192 * (Real.cos (2 * θ)) ^ 3| ≤ 192 := by
    rw [abs_mul, abs_pow]
    have h192 : |(192 : ℝ)| = 192 := by norm_num
    rw [h192]
    have hm : |Real.cos (2 * θ)| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
    nlinarith [hm, abs_nonneg (Real.cos (2 * θ))]
  have htri : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)| + |192 * (Real.cos (2 * θ)) ^ 3| := by
    have h := abs_add_le (384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ))
      (-(192 * (Real.cos (2 * θ)) ^ 3))
    simpa [sub_eq_add_neg] using h
  have hX : |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ 1000 := by
    linarith
  calc (Real.sin (2 * θ)) ^ 2
        * |384 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) - 192 * (Real.cos (2 * θ)) ^ 3|
      ≤ (Real.sin (2 * θ)) ^ 2 * 1000 := mul_le_mul_of_nonneg_left hX (sq_nonneg _)
    _ = 1000 * (Real.sin (2 * θ)) ^ 2 := by ring

/-- **The angular bound for the iterated `D_θ`-derivatives of `c2m`.**  For `1 ≤ j ≤ 4`
and every `θ : ℝ`, `|D_θ^j (c2m) θ| ≤ 1000 · sin(2θ)²`. -/
theorem dthU_c2m_bound (j : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4) (θ : ℝ) :
    |(Work.Spaces.dthU^[j] Work.Construction.c2m) θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  interval_cases j
  · exact dthU_c2m_iter_one_bound θ
  · exact dthU_c2m_iter_two_bound θ
  · exact dthU_c2m_iter_three_bound θ
  · exact dthU_c2m_iter_four_bound θ

end Work.FTS.Nonlinear.FstarPkg
