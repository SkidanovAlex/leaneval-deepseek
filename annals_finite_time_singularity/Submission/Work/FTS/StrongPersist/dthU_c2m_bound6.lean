import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bound `|D_θ^j (c2m)| ≤ 100000 · sin(2θ)²` for `1 ≤ j ≤ 6`

`Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound` supplies the four orders `1 ≤ j ≤ 4` for the
angular coefficient `Work.Construction.c2m θ = cos(2θ) - sin²θ` of the transport term.  This
file adds the two remaining orders `j = 5, 6` needed by
`Work.FTS.StrongPersist.dthU_c2m_bound6`.

With `u = sin(2θ)`, `v = cos(2θ)` (so that `c2m = (3v-1)/2`, `u' = 2v`, `v' = -2u` and
`D_θ = u ∂_θ`), the closed forms are

* `D_θ^5 c2m = 4224 u⁴v² - 768 u⁶ - 768 u²v⁴ = u²(4224 u²v² - 768 u⁴ - 768 v⁴)`, whence
  `|D_θ^5 c2m| ≤ 5760 u²` (only `|u|, |v| ≤ 1` are used);
* `D_θ^6 c2m = 39936 u⁴v³ - 26112 u⁶v - 3072 u²v⁵ = u²(39936 u²v³ - 26112 u⁴v - 3072 v⁵)`,
  whence `|D_θ^6 c2m| ≤ 69120 u²`.

The derivatives are obtained by explicit differentiation (`HasDerivAt` on the two
trigonometric factors), as in `dthU_c2m_bound`.
-/

namespace Work.FTS.StrongPersist

open Work.Spaces

/-! ## The fifth iterate `D_θ^5 c2m` -/

/-- `(θ ↦ 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³)' = 4224 sin(2θ)³cos(2θ)²
- 768 sin(2θ)⁵ - 768 sin(2θ)cos(2θ)⁴`. -/
private lemma dthU_c2m_f4_deriv (θ : ℝ) :
    deriv (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3) θ
      = 4224 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 5
        - 768 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 4 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hA : HasDerivAt (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
      ((384 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (384 * (Real.sin (2 * θ)) ^ 4) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs4.const_mul 384).mul hc
  have hB : HasDerivAt (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      ((192 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (192 * (Real.sin (2 * θ)) ^ 2)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 192).mul hc3
  have hfin := hA.sub hB
  rw [show (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      = ((fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
        - (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)) from by
    funext t; rfl,
    hfin.deriv]
  ring

/-- `D_θ (384 u⁴v - 192 u²v³) = 4224 u⁴v² - 768 u⁶ - 768 u²v⁴`. -/
private lemma dthU_f4_eq :
    dthU (fun θ : ℝ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      = fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
          - 768 * (Real.sin (2 * θ)) ^ 6
          - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  funext θ
  rw [dthU_apply, dthU_c2m_f4_deriv θ]
  ring

/-! ## The sixth iterate `D_θ^6 c2m` -/

/-- `(θ ↦ 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴)' =
39936 sin(2θ)³cos(2θ)³ - 26112 sin(2θ)⁵cos(2θ) - 3072 sin(2θ)cos(2θ)⁵`. -/
private lemma dthU_c2m_f5_deriv (θ : ℝ) :
    deriv (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4) θ
      = 39936 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 5 * Real.cos (2 * θ)
        - 3072 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 5 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hv2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hv4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hA : HasDerivAt (fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
      ((4224 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 2
        + (4224 * (Real.sin (2 * θ)) ^ 4)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 4224).mul hv2
  have hB : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6)
      (768 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs6.const_mul 768
  have hC : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      ((768 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 4
        + (768 * (Real.sin (2 * θ)) ^ 2)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 768).mul hv4
  have hfin := (hA.sub hB).sub hC
  rw [show (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      = (((fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
          - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6))
        - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)) from by
    funext t; rfl,
    hfin.deriv]
  ring

/-- `D_θ (4224 u⁴v² - 768 u⁶ - 768 u²v⁴) = 39936 u⁴v³ - 26112 u⁶v - 3072 u²v⁵`. -/
private lemma dthU_f5_eq :
    dthU (fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4)
      = fun θ : ℝ => 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
          - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  funext θ
  rw [dthU_apply, dthU_c2m_f5_deriv θ]
  ring

/-! ## The two iterates, as values -/

/-- `D_θ^5 c2m = 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴`. -/
private lemma dthU_c2m_iter_five (θ : ℝ) :
    (dthU^[5]) Work.Construction.c2m θ
      = 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_f4_eq]

/-- `D_θ^6 c2m = 39936 sin(2θ)⁴cos(2θ)³ - 26112 sin(2θ)⁶cos(2θ) - 3072 sin(2θ)²cos(2θ)⁵`. -/
private lemma dthU_c2m_iter_six (θ : ℝ) :
    (dthU^[6]) Work.Construction.c2m θ
      = 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_f4_eq, dthU_f5_eq]

/-! ## The two pointwise bounds -/

/-- `|c · u^a · v^b| ≤ c` when `c ≥ 0` and `|u|, |v| ≤ 1`. -/
private lemma abs_mul_pow_pow_le {c u v : ℝ} (hc : 0 ≤ c) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (a b : ℕ) : |c * u ^ a * v ^ b| ≤ c := by
  have h1 : |u| ^ a ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
  have h2 : |v| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg v) hv
  have hp : |u| ^ a * |v| ^ b ≤ 1 := by
    have := mul_le_mul h1 h2 (pow_nonneg (abs_nonneg v) b) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc |c * u ^ a * v ^ b| = c * (|u| ^ a * |v| ^ b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_pow, abs_pow]; ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hp hc
    _ = c := by ring

/-- `|D_θ^5 c2m θ| ≤ 100000 sin(2θ)²`. -/
private lemma dthU_c2m_iter_five_bound (θ : ℝ) :
    |(dthU^[5]) Work.Construction.c2m θ| ≤ 100000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_five]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hu4 : (Real.sin (2 * θ)) ^ 4 ≤ 1 := by
    nlinarith [hu2, sq_nonneg (Real.sin (2 * θ))]
  have hv4 : (Real.cos (2 * θ)) ^ 4 ≤ 1 := by
    nlinarith [hv2, sq_nonneg (Real.cos (2 * θ))]
  have huv : (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [hu2, hv2, sq_nonneg (Real.sin (2 * θ)), sq_nonneg (Real.cos (2 * θ))]
  have hkey : (4224 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4
      = (Real.sin (2 * θ)) ^ 2
        * (4224 * ((Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
          - 768 * (Real.sin (2 * θ)) ^ 4 - 768 * (Real.cos (2 * θ)) ^ 4) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hX : |(4224 : ℝ) * ((Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
      - 768 * (Real.sin (2 * θ)) ^ 4 - 768 * (Real.cos (2 * θ)) ^ 4| ≤ 100000 := by
    rw [abs_le]
    constructor <;>
      nlinarith [huv, hu4, hv4, sq_nonneg (Real.sin (2 * θ)), sq_nonneg (Real.cos (2 * θ)),
        mul_nonneg (sq_nonneg (Real.sin (2 * θ))) (sq_nonneg (Real.cos (2 * θ)))]
  have := mul_le_mul_of_nonneg_left hX (sq_nonneg (Real.sin (2 * θ)))
  linarith [this]

/-- `|D_θ^6 c2m θ| ≤ 100000 sin(2θ)²`. -/
private lemma dthU_c2m_iter_six_bound (θ : ℝ) :
    |(dthU^[6]) Work.Construction.c2m θ| ≤ 100000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_six]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hu : |Real.sin (2 * θ)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hu2
  have hv : |Real.cos (2 * θ)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hv2
  have hkey : (39936 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5
      = (Real.sin (2 * θ)) ^ 2
        * (39936 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
          - 3072 * (Real.cos (2 * θ)) ^ 5) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hm1 : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3| ≤ 39936 :=
    abs_mul_pow_pow_le (by norm_num) hu hv 2 3
  have hm2 : |(26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)| ≤ 26112 := by
    simpa using abs_mul_pow_pow_le (c := (26112 : ℝ)) (u := Real.sin (2 * θ))
      (v := Real.cos (2 * θ)) (by norm_num) hu hv 4 1
  have hm3 : |(3072 : ℝ) * (Real.cos (2 * θ)) ^ 5| ≤ 3072 := by
    simpa using abs_mul_pow_pow_le (c := (3072 : ℝ)) (u := Real.cos (2 * θ)) (v := (1 : ℝ))
      (by norm_num) hv (by norm_num) 5 0
  have htri1 : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)|
      ≤ |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3|
        + |(26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)| := by
    have h := abs_add_le ((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      (-((26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)))
    simpa [sub_eq_add_neg] using h
  have htri2 : |((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)) - 3072 * (Real.cos (2 * θ)) ^ 5|
      ≤ |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)|
        + |(3072 : ℝ) * (Real.cos (2 * θ)) ^ 5| := by
    have h := abs_add_le ((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ))
      (-((3072 : ℝ) * (Real.cos (2 * θ)) ^ 5))
    simpa [sub_eq_add_neg] using h
  have hX : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
      - 3072 * (Real.cos (2 * θ)) ^ 5| ≤ 100000 := by
    linarith [htri1, htri2, hm1, hm2, hm3]
  have := mul_le_mul_of_nonneg_left hX (sq_nonneg (Real.sin (2 * θ)))
  linarith [this]

theorem dthU_c2m_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ : ℝ,
    |(Work.Spaces.dthU^[j] Work.Construction.c2m) θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  refine ⟨100000, by norm_num, ?_⟩
  intro j hj1 hj6 θ
  interval_cases j
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 1 le_rfl (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 2 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 3 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 4 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · exact dthU_c2m_iter_five_bound θ
  · exact dthU_c2m_iter_six_bound θ

end Work.FTS.StrongPersist
