import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixB1.CornerMismatch
import Submission.Work.BoseFixB1.flat_boundary_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.chi_boundary_taylor` — superpolynomial boundary decay of the corpus bump

**The lemma.**  For every `N : ℕ` there is `C > 0` with

    chi z ≤ C * (1/2 - ‖z‖)^N        for all z with ‖z‖ ≤ 1/2,

i.e. the corpus localization function `Submission.BoseGases.chi` (the Mathlib `ContDiffBump` with
`rIn = 1/4`, `rOut = 1/2`) decays *faster than any polynomial* at the boundary of its support.

**Why it is provable although `chi` is an opaque `Classical.choice`.**  `chiBase` unfolds
(`Submission/CubicChi.lean`) to

    chiBase x = (someContDiffBumpBase ℝ³).toFun 2 (4 • x),

and `someContDiffBumpBase` is `Classical.choice` of a `Nonempty` proof, hence the *formula* of the
underlying `ContDiffBumpBase` is hidden (see `Work.SmallBoxOneBody.someContDiffBumpBase_eq_choice`
and `NOTES_chiNormSq.md`).  What survives are the fields of the structure
`ContDiffBumpBase` (`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`):

* `mem_Icc`      : `0 ≤ toFun R x ≤ 1`;
* `symmetric`    : `toFun R (-x) = toFun R x`;
* `smooth`       : `ContDiffOn ℝ ∞ (uncurry toFun) (Ioi 1 ×ˢ univ)`;
* `eq_one`       : `toFun R x = 1` for `1 < R`, `‖x‖ ≤ 1`;
* `support`      : `Function.support (toFun R) = ball 0 R` for `1 < R`.

The last two together with smoothness are *enough*: `φ := toFun 2` is `C^∞` on all of `ℝ³`
(`smooth` at `R = 2`, restricted) and vanishes on the closed exterior of the ball of radius `2`
(`support`).  A `C^k` function vanishing outside a ball is *flat* at the sphere in the strong
sense that `‖f x‖ = O((2 - ‖x‖)^k)`; this is the general lemma `flat_boundary_decay`
(`Submission/Work/BoseFixB1/flat_boundary_decay.lean`), proved by induction on `k` with the mean
value theorem applied to the segment from `x` to the boundary point `2 • x/‖x‖` — a proof that
uses only the five fields above.

This is *not* in conflict with the recorded finding that numeric properties of `chi` (such as
`1/6 ≤ chiNormSq`) are unprovable: those require knowing the shape of the bump, while the
boundary decay is a shape-independent consequence of smoothness plus compact support.

**Assembly.**  Evaluating `flat_boundary_decay` at `x = 4 • z` gives
`chiBase z ≤ C₀ (2 - 4‖z‖)^N = C₀ 4^N (1/2 - ‖z‖)^N`, and `chi = chiBase / √chiNormSq` with
`√chiNormSq > 0`; the shell constant is `(C₀ + 1) * 4^N * (√chiNormSq)⁻¹ > 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## 1.  The corpus bump as a function of `(someContDiffBumpBase ℝ³).toFun 2` -/

/-- `chiBase x = (someContDiffBumpBase ℝ³).toFun 2 (4 • x)`: this is `ContDiffBump.apply` for
`chiBump` (`rIn = 1/4`, `rOut = 1/2`, centre `0`). -/
private lemma chiBase_eq_baseToFun (x : ℝ³) :
    chiBase x = (someContDiffBumpBase ℝ³).toFun 2 ((4 : ℝ) • x) := by
  rw [chiBase, ContDiffBump.apply]
  norm_num [chiBump]

/-- **The chosen bump base at `R = 2` is smooth**: the `smooth` field of `ContDiffBumpBase` is
`ContDiffOn ℝ ∞` on `Ioi 1 ×ˢ univ`, an open neighbourhood of `(2, x)`. -/
private lemma baseToFun_contDiff (k : ℕ) :
    ContDiff ℝ k (fun x : ℝ³ => (someContDiffBumpBase ℝ³).toFun 2 x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hmem : (Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set ℝ³)) ∈ 𝓝 ((2 : ℝ), x) :=
    prod_mem_nhds (Ioi_mem_nhds (by norm_num)) univ_mem
  have h2 : ContDiffAt ℝ k (Function.uncurry (someContDiffBumpBase ℝ³).toFun)
      ((2 : ℝ), x) := ((someContDiffBumpBase ℝ³).smooth.contDiffAt hmem).of_le (mod_cast le_top)
  have h3 : ContDiffAt ℝ k (fun y : ℝ³ => ((2 : ℝ), y)) x :=
    ContDiffAt.prodMk (contDiffAt_const (n := k)) (contDiffAt_id (n := k))
  exact h2.comp x h3

/-- **The chosen bump base at `R = 2` vanishes outside the closed ball of radius `2`**: the
`support` field says the support is exactly the open ball of radius `R` (for `1 < R`). -/
private lemma baseToFun_eq_zero_of_two_le_norm (x : ℝ³) (hx : 2 ≤ ‖x‖) :
    (someContDiffBumpBase ℝ³).toFun 2 x = 0 := by
  by_contra h
  have h1 : x ∈ Function.support ((someContDiffBumpBase ℝ³).toFun 2) := h
  rw [(someContDiffBumpBase ℝ³).support 2 (by norm_num : (1 : ℝ) < 2), Metric.mem_ball,
    dist_zero_right] at h1
  linarith

/-! ## 2.  The target -/

/-- **Superpolynomial decay of the corpus bump at the boundary of its support.**  This is
`Work.BoseFixB1.flat_boundary_decay` (`k := N`) applied to `φ := (someContDiffBumpBase ℝ³).toFun 2`
— smooth by the `smooth` field, vanishing outside the closed ball of radius `2` by the `support`
field — evaluated at `4 • z`, together with `chiBase z = φ (4 • z)` and
`chi = chiBase / √chiNormSq` with `√chiNormSq > 0`:

`2 - ‖4 • z‖ = 4 (1/2 - ‖z‖)`, so `4^N` is absorbed into the constant. -/
theorem chi_boundary_taylor (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖z‖ ≤ 1 / 2 → Submission.BoseGases.chi z ≤ C * ((1 / 2 : ℝ) - ‖z‖) ^ N := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    flat_boundary_decay N (fun x : ℝ³ => (someContDiffBumpBase ℝ³).toFun 2 x)
      (baseToFun_contDiff N) (fun x hx => baseToFun_eq_zero_of_two_le_norm x hx)
  have hsqrt_pos : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
  refine ⟨(C₀ + 1) * (4 : ℝ) ^ N * (Real.sqrt chiNormSq)⁻¹, by positivity, ?_⟩
  intro z hz
  -- the flatness bound at the rescaled point `4 • z`
  have h4z : ‖(4 : ℝ) • z‖ ≤ 2 := by
    rw [norm_smul, Real.norm_ofNat]
    linarith
  have h1 : chiBase z ≤ C₀ * (2 - ‖(4 : ℝ) • z‖) ^ N := by
    have h2 := hbound ((4 : ℝ) • z) h4z
    have hnn : 0 ≤ (someContDiffBumpBase ℝ³).toFun 2 ((4 : ℝ) • z) :=
      ((someContDiffBumpBase ℝ³).mem_Icc 2 ((4 : ℝ) • z)).1
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, ← chiBase_eq_baseToFun] at h2
    exact h2
  have harg : 2 - ‖(4 : ℝ) • z‖ = 4 * (1 / 2 - ‖z‖) := by
    rw [norm_smul, Real.norm_ofNat]; ring
  have h4 : chiBase z ≤ C₀ * (4 : ℝ) ^ N * ((1 / 2 : ℝ) - ‖z‖) ^ N := by
    rw [harg, mul_pow] at h1
    linarith [h1]
  have h5 : chi z ≤ C₀ * (4 : ℝ) ^ N * ((1 / 2 : ℝ) - ‖z‖) ^ N * (Real.sqrt chiNormSq)⁻¹ := by
    rw [chi, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h4 (inv_nonneg.mpr hsqrt_pos.le)
  have h6 : (0 : ℝ) ≤ ((1 / 2 : ℝ) - ‖z‖) ^ N * (Real.sqrt chiNormSq)⁻¹ := by positivity
  calc chi z ≤ C₀ * (4 : ℝ) ^ N * ((1 / 2 : ℝ) - ‖z‖) ^ N * (Real.sqrt chiNormSq)⁻¹ := h5
    _ ≤ (C₀ + 1) * (4 : ℝ) ^ N * (Real.sqrt chiNormSq)⁻¹ * ((1 / 2 : ℝ) - ‖z‖) ^ N := by
        nlinarith [h6, hC₀, pow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) N]

end Work.BoseFixB1
