/-
# `EpsE4Thr/ZeroOrder.lean` — the leading order of the `ε`-scheme's right-hand side at `z = 0`

**Purpose.**  `Submission/Work/FTS/StrongEps/EpsLocalPStar/NOTES_EpsLocalPStar_FALSE.md` argues
that the projected `ε`-scheme's right-hand side at the zero profile has a *nonvanishing linear*
behaviour at `z = 0`,

  `profRHS α Φs E 0 z θ / z → -4α Γ(θ)/c ≠ 0`,

and concludes that the scheme's flow leaves the class `C` immediately, so that `EpsLocalPStar`
(=`LocalStepP`) — and with it `EpsUniformMem` — is unachievable.

**That evaluation is wrong.**  Its displayed identity

  `profRHS α Φs E 0 z θ = -2 F_*(z,θ) + 2α(1-μ) AK(z,θ) - UVR α F_* Φ z θ`

is correct (it is `profRHS_eq_neg_dynLHS` at `w = 0` together with `MainLHSSubN`), but the
`O(αz)` term `-2F_*` **cancels** against the `+(1/α) L₁₂(F_*) F_*` piece of `-UVR` — the piece
that the note describes as `O(Cs α² z)` (it is not: `UVR α F_* Φ = [Θ] - (N₁+N₂+N₃)` and
`[Θ] = -(1/α)L₁₂(F_*)F_* - N₀₁ - N₀₂ + N₄ + N₅` is `O(αz)`).  After the cancellation the whole
expression is `O(z²)`: the `z`-linear terms combine, via the paper's own identity
`N₀₁ + N₀₂ = 8α² c2m(θ) z² Γ(θ)/(c(1+z)⁴)` (`Work.Construction.N0_first_two_eq'`), into the
`O(α²z²)` function `sep6`, and the elliptic-residual terms are `O(z²)` because the star package
bounds `((z+1)/z)·R(Φ̃_*)`, `((z+1)/z)·(U(Φ̃_*)/s2)` and `((z+1)/z)·V(Φ̃_*)`.

The precise form of the identity proved here is

  `profRHS α Φs E 0 z θ = -2αμ AK α z θ + sep6 α z θ + N α (Fstar α) Φ z θ`,

i.e. the scheme's right-hand side is **minus the stationary residual, whose leading part is the
`O(z²)` function `sep6`** — exactly the source term of the modulation equation
(`L_Γ^T(g) = -μ̄ AK + N₀ + N + N_*`), not a `z`-linear drift.  Consequently the flow from the zero
profile moves `W(τ) = O(τ z²)`, and `W(τ)(z,θ)/z = O(τz) → 0`, so the class-`C` axis condition
is *not* violated at the leading order.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.StrongEps.EpsLocalPStar.StatResidual
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.Stability.MainLHSSubN
import Submission.Work.Construction.Terms
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **(L1) The stationary-residual form of the `I^{N₀}_1 + I^{N₀}_2` combination.**

`MainLHS α μ (lamfun μ) F_* = 2αμ·AK - sep6`: the `z`-linear parts of
`(1+μ)F_* + (1-μ)z∂_zF_*`, of `-(1/α)L₁₂(F_*)F_*` and of
`-(3/(2α))s2 L₁₂(F_*)∂_θF_* + c2m L₁₂(F_*)z∂_zF_*` cancel by the fundamental-model identities
`F_* + z∂_zF_* = (1/α)L₁₂(F_*)F_*`, `F_* - z∂_zF_* = 2αAK` and the paper's
`N₀₁ + N₀₂ = 8α² c2m z²Γ/(c(1+z)⁴)`.  Consequently the left-hand side is `O(z²)` at `z = 0`
and `-MainLHS α μ (lamfun μ) F_*` has **no** `z`-linear term. -/
theorem MainLHS_fstar_sep6 {α μ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hμ : 1 + μ ≠ 0)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Construction.MainLHS α μ (Work.Construction.lamfun μ)
        (Work.Construction.Fstar α) z θ
      = 2 * α * μ * Work.Construction.AK α z θ
        - Work.FTS.StrongPersist.H6Rows.sep6 α z θ := by
  have hzm1 : -1 < z := by linarith
  have hstat : Work.Construction.Fstar α z θ
      + Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      - 1 / α * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ = 0 :=
    Work.Construction.Fstar_stationary_identity (α := α) (z := z) (θ := θ) hα hα1 hz
  have hsub : Work.Construction.Fstar α z θ
      - Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = 2 * α * Work.Construction.AK α z θ :=
    Work.Construction.Fstar_sub_DzFstar (α := α) (z := z) (θ := θ) hα hzm1
  have hsep : Work.FTS.StrongPersist.H6Rows.sep6 α z θ
      = (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
    rw [Work.FTS.StrongPersist.H6Rows.sep6_eq_N012 (α := α) hα hα1 hz hθ]
    simp only [Work.FTS.StrongPersist.H6Rows.N012]
  have hlam : (1 + μ) * (1 + Work.Construction.lamfun μ) = 1 - μ := by
    simp only [Work.Construction.lamfun]
    field_simp
    ring
  have hkey : (1 + μ) * Work.Construction.Fstar α z θ
      + (1 - μ) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      - (1 / α) * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ = 2 * α * μ * Work.Construction.AK α z θ := by
    linear_combination hstat + μ * hsub
  simp only [Work.Construction.MainLHS]
  rw [hlam, hsep]
  linarith [hkey]

/-! ## The two `O(z²)` source terms -/

/-- `AK α z θ = (Γ(θ)/c)·2z²/(1+z)³` is `O(z²)` on the unit radial interval: `Γ ≤ 1` and
`c ≥ 1/10` give `|Γ/c| ≤ 10`, and `2z²/(1+z)³ ≤ 2z²`. -/
theorem AK_bound {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.AK α z θ| ≤ 20 * z ^ 2 := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc.1
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  rw [Work.Construction.AK, abs_mul]
  have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_of_nonneg (div_nonneg hG.1 hcpos.le), div_le_iff₀ hcpos]
    nlinarith [hG.2, hc.1]
  have h2 : |2 * z ^ 2 / (1 + z) ^ 3| ≤ 2 * z ^ 2 := by
    have hnum : (0 : ℝ) ≤ 2 * z ^ 2 := by positivity
    have h3 : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
    rw [abs_of_nonneg (div_nonneg hnum (by positivity)), div_le_iff₀ (by positivity)]
    nlinarith [hnum, h3, sq_nonneg z]
  calc |Work.Spaces.Gam α θ / Work.Spaces.c α| * |2 * z ^ 2 / (1 + z) ^ 3|
      ≤ 10 * (2 * z ^ 2) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 20 * z ^ 2 := by ring

/-- `sep6 α z θ = 8α²c2m(θ)z²Γ(θ)/(c(1+z)⁴)` is `O(α²z²)`: `|c2m| ≤ 2`, `Γ ≤ 1`,
`c(1+z)⁴ ≥ 1/10` and `(1+z)⁴ ≥ 1`. -/
theorem sep6_bound {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.StrongPersist.H6Rows.sep6 α z θ| ≤ 160 * α ^ 2 * z ^ 2 := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc.1
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
    have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
    rw [Work.Construction.c2m]
    calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
        ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  have hc2mup : Work.Construction.c2m θ ≤ 2 := le_trans (le_abs_self _) hc2m
  have hc2mlow : -2 ≤ Work.Construction.c2m θ := by
    have := neg_le_abs (Work.Construction.c2m θ); linarith
  have h1z : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
  have hcz : (1 : ℝ) / 10 ≤ Work.Spaces.c α * (1 + z) ^ 4 := by nlinarith [hc.1, h1z]
  have hGcz : Work.Spaces.Gam α θ ≤ 10 * (Work.Spaces.c α * (1 + z) ^ 4) := by
    nlinarith [hG.2, hcz]
  have hQlo : -(2:ℝ) ≤ Work.Construction.c2m θ * Work.Spaces.Gam α θ := by
    nlinarith [hc2mlow, hG.1, hG.2]
  have hQhi : Work.Construction.c2m θ * Work.Spaces.Gam α θ ≤ 2 := by
    nlinarith [hc2mup, hG.1, hG.2]
  have hQabs : |Work.Construction.c2m θ * Work.Spaces.Gam α θ| ≤ 2 :=
    abs_le.mpr ⟨hQlo, hQhi⟩
  have hP : (0:ℝ) ≤ α ^ 2 * z ^ 2 := by positivity
  rw [Work.FTS.StrongPersist.H6Rows.sep6_eq_close6]
  have hfac : Work.FTS.StrongPersist.H6Rows.close6 α z θ
      = (8 * (α ^ 2 * z ^ 2) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
    simp only [Work.FTS.StrongPersist.H6Rows.close6]; ring
  have hden : (0:ℝ) < Work.Spaces.c α * (1 + z) ^ 4 := by positivity
  have hnum : |8 * (α ^ 2 * z ^ 2) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ)|
      = 8 * (α ^ 2 * z ^ 2) * |Work.Construction.c2m θ * Work.Spaces.Gam α θ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * (α ^ 2 * z ^ 2))]
  rw [hfac, abs_div, abs_of_pos hden, hnum, div_le_iff₀ hden]
  have hs1 : 8 * (α ^ 2 * z ^ 2) * |Work.Construction.c2m θ * Work.Spaces.Gam α θ|
      ≤ 16 * (α ^ 2 * z ^ 2) := by nlinarith [hQabs, hP]
  have hs2 : 16 * (α ^ 2 * z ^ 2)
      ≤ 160 * α ^ 2 * z ^ 2 * (Work.Spaces.c α * (1 + z) ^ 4) := by
    nlinarith [hP, hcz]
  linarith [hs1, hs2]

end Work.FTS.StrongEps.EpsE4Thr
