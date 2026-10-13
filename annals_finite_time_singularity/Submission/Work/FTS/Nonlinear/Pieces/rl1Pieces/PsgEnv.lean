/-
# `PsgEnv` — the five `sg`-rows of `N` in the `rl¹`-norm, in the a-priori envelope

The pieces are `N₁^{sg} = 2ℛ(Φ̃_*)·g`, `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θ g`, `N₃^{sg} = -2α𝒱(Φ̃_*)·D_z g`,
`N₄^{sg} = -(1/2)FK(F_*)·D_θ g` and `N₅^{sg} = -sin²θ·FK(F_*)·g`, and the statement bounds each
of their `rl¹`-norms by the same envelope `K·(α² + √α·|g|_{ℋ⁴} + α^{-3/2}|g|_{ℋ⁴}²)`.

The route is

* `rl1Pieces.sgRowsPtwise` : the five pointwise angular bounds (`|K θ·Nᵢ^{sg}| ≤ cᵢ·|kᵢ|`, with
  `k₁ = k₅ = g`, `k₂ = k₄ = ∂_θ g`, `k₃ = D_z g` and the radial factor `r/(1+r)²` for `i = 4,5`);
* `rl1Tools.envG`, `rl1Tools.envDz`, `rl1Pieces.envPth` : the three *basis* bounds, i.e. the
  `rl¹`-norms of `g`, `D_z g` and `∂_θ g` against `r⁻¹`, each in terms of `|g|_{ℋ⁴}`;
* the two generic reduction lemmas `rl1_row_le` / `rl1_row_le_radial`, which turn a pointwise
  bound `|K θ·N| ≤ c·|k|` (resp. `c·(r/(1+r)²)·|k|`, using `r⁻¹·r/(1+r)² = 1/(1+r)² ≤ r⁻¹`)
  into the `rl¹`-bound `ofReal c` times the basis bound of `k`;
* the arithmetic absorption of the five constants into `K·env`, with the universal choice
  `1000·(max Cs 0 + 1)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.envPth
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.sgRowsPtwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Generic reduction lemmas -/

/-- **Row reduction with a constant coefficient.**  If `|K θ · N(r,θ)| ≤ c·|k(r,θ)|` pointwise
(with `c ≥ 0`), then the `rl¹`-norm of `N` is at most `ofReal c` times that of `k`. -/
theorem rl1_row_le {N k : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hpt : ∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * N r θ| ≤ c * |k r θ|)
    {B : ENNReal}
    (hk : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) ≤ B) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ENNReal.ofReal c * B := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal |k r θ| := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (hpt r hr θ hθ))
    rwa [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have hA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul' le_rfl (hinner r hr)
  have hB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    rw [show (fun r : ℝ => ENNReal.ofReal r⁻¹ *
        (ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
        = (fun r : ℝ => ENNReal.ofReal c * (ENNReal.ofReal r⁻¹ *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))) from by funext r; ring]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact le_trans hA (le_trans (le_of_eq hB) (mul_le_mul' le_rfl hk))

/-- **Row reduction with the radial factor `r/(1+r)²`.**  Since `r⁻¹·r/(1+r)² = 1/(1+r)² ≤ r⁻¹`
on `r > 0`, a pointwise bound `|K θ·N| ≤ c·(r/(1+r)²)·|k|` gives the same `rl¹`-bound. -/
theorem rl1_row_le_radial {N k : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hpt : ∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.K θ * N r θ| ≤ c * (r / (1 + r) ^ 2) * |k r θ|)
    {B : ENNReal}
    (hk : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) ≤ B) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ENNReal.ofReal c * B := by
  have hinner : ∀ r : ℝ, 0 < r →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (c * (r / (1 + r) ^ 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
    intro r hr
    have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (c * (r / (1 + r) ^ 2)) * ENNReal.ofReal |k r θ| := by
      refine MeasureTheory.lintegral_mono_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc (by positivity))]
        exact ENNReal.ofReal_le_ofReal (hpt r hr θ hθ))
    rwa [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  have hrad : ∀ r : ℝ, 0 < r → r⁻¹ * (c * (r / (1 + r) ^ 2)) ≤ c * r⁻¹ := by
    intro r hr
    have h2 : r⁻¹ * (r / (1 + r) ^ 2) = ((1 + r) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    have hle : ((1 + r) ^ 2)⁻¹ ≤ r⁻¹ := by
      rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (1 + r) ^ 2) hr]
      nlinarith [sq_nonneg r]
    rw [show r⁻¹ * (c * (r / (1 + r) ^ 2))
        = c * (r⁻¹ * (r / (1 + r) ^ 2)) from by ring, h2]
    exact mul_le_mul_of_nonneg_left hle hc
  have hA : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal c *
        (ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (hinner r hr0)) ?_
    have hstep : ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (c * (r / (1 + r) ^ 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))
        = ENNReal.ofReal (r⁻¹ * (c * (r / (1 + r) ^ 2)))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) := by
      rw [show ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (c * (r / (1 + r) ^ 2))
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|))
          = (ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c * (r / (1 + r) ^ 2)))
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|) from by rw [← mul_assoc]]
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    rw [hstep]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hrad r hr0)) le_rfl) ?_
    rw [ENNReal.ofReal_mul hc]
    exact le_of_eq (by ring)
  have hB : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal c *
        (ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact le_trans hA (le_trans (le_of_eq hB) (mul_le_mul' le_rfl hk))

/-! ## Scalar arithmetic facts -/

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
lemma alpha_le_sqrt_self {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : α ≤ Real.sqrt α := by
  have h := Real.sq_sqrt hα.le
  have h2 : α ^ 2 ≤ α := by nlinarith
  nlinarith [Real.sqrt_nonneg α]

/-- `α·√(10/α) = √10·√α` for `α > 0`. -/
lemma alpha_mul_sqrt_div {α : ℝ} (hα : 0 < α) :
    α * Real.sqrt (10 / α) = Real.sqrt 10 * Real.sqrt α := by
  have hdiv : 0 ≤ 10 / α := div_nonneg (by norm_num) hα.le
  have hstep : Real.sqrt (10 / α) * Real.sqrt (α ^ 2) = Real.sqrt (10 / α * α ^ 2) :=
    (Real.sqrt_mul hdiv (α ^ 2)).symm
  rw [Real.sqrt_sq hα.le] at hstep
  have h1 : Real.sqrt (10 / α) * α = Real.sqrt (10 * α) := by
    rw [hstep]
    congr 1
    rw [div_mul_eq_mul_div, mul_div_assoc, pow_two, mul_div_cancel_left₀ α (ne_of_gt hα)]
  rw [mul_comm α (Real.sqrt (10 / α)), h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]

/-- `√10 ≤ 4`. -/
lemma sqrt_ten_le_four : Real.sqrt 10 ≤ 4 := by
  have h := Real.sqrt_le_sqrt (show (10 : ℝ) ≤ 16 by norm_num)
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h16] at h

/-! ## The target -/

theorem PsgEnv {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
        ≤ ENNReal.ofReal (K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
  refine ⟨1000 * (max Cs 0 + 1), ?_, ?_⟩
  · have h := le_max_right Cs 0
    nlinarith [h]
  intro α g Φs Φg hα hα1 hαα₂ hN hgal hs hell
  -- ### the data
  obtain ⟨hsm, hmem, _⟩ :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (show (4 : ℕ) ≤ 6 by norm_num)
  obtain ⟨hrow1, hrow2, hrow3, hrow4, hrow5⟩ := sgRowsPtwise hα hα1 hs
  have hG := Work.FTS.Nonlinear.Pieces.rl1Tools.envG hα hsm hmem
  have hDz := Work.FTS.Nonlinear.Pieces.rl1Tools.envDz hα hsm hmem
  have hPth := envPth hα hα1 hsm hmem
  -- ### the numbers
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCs0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hCs1 : 0 < max Cs 0 + 1 := by linarith
  have hsq : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hAs : α ≤ Real.sqrt α := alpha_le_sqrt_self hα hα1
  have hA1 : α * Work.FTS.Nonlin.Xn α g ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hAs hX0
  have hpow : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hB1 : Real.sqrt α * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg hpow (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    linarith
  have hA2 : α ^ 2 * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have ha2 : (0 : ℝ) ≤ α ^ 2 := by positivity
    have hspos : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg hpow (sq_nonneg _)
    have hqpos : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := mul_nonneg hsq hX0
    rcases lt_or_ge (Work.FTS.Nonlin.Xn α g) 1 with h1 | h1
    · have h2 : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ α ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_left (le_of_lt h1) ha2
        simpa using h3
      linarith
    · have h1' : 1 ≤ Work.FTS.Nonlin.Xn α g := h1
      have hx : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.Nonlin.Xn α g ^ 2 := by nlinarith
      have h3 : α ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α) (y := (2 : ℝ))
          (z := -(3 / 2 : ℝ)) (by norm_num : (-(3 / 2 : ℝ)) ≤ 2)
        simpa using h
      have h4 : α ^ 2 * Work.FTS.Nonlin.Xn α g
          ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul h3 hx hX0 hpow
      linarith
  have hAalpha : α * Work.FTS.Nonlin.Xn α g
      ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
    le_trans hA1 hB1
  -- ### the absorption of a constant times one of the three shapes
  have key : ∀ c S : ℝ, 0 ≤ c → 0 ≤ S →
      S ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 →
      c ≤ 1000 * (max Cs 0 + 1) →
      c * S ≤ (1000 * (max Cs 0 + 1)) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    intro c S hc0 hS0 hSenv hcK
    have henv0' : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := le_trans hS0 hSenv
    exact le_trans (mul_le_mul_of_nonneg_left hSenv hc0)
      (mul_le_mul_of_nonneg_right hcK henv0')
  have hc1 : 12 * max Cs 0 ≤ 1000 * (max Cs 0 + 1) := by nlinarith [hCs0]
  have hc2 : 240 * Real.sqrt 10 * max Cs 0 ≤ 1000 * (max Cs 0 + 1) := by
    have hs4 := sqrt_ten_le_four
    nlinarith [hCs0, Real.sqrt_nonneg 10]
  have hc4 : 30 * Real.sqrt 10 ≤ 1000 * (max Cs 0 + 1) := by
    have hs4 := sqrt_ten_le_four
    nlinarith [hCs1, Real.sqrt_nonneg 10]
  have hc5 : (12 : ℝ) ≤ 1000 * (max Cs 0 + 1) := by nlinarith [hCs1]
  -- ### the five rows
  have hb1 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N1sg α Φs g) (k := g)
      (c := 6 * max Cs 0 * α)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le) hrow1 hG
    have h2 : ENNReal.ofReal (6 * max Cs 0 * α) * ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 * max Cs 0) * (α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (12 * max Cs 0) (α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) hCs0) (mul_nonneg hα.le hX0) hAalpha hc1
  have hb2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N2sg α Φs g) (k := Work.Spaces.pth g)
      (c := 24 * max Cs 0 * α)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le) hrow2 hPth
    have h2 : ENNReal.ofReal (24 * max Cs 0 * α) *
          ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((240 * Real.sqrt 10 * max Cs 0)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)]
      congr 1
      have e1 : (24 : ℝ) * max Cs 0 * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
          = 240 * (max Cs 0 * (α * Real.sqrt (10 / α))) * Work.FTS.Nonlin.Xn α g := by ring
      rw [e1, alpha_mul_sqrt_div hα]
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (240 * Real.sqrt 10 * max Cs 0) (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) hCs0)
      (mul_nonneg hsq hX0) hB1 hc2
  have hb3 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le (N := Work.FTS.Nonlin.N3sg α Φs g) (k := Work.Spaces.Dz g)
      (c := 6 * max Cs 0 * α ^ 2)
      (mul_nonneg (mul_nonneg (by norm_num) hCs0) (by positivity)) hrow3 hDz
    have h2 : ENNReal.ofReal (6 * max Cs 0 * α ^ 2) *
          ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 * max Cs 0) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hCs0) (by positivity))]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (12 * max Cs 0) (α ^ 2 * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) hCs0) (mul_nonneg (by positivity) hX0) hA2 hc1
  have hb4 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le_radial (N := Work.FTS.Nonlin.N4sg α g) (k := Work.Spaces.pth g)
      (c := 3 * α) (by positivity) hrow4 hPth
    have h2 : ENNReal.ofReal (3 * α) *
          ENNReal.ofReal (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((30 * Real.sqrt 10) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * α)]
      congr 1
      have e1 : (3 : ℝ) * α * (10 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g)
          = 30 * (α * Real.sqrt (10 / α)) * Work.FTS.Nonlin.Xn α g := by ring
      rw [e1, alpha_mul_sqrt_div hα]
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key (30 * Real.sqrt 10) (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg 10)) (mul_nonneg hsq hX0) hB1 hc4
  have hb5 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
      ≤ ENNReal.ofReal (1000 * (max Cs 0 + 1) * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)) := by
    have h1 := rl1_row_le_radial (N := Work.FTS.Nonlin.N5sg α g) (k := g)
      (c := 6 * α) (by positivity) hrow5 hG
    have h2 : ENNReal.ofReal (6 * α) * ENNReal.ofReal (2 * Work.FTS.Nonlin.Xn α g)
        = ENNReal.ofReal ((12 : ℝ) * (α * Work.FTS.Nonlin.Xn α g)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 * α)]
      congr 1
      ring
    refine le_trans h1 (le_trans (le_of_eq h2) ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    exact key 12 (α * Work.FTS.Nonlin.Xn α g) (by norm_num) (mul_nonneg hα.le hX0) hAalpha hc5
  exact ⟨hb1, hb2, hb3, hb4, hb5⟩

end Work.FTS.Nonlinear.Pieces.rl1Pieces
