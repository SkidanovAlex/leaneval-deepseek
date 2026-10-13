/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise level-`6` product bound for `A · D_θ f`: the budget and the pricing

This file collects the vocabulary used by `Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDth`:

* `ptdBud` — the *pointwise budget*, the combination of the three RHS terms of the target
  estimate that every Leibniz summand of `D_z^j D_θ^i (A · D_θ f)` is priced against:
  `MA²·HkIntegrand α 7 f + (γ-1)⁻¹HkSq α 6 A·HkIntegrand α 6 f
   + (γ-1)⁻¹HkSq α 6 f·HkIntegrand α 6 A + (D_z⁵A·D_θ²f·W)²`;
* `CP` — the universal constant of `Work.FTS.StrongPersist.N6.PwAny6`, the pointwise price
  `(D_z^bD_θ^a g)² ≤ CP (γ-1)⁻¹ |g|²_{ℋ⁶}` for `a + b ≤ 4`, which is the device that makes the
  pointwise estimate possible (the `(γ-1)⁻¹` loss is exactly the coefficient of the middle RHS
  term);
* the elementary weight comparison `abs_light_le_abs_Wt` (`w/sin(2θ)^{η/2} ≤ W` since `η < γ`),
  which lets a `D_z`-slot of `A · D_θ f` be compared with a mixed slot of `f`;
* the Cauchy–Schwarz bookkeeping `sq_sum_le_card_mul_sum_sq`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongEps.H5.LevelShift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-! ## The budget -/

/-- The pointwise budget of the level-`6` product bound for `A · D_θ f`.  Its four summands are
the two terms of the target estimate that are not of the form `K · (·)²` of a single slot, split
into the pairs (price, kept slot) that occur in the Leibniz expansion. -/
def ptdBud (α : ℝ) (A f : ℝ → ℝ → ℝ) (MA : ℝ) (z θ : ℝ) : ℝ :=
  MA ^ 2 * HkIntegrand α 7 f z θ
    + (gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ
    + (gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ
    + (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2

theorem ptdBud_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA : ℝ) (z θ : ℝ) :
    0 ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h1 := HkIntegrand_nonneg α 7 f z θ
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  rw [ptdBud]
  positivity

/-- The `MA²`-component of the budget. -/
theorem MAsq_mul_Hk7_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    MA ^ 2 * HkIntegrand α 7 f z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  rw [ptdBud]
  nlinarith [mul_nonneg hγ (mul_nonneg h2 h5), mul_nonneg hγ (mul_nonneg h3 h4),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The `(γ-1)⁻¹ HkSq 6 A · HkIntegrand 6 f`-component of the budget. -/
theorem inv_hA_mul_Hk6f_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * HkSq α 6 A * HkIntegrand α 6 f z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h3 := HkSq_nonneg α 6 f
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have h1 := HkIntegrand_nonneg α 7 f z θ
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h3 h4),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The `(γ-1)⁻¹ HkSq 6 f · HkIntegrand 6 A`-component of the budget. -/
theorem inv_hf_mul_Hk6A_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (gam α - 1)⁻¹ * HkSq α 6 f * HkIntegrand α 6 A z θ ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  have h1 := HkIntegrand_nonneg α 7 f z θ
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h2 h5),
    sq_nonneg (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ)]

/-- The exceptional squared slot `(D_z⁵A · D_θ²f · W)²` is a summand of the budget. -/
theorem exc_le_ptdBud {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    (DzIter 5 A z θ * mixed 0 2 f z θ * Wt α z θ) ^ 2 ≤ ptdBud α A f MA z θ := by
  have hγ : 0 ≤ (gam α - 1)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (by rw [gam_sub_one]; linarith))
  have h2 := HkSq_nonneg α 6 A
  have h3 := HkSq_nonneg α 6 f
  have h1 := HkIntegrand_nonneg α 7 f z θ
  have h4 := HkIntegrand_nonneg α 6 A z θ
  have h5 := HkIntegrand_nonneg α 6 f z θ
  have h6 : 0 ≤ MA ^ 2 := sq_nonneg MA
  rw [ptdBud]
  nlinarith [mul_nonneg h6 h1, mul_nonneg hγ (mul_nonneg h2 h5),
    mul_nonneg hγ (mul_nonneg h3 h4)]

/-! ## The universal pricing constant -/

/-- The universal constant of the level-six pointwise price `PwAny6`. -/
def CP : ℝ := Classical.choose Work.FTS.StrongPersist.N6.PwAny6

theorem CP_pos : 0 < CP := (Classical.choose_spec Work.FTS.StrongPersist.N6.PwAny6).1

/-- The pointwise price: every slot `D_z^bD_θ^a g` with `a + b ≤ 4` of a `C^∞`-on-the-quadrant
datum `g ∈ ℋ⁶` is bounded by `CP (γ-1)⁻¹ |g|²_{ℋ⁶}` (with `CP` the universal constant above). -/
theorem CP_price (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) (hab : a + b ≤ 4)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (mixed b a f z θ) ^ 2 ≤ CP / (gam α - 1) * HkSq α 6 f :=
  (Classical.choose_spec Work.FTS.StrongPersist.N6.PwAny6).2 α f b a hα hα1 hf hmem hab z hz θ hθ

/-- The constant of the per-summand estimates. -/
def ptdK2 : ℝ := 4096 * (CP + 1)

theorem ptdK2_pos : 0 < ptdK2 := by
  have := CP_pos
  rw [ptdK2]; positivity

theorem one_le_ptdK2 : 1 ≤ ptdK2 := by
  have := CP_pos
  rw [ptdK2]; nlinarith

theorem CP_le_ptdK2 : CP ≤ ptdK2 := by
  have := CP_pos
  rw [ptdK2]; nlinarith

theorem CP_mul_ptdBud_le {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA z θ : ℝ) :
    CP * ptdBud α A f MA z θ ≤ ptdK2 * ptdBud α A f MA z θ :=
  mul_le_mul_of_nonneg_right CP_le_ptdK2 (ptdBud_nonneg hα A f MA z θ)

/-! ## The weight comparison `w/sin(2θ)^{η/2} ≤ W` -/

theorem div_rpow_le_wTheta {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : (Real.sin (2 * θ) ^ (eta / 2))⁻¹ ≤ wTheta α θ := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : eta / 2 ≤ gam α / 2 := by
    have : eta ≤ gam α := by rw [eta, gam]; linarith
    linarith
  have hle : Real.sin (2 * θ) ^ (gam α / 2) ≤ Real.sin (2 * θ) ^ (eta / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hexp
  rw [wTheta, Real.rpow_neg hs0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hs0 _) hle

theorem wTheta_pos {α θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : 0 < wTheta α θ := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  rw [wTheta, Real.rpow_neg hs0.le]
  exact inv_pos.mpr (Real.rpow_pos_of_pos hs0 _)

/-- `w/sin(2θ)^{η/2} ≤ W` on the open quadrant, because `η < γ`. -/
theorem abs_light_le_abs_Wt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |w z / Real.sin (2 * θ) ^ (eta / 2)| ≤ |Wt α z θ| := by
  have hs0 : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos ⟨hθ0, hθ1⟩
  have hw : 0 < w z := Work.FTS.TransportS.w_pos_of_pos hz
  have h1 := div_rpow_le_wTheta hα hα1 hθ0 hθ1
  have h2 : 0 < w z / Real.sin (2 * θ) ^ (eta / 2) :=
    div_pos hw (Real.rpow_pos_of_pos hs0 _)
  have h3 : 0 < wTheta α θ := wTheta_pos hθ0 hθ1
  rw [abs_of_pos h2, Wt, abs_of_pos (mul_pos hw h3), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h1 hw.le

/-- The `L²`-form of the weight comparison: a light-weighted slot is dominated by the
`W`-weighted one. -/
theorem sq_light_le_sq_Wt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (Y : ℝ) :
    (Y * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 ≤ (Y * (Wt α z θ)) ^ 2 := by
  have h := abs_light_le_abs_Wt hα hα1 hz hθ0 hθ1
  refine sq_le_sq.mpr ?_
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg Y)

/-! ## Cauchy–Schwarz bookkeeping -/

/-- `(∑ x ∈ s, f x)² ≤ s.card · ∑ x ∈ s, (f x)²`. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
  have h2 : (∑ i ∈ s, f i ^ 2) * (s.card : ℝ) = (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 :=
    mul_comm _ _
  rw [← h2]
  simpa using h

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
