/-
# Definitions and elementary facts for the `L₁₂`-bound of route (Cauchy–Schwarz, `α`-free)

This module collects the objects and elementary facts used by
`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`, so that the pieces of that proof can live in
separate files.

* `Sw θ = sin(2θ)^{η/2}` — the angular factor carried by the weighted datum `g = h·w/Sw`
  (its square is the `D_z^0`-summand of `HkIntegrand`);
* `Wlam s = s/(1+s)²` — the sublinear radial weight `1/(s·w s)`;
* `Gaz h z θ = h z θ · (w z / Sw θ)` — the weighted datum itself;
* `BK = √(∫_θ (K·Sw)²)` and `W2 = ∫_{(0,∞)} Wlam²` — the two `α`-free constants.

The elementary facts proved here are the positivity/continuity of `Sw` and `K` on the angular
interval, the vanishing of `K` at the endpoints (where `Sw` vanishes), and the pointwise
domination of `Gaz²` by the `ℋ⁴`-integrand.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-! ## The objects -/

/-- `Sw θ = sin(2θ)^{η/2}`: the angular factor of the weighted datum
`g = h·w/Sw`, whose square is the `D_z^0`-summand of `HkIntegrand`. -/
def Sw (θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)

/-- `Wlam s = s/(1+s)²`: the sublinear radial weight (equal to `1/(s·w s)` for `s ≠ 0`). -/
def Wlam (s : ℝ) : ℝ := s / (1 + s) ^ 2

/-- The weighted datum `g = h·w/Sw` of the Cauchy–Schwarz argument. -/
def Gaz (h : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := h z θ * (Work.Spaces.w z / Sw θ)

/-- `BK = √(∫_θ (K(θ)·Sw θ)² dθ)`, the (finite, `α`-free) `L²`-norm of the angular profile
`K·Sw`. -/
def BK : ℝ := Real.sqrt (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ * Sw θ) ^ 2)

/-- `W2 = ∫_{(0,∞)} Wlam² `, the (finite) `L²`-norm of the radial weight. -/
def W2 : ℝ := ∫ s in Set.Ioi 0, Wlam s ^ 2

@[simp] lemma Sw_apply (θ : ℝ) : Sw θ = Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := rfl
@[simp] lemma Wlam_apply (s : ℝ) : Wlam s = s / (1 + s) ^ 2 := rfl
@[simp] lemma Gaz_apply (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gaz h z θ = h z θ * (Work.Spaces.w z / Sw θ) := rfl

/-! ## Elementary facts about `Sw` -/

lemma two_mul_mem_Icc_pi {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 2 * θ ∈ Set.Icc 0 π := by
  have h : θ ≤ π / 2 := hθ.2
  have h0 : 0 ≤ θ := hθ.1
  exact ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- On the angular interval, `sin(2θ) ≥ 0`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc (two_mul_mem_Icc_pi hθ)

/-- `Sw ≥ 0` on the angular interval. -/
lemma Sw_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Sw θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `Sw > 0` in the interior of the angular interval. -/
lemma Sw_pos_of_mem_Ioo {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < π / 2) : 0 < Sw θ :=
  Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) _

/-- `Sw` is continuous (globally: it is `Real.continuous_rpow_const` composed with `sin`). -/
lemma continuous_sw : Continuous Sw :=
  (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta] : (0:ℝ) ≤ Work.Spaces.eta / 2)).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on the angular interval. -/
lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  rw [Work.Spaces.K]
  positivity

/-- `K(θ) ≤ 3` on the angular interval. -/
lemma K_le_three_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    have h := Real.cos_sq_le_one θ
    linarith
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  nlinarith

/-- Where `Sw` vanishes on the angular interval, so does `K`. -/
lemma sw_eq_zero_imp_K_eq_zero {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : Sw θ = 0) :
    Work.Spaces.K θ = 0 := by
  have hsin := sin_two_nonneg_of_mem_Iθ hθ
  have hη : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  have hzero : Real.sin (2 * θ) = 0 :=
    ((Real.rpow_eq_zero_iff_of_nonneg hsin).mp h).1
  rw [Real.sin_two_mul] at hzero
  have : Real.sin θ = 0 ∨ Real.cos θ = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact Or.inl (by linarith [h'])
    · exact Or.inr h'
  rw [Work.Spaces.K]
  rcases this with h' | h' <;> simp [h']

/-! ## The weighted datum and the `ℋ⁴`-integrand -/

/-- The square of the weighted datum is the `D_z^0`-summand of the `ℋ⁴`-integrand. -/
lemma Gaz_sq_le_HkIntegrand (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ 0 (by norm_num)

/-- On the angular interval, `|Gaz|` is dominated by the square root of the `ℋ⁴`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand (α : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand α h z θ)

/-! ## Elementary facts about `Wlam` -/

lemma one_add_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < 1 + s := by linarith

lemma Wlam_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Wlam s := by
  rw [Wlam]
  exact div_nonneg hs (sq_nonneg _)

lemma Wlam_pos {s : ℝ} (hs : 0 < s) : 0 < Wlam s := by
  rw [Wlam]
  exact div_pos hs (pow_pos (one_add_pos_of_pos hs) 2)

lemma Wlam_ne_zero {s : ℝ} (hs : 0 < s) : Wlam s ≠ 0 := ne_of_gt (Wlam_pos hs)

/-- `w s · Wlam s = 1/s` for `s > 0`: the radial weight is exactly what absorbs the `1/s` of
the `L₁₂`-density. -/
lemma w_mul_Wlam {s : ℝ} (hs : 0 < s) : Work.Spaces.w s * Wlam s = 1 / s := by
  rw [Wlam, Work.Spaces.w]
  field_simp

/-! ## The two constants -/

lemma BK_nonneg : 0 ≤ BK := Real.sqrt_nonneg _

lemma W2_nonneg : 0 ≤ W2 := integral_nonneg fun _ => sq_nonneg _

end Work.FTS.GalBasis.cc
