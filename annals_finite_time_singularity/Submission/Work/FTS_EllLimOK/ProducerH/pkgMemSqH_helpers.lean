import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.pkgMemSqH_helpers`

Elementary helpers for the producer `pkgMemSqH_of_ellClassOk` (the `L2` field `PkgMemSqH` of
`RulingELF.ProducerH`): monotonicity of `SlotBd`, the level-`0` `ℋ`-integrand in factored form,
the pointwise domination of `HkIntegrand α 0` under sums and under division by `cos θ`,
homogeneity, and the scaling limit `t² S ≤ C(1+tX)² ∀ t > 0 ⟹ S ≤ C X²` together with the two
arithmetic bookkeeping lemmas used in the assembly.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `SlotBd` and the level-`0` integrand -/

/-- `SlotBd` is monotone in the bound. -/
theorem SlotBd_mono {α : ℝ} {Φ : Fn} {M M' : ℝ} (h : Work.FTS.StreamBdryIface.SlotBd α Φ M)
    (hMM' : M ≤ M') : Work.FTS.StreamBdryIface.SlotBd α Φ M' := by
  intro z θ hz
  obtain ⟨h1, h2, h3⟩ := h z θ hz
  exact ⟨fun j hj => le_trans (h1 j hj) hMM', le_trans h2 hMM', fun j hj => le_trans (h3 j hj) hMM'⟩

/-- The level-`0` integrand is the square of one explicit factor. -/
theorem HkIntegrand_zero_factor (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
  Work.FTS_EllLimOK.HkIntegrand_zero_eq α f z θ

/-- Pointwise: `HkIntegrand α 0 (a+b) ≤ 2 HkIntegrand α 0 a + 2 HkIntegrand α 0 b`. -/
theorem HkIntegrand_zero_add_le (α : ℝ) (a b : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ + b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ := by
  rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor, HkIntegrand_zero_factor]
  set c : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
  nlinarith [sq_nonneg ((a z θ + b z θ) * c), sq_nonneg ((a z θ - b z θ) * c),
    sq_nonneg (a z θ * c), sq_nonneg (b z θ * c)]

/-- Pointwise: dividing by `cos θ` does not decrease the level-`0` integrand. -/
theorem HkIntegrand_zero_le_cosDiv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => F z θ / Real.cos θ) z θ := by
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · have hsin : Real.sin (2 * θ) = 0 := by rw [Real.sin_two_mul, hc, mul_zero]
    have hc0 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hsin, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
    rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor, hc0]
    simp
  · have hcos2 : (Real.cos θ) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor]
    have h1 : (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((F z θ / Real.cos θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          * (Real.cos θ) ^ 2 := by
      field_simp
    rw [h1]
    exact mul_le_of_le_one_right (sq_nonneg _) hcos2

/-- Pointwise: the level-`0` integrand is homogeneous of degree `2`. -/
theorem HkIntegrand_zero_smul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 (c • f) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 f z θ := by
  rw [HkIntegrand_zero_factor, HkIntegrand_zero_factor]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The level-`0` slice integral is homogeneous of degree `2`. -/
theorem integral_HkIntegrand_zero_smul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (c • f) z θ)
      = c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ) := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    simp only [HkIntegrand_zero_smul])

/-! ## Scaling and arithmetic -/

/-- Scaling: from `t^2 * S ≤ C * (1 + t*X)^2` for all `t > 0`, conclude `S ≤ C * X^2`. -/
theorem scale_limit {C S X : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ^ 2 * S ≤ C * (1 + t * X) ^ 2) :
    S ≤ C * X ^ 2 := by
  have hnat : ∀ n : ℕ, S ≤ C * (1 / ((n : ℝ) + 1) + X) ^ 2 := by
    intro n
    have ht : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 := h _ ht
    have h2 : ((1 : ℝ) / ((n : ℝ) + 1) + X) = (1 + ((n : ℝ) + 1) * X) / ((n : ℝ) + 1) := by
      field_simp
    rw [h2, div_pow, show C * ((1 + ((n : ℝ) + 1) * X) ^ 2 / ((n : ℝ) + 1) ^ 2)
        = (C * (1 + ((n : ℝ) + 1) * X) ^ 2) / ((n : ℝ) + 1) ^ 2 from by ring]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mpr (by nlinarith [h1])
  have hlim : Filter.Tendsto
      (fun n : ℕ => C * (1 / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop (𝓝 (C * X ^ 2)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) + X) Filter.atTop (𝓝 (0 + X)) :=
      h1.add tendsto_const_nhds
    have h3 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop
        (𝓝 ((0 + X) ^ 2)) := h2.pow 2
    have h4 := h3.const_mul C
    simpa using h4
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hnat

/-- Arithmetic: `s ≤ CC * (1 + X)^2` from the two per-piece bounds. -/
theorem norm_arith {CC CB CT Ce X s : ℝ} (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) (hX : 0 ≤ X)
    (h1 : s ≤ 2 * (CB * (Ce * X) ^ 2) + 2 * (CT * (1 + X) ^ 2))
    (hCC : 2 * CB * Ce ^ 2 + 2 * CT ≤ CC) : s ≤ CC * (1 + X) ^ 2 := by
  have hX1 : 0 ≤ (1 + X) ^ 2 := by positivity
  have h2 : (Ce * X) ^ 2 ≤ Ce ^ 2 * (1 + X) ^ 2 := by
    nlinarith [sq_nonneg Ce, sq_nonneg X, hX, sq_nonneg (1 + X)]
  have hmul : CB * (Ce * X) ^ 2 ≤ CB * (Ce ^ 2 * (1 + X) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hCB
  have hfac : 2 * (CB * (Ce ^ 2 * (1 + X) ^ 2)) + 2 * (CT * (1 + X) ^ 2)
      = (2 * CB * Ce ^ 2 + 2 * CT) * (1 + X) ^ 2 := by ring
  have hsum : 2 * (CB * (Ce * X) ^ 2) + 2 * (CT * (1 + X) ^ 2)
      ≤ (2 * CB * Ce ^ 2 + 2 * CT) * (1 + X) ^ 2 := by
    rw [← hfac]; linarith [hmul]
  exact le_trans (le_trans h1 hsum) (mul_le_mul_of_nonneg_right hCC hX1)

/-- Arithmetic: the per-slice combination. -/
theorem slice_arith {CC CB CS K Ce X z a b M2 U2 : ℝ}
    (hCB : 0 ≤ CB) (hCS : 0 ≤ CS) (hz : 0 < z) (hX : 0 ≤ X)
    (h1 : a ≤ CB * (1 + 1 / z) * (M2 + U2))
    (h2 : b ≤ CS * (1 + 1 / z) * X ^ 2)
    (hM2 : M2 ≤ K ^ 2 * Ce ^ 2 * (1 + X) ^ 2)
    (hU2 : U2 ≤ Ce ^ 2 * (1 + X) ^ 2)
    (hCC : 2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS ≤ CC) :
    2 * a + 2 * b ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
  have hcoef : 0 ≤ 1 + 1 / z := by positivity
  have hX1 : 0 ≤ (1 + X) ^ 2 := by positivity
  have hX2 : X ^ 2 ≤ (1 + X) ^ 2 := by nlinarith [hX]
  have hMU : M2 + U2 ≤ (K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2 := by
    have e : K ^ 2 * Ce ^ 2 * (1 + X) ^ 2 + Ce ^ 2 * (1 + X) ^ 2
        = (K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2 := by ring
    linarith [hM2, hU2, e]
  have hC1 : CB * (1 + 1 / z) * (M2 + U2)
      ≤ CB * (1 + 1 / z) * ((K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2) := by
    have h0 : 0 ≤ CB * (1 + 1 / z) := mul_nonneg hCB hcoef
    exact mul_le_mul_of_nonneg_left hMU h0
  have hC2 : CS * (1 + 1 / z) * X ^ 2 ≤ CS * (1 + 1 / z) * (1 + X) ^ 2 := by
    have h0 : 0 ≤ CS * (1 + 1 / z) := mul_nonneg hCS hcoef
    exact mul_le_mul_of_nonneg_left hX2 h0
  calc 2 * a + 2 * b
      ≤ 2 * (CB * (1 + 1 / z) * (M2 + U2)) + 2 * (CS * (1 + 1 / z) * X ^ 2) := by linarith
    _ ≤ 2 * (CB * (1 + 1 / z) * ((K ^ 2 * Ce ^ 2 + Ce ^ 2) * (1 + X) ^ 2))
          + 2 * (CS * (1 + 1 / z) * (1 + X) ^ 2) := by linarith [hC1, hC2]
    _ = (2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS) * (1 + 1 / z) * (1 + X) ^ 2 := by ring
    _ ≤ CC * (1 + 1 / z) * (1 + X) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hcoef) hX1

end Work.FTS_EllLimOK.ProducerH
