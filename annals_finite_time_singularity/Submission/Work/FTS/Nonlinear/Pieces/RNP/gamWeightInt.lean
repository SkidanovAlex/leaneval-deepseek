import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.LocData.angMaj_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A *uniform in `α`* angular mass bound for the `Γ²`-weight of the nonlinear estimates

The lemma of this file is the angular mass estimate

`∫_{Iθ} Γ(θ)² (α + sin 2θ)² sin(2θ)^{-γ(α)} dθ ≤ M`  for all `0 < α ≤ 1`,

with `Γ(θ) = (sin θ cos²θ)^{α/3}`, `γ(α) = 1 + α/10` (`Work.Spaces.Gam`, `Work.Spaces.gam`)
and the angular weight `sin(2θ)^{-γ} = Work.FTS.Nonlinear.RadialProd.smG α`.

## Why the extra factor `(α + sin 2θ)²` is what makes the constant uniform

The companion estimate `Work.FTS.LocData.angMaj_mem` gives only the `α`-dependent bound

`∫_{Iθ} Γ² sin(2θ)^{-γ} ≤ 3000/(17α)`,

which *diverges* as `α ↓ 0` (near `θ = 0` the integrand is `θ^{17α/30-1}`).  The factor
`(α + sin 2θ)²` of this file vanishes quadratically where `sin 2θ ≪ α`, exactly cancelling
the divergence: with `X = sin 2θ` and `s = 17α/30 - 1 = 2α/3 - γ(α) ∈ (-1,0]`,

* `GamSq_sin_neg_gam_le` gives `Γ² X^{-γ} ≤ 2^{-2α/3} X^s`, hence
* `Γ² (α+X)² X^{-γ} ≤ X^s (α+X)² = α² X^s + 2α X^{s+1} + X^{s+2} ≤ α² X^s + 2α + 1`,
* and `∫_{Iθ} X^s ≤ 3000/(17α)` (`Work.Spaces.sin_two_rpow`) so that the dangerous term
  contributes `α²·3000/(17α) = 3000α/17 ≤ 3000/17`.

The numerical constant `M = 1000` is generous: the sum is at most `3000/17 + 6 ≤ 206`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

/-! ## The pointwise domination

`Γ²(α+X)²X^{-γ} ≤ α²X^{17α/30-1} + 2α + 1`, where `X = sin 2θ`.  The `α²` in front of the
singular term `X^{s}` is what makes the subsequent integral uniform in `α`. -/
theorem gamWeightPt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1) := by
  set X : ℝ := Real.sin (2 * θ) with hXdef
  set s : ℝ := 17 * α / 30 - 1 with hsdef
  have hX0 : 0 ≤ X := by
    rw [hXdef, Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
  have hX1 : X ≤ 1 := by rw [hXdef]; exact Real.sin_le_one _
  have hs1 : 0 ≤ s + 1 := by rw [hsdef]; linarith
  have hne1 : s + 1 ≠ 0 := by rw [hsdef]; linarith
  have hb2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
  -- the companion bound `Γ² X^{-γ} ≤ 2^{-2α/3} X^s`
  have hbase : Work.Spaces.Gam α θ ^ 2 * X ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * X ^ s := by
    rw [hXdef, hsdef]
    exact Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hXs : 0 ≤ X ^ s := Real.rpow_nonneg hX0 s
  -- `X^s X ≤ 1`, `(X^s X) X ≤ 1`
  have hA : X ^ (s + 1) = X ^ s * X := by
    rw [Real.rpow_add' hX0 hne1, Real.rpow_one X]
  have h1 : X ^ s * X ≤ 1 := by rw [← hA]; exact Real.rpow_le_one hX0 hX1 hs1
  have h3 : (X ^ s * X) * X ≤ 1 := by
    have := mul_le_mul h1 hX1 hX0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  -- the `X`-part of the bound
  have hkey : X ^ s * (α + X) ^ 2 ≤ α ^ 2 * X ^ s + (2 * α + 1) := by
    have e1 : (2 * α) * (X ^ s * X) ≤ (2 * α) * 1 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have e0 : X ^ s * (α + X) ^ 2
        = α ^ 2 * X ^ s + (2 * α) * (X ^ s * X) + (X ^ s * X) * X := by ring
    rw [e0]
    linarith
  -- assemble
  have hstep1 : Work.Spaces.Gam α θ ^ 2 * (α + X) ^ 2 * X ^ (-(Work.Spaces.gam α))
      ≤ (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2 := by
    calc Work.Spaces.Gam α θ ^ 2 * (α + X) ^ 2 * X ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.Gam α θ ^ 2 * X ^ (-(Work.Spaces.gam α))) * (α + X) ^ 2 := by ring
      _ ≤ (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2 :=
          mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
  have hstep2 : (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2
      ≤ α ^ 2 * X ^ s + (2 * α + 1) := by
    have hpos : 0 ≤ X ^ s * (α + X) ^ 2 := mul_nonneg hXs (sq_nonneg _)
    calc (2 ^ (-(2 * α / 3)) * X ^ s) * (α + X) ^ 2
        = 2 ^ (-(2 * α / 3)) * (X ^ s * (α + X) ^ 2) := by ring
      _ ≤ X ^ s * (α + X) ^ 2 := mul_le_of_le_one_left hpos hb2
      _ ≤ α ^ 2 * X ^ s + (2 * α + 1) := hkey
  exact le_trans hstep1 hstep2

/-! ## The integral of the dominating function

`∫_{Iθ} (α² sin(2θ)^{17α/30-1} + (2α+1)) ≤ 1000`: the singular part contributes
`α²·3000/(17α) = 3000α/17 ≤ 3000/17`, the constant contributes `(2α+1)π/2 ≤ 6`. -/
theorem gamWeightDom (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1)) ≤ 1000 := by
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1)
    (by linarith) (by linarith)
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hf1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) Work.Spaces.Iθ :=
    hIntS.const_mul _
  have hf2 : MeasureTheory.IntegrableOn (fun _ : ℝ => (2 * α + 1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (2 * α + 1))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol2 : ∫ θ in Work.Spaces.Iθ, (2 * α + 1 : ℝ) = (2 * α + 1) * (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
    ring
  constructor
  · exact hf1.add hf2
  · have hsum : ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1)
        = α ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
          + (2 * α + 1) * (Real.pi / 2) := by
      rw [MeasureTheory.integral_add hf1 hf2, MeasureTheory.integral_const_mul, hvol2]
    rw [hsum]
    have h1 : α ^ 2 * (3000 / (17 * α)) ≤ 200 := by
      have he : α ^ 2 * (3000 / (17 * α)) = 3000 * α / 17 := by field_simp
      rw [he]
      nlinarith [hα1]
    have h2 : (2 * α + 1) * (Real.pi / 2) ≤ 6 := by
      have hp : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
      have ha : 2 * α + 1 ≤ 3 := by linarith
      have h0 : (0 : ℝ) ≤ 2 * α + 1 := by linarith
      nlinarith [mul_le_mul ha hp (by positivity : (0 : ℝ) ≤ Real.pi / 2)
        (by norm_num : (0 : ℝ) ≤ 3)]
    have hmb : α ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        ≤ α ^ 2 * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hBdS' (sq_nonneg α)
    linarith

/-! ## The main lemma -/

theorem gamWeightInt :
    ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) ≤ M := by
  refine ⟨1000, by norm_num, fun α hα hα1 => ?_⟩
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hdom := gamWeightDom α hα hα1
  -- the a.e. pointwise domination
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ α ^ 2 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) + (2 * α + 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    rw [Work.FTS.Nonlinear.RadialProd.smG]
    exact gamWeightPt α hα hα1 hθ
  -- measurability of the integrand
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam, Work.FTS.Nonlinear.RadialProd.smG]
    fun_prop
  have hfint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ :=
    hdom.1.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Work.FTS.Nonlinear.RadialProd.smG_nonneg h2))]
      exact h1)
  exact ⟨hfint, le_trans (MeasureTheory.integral_mono_ae hfint hdom.1 hpt) hdom.2⟩

end Work.FTS.Nonlinear.Pieces.RNP
