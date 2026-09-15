import Submission.FUP.Spec
import Submission.Commons.Analysis.Fourier.exists_schwartzMap_fourier_support_ball
import Submission.Commons.Analysis.Fourier.fourier_mul_support_Lp
import Submission.Commons.Analysis.Fourier.fourier_comp_smul_support_schwartz
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.L2Space

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators FourierTransform
open Submission.FUP

set_option autoImplicit false
set_option linter.style.haveILetI false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

section Dilate

/-- The continuous linear equivalence `x ↦ c • x` of `ℝᵈ`, for `c ≠ 0`. -/
noncomputable def smulCLE (c : ℝ) (hc : c ≠ 0) : ℝᵈ ≃L[ℝ] ℝᵈ where
  toFun := fun x => c • x
  invFun := fun x => c⁻¹ • x
  map_add' := fun x y => smul_add c x y
  map_smul' := fun a x => smul_comm c a x
  left_inv := fun x => by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv := fun x => by simp [smul_smul, mul_inv_cancel₀ hc]
  continuous_toFun := continuous_const_smul c
  continuous_invFun := continuous_const_smul c⁻¹

@[simp] lemma smulCLE_apply (c : ℝ) (hc : c ≠ 0) (x : ℝᵈ) : smulCLE c hc x = c • x := rfl

/-- The dilation `x ↦ φ (c • x)` of a Schwartz function, as a Schwartz function. -/
noncomputable def dilateSchwartz (c : ℝ) (hc : c ≠ 0) (φ : SchwartzMap ℝᵈ ℂ) :
    SchwartzMap ℝᵈ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (smulCLE c hc) φ

lemma dilateSchwartz_apply (c : ℝ) (hc : c ≠ 0) (φ : SchwartzMap ℝᵈ ℂ) (x : ℝᵈ) :
    (dilateSchwartz c hc φ : ℝᵈ → ℂ) x = (φ : ℝᵈ → ℂ) (c • x) := by
  simp [dilateSchwartz, smulCLE_apply]

/-- **Fourier support of a dilated Schwartz function.**  If `𝓕φ` vanishes outside the unit ball,
then the Fourier transform of `x ↦ φ (c • x)` vanishes outside the ball of radius `c`. -/
lemma dilateSchwartz_supp {c : ℝ} (hc : 0 < c) (φ : SchwartzMap ℝᵈ ℂ)
    (hφ : ∀ ξ, ξ ∉ closedBall (0 : ℝᵈ) 1 → FourierTransform.fourier φ ξ = 0) :
    ∀ ξ, ξ ∉ closedBall (0 : ℝᵈ) c →
      FourierTransform.fourier (dilateSchwartz c hc.ne' φ : ℝᵈ → ℂ) ξ = 0 := by
  intro ξ hξ
  have h := Commons.Analysis.Fourier.fourier_comp_smul_support_schwartz (d := d) φ hc
    (K := closedBall (0 : ℝᵈ) 1) hφ
  have hcoe : (dilateSchwartz c hc.ne' φ : ℝᵈ → ℂ)
      = fun x => (φ : ℝᵈ → ℂ) (c • x) := by
    funext x; exact dilateSchwartz_apply c hc.ne' φ x
  rw [hcoe]
  refine h ξ (fun a ha heq => ?_)
  have hξn : c < ‖ξ‖ := by simpa [mem_closedBall, dist_eq_norm] using hξ
  have han : ‖a‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using ha
  have hnorm : ‖ξ‖ = c * ‖a‖ := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  nlinarith [norm_nonneg a]

end Dilate

/-- Elementary decay of a negative power under a dilation with `c ∈ (0,1)`. -/
lemma rpow_neg_half_dilate (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (1 + c ^ 2 * s) ^ (-(d : ℝ) / 2) ≤ (c ^ d)⁻¹ * (1 + s) ^ (-(d : ℝ) / 2) := by
  have hz : -(d : ℝ) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ (d : ℝ) := by positivity
    linarith
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  have hbase : 0 < c ^ 2 * (1 + s) := by positivity
  have hkey : c ^ 2 * (1 + s) ≤ 1 + c ^ 2 * s := by nlinarith [sq_nonneg c, sq_nonneg (c - 1)]
  have h := Real.rpow_le_rpow_of_nonpos hbase hkey hz
  have hrw : (c ^ 2 * (1 + s)) ^ (-(d : ℝ) / 2)
      = (c ^ d)⁻¹ * (1 + s) ^ (-(d : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ c ^ 2) hs1.le]
    have hcd : (c ^ 2) ^ (-(d : ℝ) / 2) = (c ^ d)⁻¹ := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le]
      rw [show ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by push_cast; ring]
      rw [Real.rpow_neg hc.le, Real.rpow_natCast]
    rw [hcd]
  rwa [hrw] at h

section Main

/-- **The higher-dimensional Beurling–Malliavin theorem and the `⟨x⟩^{-d}` bound.**

The `L²` form of the Beurling–Malliavin multiplier theorem used in §6.1 of Cohen's paper
follows from the theorem itself (`Spec.higher_dim_BM_statement`): multiplying the function
produced by Beurling–Malliavin by a fixed Schwartz beacon with Fourier transform supported in a
small ball produces a function which, in addition to the exponential bound `e^{cσω}`, satisfies
the global decay bound `‖f x‖ ≤ M ⟨x⟩^{-d}`, and which is bounded below on a small ball (whence
the `L²` normalisation). -/
theorem higher_dim_BM_damping_of_BM (hd : 1 ≤ d)
    (hBM : Spec.higher_dim_BM_statement (d := d)) :
    Spec.higher_dim_BM_damping_statement (d := d) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  intro Creg Cgr hCreg hCgr σ hσ0 hσ1
  obtain ⟨φ, Cφ, hCφpos, hφ0, hφsupp, hφdec⟩ :=
    Commons.Analysis.Fourier.exists_schwartzMap_fourier_support_ball (d := d) (by omega)
  set c₀ : ℝ := σ / 2 with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; linarith
  have hc₀lt : c₀ < 1 := by rw [hc₀def]; linarith
  have hc₀ne : c₀ ≠ 0 := hc₀pos.ne'
  set φs : SchwartzMap ℝᵈ ℂ := dilateSchwartz c₀ hc₀ne φ with hφsdef
  have hφscoe : (φs : ℝᵈ → ℂ) = fun x => (φ : ℝᵈ → ℂ) (c₀ • x) := by
    funext x; rw [hφsdef]; exact dilateSchwartz_apply c₀ hc₀ne φ x
  have hφs0 : (φs : ℝᵈ → ℂ) 0 = 1 := by rw [hφscoe]; simpa using hφ0
  have hφssupp : ∀ ξ, ξ ∉ closedBall (0 : ℝᵈ) c₀ →
      FourierTransform.fourier (φs : ℝᵈ → ℂ) ξ = 0 := by
    rw [hφsdef]; exact dilateSchwartz_supp hc₀pos φ hφsupp
  have hφsdec : ∀ x : ℝᵈ,
      ‖(φs : ℝᵈ → ℂ) x‖ ≤ Cφ * (c₀ ^ d)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) := by
    intro x
    rw [hφscoe]
    refine (hφdec (c₀ • x)).trans ?_
    have hnorm : ‖c₀ • x‖ ^ 2 = c₀ ^ 2 * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc₀pos]; ring
    rw [hnorm]
    have h := rpow_neg_half_dilate c₀ hc₀pos hc₀lt.le d (‖x‖ ^ 2) (sq_nonneg _)
    calc Cφ * (1 + c₀ ^ 2 * ‖x‖ ^ 2) ^ (-(d:ℝ)/2)
        ≤ Cφ * ((c₀ ^ d)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2)) :=
          mul_le_mul_of_nonneg_left h hCφpos.le
      _ = Cφ * (c₀ ^ d)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) := by ring
  -- a neighbourhood of the origin on which the beacon is bounded below
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ x : ℝᵈ, dist x 0 < δ →
      dist ((φs : ℝᵈ → ℂ) x) ((φs : ℝᵈ → ℂ) 0) < 1/4 := by
    have hcont := Metric.continuousAt_iff.mp (φs.continuous.continuousAt (x := (0:ℝᵈ)))
      (1/4) (by norm_num)
    obtain ⟨δ, hδpos, hδ⟩ := hcont
    exact ⟨δ, hδpos, fun x hx => hδ hx⟩
  set ρ : ℝ := min (δ/2) (1/2) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by norm_num)
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hφslow : ∀ x : ℝᵈ, ‖x‖ ≤ ρ → (3/4 : ℝ) ≤ ‖(φs : ℝᵈ → ℂ) x‖ := by
    intro x hx
    have hdist : dist x 0 < δ := by rw [dist_zero_right]; linarith [hx, min_le_left (δ/2) (1/2)]
    have hb := hδ x hdist
    rw [hφs0] at hb
    have hb' : ‖(φs : ℝᵈ → ℂ) x - 1‖ < 1/4 := by simpa [dist_eq_norm] using hb
    have h1 : (1:ℝ) ≤ ‖(φs : ℝᵈ → ℂ) x‖ + ‖(φs : ℝᵈ → ℂ) x - 1‖ := by
      have h2 := norm_sub_le ((φs : ℝᵈ → ℂ) x) (((φs : ℝᵈ → ℂ) x) - 1)
      simpa using h2
    linarith
  -- the Beurling–Malliavin output
  obtain ⟨c, rmin, M, hcpos, hrminpos, hMpos, hmain⟩ :=
    hBM Creg Cgr hCreg hCgr c₀ hc₀pos hc₀lt
  refine ⟨c / 2, min rmin ρ, 2 * M * (Cφ * (c₀ ^ d)⁻¹),
    min (1/2) ((1/4) * (volume (closedBall (0:ℝᵈ) (min rmin ρ))).toReal),
    by linarith, lt_min hrminpos hρpos, by positivity, ?_, ?_⟩
  · refine lt_min (by norm_num) ?_
    have hvolpos : (0:ℝ) < (volume (closedBall (0:ℝᵈ) (min rmin ρ))).toReal := by
      rw [EuclideanSpace.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (le_of_lt (lt_min hrminpos hρpos)),
        ENNReal.toReal_ofReal (by positivity)]
      positivity
    positivity
  · intro ω hωnonpos hωzero hωcont hωreg hωgrowth
    obtain ⟨f, hfsupp, hflow, hfexp⟩ := hmain ω hωnonpos hωzero hωcont hωreg hωgrowth
    obtain ⟨h, hheq, hhsupp⟩ :=
      Commons.Analysis.Fourier.fourier_mul_support_Lp f φs hfsupp hφssupp
    set g : Lp ℂ 2 (volume : Measure ℝᵈ) := (2:ℂ) • h with hgdef
    have hgsmul : ∀ᵐ x ∂(volume : Measure ℝᵈ),
        (g : ℝᵈ → ℂ) x = (2:ℂ) • ((h : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x := by
      rw [hgdef]; exact Lp.coeFn_smul (2:ℂ) h
    -- Fourier support
    have hgsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0:ℝᵈ) σ →
        ((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 := by
      filter_upwards [hhsupp,
        Lp.coeFn_smul (2:ℂ) (𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ))] with ξ hxi hcoe
      intro hξ
      have hgs : (𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ))
          = (2:ℂ) • (𝓕 h : Lp ℂ 2 (volume : Measure ℝᵈ)) := by
        rw [hgdef]; exact fourier_smul (2:ℂ) h
      rw [hgs, hcoe, Pi.smul_apply]
      have hcon : ∀ a ∈ closedBall (0:ℝᵈ) c₀, ∀ b ∈ closedBall (0:ℝᵈ) c₀, ξ ≠ a + b := by
        intro a ha b hb heq
        have han : ‖a‖ ≤ c₀ := by simpa [mem_closedBall, dist_eq_norm] using ha
        have hbn : ‖b‖ ≤ c₀ := by simpa [mem_closedBall, dist_eq_norm] using hb
        have hξn : σ < ‖ξ‖ := by simpa [mem_closedBall, dist_eq_norm] using hξ
        have hle : ‖ξ‖ ≤ σ := by
          rw [heq]
          calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
            _ ≤ c₀ + c₀ := add_le_add han hbn
            _ = σ := by rw [hc₀def]; ring
        linarith
      rw [hxi hcon, smul_zero]
    -- global exponential bound
    have hgexp : ∀ᵐ x ∂(volume : Measure ℝᵈ),
        ‖(g : ℝᵈ → ℂ) x‖ ≤ 2 * M * (Cφ * (c₀ ^ d)⁻¹) * Real.exp (c / 2 * σ * ω x) := by
      filter_upwards [hgsmul, hheq, hfexp] with x hgx hhx hfx
      rw [hgx, norm_smul, hhx, norm_mul]
      have hn2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [hn2]
      have hφsA : ‖(φs : ℝᵈ → ℂ) x‖ ≤ Cφ * (c₀ ^ d)⁻¹ := by
        refine (hφsdec x).trans ?_
        have h1 : (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) ≤ 1 := by
          refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
          · have : (0:ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
            linarith
          · have : (0:ℝ) ≤ (d:ℝ) := by positivity
            linarith
        have hA : (0:ℝ) ≤ Cφ * (c₀ ^ d)⁻¹ := by positivity
        calc Cφ * (c₀ ^ d)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2)
            ≤ Cφ * (c₀ ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 hA
          _ = Cφ * (c₀ ^ d)⁻¹ := by ring
      have hcc : c * c₀ * ω x = c / 2 * σ * ω x := by rw [hc₀def]; ring
      calc 2 * (‖(f : ℝᵈ → ℂ) x‖ * ‖(φs : ℝᵈ → ℂ) x‖)
          ≤ 2 * ((M * Real.exp (c / 2 * σ * ω x)) * (Cφ * (c₀ ^ d)⁻¹)) := by
            rw [← hcc]
            have h1 : ‖(f : ℝᵈ → ℂ) x‖ * ‖(φs : ℝᵈ → ℂ) x‖
                ≤ (M * Real.exp (c * c₀ * ω x)) * (Cφ * (c₀ ^ d)⁻¹) :=
              calc ‖(f : ℝᵈ → ℂ) x‖ * ‖(φs : ℝᵈ → ℂ) x‖
                  ≤ (M * Real.exp (c * c₀ * ω x)) * ‖(φs : ℝᵈ → ℂ) x‖ :=
                    mul_le_mul_of_nonneg_right hfx (norm_nonneg _)
                _ ≤ (M * Real.exp (c * c₀ * ω x)) * (Cφ * (c₀ ^ d)⁻¹) :=
                    mul_le_mul_of_nonneg_left hφsA
                      (mul_nonneg (le_of_lt hMpos) (Real.exp_pos _).le)
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 2 * M * (Cφ * (c₀ ^ d)⁻¹) * Real.exp (c / 2 * σ * ω x) := by ring
    -- global decay bound
    have hgdec : ∀ᵐ x ∂(volume : Measure ℝᵈ),
        ‖(g : ℝᵈ → ℂ) x‖ ≤ 2 * M * (Cφ * (c₀ ^ d)⁻¹) * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) := by
      filter_upwards [hgsmul, hheq, hfexp] with x hgx hhx hfx
      rw [hgx, norm_smul, hhx, norm_mul]
      have hn2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [hn2]
      have hexp1 : Real.exp (c * c₀ * ω x) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have h1 : 0 < c * c₀ := mul_pos hcpos hc₀pos
        nlinarith [hωnonpos x]
      have hfx' : ‖(f : ℝᵈ → ℂ) x‖ ≤ M := by
        calc ‖(f : ℝᵈ → ℂ) x‖ ≤ M * Real.exp (c * c₀ * ω x) := hfx
          _ ≤ M * 1 := by
              exact mul_le_mul_of_nonneg_left hexp1 (le_of_lt hMpos)
          _ = M := by ring
      calc 2 * (‖(f : ℝᵈ → ℂ) x‖ * ‖(φs : ℝᵈ → ℂ) x‖)
          ≤ 2 * (M * (Cφ * (c₀ ^ d)⁻¹ * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul hfx' (hφsdec x) (norm_nonneg _) (le_of_lt hMpos)
        _ = 2 * M * (Cφ * (c₀ ^ d)⁻¹) * (1 + ‖x‖ ^ 2) ^ (-(d:ℝ)/2) := by ring
    -- lower bound on the small ball
    have hglow : ∀ᵐ x ∂(volume.restrict (closedBall (0:ℝᵈ) (min rmin ρ))),
        (1/2 : ℝ) ≤ ‖(g : ℝᵈ → ℂ) x‖ := by
      have hsub : closedBall (0:ℝᵈ) (min rmin ρ) ⊆ closedBall (0:ℝᵈ) rmin :=
        closedBall_subset_closedBall (min_le_left _ _)
      have hflow' := ae_restrict_of_ae_restrict_of_subset hsub hflow
      filter_upwards [hflow', ae_restrict_of_ae hheq, ae_restrict_of_ae hgsmul,
        ae_restrict_mem measurableSet_closedBall] with x hx1 hx2 hx3 hxmem
      have hxle : ‖x‖ ≤ ρ := by
        rw [mem_closedBall, dist_zero_right] at hxmem
        exact hxmem.trans (min_le_right _ _)
      have hφx := hφslow x hxle
      rw [hgdef, hx3, norm_smul, hx2, norm_mul]
      have hn2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [hn2]
      nlinarith [hx1, hφx, norm_nonneg ((f : ℝᵈ → ℂ) x), norm_nonneg ((φs : ℝᵈ → ℂ) x)]
    refine ⟨g, hgsupp, hglow, ?_, hgexp, hgdec⟩
    -- `L²` normalisation
    have hgint : Integrable (fun x : ℝᵈ => ‖(g : ℝᵈ → ℂ) x‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
    have hlow2 : ∀ᵐ x ∂(volume.restrict (closedBall (0:ℝᵈ) (min rmin ρ))),
        (1/4 : ℝ) ≤ ‖(g : ℝᵈ → ℂ) x‖ ^ 2 :=
      hglow.mono (fun x hx => by nlinarith [hx, norm_nonneg ((g : ℝᵈ → ℂ) x)])
    have hsub : closedBall (0:ℝᵈ) (min rmin ρ) ⊆ ball (0:ℝᵈ) 1 := by
      intro x hx
      rw [mem_closedBall, dist_zero_right] at hx
      rw [mem_ball, dist_zero_right]
      refine lt_of_le_of_lt (hx.trans (min_le_right _ _)) ?_
      exact hρ1
    have hne : volume (closedBall (0:ℝᵈ) (min rmin ρ)) ≠ ∞ := by
      refine ne_of_lt ?_
      exact (isCompact_closedBall (0:ℝᵈ) (min rmin ρ)).measure_lt_top
    calc min (1/2) ((1/4) * (volume (closedBall (0:ℝᵈ) (min rmin ρ))).toReal)
        ≤ (1/4) * (volume (closedBall (0:ℝᵈ) (min rmin ρ))).toReal := min_le_right _ _
      _ = ∫ x in closedBall (0:ℝᵈ) (min rmin ρ), (1/4 : ℝ) := by
            rw [setIntegral_const]; simp [MeasureTheory.Measure.real, smul_eq_mul]; ring
      _ ≤ ∫ x in closedBall (0:ℝᵈ) (min rmin ρ), ‖(g : ℝᵈ → ℂ) x‖ ^ 2 :=
            setIntegral_mono_ae_restrict (integrableOn_const hne) hgint.integrableOn hlow2
      _ ≤ ∫ x in ball (0:ℝᵈ) 1, ‖(g : ℝᵈ → ℂ) x‖ ^ 2 :=
            setIntegral_mono_set hgint.integrableOn
              (by filter_upwards with x; positivity) (Filter.Eventually.of_forall hsub)

end Main

end Submission.FUP
