/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-uniform `z`-slice bound for mixed slots

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and
honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), every mixed slot `D_z^j D_θ^i f` with `i ≥ 1`
and `i + j ≤ 3` satisfies the **`θ`-uniform** radial `L²` bound

  `∫_z (D_z^j D_θ^i f(z,θ))² w(z)² dz  ≤  2 · |f|²_{ℋ⁴}`   for every `θ ∈ (0,π/2)`.

This is the radial dual of `Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform` (which is uniform
in `z`); it is *not* a consequence of a pointwise domination by `HkIntegrand` (a slice can exceed
its own angular average), and it is proved here by an **angular total-variation / Agmon device**
at fixed radius `z`:

* for `0 < a < θ < b < π/2` and every `z ∈ Iz` with `z > 0` the total-variation bound
  `Ξ(θ) ≤ (1/(b-a)) ∫_a^b Ξ + ∫_a^b |Ξ'|`, where `Ξ(σ) = (D_z^jD_θ^if(z,σ))² w(z)²` and
  `Ξ'(σ) = 2 D_z^jD_θ^if(z,σ) ∂_θ(D_z^jD_θ^if)(z,σ) w(z)²`,
  holds with **no** boundary trace hypothesis, because it is applied on an interior
  sub-interval `[a,b] ⊂ (0,π/2)`;
* both integrals are dominated by the *same* angular slice `M(z) = ∫_{Iθ} HkIntegrand α 4 f z ·`:
  `Ξ(z,σ) ≤ HkIntegrand α 4 f z σ` and
  `2|D_z^jD_θ^if · ∂_θ(D_z^jD_θ^if)| w² ≤ HkIntegrand α 4 f z σ`
  (the second is the AM–GM / two-slot bound, using
  `sin(2σ)·∂_θ(D_z^jD_θ^if) = D_z^jD_θ^{i+1}f` on the open quadrant, the hypothesis `i + j ≤ 3`,
  and `γ ≥ 1`);
* the interval is chosen with length exactly `1 < π/2`, so the coefficient is
  `1/(b-a) + 1 = 2`.

The passage from the pointwise-in-`z` inequality `Ξ(z,θ) ≤ 2 M(z)` to the statement is done in
the `ℝ≥0∞`-lintegral world (`ofReal(∫ f) ≤ ∫⁻ ofReal f`), which needs **no** measurability or
integrability of the individual angular slices.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe
import Submission.Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.absPairMulWLeHkIntegrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.NauxAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

variable {α : ℝ} {f : ℝ → ℝ → ℝ}

/-! ## Elementary facts about the weight `w` -/

theorem w_zero_fts : Work.Spaces.w 0 = 0 := by
  norm_num [Work.Spaces.w]

theorem w_nonneg_of_mem_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : 0 ≤ Work.Spaces.w z := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
  · rw [← h, w_zero_fts]
  · exact le_trans zero_le_one (Work.FTS.TransportS.one_le_w h)

theorem HkIntegrand_slice_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ :=
  integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f z σ

/-- `ENNReal.ofReal` of the integral of an a.e. nonnegative function is at most the lintegral of
`ENNReal.ofReal` of that function. -/
theorem ofReal_integral_le_lintegral {μ : Measure ℝ} {g : ℝ → ℝ} (hg : 0 ≤ᵐ[μ] g) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  by_cases h : Integrable g μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h hg]
  · rw [MeasureTheory.integral_undef h]
    simp

/-! ## The `θ`-derivative of the `θ`-slice -/

theorem hasDerivAt_slice_theta_fts {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn
      (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt

/-! ## The pointwise-in-`z` slice bound -/

theorem slice_le_two_sliceIntegral (hα : 0 < α) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 3)
    {a b θ : ℝ} (ha : 0 < a) (haθ : a ≤ θ) (hθb : θ ≤ b) (hb : b < π / 2)
    (hba : b - a = 1) :
    ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- `z = 0`: the weight vanishes
    have hw : Work.Spaces.w z = 0 := by rw [← hz0]; exact w_zero_fts
    rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (HkIntegrand_slice_nonneg α f z)
  · -- `z > 0`: the total-variation / average device
    have hab : a < b := by linarith [haθ, hθb]
    have hsub : ∀ σ ∈ Set.Icc a b, σ ∈ Set.Ioo 0 (π / 2) := fun σ hσ =>
      ⟨lt_of_lt_of_le ha hσ.1, lt_of_le_of_lt hσ.2 hb⟩
    have hcont : ContinuousOn (fun σ => Work.Spaces.mixed j i f z σ) (Set.Icc a b) :=
      ((hF.mixed j i).curry_θ hzpos).continuousOn.mono hsub
    have hcontpth : ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed j i f) z σ)
        (Set.Icc a b) :=
      (((hF.mixed j i).pth).curry_θ hzpos).continuousOn.mono hsub
    have hcontU : ContinuousOn
        (fun σ => (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Icc a b) :=
      (hcont.pow 2).mul continuousOn_const
    have hIntU : IntervalIntegrable
        (fun σ => (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        volume a b := by
      refine (show ContinuousOn
        (fun σ => (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        (Set.uIcc a b) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab.le]; exact hcontU
    have hcontF : ContinuousOn
        (fun σ => 2 * |Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2)
        (Set.Icc a b) :=
      ((continuousOn_const.mul (hcont.mul hcontpth).abs).mul continuousOn_const)
    have hIntF : IntervalIntegrable
        (fun σ => 2 * |Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2)
        volume a b := by
      refine (show ContinuousOn
        (fun σ => 2 * |Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2)
        (Set.uIcc a b) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab.le]; exact hcontF
    -- the derivative of `U (σ) = (D_z^jD_θ^if(z,σ))² w(z)²` on `[a,b]`
    have hderiv : ∀ x ∈ Set.Icc a b,
        HasDerivAt (fun σ => (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
          (2 * Work.Spaces.mixed j i f z x
            * Work.Spaces.pth (Work.Spaces.mixed j i f) z x * (Work.Spaces.w z) ^ 2) x := by
      intro x hx
      have hxI : x ∈ Set.Ioo 0 (π / 2) := hsub x hx
      have hd : HasDerivAt (fun σ => Work.Spaces.mixed j i f z σ)
          (Work.Spaces.pth (Work.Spaces.mixed j i f) z x) x :=
        hasDerivAt_slice_theta_fts (hF.mixed j i) hzpos hxI
      have h2 : HasDerivAt
          (fun σ => Work.Spaces.mixed j i f z σ * Work.Spaces.mixed j i f z σ)
          (2 * Work.Spaces.mixed j i f z x
            * Work.Spaces.pth (Work.Spaces.mixed j i f) z x) x := by
        have h := hd.mul hd
        have he : (2 * Work.Spaces.mixed j i f z x
              * Work.Spaces.pth (Work.Spaces.mixed j i f) z x)
            = Work.Spaces.pth (Work.Spaces.mixed j i f) z x * Work.Spaces.mixed j i f z x
              + Work.Spaces.mixed j i f z x
                * Work.Spaces.pth (Work.Spaces.mixed j i f) z x := by ring
        rw [he]; exact h
      have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)
      convert h3 using 1 <;> (try funext σ) <;> ring
    -- the total-variation bound
    have hTV : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (1 / (b - a)) * (∫ σ in a..b,
              (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
          + ∫ σ in a..b, |2 * Work.Spaces.mixed j i f z σ
              * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ * (Work.Spaces.w z) ^ 2| :=
      Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.tvAverageLe hab haθ hθb hderiv
        (by
          refine (show ContinuousOn
            (fun σ => 2 * Work.Spaces.mixed j i f z σ
              * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ * (Work.Spaces.w z) ^ 2)
            (Set.uIcc a b) from ?_).intervalIntegrable
          rw [Set.uIcc_of_le hab.le]
          exact (((continuousOn_const.mul hcont).mul hcontpth).mul continuousOn_const))
        hIntU
    -- rewrite the absolute value
    have hAbsEq : (∫ σ in a..b, |2 * Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ * (Work.Spaces.w z) ^ 2|)
        = ∫ σ in a..b, 2 * |Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2 := by
      refine intervalIntegral.integral_congr fun σ _ => ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_mul]
      ring
    -- the two integrals, each dominated by the angular slice of `HkIntegrand`
    have hIntH : IntervalIntegrable (fun σ => Work.Spaces.HkIntegrand α 4 f z σ) volume a b := by
      refine (show IntegrableOn (fun σ => Work.Spaces.HkIntegrand α 4 f z σ)
        (Set.uIcc a b) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hab.le]
      exact (hmem.1 z hz).mono_set (fun σ hσ => ⟨le_of_lt (lt_of_lt_of_le ha hσ.1),
        le_of_lt (lt_of_le_of_lt hσ.2 hb)⟩)
    have hsubIntH : (∫ σ in a..b, Work.Spaces.HkIntegrand α 4 f z σ)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
        (Eventually.of_forall fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f z σ) ?_
      exact Eventually.of_forall fun σ hσ => ⟨le_of_lt (lt_trans ha hσ.1),
        le_of_lt (lt_of_le_of_lt hσ.2 hb)⟩
    have hbound1 : (∫ σ in a..b, (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ := by
      have hpoint : ∀ σ ∈ Set.Icc a b,
          (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
        intro σ hσ
        obtain ⟨hσ0, hσ1⟩ := hsub σ hσ
        have hs : 0 < Real.sin (2 * σ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have hrp : 1 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
          have h1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
          have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _)
            (show -(Work.Spaces.gam α) ≤ 0 by linarith)
          rwa [Real.rpow_zero] at h
        have h1 : (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ (Work.Spaces.mixed j i f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
          rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hs]
          have hnn : 0 ≤ (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
            mul_nonneg (sq_nonneg _) (sq_nonneg _)
          calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
              = (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 := by ring
            _ ≤ (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
                mul_le_mul_of_nonneg_left hrp hnn
            _ = (Work.Spaces.mixed j i f z σ) ^ 2
                  * ((Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by ring
        exact h1.trans (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ i j hi (by omega))
      exact (intervalIntegral.integral_mono_on hab.le hIntU hIntH hpoint).trans hsubIntH
    have hbound2 : (∫ σ in a..b, 2 * |Work.Spaces.mixed j i f z σ
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ := by
      have hpoint : ∀ σ ∈ Set.Icc a b,
          2 * |Work.Spaces.mixed j i f z σ
              * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        fun σ hσ =>
          Work.FTS.StrongEps.E4R3.NauxAux.ZSliceAux.absPairMulWLeHkIntegrand
            hα hF j i hi hij hz (hsub σ hσ)
      exact (intervalIntegral.integral_mono_on hab.le hIntF hIntH hpoint).trans hsubIntH
    -- combine
    have hstep1 : (1 / (b - a)) * (∫ σ in a..b,
          (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ := by
      rw [hba]
      simpa using hbound1
    have hMnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ :=
      HkIntegrand_slice_nonneg α f z
    calc (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (1 / (b - a)) * (∫ σ in a..b,
              (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
            + ∫ σ in a..b, |2 * Work.Spaces.mixed j i f z σ
                * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ * (Work.Spaces.w z) ^ 2| := hTV
      _ = (1 / (b - a)) * (∫ σ in a..b,
              (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
            + ∫ σ in a..b, 2 * |Work.Spaces.mixed j i f z σ
                * Work.Spaces.pth (Work.Spaces.mixed j i f) z σ| * (Work.Spaces.w z) ^ 2 := by
            rw [hAbsEq]
      _ ≤ 2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ) := by
            linarith

/-! ## The main theorem -/

theorem zSliceNormLeHkSq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 2 * Work.Spaces.HkSq α 4 f := by
  intro j i hi hij θ hθ hθ2
  -- an interval `[a,b] ⊆ (0,π/2)` of length `1` containing `θ`
  have hpi2 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  obtain ⟨a, b, ha, haθ, hθb, hb, hba⟩ : ∃ a b : ℝ,
      0 < a ∧ a ≤ θ ∧ θ ≤ b ∧ b < Real.pi / 2 ∧ b - a = 1 := by
    by_cases hcase : θ ≤ Real.pi / 2 - 1
    · refine ⟨θ / 2, θ / 2 + 1, by linarith, by linarith, by linarith, by linarith,
        by ring⟩
    · push Not at hcase
      refine ⟨(θ + Real.pi / 2) / 2 - 1, (θ + Real.pi / 2) / 2, ?_, ?_, ?_, ?_, by ring⟩
      · linarith
      · linarith
      · linarith
      · linarith
  -- the pointwise-in-`z` bound
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ 2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ) :=
    slice_le_two_sliceIntegral hα hF hmem j i hi hij ha haθ hθb hb hba
  -- the `ℝ≥0∞` chain
  have hMnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => 2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ)) :=
    Eventually.of_forall fun z => mul_nonneg (by norm_num) (HkIntegrand_slice_nonneg α f z)
  have hInt2M : Integrable
      (fun z => 2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ))
      (volume.restrict Work.Spaces.Iz) := hmem.2.const_mul 2
  have hmain : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ENNReal.ofReal (2 * Work.Spaces.HkSq α 4 f) := by
    calc ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          ofReal_integral_le_lintegral
            (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (2 * (∫ σ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z σ)) :=
          MeasureTheory.lintegral_mono_ae
            (ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
              ENNReal.ofReal_le_ofReal (hpt z hz))
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            2 * (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt2M hMnn).symm
      _ = ENNReal.ofReal (2 * Work.Spaces.HkSq α 4 f) := by
          congr 1
          rw [MeasureTheory.integral_const_mul]
          rfl
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num) (Work.Spaces.HkSq_nonneg α 4 f))).mp hmain

end Work.FTS.StrongEps.E4R3.NauxAux
