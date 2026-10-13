/-
# `wtoHQ_of_pointwise` — the pointwise form of `𝒲^{4,∞} ⟹ ℋ⁴`

The statement is `wtoHQ_quad` (`Submission/Work/FTS/Nonlinear/Pieces/RNP/wtoHQ_quad.lean`) with
the `𝒲^{4,∞}`-membership hypothesis `WlInfMem α 4 ((z+1)³/z²·f)` *and* the norm
`WlInf α 4 ((z+1)³/z²·f)` replaced by raw pointwise bounds with an arbitrary `W ≥ 0`:

* `hA : ∀ m ≤ 4, |(1+z)·w(z)·z^m·∂_z^m f(z,θ)| ≤ 200000·W` (`z > 0`, `θ ∈ (0,π/2)`);
* `hB : ∀ 1 ≤ i, l+i ≤ 4, |(1+z)·w(z)·z^l·∂_z^l(D_θ^i f)(z,θ)| ≤ 200000·W·(α+sin 2θ)·sin(2θ)^{α/5}`.

These are *exactly* the hypotheses `hA`/`hB` of the already proved
`Work.FTS.H2.Q.hkIntegrand_le_Q`, whose conclusion is the pointwise domination of the whole
`ℋ⁴`-integrand `HkIntegrand α 4 f` by `W²/(1+z)²·(2·10¹⁵·sin(2θ)^{-η}
+ 10¹⁶·(α+sin 2θ)²·sin(2θ)^{2α/5-γ})`.  Both factors of that majorant are integrable with
`α`-uniform bounds (`WtoH_Angular`, `WtoH_IntZ`), giving `HkSq α 4 f ≤ 10²⁰·W²`, hence
`Xn α f = √(HkSq α 4 f) ≤ 10¹⁰·W`.

Nothing else is used: in particular no `WlInf`/`WlInfMem` (suprema over the *closed* quadrant,
which the hypotheses do not control on the boundary lines `θ = 0, π/2`) enters the argument.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.FTS.H2.Q.WtoH_Radial_Q
import Submission.Work.FTS.H2.Q.WtoH_Mixed_Q
import Submission.Work.FTS.H2.Q.hkIntegrand_le_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

theorem wtoHQ_of_pointwise : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (W : ℝ),
    0 < α → α ≤ 1 → 0 ≤ W → Work.FTS.LocData.SmoothQuad f →
    (∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * W) →
    (∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) →
    Work.FTS.Nonlin.Xn α f ≤ C * W := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α f W hα hα1 hW hsq hA hB
  -- the pointwise bound of the `ℋ⁴`-integrand, with `Wl := W`
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ W ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    fun z hz θ hθ =>
      Work.FTS.H2.Q.hkIntegrand_le_Q (α := α) (f := f) hα hα1 hsq hW hA hB z hz θ hθ
  -- the angular integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
    intro z hz
    have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by rw [Work.Spaces.eta]; norm_num)
        (by rw [Work.Spaces.eta]; norm_num)).1
    have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.Spaces.integrableOn_angular_weight' hα hα1
    have hmaj : Integrable (fun θ : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
        * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul _
    have hIoo : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      exact Measure.restrict_congr_set haeeq.symm
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 f z θ
          ≤ W ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, W ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hmaj hae
      _ = W ^ 2 * (1 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
          refine mul_le_mul_of_nonneg_left
            (Work.Elliptic.WtoH_Angular hα hα1 (by norm_num) (by norm_num)) ?_
          exact mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))
  -- the radial integral
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 := by
    set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
    have hI : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz := by
      refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * K)).congr ?_
      filter_upwards with z
      ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, W ^ 2 * (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * (W ^ 2 * K) := by
          rw [show (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K)
              = fun z : ℝ => (1 / (1 + z) ^ 2) * (W ^ 2 * K) from by funext z; ring]
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * (W ^ 2 * K) :=
          mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2
            (mul_nonneg (sq_nonneg _) (by rw [hK]; norm_num))
      _ = K * 2 * W ^ 2 := by rw [hK]; ring
  have hSq : Work.Spaces.HkSq α 4 f ≤ 10 ^ 20 * W ^ 2 := by
    rw [Work.Spaces.HkSq]
    have hK2 : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 ≤ 10 ^ 20 * W ^ 2 := by
      nlinarith [sq_nonneg W]
    linarith [houter]
  have hmain : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ 10 ^ 10 * W := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * W ^ 2) :=
          Real.sqrt_le_sqrt hSq
      _ = 10 ^ 10 * W := by
          rw [show (10 : ℝ) ^ 20 * W ^ 2 = (10 ^ 10 * W) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (by norm_num) hW)
  simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hmain

end Work.FTS.Nonlinear.Pieces.RNP
