/-
# `OpenPkg/WtohWin/Assembly` — pointwise inputs ⟹ `ℋ⁴`

The assembly half of `Work.FTS.OpenPkg.wtoh_field_winf` (Elgindi's `WtoH`, tex 1237, in the
open-quadrant class): given the two pointwise bounds on the plain `z`-derivatives of `f`

```
hA : |(1+z)·w(z)·z^m·∂_z^m f| ≤ 200000·W                            (m ≤ 4)
hB : |(1+z)·w(z)·z^l·∂_z^l(D_θ^i f)| ≤ 200000·W·(α+sin 2θ)·sin(2θ)^{α/5}   (1 ≤ i, i+l ≤ 4)
```

(which `WtohWin.wtoh_radial_open` / `WtohWin.wtoh_mixed_open` supply with
`W = |((z+1)³/z²)f|_{𝒲^{4,∞}}`), the `ℋ⁴`-norm of `f` is bounded by `10¹⁰ W`.

The pointwise estimates are turned into a pointwise bound of the whole `ℋ⁴`-integrand by
`WtohWin.hkIntegrand_le_open`; both angular factors of the resulting majorant integrate to
`α`-uniform constants (`Work.Elliptic.WtoH_Angular`) while `∫_0^∞ (1+z)^{-2}dz ≤ 2`
(`Work.Elliptic.WtoH_IntZ`).  This module is the verbatim counterpart of
`Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise` with the `SmoothQuad f` hypothesis replaced by
`SmoothOpen f`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.WtoHQ
import Submission.Work.FTS.OpenPkg.WtohWin.Basics

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WtohWin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The pointwise form of `W^{4,∞} ⟹ ℋ⁴` in the open-quadrant class.**  Given the two
pointwise bounds `hA`, `hB` on the plain `z`-derivatives of `f`, the `ℋ⁴`-norm of `f` is
bounded by `10¹⁰ W`.  No finiteness of `f` beyond `SmoothOpen f` is used. -/
theorem wtoHQ_pointwise_open {α : ℝ} {f : ℝ → ℝ → ℝ} {W : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hW : 0 ≤ W)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hA : ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * W)
    (hB : ∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    Work.FTS.Nonlin.Xn α f ≤ 10 ^ 10 * W := by
  -- the pointwise bound of the `ℋ⁴`-integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ W ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    fun z hz θ hθ => hkIntegrand_le_open (α := α) (f := f) hα hα1 hsm hW hA hB z hz θ hθ
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

end Work.FTS.OpenPkg.WtohWin
