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

namespace Work.FTS.H2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Elgindi's `WtoH` (tex 1237) in the *interior* class `Work.FTS.Nonlin.RegQ` of the frozen
`Submission/Work/FTS/Vocab.lean`: if `((z+1)³/z²) f ∈ 𝒲^{4,∞}` and `RegQ α 4 f`, then
`|f|_{ℋ⁴} ≤ C |((z+1)³/z²) f|_{𝒲^{4,∞}}`, `C` universal.  This is the design document's
`WtoHQ` (§3.3 L-N4.5), used in rows #11, #15 and #19 of the table of §3.4 (where `f` is
`ℛ(Φ̃_*)` or `U(Φ̃_*)∂_θF_*`, whose `(z+1)/z`-weighted version is in `𝒲^{4,∞}`).

It is the replaceable form of `Work.Elliptic.WtoH`, whose hypotheses use `Spaces.SmoothNbhd`
(analyticity on a neighbourhood of the closed quadrant — false for `F_*` and for the stream
functions; design §5 T1).  The proof is the delivered one: the main term of `|f|_{ℋ⁴}` is
`|D_z⁴ f w/√(sin(2θ)^η)|_{L²}`, bounded by `C∑_{i=1}^4|(z+1)∂_z^i f z^i w|_{L∞}` (using only
`∫sin(2θ)^{-η} < ∞`), and `|((z+1)³/z²) f|_{𝒲^{4,∞}}` dominates
`∑_{i≤4}|(z+1)^{i+3}∂_z^i k|_{L∞}` for `f = z²k`.  On the boundary lines `θ = 0, π/2` the
`θ`-weights in the two norms are finite, so the identity only has to be assembled on the open
quadrant, where `SmoothQuad` (inside `RegQ`) supplies the differentiability.

The pieces of the assembly (the genuine-`C^∞` versions of the pointwise estimates, in
`Submission/Work/FTS/H2/Q/`) are `WtoH_Radial_Q`, `WtoH_Mixed_Q` and `hkIntegrand_le_Q`; the
integral comparison with `WtoH_Angular` and `WtoH_IntZ` is performed here. -/
theorem WtoHQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
    Work.FTS.Nonlin.RegQ α 4 f →
    Work.FTS.Nonlin.Xn α f ≤ C * Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α f hα hα1 hmem hreg
  obtain ⟨hsq, _hmemHk, _hbd⟩ := hreg
  set G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ with hG
  set Wl : ℝ := Work.Spaces.WlInf α 4 G with hWl
  have hWlnn : 0 ≤ Wl := by
    rw [hWl, Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmem)
      (Work.Spaces.wlThSum_nonneg α 4 G hmem)
  -- the two pointwise estimates of the paper
  have hrad := Q.WtoH_Radial_Q (α := α) (f := f) hα hα1 hsq hmem
  have hmix := Q.WtoH_Mixed_Q (α := α) (f := f) hα hα1 hsq hmem
  -- the pointwise bound of the `ℋ⁴`-integrand on the open quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
    fun z hz θ hθ => Q.hkIntegrand_le_Q (α := α) (f := f) hα hα1 hsq hWlnn hrad hmix z hz θ hθ
  -- the angular integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
    intro z hz
    have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by rw [Work.Spaces.eta]; norm_num)
        (by rw [Work.Spaces.eta]; norm_num)).1
    have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.Spaces.integrableOn_angular_weight' hα hα1
    have hmaj : Integrable (fun θ : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2)
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
          ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hmaj hae
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ Wl ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
          refine mul_le_mul_of_nonneg_left
            (Work.Elliptic.WtoH_Angular hα hα1 (by norm_num) (by norm_num)) ?_
          exact mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _))
  -- the radial integral
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * Wl ^ 2 := by
    set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
    have hI : IntegrableOn (fun z : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz := by
      refine (Work.Elliptic.WtoH_IntZ.1.mul_const (Wl ^ 2 * K)).congr ?_
      filter_upwards with z
      ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, Wl ^ 2 * (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * (Wl ^ 2 * K) := by
          rw [show (fun z : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2) * K)
              = fun z : ℝ => (1 / (1 + z) ^ 2) * (Wl ^ 2 * K) from by funext z; ring]
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * (Wl ^ 2 * K) :=
          mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2
            (mul_nonneg (sq_nonneg _) (by rw [hK]; norm_num))
      _ = K * 2 * Wl ^ 2 := by rw [hK]; ring
  have hSq : Work.Spaces.HkSq α 4 f ≤ 10 ^ 20 * Wl ^ 2 := by
    rw [Work.Spaces.HkSq]
    have hK2 : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * Wl ^ 2 ≤ 10 ^ 20 * Wl ^ 2 := by
      nlinarith [sq_nonneg Wl]
    linarith [houter]
  have hmain : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ 10 ^ 10 * Wl := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * Wl ^ 2) :=
          Real.sqrt_le_sqrt hSq
      _ = 10 ^ 10 * Wl := by
          rw [show (10 : ℝ) ^ 20 * Wl ^ 2 = (10 ^ 10 * Wl) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (by norm_num) hWlnn)
  simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hWl] using hmain

end Work.FTS.H2
