/-
# `Work.FTS_RegExport.RXB.DzSlice_l2` — the `L²`-size of the first `D_z`-slot as a function of `θ`

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and
honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4`), the angular slice function

  `θ ↦ √(∫_0^∞ (D_z f(t,θ) · w(t))² dt)  =  √(∫_t (DzIter 1 f t θ · w t)²)`

is finite a.e., a.e.-strongly measurable, and its square is integrable in `θ` with

  `∫_{Iθ} (√(∫_t (DzIter 1 f t θ · w t)²))² ≤ HkSq α 4 f`.

The point is that the radial weight `w` and the angular weight `sin(2θ)^{η}` split cleanly in
the first slot of `HkIntegrand`:

  `(DzIter 1 f t θ · w t)² = sin(2θ)^{η} · (DzIter 1 f t θ · w t / sin(2θ)^{η/2})²`,

and for `θ ∈ (0,π/2)` we have `sin(2θ)^{η} ≤ 1`, so the left-hand side is dominated
*pointwise in `t`* by the corresponding summand of `HkIntegrand α 4 f t θ`
(`Work.Spaces.sq_le_HkIntegrand_z`).  Integrating in `t` and then in `θ` and swapping the two
iterated integrals with `Work.FTS_RegExport.C4.HkSqSwap_C4` (valid because `f` is smooth on the
open quadrant, hence the integrand is a.e. strongly measurable for the product measure) gives
the bound.

The file is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false

/-! ## The joint continuity of the slot integrand on the open quadrant -/

/-- The integrand `(t,θ) ↦ (D_z f(t,θ) · w(t))²` is continuous on the open quadrant `(0,∞) ×
(0,π/2)`: `D_z f` is smooth there (`SmoothOpen.DzIter`) and the radial weight `w` is continuous
because the denominator `t²` does not vanish for `t > 0`. -/
theorem continuousOn_dzSlot {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) := by
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    (hF.DzIter 1).continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  exact (hD.mul hw).pow 2

/-- The slot integrand is almost everywhere strongly measurable for the product of the
restrictions of Lebesgue measure to `(0,∞)` and to `Iθ`; the two restrictions on the first
factor (open half-line and `Iz = [0,∞)`) agree because they differ by the null set `{0}`. -/
theorem aesm_dzSlot_prod {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h := Work.Spaces.aesm_of_continuousOn_Qd _
    (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) from continuousOn_dzSlot hF)
  have hz : MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
  rw [← hz] at h
  exact h

/-! ## The pointwise domination by the `i = 1` summand of `HkIntegrand` -/

/-- For `θ ∈ (0,π/2)` the unweighted (in `θ`) radial slot `(D_z f(t,θ) · w(t))²` is dominated
by the full `ℋ⁴`-integrand at `(t,θ)`: the `i = 1` summand of `HkIntegrand` is
`(D_z f·w)² sin(2θ)^{-η}` and `sin(2θ)^{η} ≤ 1`. -/
theorem dzSlot_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {t θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f t θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f t θ 1 (by norm_num)
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have heq : (Work.Spaces.DzIter 1 f t θ
        * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2
      = (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hone
    _ = (Work.Spaces.DzIter 1 f t θ
          * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f t θ := hkey

/-! ## The main statement -/

theorem DzSlice_l2 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun t => (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2) (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun θ => Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  -- The exchange of the two iterated integrals for the smooth open datum.
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (hF.forall 4) hmem
  -- Joint a.e. strong measurability of the (uncurried) slot integrand.
  have hGprod := aesm_dzSlot_prod hF
  -- ... hence of the `t`-slices, a.e. in `θ`.
  have hAESMslice := hGprod.prodMk_right
  -- ... and of `θ ↦ ∫_t (D_z f · w)²`.
  have hAESMint : AEStronglyMeasurable
      (fun θ => ∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.2 p.1 * Work.Spaces.w p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))) := hGprod.prod_swap
    have h3 := h2.integral_prod_right'
    simpa only using h3
  -- The square root of that is a.e. strongly measurable.
  have hb := Real.continuous_sqrt.comp_aestronglyMeasurable hAESMint
  -- For a.e. `θ` we are in the open interval.
  have hae_θ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ⟨h0, h1⟩)
  -- The two restrictions of Lebesgue measure to `Iz` and to the open half-line coincide.
  have hIz_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  -- The key a.e. bound: the squared `θ`-slice `L²` of the slot is dominated by the sliced
  -- `ℋ⁴`-integrand.
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sqrt (∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
    filter_upwards [hae_θ, hAeIntHk] with θ hθ hInt
    rw [Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]
    calc ∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2
        = ∫ t in Work.Spaces.Iz, (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2 := by
          rw [hIz_eq]
      _ ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hInt
            (Eventually.of_forall fun t => dzSlot_le_HkIntegrand (f := f) hθ.1 hθ.2)
  refine ⟨?_, hb, ?_, ?_⟩
  · -- a.e. integrability of the `t`-slice, by domination from the sliced `HkIntegrand`
    filter_upwards [hae_θ, hAESMslice, hAeIntHk] with θ hθ hAESM hInt
    refine Integrable.mono' (hInt.mono_set ?_) hAESM ?_
    · exact Set.Ioi_subset_Ici_self
    · filter_upwards with t
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact dzSlot_le_HkIntegrand hθ.1 hθ.2
  · -- integrability of the square of the slice norm
    refine Integrable.mono' hIntHkθ (hb.pow 2) ?_
    filter_upwards [hbound] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ
  · -- the `L²`-bound, by monotonicity of the integral and the exchange of the two
    -- iterated integrals
    calc ∫ θ in Work.Spaces.Iθ, (Real.sqrt (∫ t in Set.Ioi (0:ℝ),
            (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hIntHkθ hbound
      _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS_RegExport.RXB
