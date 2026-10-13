import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.intervalIntegrable_mixed_div_sin
import Submission.Work.H2.T1Q.SlotBoundQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotIntegrableHonest` — the `θ`-integrability of a single `ℋ⁴`-slot

The hard slots of the `N6` transport analysis are the functions

  `θ ↦ (D_z^b D_θ^a g z θ)² · sin(2θ)^{-q}`,   `a + b = 4`,

with the exponent `q ∈ {0, η, γ}` (`η = 99/100`, `γ = 1 + α/10`).  This file shows that each of
them is integrable on `Iθ = [0, π/2]` at every `z > 0`, for a datum `g` which is `C^∞` on the
*open* quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and lies in `ℋ⁴` (`Work.Spaces.HkMem α 4 g`).

The mathematical content is one line: every one of these slots is a summand of the (integrable)
`ℋ⁴`-integrand `Work.Spaces.HkIntegrand α 4 g z ·`, with the angular weight `sin(2θ)^{-γ}`
being the *strongest* one (`sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` and `1 ≤ sin(2θ)^{-η}` on `Iθ` since
`sin(2θ) ≤ 1` and `η < 1 < γ`).  The `η`-slot `(D_z⁴g)² sin(2θ)^{-η}` is the light-weighted
summand `Work.FTS.EllipticEst.integrableOn_zSummand` of `OpenQDefs`.

The whole business is therefore bookkeeping of the two weights; the only smoothness input used is
the *continuity on the open quadrant* needed for a.e. strong measurability of the slots (the
`SmoothQuad` version of these facts lives in `Work.FTS.H2.HQ.Glue` / `Work.H2.T1Q.SlotBoundQ`,
which we cannot use since our datum is only smooth on `Ioi 0`, not on `Ioi (-1)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

set_option maxHeartbeats 800000

/-- The restriction of Lebesgue measure to `Iθ = [0, π/2]` agrees with the restriction to the
open interval `(0, π/2)`: the two endpoints are null. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set (by
    show Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc)).symm

/-- `sin(2θ)` is positive on the open interval. -/
theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **Monotonicity of the slot weight.**  On the open interval the map
`p ↦ sin(2θ)^{-p}` is decreasing (the base lies in `(0,1)`), so a smaller exponent gives a
smaller weight: this is what makes the `η`- and `0`-slots dominated by the `γ`-slots. -/
theorem rpow_sin_two_neg_le {q γ : ℝ} (hq : q ≤ γ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-γ) :=
  Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_Ioo hθ) (Real.sin_le_one _) (by linarith)

/-- The two endpoints of `Iθ` are null for the restricted measure. -/
theorem ae_restrict_Iθ_of_forall_mem_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (π / 2))), p θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h
  rwa [← restrict_Iθ_eq_restrict_Ioo] at h1

/-- The `θ`-slice of a function which is `C^∞` on the open quadrant is continuous on the open
angular interval. -/
theorem continuousOn_slice_of_smoothOpen {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
  hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun θ hθ => ⟨hz, hθ⟩)

/-- The slot weight `θ ↦ sin(2θ)^p` is continuous on the open angular interval. -/
theorem continuousOn_sin_two_rpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo (0 : ℝ) (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_Ioo hθ)))

theorem continuousOn_Wt_slice (α z : ℝ) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.Wt α z θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    funext fun _ => rfl
  rw [hfun]
  exact continuousOn_const.mul (continuousOn_sin_two_rpow _)

theorem SlotIntegrableHonest (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b = 4)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hq0 : a = 0 → q = Work.Spaces.eta) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  -- the `ℋ⁴`-integrand of the angular slice, which dominates every slot
  have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    have h : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
        (volume.restrict Work.Spaces.Iθ) := hmem.1 z (le_of_lt hz)
    rwa [restrict_Iθ_eq_restrict_Ioo] at h
  -- it suffices to work on the open interval
  change Integrable (fun θ : ℝ =>
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
    (volume.restrict Work.Spaces.Iθ)
  rw [restrict_Iθ_eq_restrict_Ioo]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z⁴`-slot with exponent `η`
    have hq : q = Work.Spaces.eta := hq0 ha0
    have hb : b = 4 := by omega
    subst ha0
    subst hb
    rw [hq]
    rw [Work.Spaces.mixed_zero_right]
    -- the light-weighted slot is exactly the `HkMem`-integrable summand of the norm
    have hZ : Integrable (fun θ : ℝ => (Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have h : Integrable (fun θ : ℝ => (Work.Spaces.DzIter 4 g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hg hmem 4 le_rfl (z := z) (le_of_lt hz)
      rwa [restrict_Iθ_eq_restrict_Ioo] at h
    refine (hZ.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
    rw [show (Work.Spaces.DzIter 4 g z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter 4 g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring]
    rw [inv_mul_cancel_left₀ hw2ne]
  · -- ## `a ≥ 1`: every slot is a summand of the `ℋ⁴`-integrand with weight `sin(2θ)^{-γ}`
    have hb4 : a + b ≤ 4 := le_of_eq hab
    have hcontm : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed b a g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      continuousOn_slice_of_smoothOpen (hg.mixed b a) hz
    -- the weighted mixed slot is dominated by `HkIntegrand`
    have hM : Integrable (fun θ : ℝ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.mul (continuousOn_Wt_slice α z)).pow 2) measurableSet_Ioo
      refine Integrable.mono' hHk haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hb4
    -- undoing the radial weight turns this into the `γ`-weighted slot
    have hgamma : Integrable (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hM.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.mixed b a g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    -- a smaller exponent gives a smaller weight, so every `q ≤ γ` is integrable as well
    have hred : ∀ p : ℝ, p ≤ Work.Spaces.gam α → Integrable
        (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      intro p hp
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.pow 2).mul (continuousOn_sin_two_rpow (-p))) measurableSet_Ioo
      refine Integrable.mono' hgamma haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg
          (Work.Spaces.sin_two_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _))]
      exact mul_le_mul_of_nonneg_left (rpow_sin_two_neg_le hp hθ) (sq_nonneg _)
    obtain hq | hq | hq := hqa hapos
    · rw [hq]
      exact hred 0 (le_of_lt (Work.Spaces.gam_pos hα))
    · rw [hq]
      exact hred Work.Spaces.eta (le_trans (le_of_lt Work.Spaces.eta_lt_one)
        (le_of_lt (Work.Spaces.one_lt_gam hα)))
    · rw [hq]
      exact hred (Work.Spaces.gam α) le_rfl

end Work.FTS.StrongPersist.N6Trans.HardSlotAux
