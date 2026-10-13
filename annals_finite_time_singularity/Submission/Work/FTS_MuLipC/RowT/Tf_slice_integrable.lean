import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The transport field `Tf g` of `FTS_MuLipC` is the coercivity transport field

`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)` and
`Work.Coercivity.Transport g = fun z θ => 3·D_θg z θ/(1+z)` have the same body, so they are
definitionally equal; this lets us use the (already proved) `L₁₂`-machinery built for the
coercivity transport term (`Work.FTS.StrongPersist.L3Aux`), in particular the factorisation
`K θ·3 D_θg s θ/(s(1+s)) = Wlam3 s · (KG α θ · (D_θg s θ · Wt α s θ))` of the angular slice. -/

/-- `Tf g` is `Work.Coercivity.Transport g` (the two definitions have the same body, so this
is `rfl`). -/
private theorem tf_eq_Transport (g : ℝ → ℝ → ℝ) : Tf g = Work.Coercivity.Transport g := rfl

/-- The joint integrand `(z,θ) ↦ K θ·Tf g z θ/z` is continuous on the open quadrant, for `g`
of class `SmoothOpen`. -/
private theorem tf_integrand_continuousOn {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Tf g p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hg.Dth.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hc : Continuous fun θ : ℝ => Work.Spaces.K θ := by
      change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    exact (hc.comp continuous_snd).continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const.add continuousOn_fst
  refine ContinuousOn.div (hK.mul ?_) continuousOn_fst
    (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  refine ContinuousOn.div (continuousOn_const.mul hD) hden (fun p hp => ?_)
  have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
  linarith

/-- **Pointwise bound on an angular slice.**  For `s > 0` and `θ ∈ Iθ`, the slice integrand of
the `L₁₂`-density of `Tf g` is dominated by `Wlam3 s·9(1 + HkIntegrand α 4 g s θ)/2`, an
integrable function of `θ` as soon as `g ∈ ℋ⁴_α`.  The `ℋ⁴`-slot used is the `(i,j) = (1,0)`
one, `(D_θg·W)² ≤ HkIntegrand α 4 g`, and the angular profile `KG α` is bounded by `9`. -/
private theorem tf_slice_pointwise_le {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Tf g s θ / s|
      ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s
        * (9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2) := by
  have hW3 : 0 ≤ Work.FTS.StrongPersist.L3Aux.Wlam3 s :=
    Work.FTS.StrongPersist.L3Aux.tl12_Wlam3_nonneg (le_of_lt hs)
  have hTf : Tf g = Work.Coercivity.Transport g := tf_eq_Transport g
  rw [hTf, Work.FTS.StrongPersist.L3Aux.tl12_Transport_integrand_eq α g hs hθ]
  rw [abs_mul, abs_of_nonneg hW3]
  refine mul_le_mul_of_nonneg_left ?_ hW3
  have hKGnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.KG α θ :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_nonneg α hθ
  have hKGle : Work.FTS.StrongPersist.L3Aux.KG α θ ≤ 9 :=
    Work.FTS.StrongPersist.L3Aux.tl12_KG_le_nine α hθ
      (Work.FTS.StrongPersist.L3Aux.tl12_gam_half_nonneg hα)
  have hsq : (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g s θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 g s θ 1 0 (le_refl 1) (by norm_num)
  have hb : |Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ|
      ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hAM := Work.FTS.GalBasis.cc.sqrt_le_half_one_add
    (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  calc |Work.FTS.StrongPersist.L3Aux.KG α θ
        * (Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ)|
      = Work.FTS.StrongPersist.L3Aux.KG α θ
          * |Work.Spaces.mixed 0 1 g s θ * Work.Spaces.Wt α s θ| := by
        rw [abs_mul, abs_of_nonneg hKGnn]
    _ ≤ 9 * Real.sqrt (Work.Spaces.HkIntegrand α 4 g s θ) :=
        mul_le_mul hKGle hb (abs_nonneg _) (by norm_num)
    _ ≤ 9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2 := by
        have h := mul_le_mul_of_nonneg_left hAM (by norm_num : (0 : ℝ) ≤ 9)
        linarith

/-- **The angular slice of the transport field is `L¹`.**  For a profile `g` which is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`) and honestly in `ℋ⁴_α`
(`Work.Spaces.HkMem α 4 g`), the slice of the `L₁₂`-integrand of the transport field
`Work.FTS_MuLipC.Tf g = fun z θ => 3·D_θg z θ/(1+z)` is integrable on `Iθ = [0,π/2]` for every
`s > 0`.  This is precisely the `h1`/`h2` input of `Work.FTS.LocData.L12_add_mul` at the fields
`a = Tf f'`, `b = Tf (f - f')`, and it is what makes the transport zero-mode additive over a
difference of class-`C` profiles.

Route (mirror `Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`, for `Tf g` in place
of `g`): the pointwise domination
`|D_θg s θ| ≤ √(HkIntegrand α 4 g s θ)/w s`  (`s > 0`, `θ ∈ (0,π/2)`) — from
`Work.FTS.Nonlinear.Pieces.slot_mixed_le_HkIntegrand` at `(j,i) = (0,1)` (since `mixed 0 1 g = D_θ g`
by `Work.Spaces.mixed_zero_left`/`DthIter`) together with `Wt α s θ = w s · sin(2θ)^{-γ/2}` and
`(sin 2θ)^{-γ} ≥ 1` — turns the slice into
`≤ 9s/(1+s)³·√(HkIntegrand α 4 g s θ) ≤ 9s/(1+s)³·(1 + HkIntegrand α 4 g s θ)/2`, which is
integrable in `θ` by `hmem.1 s hs.le`.  Then close with `Integrable.mono'`, the a.e. strong
measurability coming from continuity of the slice (from `hg.Dth` and
`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem Tf_slice_integrable {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf g s θ / s) Work.Spaces.Iθ := by
  intro s hs
  have hs' : 0 < s := hs
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g s θ) Work.Spaces.Iθ :=
    hmem.1 s hs'.le
  have haesm : AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * Tf g s θ / s) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (tf_integrand_continuousOn hg) hs'
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hmaj : IntegrableOn (fun θ => Work.FTS.StrongPersist.L3Aux.Wlam3 s
      * (9 * (1 + Work.Spaces.HkIntegrand α 4 g s θ) / 2)) Work.Spaces.Iθ := by
    have h1 : IntegrableOn (fun θ => (Work.FTS.StrongPersist.L3Aux.Wlam3 s * (9 / 2))
        * (1 + Work.Spaces.HkIntegrand α 4 g s θ)) Work.Spaces.Iθ :=
      (hconst.add hHk).const_mul _
    refine h1.congr_fun (fun θ _ => ?_) hIθ
    ring
  refine hmaj.mono' haesm ?_
  rw [ae_restrict_iff' hIθ]
  exact Eventually.of_forall fun θ hθ => by
    rw [Real.norm_eq_abs]
    exact tf_slice_pointwise_le hα hs' hθ

end Work.FTS_MuLipC.RowT
