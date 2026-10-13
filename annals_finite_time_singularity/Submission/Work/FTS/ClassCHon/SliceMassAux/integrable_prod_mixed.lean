import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.PhiStar.Honesty.IPMemOfHkMem
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux
import Submission.Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Product integrability of `2 F ∂_z F · sin(2θ)^{-η}`

This is the Fubini ingredient of the continuity proof for the angular slice mass
`m F z = ∫_θ (F z θ)² sin(2θ)^{-η}` of `Work.FTS.ClassCHon.sliceMass_continuous`.

For `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, with both `F` and its weighted
radial derivative `z ∂_z F` in `ℋ⁰` (`Work.Spaces.HkMem α 0`), the function

`(z,θ) ↦ 2 F z θ ∂_zF z θ · sin(2θ)^{-η}`

is integrable for the product of the restrictions of Lebesgue measure to `Iz = [0,∞)` and
`Iθ = [0,π/2]`.

**Proof.** At `k = 0` the `ℋ`-integrand collapses to a single square,
`HkIntegrand α 0 G z θ = (G z θ · w z / sin(2θ)^{η/2})²`, and `HkMem α 0 G` is exactly the
integrability of `HkIntegrand α 0 G` (first over `θ` for every `z ∈ Iz`, then over `z`), hence,
by Tonelli (`Work.Spaces.integrable_prod_of_iterated`), the *product* integrability of
`HkIntegrand α 0 G` for `G = F` and for `G = z ∂_z F` (the smoothness on the open quadrant gives
a.e. strong measurability of the uncurried integrand, `Work.Spaces.aesm_of_continuousOn_Qd`).

The pointwise AM–GM estimate is
`2 |F ∂_zF| sEta ≤ HkIntegrand α 0 F + HkIntegrand α 0 (z ∂_z F)`:
with `s = sin(2θ) ≥ 0`, `w = w z` and `r = w/s^{η/2}` one has `r² = w² sEta` and
`(z r)² = (z w)² sEta`, while `w ≥ 1` and `z w ≥ (1+z)²/z ≥ 1` for `z > 0`; hence
`sEta ≤ r²` and `sEta ≤ (z r)²`, and `2|F ∂_zF| ≤ F² + (∂_zF)²` finishes the comparison.
The estimate holds a.e. in `z` (only `z = 0` is exceptional, where `w 0 = 0` kills both
`Hk`-integrands), and the domination is transferred with `MeasureTheory.Integrable.mono'`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.SliceMassAux

set_option maxHeartbeats 800000

/-! ## Elementary pointwise facts -/

/-- At `k = 0` the `ℋ`-integrand collapses to the single square
`(G z θ · w z / sin(2θ)^{η/2})²` (the mixed-derivative double sum is empty). -/
private lemma HkIntegrand_zero_eq (α : ℝ) (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 G z θ
      = (G z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- `sin(2θ) ≥ 0` on `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The weight `sEta θ = sin(2θ)^{-η}` is continuous on the open quadrant (as a function of the
second variable). -/
private lemma continuousOn_sEta_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
    funext p; rfl
  rw [hfun]
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- `(sin(2θ)^{-η/2})² = sEta θ` on `Iθ`. -/
private lemma sq_sin_rpow_half_eta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = Work.FTS.EllipticEst.sEta θ := by
  have hs_nn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.FTS.EllipticEst.sEta, ← Real.rpow_natCast, ← Real.rpow_mul hs_nn]
  congr 1
  push_cast
  ring

/-- The square of the angular factor `w/s^{η/2}` is `w² sEta` (on `Iθ`). -/
private lemma sq_wdiv_eq {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hs_nn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [div_eq_mul_inv, ← Real.rpow_neg hs_nn (Work.Spaces.eta / 2), mul_pow]
  rw [sq_sin_rpow_half_eta hθ]

/-- `w z ≥ 1` for `z > 0` (so that `w z / sin(2θ)^{η/2} ≥ 1` on the open quadrant). -/
private lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  exact one_le_pow₀ hw

/-- `z · w z ≥ 1` for `z > 0` (so that the radial factor in the weighted derivative of the
`ℋ⁰`-integrand of `z ∂_z F` beats `1/s^{η/2}`). -/
private lemma one_le_zw_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (z * Work.Spaces.w z) ^ 2 :=
  one_le_pow₀ (Work.Spaces.one_le_mul_w z hz)

/-! ## The pointwise AM–GM estimate -/

/-- **Pointwise domination.**  For `z > 0` and `θ ∈ Iθ`,
`2 |F ∂_zF| sEta ≤ HkIntegrand α 0 F + HkIntegrand α 0 (z ∂_z F)`.

Indeed `HkIntegrand α 0 F = (F w/s^{η/2})²` and `HkIntegrand α 0 (z∂_zF) = (z∂_zF · w/s^{η/2})²`,
and on `Iθ` the angular factor `w/s^{η/2}` has square `w² sEta`, with `w² ≥ 1` and
`(z w)² ≥ 1` for `z > 0`. -/
private lemma key_pointwise {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      ≤ Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ := by
  have hsEta_nn : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  have hle1 : Work.FTS.EllipticEst.sEta θ
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [sq_wdiv_eq hθ]
    exact le_mul_of_one_le_left hsEta_nn (one_le_w_sq hz)
  have hle2 : Work.FTS.EllipticEst.sEta θ
      ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have h : (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (z * Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [mul_pow, sq_wdiv_eq hθ]; ring
    rw [h]
    exact le_mul_of_one_le_left hsEta_nn (one_le_zw_sq hz)
  have hA : (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (F z θ) ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hle1 (sq_nonneg _)
      _ = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  have hB : (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ ((z * Work.Spaces.pz F z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (Work.Spaces.pz F z θ) ^ 2
            * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hle2 (sq_nonneg _)
      _ = ((z * Work.Spaces.pz F z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
  have hamgm : 2 * |F z θ * Work.Spaces.pz F z θ|
      ≤ (F z θ) ^ 2 + (Work.Spaces.pz F z θ) ^ 2 := by
    rw [abs_mul, ← sq_abs (F z θ), ← sq_abs (Work.Spaces.pz F z θ)]
    nlinarith [sq_nonneg (|F z θ| - |Work.Spaces.pz F z θ|)]
  have habs : |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      = 2 * |F z θ * Work.Spaces.pz F z θ| * Work.FTS.EllipticEst.sEta θ := by
    simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), abs_of_nonneg hsEta_nn]
    ring
  calc |2 * F z θ * Work.Spaces.pz F z θ * Work.FTS.EllipticEst.sEta θ|
      = 2 * |F z θ * Work.Spaces.pz F z θ| * Work.FTS.EllipticEst.sEta θ := habs
    _ ≤ ((F z θ) ^ 2 + (Work.Spaces.pz F z θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right hamgm hsEta_nn
    _ = (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + (Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by ring
    _ ≤ (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + ((z * Work.Spaces.pz F z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := add_le_add hA hB
    _ = Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ) z θ := by
        simp only [Work.Spaces.HkIntegrand]
        norm_num

/-! ## Product integrability of the `ℋ⁰`-integrand -/

/-- **Tonelli for the level-`0` `ℋ`-integrand.**  If `G ∈ C^∞` on the open quadrant and
`HkMem α 0 G`, then the uncurried `HkIntegrand α 0 G` is integrable for the product measure. -/
private lemma integrable_prod_HkIntegrand_zero {α : ℝ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) (h : Work.Spaces.HkMem α 0 G) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α 0 G z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α 0)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 0 G z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact h.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 0 G z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := h.2
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 G z θ) haesm hslice houter).1

/-! ## The theorem -/

theorem integrable_prod_mixed {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the two dominating `ℋ⁰`-integrands are product integrable
  have hA : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 F p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_prod_HkIntegrand_zero hsm h0
  have hB : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz F z θ)
        p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_prod_HkIntegrand_zero hsm.Dz h1
  -- a.e. strong measurability of the target, from continuity on the open quadrant
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn
    have hPc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.pz.continuousOn
    have hmain : ContinuousOn (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
        * Work.FTS.EllipticEst.sEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hmain' : ContinuousOn ((((fun _ : ℝ × ℝ => (2 : ℝ)) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        ((continuousOn_const.mul hFc).mul hPc).mul continuousOn_sEta_snd
      have hfun : ((((fun _ : ℝ × ℝ => (2 : ℝ)) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2))
          * (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2))
          = (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
              * Work.FTS.EllipticEst.sEta p.2) := by
        funext p
        simp only [Pi.mul_apply]
      rwa [hfun] at hmain'
    have hgoal : (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ))
        = (fun p : ℝ × ℝ => 2 * F p.1 p.2 * Work.Spaces.pz F p.1 p.2
            * Work.FTS.EllipticEst.sEta p.2) := rfl
    rw [hgoal]
    exact hmain
  refine MeasureTheory.Integrable.mono' (hA.add hB) haesm ?_
  -- the pointwise domination holds almost everywhere (only `z = 0` is exceptional)
  have hz_ae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
      rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem (s := {p : ℝ × ℝ | 0 < p.1}) ?_).mpr ?_
    · exact (isOpen_Ioi.preimage continuous_fst).measurableSet
    · filter_upwards [hpos] with z hz
      exact Filter.Eventually.of_forall (fun θ => hz)
  have hθ_ae : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := {p : ℝ × ℝ | p.2 ∈ Work.Spaces.Iθ}) ?_).mpr ?_
    · exact measurableSet_Icc.preimage measurable_snd
    · exact Filter.Eventually.of_forall
        (fun _ => MeasureTheory.ae_restrict_mem measurableSet_Icc)
  filter_upwards [hz_ae, hθ_ae] with p hpz hpθ
  simpa only [Function.uncurry, Real.norm_eq_abs, Pi.add_apply] using
    key_pointwise (α := α) (F := F) hpz hpθ

end Work.FTS.ClassCHon.SliceMassAux
