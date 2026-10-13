/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/hardyG_ae_open`: the honest radial Hardy inequality for the `(1,1)`-slot

The frozen sibling `Work.FTS.TransportS.T2Sup.delicate_hardyG_ae` proves

`(D_zD_θ g(z,θ))² ≤ ∫_s w(s)² (D_z²D_θ g(s,θ))² ds`   for a.e. `θ` and every `z > 0`

for `g` in the frozen bundle `T2SG α g = RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`, whose
`RegQ`-component carries `SmoothQuad` (smoothness on the *half-strip* `Ioi (-1) ×ˢ Ioo 0 (π/2)`)
and the pointwise boundary traces `BdryTraces α 4 g`.

This file proves the same inequality for the *honest* bundle
`SmoothOpen g ∧ HkMem α 4 g ∧ DecayAll 4 g` — smoothness only on the **open** quadrant, no
boundary traces, and only order `4` of honesty.  Nothing in the proof of the frozen sibling
uses the half-strip smoothness or the traces: the only inputs are

* `Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` (`SmoothOpen g` + `HkMem α 4 g`), giving
  the a.e. radial integrability of the `(2,1)`-slot of the `ℋ⁴`-integrand;
* `Work.FTS.H2.hardyZ_open` applied to the slice `s ↦ D_zD_θg(s,θ)`, whose three hypotheses are
  the slice `C¹` (from `SmoothOpen g`), the decay `mixed 1 1 g · θ → 0` at `z → ∞` (from
  `DecayAll 4 g`) and the integrability of `(s ∂_s (mixed 1 1 g) s θ)² w(s)²` (which is the
  `(2,1)`-slot, since `mixed 2 1 g = D_z(D_zD_θ g) = s ∂_s (mixed 1 1 g)`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2Sup.delicateBound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem hardyG_ae_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hdec : Work.Spaces.DecayAll 4 g) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (Work.Spaces.mixed 1 1 g z θ) ^ 2
          ≤ ∫ s in Work.Spaces.Iz,
              (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
  obtain ⟨_hswap, _hmarg, hslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hsm hmem
  have hIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) ∧
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          Work.Spaces.Iz := by
    filter_upwards [hIoo, hslice] with θ hθ hI
    refine ⟨hθ, ?_⟩
    refine hI.mono' ?_ ?_
    · have hcont : ContinuousOn
          (fun s : ℝ => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          (Set.Ioi 0) := by
        have h1 : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi 0) := by
          simp only [Work.Spaces.w]
          exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
            (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))).pow 2
        exact h1.mul (((hsm.mixed 2 1).curry_z hθ).continuousOn.pow 2 |>.mono
          (fun s hs => by simp only [Set.mem_Ioi] at hs ⊢; linarith))
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hspos
      · subst h0
        have hzero : (Work.Spaces.w 0) ^ 2 * (Work.Spaces.mixed 2 1 g 0 θ) ^ 2 = 0 := by
          rw [show Work.Spaces.w 0 = 0 from by simp [Work.Spaces.w]]
          ring
        rw [hzero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
      · have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by show (0 : ℝ) < 2 * θ; linarith [hθ.1])
            (by show 2 * θ < Real.pi; linarith [hθ.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hslot := Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g
          (Work.Spaces.gam_pos hα) le_rfl hspos hθI 2 1 le_rfl (by norm_num)
        have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
            = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθI,
            show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
            Work.FTS.H2.hbi_Wm_sq α s θ (le_of_lt hsin)]
        have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Work.FTS.TransportS.T2Sup.delicate_one_le_rpow_neg hsin (Real.sin_le_one _)
            (le_of_lt (Work.Spaces.gam_pos hα))
        calc (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
            ≤ (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              have h0 : 0 ≤ (Work.Spaces.mixed 2 1 g s θ) ^ 2 := sq_nonneg _
              have h1 : (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
                  ≤ (Work.Spaces.w s) ^ 2
                    * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                      * (Work.Spaces.mixed 2 1 g s θ) ^ 2) :=
                mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h0 hone) (sq_nonneg _)
              linarith [h1]
          _ = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              rw [hcanon]
          _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hslot
  filter_upwards [hae] with θ hθ z hz
  obtain ⟨hθIoo, hIint⟩ := hθ
  have hslicecont : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) (Set.Ioi 0) :=
    ((hsm.mixed 1 1).curry_z hθIoo).of_le
        (by simp [Work.Stability.smoothOrder]) |>.mono
      (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)
  have hdec' : Tendsto (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) atTop (𝓝 0) :=
    hdec.2 1 1 (by norm_num) θ ⟨le_of_lt hθIoo.1, le_of_lt hθIoo.2⟩
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun s' : ℝ => Work.Spaces.mixed 1 1 g s' θ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using hIint
  have h := Work.FTS.H2.hardyZ_open hslicecont hdec' hint z hz
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using h

end Work.FTS.StrongPersist.N6Trans.Hon
