/-
# `Submission/Work/FTS/StrongPersist/L3Rhs/NfkAux/FkSlots.lean`

The weighted-`L²` slots of a *radial* function, and their relation to the `ℋ⁴`-integrand of its
radial extension.  These are the quantitative inputs of the pointwise jet bounds of the angular
moment `FK f` (`NfkAux.FkTerms`).

* `restrict_Ioi_eq_Iz` — the two radial intervals agree up to a null set;
* `contDiffOn_radial_Q0`, `contDiffOn_DzdIter_of_radial`, `continuousOn_DzdIter_of_radial` —
  finite-order smoothness of the radial function and of its `D_z`-iterates on `(0,∞)`;
* `slot_le_integrand`, `FK_slot_le` — the `a`-th slot
  `∫_z (D_z^a r z)² w(z)² dz` is integrable and bounded by `(4/π)·|r|²_{ℋ⁴}`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks
import Submission.Work.FTS.LocData.hLoc_hk
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Auxiliary: the null-set identity of the two radial intervals -/

/-- `(0,∞)` and `[0,∞)` agree up to a null set, hence the restricted measures agree. -/
theorem restrict_Ioi_eq_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))

/-! ## The 2-D extension of a radial function, and its `D_z`-iterates -/

/-- The uncurried extension of a radial function is `C^n` on the open quadrant as soon as the
function is `C^n` on `(0,∞)`. -/
theorem contDiffOn_radial_Q0 {r : ℝ → ℝ} {n : ℕ} (h : ContDiffOn ℝ n r (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (Function.uncurry (fun z (_ : ℝ) => r z))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hfst : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := contDiffOn_fst
  have hcomp := h.comp hfst (fun p hp => hp.1)
  have hfun : (fun p : ℝ × ℝ => r p.1) = Function.uncurry (fun z (_ : ℝ) => r z) := rfl
  rw [← hfun]
  exact hcomp

/-- **Smoothness of the `D_z`-iterates of a radial function.**  If `r` is `C^m` on `(0,∞)` for
all `m ≤ n`, then `z ↦ D_z^a r z` is `C^t` on `(0,∞)` whenever `a + t ≤ n`. -/
theorem contDiffOn_DzdIter_of_radial {r : ℝ → ℝ} {n : ℕ}
    (h : ∀ (m : ℕ), m ≤ n → ContDiffOn ℝ m r (Set.Ioi (0 : ℝ))) {a t : ℕ} (hat : a + t ≤ n) :
    ContDiffOn ℝ t (fun z => Work.Elliptic.DzdIter a r z) (Set.Ioi (0 : ℝ)) := by
  have hCD : ContDiffOn ℝ (a + t) (Function.uncurry (fun z (_ : ℝ) => r z))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    contDiffOn_radial_Q0 (h (a + t) hat)
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hIter := Work.FTS.CoercivityFix.Transfer.contDiffOn_DzIter_nat
    (G := (fun z (_ : ℝ) => r z)) hV (j := a) (t := t) hCD
  have hθ : (π / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hslice : ContDiffOn ℝ t
      (fun z => Work.Spaces.DzIter a (fun z (_ : ℝ) => r z) z (π / 4)) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.FinalClock.contDiffOn_zslice hIter hθ
  have hfun : (fun z => Work.Spaces.DzIter a (fun z (_ : ℝ) => r z) z (π / 4))
      = fun z => Work.Elliptic.DzdIter a r z :=
    funext fun z => Work.Elliptic.DzIter_rad r a z (π / 4)
  rwa [hfun] at hslice

/-- The continuity form of `contDiffOn_DzdIter_of_radial`. -/
theorem continuousOn_DzdIter_of_radial {r : ℝ → ℝ} {n : ℕ}
    (h : ∀ (m : ℕ), m ≤ n → ContDiffOn ℝ m r (Set.Ioi (0 : ℝ))) {a : ℕ} (ha : a ≤ n) :
    ContinuousOn (fun z => Work.Elliptic.DzdIter a r z) (Set.Ioi (0 : ℝ)) :=
  (contDiffOn_DzdIter_of_radial h (a := a) (t := 0) (by omega)).continuousOn

/-- The weight `w²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The radial slots -/

/-- **The slot bound.**  If `r` is `C^n` on `(0,∞)` with `n ≥ a` and honest in `ℋ⁴`, then the
`a`-th slot of the radial function is dominated by the `ℋ⁴`-integrand of its radial extension. -/
theorem slot_le_integrand {α : ℝ} {r : ℝ → ℝ} {n : ℕ}
    (h : ∀ (m : ℕ), m ≤ n → ContDiffOn ℝ m r (Set.Ioi (0 : ℝ)))
    (hmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z))
    {a : ℕ} (ha : a ≤ 4) (han : a ≤ n) :
    ∀ z ∈ Work.Spaces.Iz,
      (π / 4) * ((Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
  intro z hz
  have hpt : ∀ θ ∈ Set.Icc (π / 8) (3 * π / 8),
      (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos]) ?_
      linarith [hθ.2, Real.pi_pos]
    have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hrpow : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have h1 : 1 ≤ (Real.sin (2 * θ))⁻¹ := (one_le_inv₀ hsin).mpr hsinle
      have h2 : 1 ≤ ((Real.sin (2 * θ))⁻¹) ^ (Work.Spaces.eta) :=
        Real.one_le_rpow h1 (by rw [Work.Spaces.eta]; norm_num)
      rwa [Real.inv_rpow (le_of_lt hsin), ← Real.rpow_neg (le_of_lt hsin)] at h2
    have hsum := Work.Spaces.sq_le_HkIntegrand_z α 4 (fun z (_ : ℝ) => r z) z θ a ha
    rw [Work.Elliptic.DzIter_rad r a z θ] at hsum
    have hid : (Work.Elliptic.DzdIter a r z * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [show Work.Elliptic.DzdIter a r z * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = Work.Elliptic.DzdIter a r z * 1 * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) by ring]
      rw [Work.FTS.LocData.sep_sq1 (Work.Elliptic.DzdIter a r z) 1 (Work.Spaces.w z)
        (Real.sin (2 * θ)) (Work.Spaces.eta) (le_of_lt hsin)]
      ring
    rw [hid] at hsum
    calc (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := hsum
  have hsubI : Set.Icc (π / 8) (3 * π / 8) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hvol : MeasureTheory.volume.real (Set.Icc (π / 8) (3 * π / 8)) = π / 4 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
    · ring
    · linarith [Real.pi_pos]
  have hsub : (π / 4) * ((Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ θ in Set.Icc (π / 8) (3 * π / 8),
          Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    have hconst : (∫ θ in Set.Icc (π / 8) (3 * π / 8),
          (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = (π / 4) * ((Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul, hvol]
    rw [← hconst]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => by positivity)
      ((hmem.1 z hz).mono_set hsubI) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => hpt θ hθ)
  refine le_trans hsub ?_
  exact MeasureTheory.setIntegral_mono_set (hmem.1 z hz)
    (Filter.Eventually.of_forall fun _ => Work.Spaces.HkIntegrand_nonneg α 4 _ z _)
    (Filter.Eventually.of_forall hsubI)

/-- **The slot integral.**  The `a`-th slot of the radial function is integrable and bounded by
`(4/π)·|r|²_{ℋ⁴}`. -/
theorem FK_slot_le {α : ℝ} {r : ℝ → ℝ} {n : ℕ}
    (h : ∀ (m : ℕ), m ≤ n → ContDiffOn ℝ m r (Set.Ioi (0 : ℝ)))
    (hmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z))
    {a : ℕ} (ha : a ≤ 4) (han : a ≤ n) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (4 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z) := by
  have hcont := continuousOn_DzdIter_of_radial h han
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.H2.T1Q.aesm_Iz_of_continuousOn (hcont.pow 2 |>.mul continuousOn_w_sq)
  have hdom : MeasureTheory.IntegrableOn
      (fun z => (4 / π) * ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ) Work.Spaces.Iz :=
    hmem.2.const_mul _
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      ((Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (4 / π) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ := by
    intro z hz
    have h2 := slot_le_integrand h hmem ha han z hz
    have h2' : (4 / π) * ((π / 4) * ((Work.Elliptic.DzdIter a r z) ^ 2
          * (Work.Spaces.w z) ^ 2))
        ≤ (4 / π) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hπ : (4 / π) * (π / 4) = 1 := by field_simp
    rw [← mul_assoc, hπ, one_mul] at h2'
    exact h2'
  constructor
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt z hz
  · have hkey : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter a r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz,
            (4 / π) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => by positivity) hdom
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
    have hval : (∫ z in Work.Spaces.Iz,
          (4 / π) * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z (_ : ℝ) => r z) z θ)
        = (4 / π) * Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z) := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    rw [hval] at hkey
    exact hkey

end Work.FTS.StrongPersist.L3Rhs.NfkAux
