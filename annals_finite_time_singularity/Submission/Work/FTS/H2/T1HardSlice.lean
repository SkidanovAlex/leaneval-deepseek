import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.IbpHardEta
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.H2.STHardBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000




/-! ## The five slots of `HardF` -/

/-- The `g`-block of the `k`-th slot of `HardF` (`k = 0` is the `D_z`-slot with weight
`sin(2θ)^{-η}`; `k = 1,…,4` are the mixed slots with weight `sin(2θ)^{-γ}`). -/
def slotV (g : ℝ → ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => Work.Spaces.DzIter 4 g
  | 1 => Work.Spaces.mixed 3 1 g
  | 2 => Work.Spaces.mixed 2 2 g
  | 3 => Work.Spaces.mixed 1 3 g
  | _ => Work.Spaces.mixed 0 4 g

/-- The singular exponent of the `k`-th slot of `HardF`. -/
def slotQ (α : ℝ) : ℕ → ℝ
  | 0 => Work.Spaces.eta
  | _ => Work.Spaces.gam α



/-! ## The pointwise data of the two kinds of slot -/

/-- The `θ`-slice of a `SmoothNbhd` function is continuous on `Iθ`. -/
theorem continuousOn_slice_of_smoothNbhd {G : ℝ → ℝ → ℝ} (hG : Work.Spaces.SmoothNbhd G)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => G z θ) Work.Spaces.Iθ := by
  have hG' : ContDiffOn ℝ ⊤ (Function.uncurry G)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := hG
  have hc := contDiffOn_thslice_of_uncurry
    (V := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1))
    (isOpen_Ioi.prod isOpen_Ioo) hG' isOpen_Ioo
    (fun θ' hθ' => ⟨Set.mem_Ioi.mpr (by have hz0 : (0:ℝ) ≤ z := hz; linarith), hθ'⟩)
  exact hc.continuousOn.mono
    (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- The `θ`-slice of a mixed derivative of a `SmoothNbhd` function is continuous. -/
theorem continuousOn_mixed_slice (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => Work.Spaces.mixed j i g z θ) Work.Spaces.Iθ :=
  continuousOn_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_mixed hg j i) hz



/-! ## The energy of a slot is bounded by the `ℋ⁴`-energy -/

/-- Each slot energy is bounded by `HkSq`: the pointwise AM–GM/square comparison, integrated. -/
theorem slot_energy {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hHk : Work.Spaces.HkMem α 4 g) (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (k : ℕ) (hk : k ∈ Finset.range 5) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-slotQ α k) * (slotV g k z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hk4 : k ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  interval_cases k
  · rw [show slotQ α 0 = Work.Spaces.eta from rfl,
      show slotV g 0 = Work.Spaces.DzIter 4 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).1
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
            * (Work.Spaces.DzIter 4 g z θ) ^ 2)
          = (Work.Spaces.DzIter 4 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by ring
        _ = (Work.Spaces.DzIter 4 g z θ * Whz z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl
  · rw [show slotQ α 1 = Work.Spaces.gam α from rfl,
      show slotV g 1 = Work.Spaces.mixed 3 1 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
          = (Work.Spaces.mixed 3 1 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 3 1 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 3 (by norm_num) (by norm_num)
  · rw [show slotQ α 2 = Work.Spaces.gam α from rfl,
      show slotV g 2 = Work.Spaces.mixed 2 2 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 2 2 g z θ) ^ 2)
          = (Work.Spaces.mixed 2 2 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 2 2 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 2 2 (by norm_num) (by norm_num)
  · rw [show slotQ α 3 = Work.Spaces.gam α from rfl,
      show slotV g 3 = Work.Spaces.mixed 1 3 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 3 g z θ) ^ 2)
          = (Work.Spaces.mixed 1 3 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 1 3 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 3 1 (by norm_num) (by norm_num)
  · rw [show slotQ α 4 = Work.Spaces.gam α from rfl,
      show slotV g 4 = Work.Spaces.mixed 0 4 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          = (Work.Spaces.mixed 0 4 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 0 4 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 4 0 (by norm_num) (by norm_num)

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.T1HardSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The generic slot bound -/


/-! ## The pointwise `W`-bound

`W` is the second factor produced by the angular integration by parts,
`W(θ) = D_θf(z,θ)/2 + (1-q)cos(2θ)f(z,θ)`; on the closed quadrant it is bounded by
`(3/2)Kf` as soon as `|f| ≤ Kf`, `|D_θf| ≤ Kf` and `|1-q| ≤ 1`. -/


/-! ## The pointwise weight identity for the five slots

The five target integrands `(block²·sin(2θ)^{-q})` become the five summands of `HkIntegrand`
after multiplication by `w(z)²`. -/


/-! ## The angular slice bound

For fixed `z ∈ Iz`, the angular integral of `T1Hard α f g z ·` is dominated by
`(3/2)·Kf·∫_θ HkIntegrand α 4 g z θ`: integrate each of the five order-five terms by parts in
`θ` (`IbpHardEta` for the `D_z`-slot, `IbpHardMixedBlock` for the mixed slots), bound the
resulting factor `W(θ) = D_θf/2 + (1-q)cos(2θ)f` by `(3/2)Kf` (`t1hb_W_bound`), and identify the
five remaining `θ`-integrals with the five top-order summands of the `ℋ⁴`-integrand
(`t1hb_slots_eq`, `HkIntegrandSlotSum`). -/


end Work.FTS.H2
end
end
