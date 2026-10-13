/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/Assembly`: the per-slot `T2Slot` estimate

This module assembles the per-slot transport estimate `T2Slot` from the per-term bounds of
`TransportS/T2Sup/Main.lean` (and the delegated radial-Hardy term `delicateBound`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2Sup.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Work.FTS.TransportS.SlotT2

/-- The statement provided by the delegated per-term bound `delicateBound`. -/
def DelicateProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α →
    Work.FTS.TransportS.T2SF α f → Work.FTS.TransportS.T2SG α g →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
          * |Work.Spaces.mixed 3 1 g z θ|)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
          * Work.Spaces.HkSq α 4 g

theorem Xn_sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α g ^ 2 = Work.Spaces.HkSq α 4 g := by
  rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]

theorem one_div_sqrt_gam_sub_one {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
  have h2 : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [Work.Spaces.gam_sub_one α, Real.sqrt_div hα.le (10:ℝ)]
  rw [h2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow (10:ℝ), Real.rpow_neg hα.le, one_div, inv_div]
  ring

/-- `SmoothQuad` implies `SmoothOpen`. -/
theorem SmoothQuad.smoothOpen {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine hg.mono ?_
  intro p hp
  rw [Work.FTS.EllipticEst.mem_Q0] at hp
  obtain ⟨hz, hθ0, hθ1⟩ := hp
  exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩

/-- The double sum of the binomial coefficients is at most `256` (for slots `a, b ≤ 4`). -/
theorem choose_mul_le {a b a1 b1 : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) :
    (a.choose a1 : ℝ) * (b.choose b1 : ℝ) ≤ 256 := by
  have h1 : a.choose a1 ≤ 2 ^ a := Nat.choose_le_two_pow a a1
  have h2 : b.choose b1 ≤ 2 ^ b := Nat.choose_le_two_pow b b1
  have hpa : 2 ^ a ≤ 16 := by
    calc 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) ha
      _ = 16 := by norm_num
  have hpb : 2 ^ b ≤ 16 := by
    calc 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hb
      _ = 16 := by norm_num
  have h1' : (a.choose a1 : ℝ) ≤ 16 := by exact_mod_cast le_trans h1 hpa
  have h2' : (b.choose b1 : ℝ) ≤ 16 := by exact_mod_cast le_trans h2 hpb
  have h1'' : (0:ℝ) ≤ (a.choose a1 : ℝ) := Nat.cast_nonneg _
  have h2'' : (0:ℝ) ≤ (b.choose b1 : ℝ) := Nat.cast_nonneg _
  nlinarith [h1', h2', h1'', h2'']

end Work.FTS.TransportS.T2Sup
