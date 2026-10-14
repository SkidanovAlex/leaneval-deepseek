import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.HkSqZfar
-- ===== merged: Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_cross_ids =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeSlotOneAe.Interp

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular unfolding of the `Tk`-slot -/



/-! ## The three operator identities on the open quadrant -/




end Work.FTS.EllipticEst.AeSlotOneAe.Interp
end
end
-- ===== merged: Submission.Work.FTS.LocData6.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData6

set_option autoImplicit false

/-- Functions of the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- The `ℋ⁶`-size `Xn₆(g) = |g|_{ℋ⁶} = Work.Spaces.HkNorm α 6 g` — the order-`6` companion of
the frozen `Work.FTS.Nonlin.Xn α g = |g|_{ℋ⁴}`. -/
abbrev Xn6 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 6 g

/-- The localised perturbation `g = locData α L β (hLoc α) - F_*` at the concrete bump of N9 —
the datum of the strong-solution route, abbreviated so that the statements of this chapter read
at the parameters of `LocData`. -/
abbrev locG6 (α L β : ℝ) : Fn := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)

theorem locG6_eq (α L β : ℝ) :
    locG6 α L β = Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) := rfl

end Work.FTS.LocData6
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.SlotJets

/-- **Weighted angular `L²` bound for the `∂_θ` of a mixed slot, uniformly in `z`.**

For `0 < α ≤ 1`, `f` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant
`(0,∞) × (0,π/2)`) with `HkMem α 6 f`, and `a + b ≤ 4`, the angular slice of
`∂_θ (D_z^b D_θ^a f)` at a radius `z > 0`, weighted by `sin(2θ)^{2-γ}` (`γ = gam α`),
has an integral bounded by a universal multiple of `HkSq α 6 f` — with a constant
independent of `z`.

Route: on `(0, π/2)` the identity `sin(2θ)·∂_θ(mixed b a f) = mixed b (a+1) f` holds
(from `Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` for `D_θ` and
`D_z^b`), so the integrand equals `(mixed b (a+1) f)²·sin(2θ)^{-γ}`; the bound is then
`Work.FTS.StrongPersist.N6.sliceAng_le6` applied to the slot `(b, a+1)` (which satisfies
`1 ≤ a+1` and `a+1+b ≤ 5`), together with the a.e. agreement of `Set.Ioo 0 (π/2)` and
`Work.Spaces.Iθ` (`Ioo_ae_eq_Icc`). -/
theorem slotPthSliceLe : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    a + b ≤ 4 → ∀ z : ℝ, 0 < z →
      ∫ θ in Set.Ioo (0:ℝ) (π/2),
          (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
            * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        ≤ C * Work.Spaces.HkSq α 6 f := by
  -- the constant of the order-6 angular slot bound
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz
  -- on `(0,π/2)`, `sin(2θ)·∂_θ(mixed b a f) = mixed b (a+1) f`, so the `sin(2θ)²` hidden in the
  -- weight `sin(2θ)^{2-γ}` exactly cancels the one produced by `∂_θ = sin(2θ)^{-1}·D_θ`
  have hkey : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2),
      (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
          * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        = (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hsinpos : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hid : Real.sin (2*θ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z θ
        = Work.Spaces.mixed b (a+1) f z θ :=
      Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open
        (f := Work.Spaces.DthIter a f) (fun n => (hF.DthIter a).forall n) b 1 hz hθ
    have hpow : (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
        = (Real.sin (2*θ))^(2:ℝ) * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
      rw [show (2:ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring]
      exact Real.rpow_add hsinpos 2 (-(Work.Spaces.gam α))
    have hs2 : (Real.sin (2*θ))^(2:ℝ) = (Real.sin (2*θ))^2 := by
      simpa using Real.rpow_natCast (Real.sin (2*θ)) 2
    rw [hpow, hs2, ← hid]
    ring
  calc ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (Work.Spaces.pth (Work.Spaces.mixed b a f) z θ)^2
          * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)
      = ∫ θ in Set.Ioo (0:ℝ) (π/2),
        (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) :=
        setIntegral_congr_fun measurableSet_Ioo hkey
    _ = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b (a+1) f z θ)^2
          * (Real.sin (2*θ))^(-(Work.Spaces.gam α)) := by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0:ℝ))
            (b := Real.pi / 2))
    _ ≤ C₀ * Work.Spaces.HkSq α 6 f :=
        hC₀ α f b (a+1) hα hα1 hF hmem (by omega) (by omega) z hz

end Work.FTS_EllLimOK.SlotJets
end
