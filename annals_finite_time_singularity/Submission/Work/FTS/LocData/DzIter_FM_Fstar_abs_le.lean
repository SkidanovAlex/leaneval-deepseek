import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.FinalClock.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

/-! ## Elementary tools -/

/-- **Fundamental theorem of calculus for the primitive.**  If `f` is continuous then
`t ↦ ∫₀^t f` has derivative `f t` everywhere. -/
theorem hasDerivAt_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) (f t) t :=
  (hf.integral_hasStrictDerivAt 0 t).hasDerivAt


/-! ## The two amplitudes of the dynamic rescaling -/

/-- **The vorticity amplitude of the dynamic rescaling.**
`Avort m τ = exp (-∫₀^τ (1 + m s) ds)` solves `A' = -(1 + m) A`, `A 0 = 1`.  In the physical
reconstruction the vorticity is `ω = A_v⁻¹ F e_θ` and the clock's amplitude is `C.A = 2·A_v`
(correction 2 of the design). -/
def Avort (m : ℝ → ℝ) (τ : ℝ) : ℝ := Real.exp (-∫ s in (0 : ℝ)..τ, (1 + m s))

/-- **The second amplitude of the dynamic rescaling.**
`Bdyn m τ = exp (-∫₀^τ (1 - m s) ds)` solves `B' = -(1 - m) B`, `B 0 = 1`.  It is the amplitude
`B(τ)` of the self-similar variable `z = ρ^{3α}/B(τ)` of `meridianEq_of_dynEq` (design §3:
`b'/b = -(1-μ)σ'`). -/
def Bdyn (m : ℝ → ℝ) (τ : ℝ) : ℝ := Real.exp (-∫ s in (0 : ℝ)..τ, (1 - m s))



/-- The *modulation bound* `|μ(τ)| ≤ 1/2` for every fake time: the hypothesis under which the
clock exists (`PhysClock.hmu_lo`, `PhysClock.hmu_hi` follow by elementary arithmetic) and the
paper's standing assumption in §`Modulation`. -/
def MuBound (m : ℝ → ℝ) : Prop := ∀ τ : ℝ, |m τ| ≤ 1 / 2

theorem MuBound.le {m : ℝ → ℝ} (hm : MuBound m) (τ : ℝ) : m τ ≤ 1 / 2 := (abs_le.mp (hm τ)).2

theorem MuBound.ge {m : ℝ → ℝ} (hm : MuBound m) (τ : ℝ) : -(1 / 2) ≤ m τ :=
  (abs_le.mp (hm τ)).1



/-! ## The `max`-extension of a modulation continuous on `[0,∞)`

`μ` is only known to be continuous on `[0,∞)` (it is `muDyn`, a functional of the fake-time
solution, which is only posed there).  The clock's amplitude, on the other hand, must be
differentiable at `τ = 0` *two-sidedly* (`PhysClock.hAderiv`), so the modulation has to be
extended to all of `ℝ`; the extension `s ↦ μ (max s 0)` is automatically continuous and agrees
with `μ` on `[0,∞)`, which is all the clock sees. -/

/-- The `max`-extension of a modulation continuous on `[0,∞)` is continuous on `ℝ`. -/
theorem continuous_maxExt {m : ℝ → ℝ} (hm : ContinuousOn m (Set.Ici 0)) :
    Continuous (fun s : ℝ => m (max s 0)) :=
  hm.comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0)


/-- The `max`-extension inherits the modulation bound. -/
theorem maxExt_bound {m : ℝ → ℝ} (h : ∀ τ : ℝ, 0 ≤ τ → |m τ| ≤ 1 / 2) :
    MuBound (fun s : ℝ => m (max s 0)) :=
  fun s => h (max s 0) (le_max_right s 0)

/-! ## Positivity and the value at `0` -/

theorem Avort_pos (m : ℝ → ℝ) (τ : ℝ) : 0 < Avort m τ := Real.exp_pos _

theorem Bdyn_pos (m : ℝ → ℝ) (τ : ℝ) : 0 < Bdyn m τ := Real.exp_pos _





@[simp] theorem Avort_zero (m : ℝ → ℝ) : Avort m 0 = 1 := by simp [Avort]

@[simp] theorem Bdyn_zero (m : ℝ → ℝ) : Bdyn m 0 = 1 := by simp [Bdyn]

/-! ## Derivatives and continuity -/

/-- `Avort m` solves the modulated amplitude equation `A' = -(1 + m) A`. -/
theorem Avort_hasDerivAt {m : ℝ → ℝ} (hc : Continuous m) (t : ℝ) :
    HasDerivAt (Avort m) (-(1 + m t) * Avort m t) t := by
  have h1 : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, (1 + m s)) (1 + m t) t :=
    hasDerivAt_intervalIntegral (continuous_const.add hc) t
  have h2 : HasDerivAt (fun u : ℝ => -(∫ s in (0 : ℝ)..u, (1 + m s))) (-(1 + m t)) t := h1.neg
  have h3 : HasDerivAt (fun u : ℝ => Real.exp (-(∫ s in (0 : ℝ)..u, (1 + m s))))
      (Real.exp (-(∫ s in (0 : ℝ)..t, (1 + m s))) * (-(1 + m t))) t := h2.exp
  have h4 : (fun u : ℝ => Real.exp (-(∫ s in (0 : ℝ)..u, (1 + m s)))) = Avort m := rfl
  rw [h4] at h3
  have hval : Real.exp (-(∫ s in (0 : ℝ)..t, (1 + m s))) * (-(1 + m t))
      = -(1 + m t) * Avort m t := by
    rw [show Real.exp (-(∫ s in (0 : ℝ)..t, (1 + m s))) = Avort m t from rfl]
    ring
  rwa [hval] at h3

/-- `Bdyn m` solves `B' = -(1 - m) B`. -/
theorem Bdyn_hasDerivAt {m : ℝ → ℝ} (hc : Continuous m) (t : ℝ) :
    HasDerivAt (Bdyn m) (-(1 - m t) * Bdyn m t) t := by
  have h1 : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, (1 - m s)) (1 - m t) t :=
    hasDerivAt_intervalIntegral (continuous_const.sub hc) t
  have h2 : HasDerivAt (fun u : ℝ => -(∫ s in (0 : ℝ)..u, (1 - m s))) (-(1 - m t)) t := h1.neg
  have h3 : HasDerivAt (fun u : ℝ => Real.exp (-(∫ s in (0 : ℝ)..u, (1 - m s))))
      (Real.exp (-(∫ s in (0 : ℝ)..t, (1 - m s))) * (-(1 - m t))) t := h2.exp
  have h4 : (fun u : ℝ => Real.exp (-(∫ s in (0 : ℝ)..u, (1 - m s)))) = Bdyn m := rfl
  rw [h4] at h3
  have hval : Real.exp (-(∫ s in (0 : ℝ)..t, (1 - m s))) * (-(1 - m t))
      = -(1 - m t) * Bdyn m t := by
    rw [show Real.exp (-(∫ s in (0 : ℝ)..t, (1 - m s))) = Bdyn m t from rfl]
    ring
  rwa [hval] at h3

theorem Avort_continuous {m : ℝ → ℝ} (hc : Continuous m) : Continuous (Avort m) :=
  continuous_iff_continuousAt.mpr fun t => (Avort_hasDerivAt hc t).continuousAt




end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## `D_z^j` of the profile as an iterate of the one-variable operator `T1F` -/


/-! ## The closed forms of the iterated derivatives -/








/-! ## The estimate -/


end Work.FTS.LocData
end
end
