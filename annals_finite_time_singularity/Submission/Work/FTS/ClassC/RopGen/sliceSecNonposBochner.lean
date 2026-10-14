import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Blocks.DivSinHalfCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.DivSinHalf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 0. Elementary angular facts -/

/-- `sin(2θ) > 0` on `(0, π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## 1. The slice facts

These are exactly the per-slice inputs the division machinery consumes at a fixed level
`z > 0`: smoothness of the slices of the `D_z`-iterates and their vanishing at the two
angular endpoints.  They come from the two standing hypotheses of `Blocks.divSin_Hk_half`
(the `SmoothSlice`-hypothesis and `VanishTheta Φ`), not from `SmoothNbhd Φ`. -/

/-- The slice facts for `D_z^j Φ` at a level `z > 0`, for `j ≤ k`. -/
theorem sliceFacts {k : ℕ} {Φ : ℝ → ℝ → ℝ}
    (hsl : ∀ z ∈ Work.Spaces.Iz, 0 < z → ∀ j : ℕ, j ≤ k →
      Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ))
    (hv : Work.Spaces.VanishTheta Φ) {j : ℕ} (hj : j ≤ k) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) :
    Work.Elliptic.SmoothSlice (fun θ => Work.Spaces.DzIter j Φ z θ) ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) 0 = 0 ∧
      (fun θ => Work.Spaces.DzIter j Φ z θ) (Real.pi / 2) = 0 :=
  ⟨hsl z hz hzpos j hj, (Work.Elliptic.vanish_DzIter hv j).1 z,
    (Work.Elliptic.vanish_DzIter hv j).2 z⟩

/-! ## 2. The generic commutations on an open set

`∂_θ` (resp. its iterates) can be moved across the iterates of `D_z` at any point of an open
set on which the function is `C^∞` (the class of `SmoothOpen`).  These are the proofs of
`HalfU.Dth_DzIter_comm_eqOn`, `HalfU.DthIter_DzIter_comm_eqOn`, `HalfU.pth_DzIter_eqOn` and
`Work.Spaces.mixed_div_comm` with joint analyticity replaced by `C^∞`-regularity; they are
recorded here because the estimates below are run on the open quadrant `Q0`, where only
`SmoothOpen Φ` is available. -/


/-- `D_θ` can be moved across any iterate of `D_z` on an open set of `C^∞`-regularity. -/
theorem Dth_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth f))) V := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (((Work.FTS.LocData.contDiffOn_DzIter hV h b).contDiffAt
          (hV.mem_nhds hy)).of_le (by rw [Work.Stability.smoothOrder]; norm_num))
      have hpz := Work.Spaces.pz_congr_of_isOpen hV ih hy
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b f)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z` on an open set of
`C^∞`-regularity. -/
theorem DthIter_DzIter_comm_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i f))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Work.Blocks.Half.Dth_congrOn hV ih hy
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn hV
          (Work.FTS.LocData.contDiffOn_DthIter hV h i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b f)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-- `∂_θ (D_z^j f) = D_z^j (∂_θ f)` on an open set of `C^∞`-regularity. -/
theorem pth_DzIter_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f))) V := by
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      intro y hy
      have hs : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j f)) V :=
        Work.FTS.LocData.contDiffOn_DzIter hV h j
      have hstep : Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j f))) y
          = Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y :=
        Work.Blocks.Half.pth_Dz_apply_of ((hs.contDiffAt (hV.mem_nhds hy)).of_le
          (by rw [Work.Stability.smoothOrder]; norm_num))
      have hcongr : Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j f))) y
          = Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f))) y :=
        Work.Blocks.Half.Dz_congrOn hV ih hy
      show Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter (j+1) f)) y
          = Function.uncurry (Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)) y
      rw [show Work.Spaces.DzIter (j+1) f = Work.Spaces.Dz (Work.Spaces.DzIter j f) from rfl,
          show Work.Spaces.DzIter (j+1) (Work.Spaces.pth f)
            = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth f)) from rfl]
      exact hstep.trans hcongr


/-! ## 3. The specialisations to the open quadrant `Q0` -/

/-- `∂_θ` commutes with the iterates of `D_z` on the open quadrant. -/
theorem pth_DzIter_eqOn_Q0 {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j Φ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth Φ)))
      Work.FTS.EllipticEst.Q0 :=
  pth_DzIter_eqOn Work.FTS.EllipticEst.isOpen_Q0 hΦ j








/-! ## 4. Continuity of the slices of the quotient on `(0, π/2)` -/



end Work.Blocks.DivSinHalf
end
end
-- ===== merged: Submission.Work.FTS.ClassC.AlphaDzGen.ProviderBridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.AlphaDzGen


theorem openTraceStmt_of_openTrace
    (h : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.PkgK5.K5c.InterpOpenTrace C) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C := h

end Work.FTS.ClassC.AlphaDzGen
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen

/-!
## `sliceSecNonposBochner` — the Bochner-integral form of the slice dichotomy

The 1-D slice dichotomy `∫ sin(2θ)^{-η} f f'' ≤ 0` is available in the workspace as
`Work.FTS.EllipticEst.AngAWeak.sliceSecondNonpos`, but *with* the extra hypothesis that the
integrand be integrable and with the integral taken over the open interval `Ioo 0 (π/2)`.
The statement requested here is the Bochner-integral form: no integrability hypothesis, and the
integral runs over `Work.Spaces.Iθ = Icc 0 (π/2)`.

The gap is closed by `MeasureTheory.integral_undef`: in Mathlib the Bochner integral of a
non-integrable function is `0`, so the non-integrable case is trivial; in the integrable case
the two `σ`-functions agree definitionally (`AngSecond.sig θ = sin(2θ)^{-η}`) and `Icc 0 (π/2)`
differs from `Ioo 0 (π/2)` by a null set.
-/




end Work.FTS.ClassC.RopGen
end
