/-
# `Assembly/StepReg2_all.lean` — the regularity ports of the corrected step, in full

`Work.FTS.CoercivityFix.Assembly.StepReg2 α n` (`Assembly/Defs.lean`) is the bundle of
*regularity ports* the re-stated step of the corrected induction consumes: it says how the
interior class `RegQ` descends when one or two derivatives are taken, that the defect `Ê₂`
and the operator `Lhat (D_z ·)` stay at the lower level, and that the one-sided comparison of
the `ℋⁿ`-norms of the three slots with `|f|_{n+1}` holds.

Every field is an immediate consequence of a lemma already proved elsewhere in the tree:

| field | reason |
|---|---|
| `mono1`, `mono2` | monotonicity of `RegQ` in the order (`GalerkinFix.RegQ.regQ_mono`) |
| `dth1`, `dz1` | the two ports `QuadPorts.RegQ_dth`, `QuadPorts.RegQ_dz` |
| `dth2`, `dz2` | `dth1`/`dz1` followed by `regQ_mono` down to `n` |
| `ldz` | `dz1` followed by `Assembly.Lhat_RegQ` |
| `e2r` | `Assembly.E2hat_RegQ` |
| `normSub` | `HkSq_mono_le`, `HkSq_Dth_le`, and the `SmoothQuad`-version of `HkSq_Dz_le` proved below |

Only `normSub` needs anything new: the delivered `CoercivityStep.Norm.HkSq_Dz_le` is stated
for the *analytic* class `Work.Spaces.SmoothNbhd`, which is unavailable for the localised data
of this route, so the `SmoothQuad` version `HkSq_Dz_le_quad` is proved here — literally the
same measure-theoretic argument with `Work.Coercivity.HkIntegrand_Dz_le` replaced by
`QuadPorts.HkIntegrand_Dz_le_succ`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.CoercivityFix.Assembly.Lhat_RegQ
import Submission.Work.FTS.CoercivityFix.Assembly.E2hat_RegQ
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_succ_le_Q
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `SmoothQuad` version of `|D_z f|_{ℋⁿ}² ≤ |f|_{ℋ^{n+1}}²` -/

/-- The squared `ℋⁿ`-norm of `D_z f` is dominated by the squared `ℋ^{n+1}`-norm of `f`, for
every `f` which is `C^∞` on the open quadrant and has an honest `ℋ^{n+1}`-integrand.

This is `Work.FTS.CoercivityStep.Norm.HkSq_Dz_le` with the analyticity hypothesis replaced by
the interior class: the pointwise domination of the integrands is
`QuadPorts.HkIntegrand_Dz_le_succ`, and the transfer to the iterated integrals is the same
`integral_mono_of_nonneg` argument (no measurability of the dominated integrand is needed). -/
theorem HkSq_Dz_le_quad (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f := by
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
    h.2 ?_
  show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (n + 1) f z θ
  exact MeasureTheory.ae_restrict_of_forall_mem hmesz fun z hz =>
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dz f) z θ)
      (h.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem hmesθ fun θ hθ =>
        Work.FTS.CoercivityFix.QuadPorts.HkIntegrand_Dz_le_succ α n hsm z θ hz hθ)

/-! ## The bundle -/

theorem StepReg2_all (α : ℝ) (hα : 0 < α) (n : ℕ) :
    Work.FTS.CoercivityFix.Assembly.StepReg2 α n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `RegQ α (n+2) f → RegQ α n f`
    intro f hf
    exact Work.FTS.GalerkinFix.RegQ.regQ_mono hf (by omega)
  · -- `RegQ α (n+2) f → RegQ α (n+1) f`
    intro f hf
    exact Work.FTS.GalerkinFix.RegQ.regQ_mono hf (by omega)
  · -- `RegQ α (n+2) f → RegQ α (n+1) (D_θ f)`
    intro f hf
    exact Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα (n := n + 1) hf
  · -- `RegQ α (n+2) f → RegQ α (n+1) (D_z f)`
    intro f hf
    exact Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 1) hf
  · -- `RegQ α (n+2) f → RegQ α n (D_θ f)`
    intro f hf
    exact Work.FTS.GalerkinFix.RegQ.regQ_mono
      (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα (n := n + 1) hf) (by omega)
  · -- `RegQ α (n+2) f → RegQ α n (D_z f)`
    intro f hf
    exact Work.FTS.GalerkinFix.RegQ.regQ_mono
      (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 1) hf) (by omega)
  · -- `RegQ α (n+2) f → RegQ α n (Lhat (D_z f))`
    intro f hf
    exact Lhat_RegQ α hα (n := n)
      (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α (n := n + 1) hf)
  · -- `RegQ α (n+1) f → RegQ α n (Ê₂ f)`
    intro f hf
    exact E2hat_RegQ α hα (n := n) hf
  · -- the one-sided norm comparison
    intro f hf
    obtain ⟨hsm, hm, _⟩ := hf
    have hm1 : Work.Spaces.HkMem α (n + 1) f := HkMem_mono_quad hsm hm
    exact ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hm1,
      Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hm1,
      HkSq_Dz_le_quad α n hsm hm1⟩

end

end Work.FTS.CoercivityFix.Assembly
