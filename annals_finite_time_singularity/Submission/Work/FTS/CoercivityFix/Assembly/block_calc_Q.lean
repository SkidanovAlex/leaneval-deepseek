import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Continuity of the weights on the open quadrant -/

/-- The weighted factor `w(z)/sin(2θ)^c` is continuous on the open quadrant (`sin 2θ > 0`
there). -/
theorem continuousOn_w_div_sinpow_Qo (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ c) Qo := by
  refine continuousOn_w_Qo.div (continuousOn_sinpow_Qo c) ?_
  intro p hp
  have h1 : 0 < p.2 := (Set.mem_Ioo.mp hp.2).1
  have h2 : p.2 < π / 2 := (Set.mem_Ioo.mp hp.2).2
  exact ne_of_gt (Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) c)

/-- The angular (`W`) weight is continuous on the open quadrant. -/
theorem continuousOn_Wt_Qo (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qo := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact continuousOn_w_Qo.mul (continuousOn_sinpow_Qo _)

/-! ## Continuity of the four blocks -/

/-- Continuity on the open quadrant of the `D_z⁰`-block `Xeta f = f·w/√(sin 2θ^η)`. -/
theorem continuousOn_Xeta_Q {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.Xeta f)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.Xeta f)
      = fun p : ℝ × ℝ => Function.uncurry f p
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_smoothQuad hf).mul (continuousOn_w_div_sinpow_Qo _)

/-- Continuity on the open quadrant of the `D_z¹`-block `XetaDz f = D_zf·w/√(sin 2θ^η)`. -/
theorem continuousOn_XetaDz_Q {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.XetaDz f)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.XetaDz f)
      = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz f) p
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_Dz_smoothQuad hf).mul (continuousOn_w_div_sinpow_Qo _)

/-- Continuity on the open quadrant of the `D_θ`-block `XgamDth α f = D_θf·W`. -/
theorem continuousOn_XgamDth_Q (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.XgamDth α f)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.XgamDth α f)
      = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dth f) p
          * Work.Spaces.Wt α p.1 p.2 := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_Dth_smoothQuad hf).mul (continuousOn_Wt_Qo α)

/-- Continuity on the open quadrant of the plain block `Xw f = f·w`. -/
theorem continuousOn_Xw_Q {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.Xw f)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.Xw f)
      = fun p : ℝ × ℝ => Function.uncurry f p * Work.Spaces.w p.1 := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_smoothQuad hf).mul continuousOn_w_Qo

/-! ## Vanishing on the axis `z = 0` (because `w 0 = 0`) -/

theorem Xeta_zero_Q (f : ℝ → ℝ → ℝ) (θ : ℝ) : Work.Coercivity.Xeta f 0 θ = 0 := by
  simp [Work.Coercivity.Xeta, Work.Spaces.w]

theorem XetaDz_zero_Q (f : ℝ → ℝ → ℝ) (θ : ℝ) : Work.Coercivity.XetaDz f 0 θ = 0 := by
  simp [Work.Coercivity.XetaDz, Work.Spaces.w]

theorem XgamDth_zero_Q (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Coercivity.XgamDth α f 0 θ = 0 := by
  simp [Work.Coercivity.XgamDth, Work.Spaces.Wt, Work.Spaces.w]

theorem Xw_zero_Q (f : ℝ → ℝ → ℝ) (θ : ℝ) : Work.Coercivity.Xw f 0 θ = 0 := by
  simp [Work.Coercivity.Xw, Work.Spaces.w]

/-! ## The abstract block lemma -/

/-- A function continuous on the open quadrant, vanishing on the axis `z = 0`, and whose
square is dominated a.e. in `θ` by the integrable `HkIntegrand α 1 f` has honest iterated
`L²`-integral, a.e. strongly measurable angular slices and an a.e. strongly measurable
uncurried form. -/
theorem block_Qd (α : ℝ) {f g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 1 f)
    (hgc : ContinuousOn (Function.uncurry g) Qo)
    (hg0 : ∀ θ, g 0 θ = 0)
    (hdom : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ) :
    Work.Spaces.L2Mem g ∧
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have haesm : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine ⟨fun z hz => ?_, Work.Spaces.aesm_of_continuousOn_Qd _ hgc⟩
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · subst h0
      have hz0 : (fun θ : ℝ => g 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; exact hg0 θ
      rw [hz0]
      exact MeasureTheory.aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hgc hpos
  refine ⟨?_, haesm⟩
  rw [← Work.Coercivity.I2Mem_sq_iff g]
  refine I2Mem_of_dominated (D := fun z θ => Work.Spaces.HkIntegrand α 1 f z θ) hmem ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => (g z θ) ^ 2)
        = fun p : ℝ × ℝ => (Function.uncurry g p) ^ 2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact hgc.pow 2
  · intro θ; rw [hg0 θ]; ring
  · intro z hz
    filter_upwards [hdom z hz] with θ hθ
    rwa [abs_of_nonneg (sq_nonneg (g z θ))]

/-! ## The four blocks -/

/-- The four weighted `ℋ¹` blocks of a merely `C^∞`-on-the-open-quadrant profile are honest
`L²`-functions with a.e. strongly measurable slices and uncurried form.

`Work.FTS.LocData.SmoothQuad f` is genuine `C^∞` on `(0,∞) × (0,π/2)` — *not* the analytic
`Work.Spaces.SmoothNbhd` used by `Work.Coercivity.Eztheta1_eq_HkSq_one` — so the existing
`Work.Coercivity.L2Mem_DzIter_Hwt` / `L2Mem_mixed_Wt_gen` / `L2Mem_Xw` and
`Work.Coercivity.aesm_blocks` (all `SmoothNbhd`-based, hence analyticity) cannot be used.
The four blocks are
`Xeta f = f·w/√(sin 2θ^η)`, `XetaDz f = D_z f·w/√(sin 2θ^η)`, `XgamDth α f = D_θ f·W`,
`Xw f = f·w`.

ROUTE.  `SmoothQuad f` gives continuity on the open quadrant of `f`, `D_z f`, `D_θ f`
(`Work.FTS.LocData.contDiffOn_DzIter`, `contDiffOn_mixed` with `V = Ioi(-1) ×ˢ Ioo 0 (π/2)`,
then `.continuousOn.mono`), and the weights `w`, `sin(2θ)^{-η/2}`, `Wt α` are continuous there
(`w 0 = 0` and `sin > 0` for `θ ∈ (0,π/2)`).  So each block is continuous on the open quadrant,
hence a.e. strongly measurable on the product measure (`Spaces.aesm_of_continuousOn_Qd`) and, at
`z > 0`, on each angular slice (`Spaces.aesm_slice_of_continuousOn_Qd`); at `z = 0` every block
vanishes identically in `θ` because `w 0 = (1+0)²/0² = 0`.

For `Spaces.L2Mem` (slicewise and outer integrability of the square) use the pointwise
domination by the (integrable) `HkIntegrand α 1 f`: `sq_le_HkIntegrand_z` at `i = 0` and
`i = 1` for `Xeta`, `XetaDz`, `sq_le_HkIntegrand_mixed` at `(i,j) = (1,0)` for `XgamDth`, and
— for `Xw` — the a.e.-in-`θ` bound `Work.FTS.CoercivityFix.Assembly.sq_Xw_le_HkIntegrand_ae`
(`Submission/Work/FTS/CoercivityFix/Assembly/H1IP_core_Q.lean`), the only place where the a.e.
qualification is needed (at `θ = 0, π/2` the weight `sin(2θ)^{-η/2}` degenerates).  Then
`Integrable.mono'` against `hmem.1 z hz` / `hmem.2`. -/
theorem block_calc_Q (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 1 f) :
    Work.Spaces.L2Mem (Work.Coercivity.Xeta f) ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Coercivity.Xeta f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.Xeta f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Work.Spaces.L2Mem (Work.Coercivity.XetaDz f) ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Coercivity.XetaDz f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.XetaDz f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Work.Spaces.L2Mem (Work.Coercivity.XgamDth α f) ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Coercivity.XgamDth α f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.XgamDth α f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Work.Spaces.L2Mem (Work.Coercivity.Xw f) ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Coercivity.Xw f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.Xw f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hEta := block_Qd α hmem (continuousOn_Xeta_Q hf) (Xeta_zero_Q f)
    (fun z _ => Filter.Eventually.of_forall (fun θ => sq_Xeta_le_HkIntegrand α f z θ))
  have hEtaDz := block_Qd α hmem (continuousOn_XetaDz_Q hf) (XetaDz_zero_Q f)
    (fun z _ => Filter.Eventually.of_forall (fun θ => sq_XetaDz_le_HkIntegrand α f z θ))
  have hGam := block_Qd α hmem (continuousOn_XgamDth_Q α hf) (XgamDth_zero_Q α f)
    (fun z _ => Filter.Eventually.of_forall (fun θ => sq_XgamDth_le_HkIntegrand α f z θ))
  have hW := block_Qd α hmem (continuousOn_Xw_Q hf) (Xw_zero_Q f)
    (fun z hz => sq_Xw_le_HkIntegrand_ae α f z)
  exact ⟨hEta.1, hEta.2.1, hEta.2.2, hEtaDz.1, hEtaDz.2.1, hEtaDz.2.2,
    hGam.1, hGam.2.1, hGam.2.2, hW.1, hW.2.1, hW.2.2⟩

end Work.FTS.CoercivityFix.Assembly
