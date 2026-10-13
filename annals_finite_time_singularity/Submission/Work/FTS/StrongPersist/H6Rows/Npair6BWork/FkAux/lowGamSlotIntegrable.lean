import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_mixed_sq_sGamma
import Submission.Work.FTS.GalBasis.cc.wwBasic
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Continuity of the weight `Wt` on the open quadrant -/

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant
(the two endpoints `θ = 0`, `θ = π/2` are excluded there, so `sin(2θ) > 0`). -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The squared weighted mixed slice `(D_z^j D_θ^i f z · · W(α,z,·))²` is a.e. strongly
measurable on `Iθ`, for `z > 0`, as soon as `f` is `C^∞` on the *open* quadrant. -/
private lemma aesm_slice_mixed_Wt_sq {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (α : ℝ) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (Work.Spaces.aesm_slice_of_continuousOn_Qd _
    (((hsm.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hz).pow 2

/-- On the open interval the squared weighted mixed slot is
`w² · (D_z^j D_θ^i f)² · sin(2θ)^{-γ}`. -/
private lemma wt_sq_mixed {α : ℝ} {f : ℝ → ℝ → ℝ} {j i : ℕ} {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    Work.FTS.GalBasis.cc.sq_rpow_neg_half (γ := Work.Spaces.gam α) hs]
  ring

/-- Almost every point of `Iθ` is an interior point of the interval. -/
private theorem ae_Ioo_of_restrict_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h := MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
    (b := Real.pi / 2)
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo

/-- Integrability of the `γ`-weighted mixed slot on the angular interval: for `0 < α ≤ 1`, a datum
`f` of the open class lying in `ℋ⁴`, a slot `(j,i)` with `1 ≤ i` and `i + j ≤ 4`, and `z > 0`, the
function `θ ↦ (D_z^j D_θ^i f z θ)² · sin(2θ)^{-γ(α)}` is integrable on `Iθ`.  The already proved
`Work.FTS.GalBasis.cc.Subcut.LNA.IntegrableOn_mixed_sq_sGamma` is the case `i = 1`, and its proof
generalises verbatim: dominate by `HkIntegrand α 4 f z ·` (integrable by `HkMem α 4 f` via the
summand bound `Work.Spaces.sq_le_HkIntegrand_mixed`) using the identity
`(D_z^j D_θ^i f·Wt α)² = (w z)²·(D_z^j D_θ^i f)²·sin(2θ)^{-γ}` and `(w z)² ≥ 1`; the a.e. strong
measurability comes from the joint continuity of the uncurried slot on the open quadrant
(`Work.Spaces.aesm_slice_of_continuousOn_Qd`). -/
theorem lowGamSlotIntegrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  -- The weighted mixed slot is a summand of `HkIntegrand α 4 f z ·`, hence integrable.
  have hmix : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ :=
    (hmem.1 z hzI).mono' (aesm_slice_mixed_Wt_sq hF α j i hz)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)
  -- Divide the weighted slot by `(w z)² ≠ 0`.
  refine (hmix.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [ae_Ioo_of_restrict_Iθ] with θ hθ
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.GalBasis.cc.sin_two_pos hθ.1 hθ.2
  rw [wt_sq_mixed (α := α) hs, inv_mul_cancel_left₀ hw2]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
