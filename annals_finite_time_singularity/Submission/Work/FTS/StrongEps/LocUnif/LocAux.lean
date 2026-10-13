import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-! ## Small auxiliary lemmas -/

/-- **Commutation of `D_z` with the iterates of `D_θ`, at the honest `C^∞` order.**  This is
`Work.Spaces.DzDthIterCommOn` with the analytic order `⊤` replaced by
`Work.Stability.smoothOrder` (which is what the open-quadrant class `SmoothOpen` provides). -/
theorem DzDthIterCommOn_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hF : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hFy : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hF.contDiffAt (hV.mem_nhds hy)).of_le (by norm_num)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hFy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
          = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- **Multiplication by a continuous function preserves local uniform convergence** on an open set. -/
theorem tendstoLocallyUniformlyOn_mul_continuousOn {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) (hg : ContinuousOn g U) :
    TendstoLocallyUniformlyOn (fun n p => g p * F n p) (fun p => g p * f p) Filter.atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hF ⊢
  intro K hKU hK
  have hFK := Metric.tendstoUniformlyOn_iff.mp (hF K hKU hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
  have hCpos : 0 < max C 1 := lt_max_of_lt_right one_pos
  filter_upwards [hFK (ε / max C 1) (by positivity)] with n hn p hp
  rw [Real.dist_eq, abs_sub_comm]
  have h1 : |g p| ≤ max C 1 := by
    refine le_trans ?_ (le_max_left _ _)
    rw [← Real.norm_eq_abs]
    exact hC p hp
  have h2 : |F n p - f p| < ε / max C 1 := by
    rw [abs_sub_comm]
    simpa [Real.dist_eq] using hn p hp
  have h3 : |g p * F n p - g p * f p| = |g p| * |F n p - f p| := by
    rw [← mul_sub, abs_mul]
  rw [h3]
  calc |g p| * |F n p - f p| ≤ (max C 1) * |F n p - f p| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ < (max C 1) * (ε / max C 1) := mul_lt_mul_of_pos_left h2 hCpos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hCpos)

/-- **Restriction of local uniform convergence to a `z`-slice.** -/
theorem tendstoLocallyUniformlyOn_slice_fst {U : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ} {θ : ℝ} {W : Set ℝ} (hW : ∀ z ∈ W, (z, θ) ∈ U)
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    TendstoLocallyUniformlyOn (fun n z' => F n (z', θ)) (fun z' => f (z', θ)) Filter.atTop W :=
  hF.comp (fun z' : ℝ => (z', θ)) hW (continuous_id.prodMk continuous_const).continuousOn

/-- **Restriction of local uniform convergence to a `θ`-slice.** -/
theorem tendstoLocallyUniformlyOn_slice_snd {U : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ}
    {f : ℝ × ℝ → ℝ} {z : ℝ} {W : Set ℝ} (hW : ∀ θ ∈ W, (z, θ) ∈ U)
    (hF : TendstoLocallyUniformlyOn F f Filter.atTop U) :
    TendstoLocallyUniformlyOn (fun n θ' => F n (z, θ')) (fun θ' => f (z, θ')) Filter.atTop W :=
  hF.comp (fun θ' : ℝ => (z, θ')) hW (continuous_const.prodMk continuous_id).continuousOn

/-- **The chain rule for the logarithmic substitution `v ↦ arctan (exp v)`.** -/
theorem hasDerivAt_arctan_exp (v : ℝ) :
    HasDerivAt (fun v' : ℝ => Real.arctan (Real.exp v'))
      (Real.sin (2 * Real.arctan (Real.exp v)) / 2) v := by
  have h1 : HasDerivAt (fun v' : ℝ => Real.exp v') (Real.exp v) v := Real.hasDerivAt_exp v
  have h2 : HasDerivAt Real.arctan (1 / (1 + (Real.exp v) ^ 2)) (Real.exp v) :=
    Real.hasDerivAt_arctan (Real.exp v)
  have h3 : HasDerivAt (fun v' : ℝ => Real.arctan (Real.exp v'))
      (1 / (1 + (Real.exp v) ^ 2) * Real.exp v) v := h2.comp v h1
  convert h3 using 1
  rw [show Real.sin (2 * Real.arctan (Real.exp v)) = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
    have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
          * (1 / √(1 + (Real.exp v) ^ 2))
        = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
    rw [Real.sq_sqrt hS.le]]
  field_simp

/-- **Smoothness of the inverse coordinate change `(z,θ) ↦ (log z, log tan θ)` on `Q0`.** -/
theorem contDiffOn_logLog_Q0 (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2)))
      Work.FTS.EllipticEst.Q0 := by
  have hlog1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log p.1) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.log ?_ ?_
    · exact (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
    · intro p hp
      exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have htan : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 := by
    have h : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2)
        Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div (Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn)
        (Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn) ?_
      intro p hp
      obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [h3]⟩)
    convert h using 1
    funext p
    exact Real.tan_eq_sin_div_cos p.2
  have hlog2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log (Real.tan p.2))
      Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.log htan ?_
    intro p hp
    obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two h2 h3)
  exact hlog1.prodMk hlog2


end Work.FTS.StrongEps.LocUnif
