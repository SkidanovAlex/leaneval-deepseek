import Submission.MasterEstimate
import Submission.Savin.SavinThm13
import Submission.Savin.ViscTwice
import Submission.Savin.Bridge
import Submission.Savin.Class

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Laplacian Metric MeasureTheory Filter Set Asymptotics
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- For a viscosity solution `g` of `-G(D²g) = 0` which is twice differentiable at `y`, the
symmetrised second derivative `A` of `g` at `y` satisfies `σ₂(A) = 1` on the positive branch. -/
theorem exists_taylor_data {g : ℝ⁴ → ℝ} {y : ℝ⁴} {s : Set ℝ⁴} (hs : IsOpen s) (hy : y ∈ s)
    (hvisc : IsViscSolution (fun M => -Gop M) g s) (htwice : IsTwiceDiffAt g y) :
    ∃ (A : ℝ⁴ →L[ℝ] ℝ⁴) (L : ℝ⁴ →L[ℝ] ℝ), A.IsSymmetric ∧ σ₂ A = 1 ∧
      0 < LinearMap.trace ℝ ℝ⁴ A.toLinearMap ∧
      (fun z => g z - g y - L (z - y) - ⟪A (z - y), (z - y)⟫ / 2)
        =o[𝓝 y] (fun z => ‖z - y‖ ^ 2) := by
  obtain ⟨L, Qb, hTayRaw⟩ := htwice
  set B : ℝ⁴ →L[ℝ] ℝ⁴ := InnerProductSpace.continuousLinearMapOfBilin Qb with hBdef
  have hBapp : ∀ v w : ℝ⁴, ⟪B v, w⟫ = Qb v w := by
    intro v w
    rw [hBdef, InnerProductSpace.continuousLinearMapOfBilin_apply]
  have hAsym : (B + B.adjoint).IsSymmetric := by
    intro v w
    change ⟪(B + B.adjoint) v, w⟫ = ⟪v, (B + B.adjoint) w⟫
    rw [add_apply, add_apply, inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hquad : ∀ v : ℝ⁴, ⟪(B + B.adjoint) v, v⟫ / 2 = Qb v v := by
    intro v
    have h1 : ⟪(B + B.adjoint) v, v⟫ = ⟪B v, v⟫ + ⟪v, B v⟫ := by
      rw [add_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
    have h2 : ⟪v, B v⟫ = ⟪B v, v⟫ := (real_inner_comm v (B v)).symm
    rw [h1, h2, hBapp v v]
    ring
  have hTay : (fun z => g z - g y - L (z - y) - ⟪(B + B.adjoint) (z - y), (z - y)⟫ / 2)
      =o[𝓝 y] (fun z => ‖z - y‖ ^ 2) := by
    have heq : (fun z => g z - g y - L (z - y) - ⟪(B + B.adjoint) (z - y), (z - y)⟫ / 2)
        = (fun z => g z - g y - L (z - y) - Qb (z - y) (z - y)) := by
      funext z
      rw [hquad]
    rw [heq]
    exact hTayRaw
  have hGop : Gop (B + B.adjoint) = 0 :=
    Gop_eq_zero_of_twiceDiff hs hy hAsym hvisc hTay
  obtain ⟨hσ, htr⟩ := (Gop_eq_zero_iff hAsym).mp hGop
  exact ⟨B + B.adjoint, L, hAsym, hσ, htr, hTay⟩

/-- **Savin's small perturbation theorem in the form used in Section 5.** -/
theorem savinInput_holds : SavinInput := by
  intro g y hy3 hvisc htwice
  obtain ⟨A, L, hAsym, hσ, htr, hTay⟩ := exists_taylor_data isOpen_ball hy3 hvisc htwice
  have hA1 : s2 A = 1 := by rw [s2_eq_sigma2 A hAsym]; exact hσ
  have hAtr : 0 < trOp A := htr
  obtain ⟨c, c', hc, hcq, hcq'⟩ := cofOp_class_bounds hAsym hA1 hAtr
  have hc'pos : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    rw [OrthonormalBasis.norm_eq_one stdB4 0, one_pow, mul_one] at h1 h2
    linarith
  obtain ⟨C₀, Λ₀, hC₀, hΛ₀, hbound⟩ := savin_hessian_bound (c := c) (c' := c') hc hc'pos
  have hcTpos : 0 < Λ₀ / 64 := by linarith
  obtain ⟨r, hrpos, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ z : ℝ⁴, dist z y < r →
      |g z - g y - L (z - y) - ⟪A (z - y), (z - y)⟫ / 2| ≤ (Λ₀ / 64) * ‖z - y‖ ^ 2 := by
    have hb : ∀ᶠ z in 𝓝 y,
        ‖g z - g y - L (z - y) - ⟪A (z - y), (z - y)⟫ / 2‖ ≤ (Λ₀ / 64) * ‖z - y‖ ^ 2 := by
      filter_upwards [hTay.bound hcTpos] with z hz
      have h2 : ‖(fun z : ℝ⁴ => ‖z - y‖ ^ 2) z‖ = ‖z - y‖ ^ 2 :=
        Real.norm_of_nonneg (sq_nonneg _)
      rwa [h2] at hz
    obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp hb
    exact ⟨r, hr, fun z hz => hrr hz⟩
  refine ⟨min r 1, Λ₀ / 64, lt_min hrpos (by norm_num), hcTpos, ?_⟩
  intro ρ hρpos hρle
  refine ⟨C₀, hC₀, ?_⟩
  intro u s hs hsub hu4 hσu hΔu hball hclose
  -- the quadratic model
  set Q : ℝ⁴ → ℝ := fun w => g y + L (w - y) + ⟪A (w - y), (w - y)⟫ / 2 with hQdef
  have hQc : ContDiff ℝ 2 Q := by
    rw [hQdef]
    exact contDiffOn_univ.mp
      ((contDiffOn_shifted_quad (A := A) L (g y) y Set.univ).congr fun w _ => by ring)
  have hQhess : ∀ w, hessOp Q w = A := by
    intro w
    rw [hQdef]
    rw [show (fun w : ℝ⁴ => g y + L (w - y) + ⟪A (w - y), w - y⟫ / 2)
        = (fun w => ⟪A (w - y), w - y⟫ / 2 + L (w - y) + g y) from by funext w; ring]
    exact hessOp_shifted_quad hAsym L (g y) y w
  -- the flatness of `u - Q` on `ball y ρ`
  have hflatQ : ∀ w ∈ ball y ρ,
      |u w - Q w| ≤ (Λ₀ / 64) * ‖w - y‖ ^ 2 + (Λ₀ / 64) * ρ ^ 2 := by
    intro w hw
    have hwr : dist w y < r := by
      rw [dist_eq_norm]
      have h1 : ‖w - y‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hw
      have h2 : ρ ≤ r := le_trans hρle (min_le_left _ _)
      linarith
    have h1 := hr w hwr
    have h2 : Q w = g y + L (w - y) + ⟪A (w - y), (w - y)⟫ / 2 := by rw [hQdef]
    have h3 := hclose w hw
    have h4 : |u w - g w| ≤ (Λ₀ / 64) * ρ ^ 2 := h3
    calc |u w - Q w| = |(u w - g w) + (g w - Q w)| := by
            congr 1; ring
      _ ≤ |u w - g w| + |g w - Q w| := abs_add_le _ _
      _ ≤ (Λ₀ / 64) * ρ ^ 2 + (Λ₀ / 64) * ‖w - y‖ ^ 2 := by
          have h1' : |g w - Q w| ≤ (Λ₀ / 64) * ‖w - y‖ ^ 2 := by
            rw [h2]
            rw [show g w - (g y + L (w - y) + ⟪A (w - y), (w - y)⟫ / 2)
                = g w - g y - L (w - y) - ⟪A (w - y), (w - y)⟫ / 2 from by ring]
            exact h1
          linarith [h4, h1']
      _ = (Λ₀ / 64) * ‖w - y‖ ^ 2 + (Λ₀ / 64) * ρ ^ 2 := by ring
  have hflatQ' : ∀ w ∈ ball y ρ, |u w - Q w| ≤ (Λ₀ / 32) * ρ ^ 2 := by
    intro w hw
    have h1 := hflatQ w hw
    have h2 : ‖w - y‖ ≤ ρ := by
      rw [mem_ball, dist_eq_norm] at hw; exact hw.le
    have h3 : ‖w - y‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [h2, norm_nonneg (w - y)]
    nlinarith [h1, h3, hρpos, hΛ₀]
  -- the rescaled function at a point `z`
  intro z hz
  set R : ℝ := ρ / 4 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hzR : ‖z - y‖ ≤ ρ / 2 := by
    rw [mem_closedBall, dist_eq_norm] at hz; exact hz
  set U : ℝ⁴ → ℝ := fun x => (u (z + R • x) - Q (z + R • x)) / R ^ 2 with hUdef
  have hmem : ∀ x ∈ ball 0 2, z + R • x ∈ s := by
    intro x hx
    have hx2 : ‖x‖ < 2 := by rwa [mem_ball, dist_zero_right] at hx
    have h1 : ‖R • x‖ < ρ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos, hRdef]
      nlinarith [hρpos]
    have h2 : z + R • x ∈ ball y ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z + R • x - y‖ = ‖(z - y) + R • x‖ := by rw [show z + R • x - y = (z - y) + R • x from by abel]
        _ ≤ ‖z - y‖ + ‖R • x‖ := norm_add_le _ _
        _ < ρ / 2 + ρ / 2 := by linarith
        _ = ρ := by ring
    exact hball h2
  have hUhess : ∀ x ∈ ball 0 2, hessOp U x = hessOp u (z + R • x) - A := by
    intro x hx
    have hzx := hmem x hx
    have hcd : ContDiffAt ℝ 2 (u - Q) (z + R • x) :=
      ((hu4.contDiffAt (hs.mem_nhds hzx)).of_le (by norm_num)).sub (hQc.contDiffAt)
    have h1 : hessOp U x = hessOp (u - Q) (z + R • x) := by
      rw [hUdef]
      exact hessOp_comp_affine_div hRpos hcd
    rw [h1, hessOp_sub_of_contDiffAt ((hu4.contDiffAt (hs.mem_nhds hzx)).of_le (by norm_num))
      (hQc.contDiffAt), hQhess]
  have hUeq : ∀ x ∈ ball 0 2, s2 (A + hessOp U x) = 1 := by
    intro x hx
    have hzx := hmem x hx
    rw [hUhess x hx,
      show A + (hessOp u (z + R • x) - A) = hessOp u (z + R • x) from by abel]
    have hsym : (hessOp u (z + R • x)).IsSymmetric :=
      hessOp_symm_of_contDiffAt ((hu4.contDiffAt (hs.mem_nhds hzx)).of_le (by norm_num))
    rw [s2_eq_sigma2 _ hsym,
      show hessOp u (z + R • x) = H u s (z + R • x) from
        (hessianWithin_eq_hessian (hs.mem_nhds hzx)).symm]
    exact hσu _ hzx
  have hUpos : ∀ x ∈ ball 0 2, 0 < trOp (A + hessOp U x) := by
    intro x hx
    have hzx := hmem x hx
    have htr : trOp (H u s (z + R • x)) = (Δ u) (z + R • x) :=
      (laplacian_eq_trace_hessian hs hzx (hu4.of_le (by norm_num))
        (stdOrthonormalBasis ℝ ℝ⁴)).symm
    rw [hUhess x hx,
      show A + (hessOp u (z + R • x) - A) = hessOp u (z + R • x) from by abel,
      show hessOp u (z + R • x) = H u s (z + R • x) from
        (hessianWithin_eq_hessian (hs.mem_nhds hzx)).symm, htr]
    exact hΔu _ hzx
  have hUcd : ContDiffOn ℝ 2 U (ball 0 2) := by
    have hu2 : ContDiffOn ℝ 2 u s := hu4.of_le (by norm_num)
    have h1 : ContDiffOn ℝ 2 (fun x : ℝ⁴ => u (z + R • x)) (ball 0 2) :=
      hu2.comp (contDiffOn_const.add (contDiffOn_id.const_smul R)) hmem
    have h2 : ContDiffOn ℝ 2 (fun x : ℝ⁴ => Q (z + R • x)) (ball 0 2) :=
      (hQc.comp (contDiff_const.add (contDiff_id.const_smul R))).contDiffOn
    exact ((h1.sub h2).div_const (R ^ 2)).congr fun x _ => by rw [hUdef]
  have hUflat : ∀ x ∈ ball 0 2, |U x| ≤ Λ₀ / 2 := by
    intro x hx
    have hx2 : ‖x‖ < 2 := by rwa [mem_ball, dist_zero_right] at hx
    have h1 : ‖R • x‖ < ρ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos, hRdef]
      nlinarith [hρpos]
    have h2 : z + R • x ∈ ball y ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖z + R • x - y‖ = ‖(z - y) + R • x‖ := by rw [show z + R • x - y = (z - y) + R • x from by abel]
        _ ≤ ‖z - y‖ + ‖R • x‖ := norm_add_le _ _
        _ < ρ / 2 + ρ / 2 := by linarith
        _ = ρ := by ring
    have h3 := hflatQ' _ h2
    have h4 : R ^ 2 = ρ ^ 2 / 16 := by rw [hRdef]; ring
    rw [hUdef, h4]
    have h5 : |u (z + R • x) - Q (z + R • x)| / (ρ ^ 2 / 16) ≤ Λ₀ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h3, hΛ₀]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ρ ^ 2 / 16)]
    exact h5
  have hres := hbound A U (Λ₀ / 2) hAsym hA1 hAtr hcq hcq' (by linarith) (by linarith)
    hUcd hUeq hUpos hUflat
  have hx0 : (0 : ℝ⁴) ∈ closedBall 0 (1 / 2) := by
    rw [mem_closedBall, dist_zero_right]; norm_num
  have hfin := hres 0 hx0
  have hzs : z ∈ s := hball (by rw [mem_ball, dist_eq_norm]; linarith [hzR, hρpos])
  have h0 : A + hessOp U 0 = hessOp u z := by
    have h1 := hUhess 0 (by rw [mem_ball, dist_zero_right]; norm_num)
    have h2 : z + R • (0 : ℝ⁴) = z := by simp
    rw [h2] at h1
    rw [h1]
    abel
  have htr : trOp (H u s z) = (Δ u) z :=
    (laplacian_eq_trace_hessian hs hzs (hu4.of_le (by norm_num))
      (stdOrthonormalBasis ℝ ℝ⁴)).symm
  rw [h0, show hessOp u z = H u s z from (hessianWithin_eq_hessian (hs.mem_nhds hzs)).symm,
    htr] at hfin
  exact hfin

end
end Submission
