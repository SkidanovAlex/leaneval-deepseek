/-
# The interior gradient estimate at an arbitrary centre, and local Lipschitzness

This file continues `Submission/SmoothGradientMain.lean`.  Two consequences of the
maximum-principle estimate `Submission.interior_gradient_bound`:

* `Submission.interior_gradient_bound_at`: the same estimate with the ball centred at an arbitrary
  point `c` and the conclusion at the centre `c` (obtained by translating `u`);
* `Submission.lipschitzOn_smooth_of_sigma2`: smooth solutions of `σ₂(D²u) = 1` with `Δu > 0`
  are locally Lipschitz, with an explicit constant.

Both are statements about *classical* solutions; the passage to viscosity solutions is the
remaining content of Trudinger--Wang's weighted interior gradient estimate.
-/
import Mathlib
import Submission.SmoothGradientMain
import Submission.Commons.Analysis.Calculus.FDeriv.hessianOp_comp_add_left
import Submission.MasterEstimate

open HessianEstimates
open Laplacian Metric MeasureTheory Filter
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace Pointwise

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

/-- Translation invariance of the Laplacian (proved here directly, to avoid a dependency on the
commons). -/
theorem laplacian_comp_add_left_local (u : ℝ⁴ → ℝ) (c y : ℝ⁴) :
    (Δ (fun z : ℝ⁴ => u (c + z))) y = (Δ u) (c + y) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
      (EuclideanSpace.basisFun (Fin 4) ℝ) (fun z : ℝ⁴ => u (c + z)) y,
    Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
      (EuclideanSpace.basisFun (Fin 4) ℝ) u (c + y)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    iteratedFDeriv_comp_add_left]

/-- The translation invariance of the Hessian operator `H`. -/
theorem hessianOp_comp_add_left_local (u : ℝ⁴ → ℝ) (c y : ℝ⁴) :
    H (fun z : ℝ⁴ => u (c + z)) (ball (0 : ℝ⁴) 1) y = H u (ball c 1) (c + y) := by
  have h := Commons.Analysis.Calculus.FDeriv.hessianOp_comp_add_left u c y (ball (0 : ℝ⁴) 1)
  rw [Metric.vadd_ball, vadd_eq_add, add_zero] at h
  unfold H
  exact h

/-- **Trudinger's interior gradient estimate at an arbitrary centre.** -/
theorem interior_gradient_bound_at :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (c : ℝ⁴) (r M : ℝ), 0 < r → 0 < M →
      ContDiffOn ℝ 3 u (ball c r) → (∀ x ∈ ball c r, |u x| ≤ M) →
      (∀ x ∈ ball c r, σ₂ (H u (ball c r) x) = 1) →
      (∀ x ∈ ball c r, 0 < (Δ u) x) →
      ‖fderiv ℝ u c‖ * r ≤ C * (1 + M) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := interior_gradient_bound
  refine ⟨C, hCpos, ?_⟩
  intro u c r M hr hM hu hub hσ2 hΔ
  set v : ℝ⁴ → ℝ := fun y => u (c + y) with hv
  have hmap : ∀ y ∈ ball (0 : ℝ⁴) r, c + y ∈ ball c r := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    simpa using hy
  have hcont : ContDiffOn ℝ 3 v (ball (0 : ℝ⁴) r) := by
    rw [hv]
    refine hu.comp ?_ ?_
    · fun_prop
    · exact hmap
  have hubv : ∀ y ∈ ball (0 : ℝ⁴) r, |v y| ≤ M := by
    intro y hy; rw [hv]; exact hub (c + y) (hmap y hy)
  have hσ2v : ∀ y ∈ ball (0 : ℝ⁴) r, σ₂ (H v (ball (0 : ℝ⁴) r) y) = 1 := by
    intro y hy
    have hH : H v (ball (0 : ℝ⁴) r) y = H u (ball c r) (c + y) := by
      rw [hv]
      have h := Commons.Analysis.Calculus.FDeriv.hessianOp_comp_add_left u c y (ball (0 : ℝ⁴) r)
      rw [Metric.vadd_ball, vadd_eq_add, add_zero] at h
      unfold H
      exact h
    rw [hH]
    exact hσ2 (c + y) (hmap y hy)
  have hΔv : ∀ y ∈ ball (0 : ℝ⁴) r, 0 < (Δ v) y := by
    intro y hy
    rw [hv]
    rw [laplacian_comp_add_left_local u c y]
    exact hΔ (c + y) (hmap y hy)
  have h := hC v r M hr hM hcont hubv hσ2v hΔv
  have hfd : fderiv ℝ v 0 = fderiv ℝ u c := by
    rw [hv]
    simpa using fderiv_comp_add_left (𝕜 := ℝ) (f := u) c (x := (0 : ℝ⁴))
  rwa [hfd] at h

/-- **Smooth solutions of `σ₂(D²u) = 1` with `Δu > 0` are locally Lipschitz.**

For `K` compact inside the open set `s`, there is a constant `L > 0` with
`|u y - u z| ≤ L dist y z` for `y, z ∈ K`. -/
theorem lipschitzOn_smooth_of_sigma2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ⁴ → ℝ) (s : Set ℝ⁴) (K : Set ℝ⁴), IsOpen s → IsCompact K →
      K ⊆ s → ContDiffOn ℝ 3 u s → (∀ x ∈ s, σ₂ (H u s x) = 1) → (∀ x ∈ s, 0 < (Δ u) x) →
      ∃ L : ℝ, 0 < L ∧ ∀ y ∈ K, ∀ z ∈ K, |u y - u z| ≤ L * dist y z := by
  obtain ⟨C, hCpos, hC⟩ := interior_gradient_bound_at
  refine ⟨C, hCpos, ?_⟩
  intro u s K hs hK hKs hu hσ2 hΔ
  rcases Set.eq_empty_or_nonempty K with hemp | ⟨x₀, hx₀K⟩
  · exact ⟨1, one_pos, fun y hy => absurd hy (by simp [hemp])⟩
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_cthickening_subset_open hs hKs
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hcontc : ContinuousOn u (cthickening δ K) :=
    hu.continuousOn.mono (fun x hx => hδsub hx)
  obtain ⟨M₀, hM₀⟩ := hK.cthickening.exists_bound_of_continuousOn hcontc
  have hM₀nn : 0 ≤ M₀ :=
    le_trans (norm_nonneg (u x₀)) (hM₀ x₀ (self_subset_cthickening K hx₀K))
  set M : ℝ := max M₀ 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hubM : ∀ x ∈ cthickening δ K, |u x| ≤ M := by
    intro x hx
    have h1 : |u x| ≤ M₀ := by simpa [Real.norm_eq_abs] using hM₀ x hx
    rw [hMdef]; exact le_trans h1 (le_max_left _ _)
  have hmem : ∀ (x : ℝ⁴) (ρ : ℝ), ρ ≤ δ → x ∈ thickening ρ K → x ∈ cthickening δ K := by
    intro x ρ hρ hx
    exact cthickening_mono hρ K (thickening_subset_cthickening ρ K hx)
  refine ⟨max (2 * C * (1 + M) ^ 2 / δ) (4 * M / δ), ?_, ?_⟩
  · refine lt_of_lt_of_le (div_pos (by positivity) hδpos) (le_max_left _ _)
  intro y hy z hz
  rcases eq_or_ne y z with rfl | hyz
  · simp
  rcases lt_or_ge (dist y z) (δ / 2) with hlt | hge
  · have hball : ball y (δ / 2) ⊆ s := by
      intro w hw
      refine hδsub (hmem w (δ / 2) (by linarith) ?_)
      rw [mem_thickening_iff]
      exact ⟨y, hy, by simpa using hw⟩
    have hzball : z ∈ ball y (δ / 2) := by rw [mem_ball, dist_comm]; exact hlt
    have hbnd : ∀ x ∈ ball y (δ / 2), |u x| ≤ M := by
      intro x hx
      refine hubM x (hmem x (δ / 2) (by linarith) ?_)
      rw [mem_thickening_iff]
      exact ⟨y, hy, by simpa using hx⟩
    have hσ2' : ∀ x ∈ ball y (δ / 2), σ₂ (H u (ball y (δ / 2)) x) = 1 := by
      intro x hx
      rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hx) (hs.mem_nhds (hball hx))]
      exact hσ2 x (hball hx)
    have hΔ' : ∀ x ∈ ball y (δ / 2), 0 < (Δ u) x := fun x hx => hΔ x (hball hx)
    have hder : ∀ x ∈ ball y (δ / 2), DifferentiableAt ℝ u x := fun x hx =>
      ((hu.mono hball).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)
    have hb : ∀ x ∈ ball y (δ / 2), ‖fderiv ℝ u x‖ ≤ 2 * C * (1 + M) ^ 2 / δ := by
      intro x hx
      have hsubx : ball x (δ / 2) ⊆ cthickening δ K := by
        intro w hw
        refine hmem w δ le_rfl ?_
        rw [mem_thickening_iff]
        refine ⟨y, hy, ?_⟩
        rw [mem_ball] at hw
        calc dist w y ≤ dist w x + dist x y := dist_triangle w x y
          _ < δ / 2 + δ / 2 := add_lt_add hw hx
          _ = δ := by ring
      have hsx : ball x (δ / 2) ⊆ s := fun w hw => hδsub (hsubx hw)
      have hbx2 : ∀ w ∈ ball x (δ / 2), |u w| ≤ M := fun w hw => hubM w (hsubx hw)
      have hσ2x : ∀ w ∈ ball x (δ / 2), σ₂ (H u (ball x (δ / 2)) w) = 1 := by
        intro w hw
        rw [H_congr_of_mem_nhds (isOpen_ball.mem_nhds hw) (hs.mem_nhds (hsx hw))]
        exact hσ2 w (hsx hw)
      have hΔx : ∀ w ∈ ball x (δ / 2), 0 < (Δ u) w := fun w hw => hΔ w (hsx hw)
      have hx2 := hC u x (δ / 2) M hδ2 hMpos (hu.mono hsx) hbx2 hσ2x hΔx
      rw [le_div_iff₀ hδpos]
      nlinarith [hx2]
    have hMVT := Convex.norm_image_sub_le_of_norm_fderiv_le hder hb (convex_ball y (δ / 2))
      (mem_ball_self hδ2) hzball
    have hMVT' : |u y - u z| ≤ 2 * C * (1 + M) ^ 2 / δ * dist y z := by
      rw [dist_eq_norm, norm_sub_rev]
      rw [Real.norm_eq_abs, abs_sub_comm] at hMVT
      exact hMVT
    calc |u y - u z| ≤ 2 * C * (1 + M) ^ 2 / δ * dist y z := hMVT'
      _ ≤ max (2 * C * (1 + M) ^ 2 / δ) (4 * M / δ) * dist y z :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  · have h1 : |u y| ≤ M := hubM y (self_subset_cthickening K hy)
    have h2 : |u z| ≤ M := hubM z (self_subset_cthickening K hz)
    have h3 : |u y - u z| ≤ 2 * M := by
      calc |u y - u z| = |u y + (-u z)| := by rw [sub_eq_add_neg]
        _ ≤ |u y| + |-u z| := abs_add_le _ _
        _ = |u y| + |u z| := by rw [abs_neg]
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring
    have h4 : 2 * M ≤ (4 * M / δ) * dist y z := by
      have h5 : (4 * M / δ) * (δ / 2) = 2 * M := by field_simp; ring
      rw [← h5]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    calc |u y - u z| ≤ 2 * M := h3
      _ ≤ (4 * M / δ) * dist y z := h4
      _ ≤ max (2 * C * (1 + M) ^ 2 / δ) (4 * M / δ) * dist y z :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

end Submission
