import Mathlib
import Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe

namespace Work.WilE7.Wit

open scoped Topology

theorem exists_levelSet_point_ne_self {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : AnalyticAt ℝ g p) (hgp : g p = 0) (hsurj : (fderiv ℝ g p).range = ⊤) (hk : k < n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : Fin n → ℝ, g y = 0 ∧ y ≠ p ∧ dist y p < ε := by
  classical
  -- `g` is strictly differentiable at `p`; chart its level set over the kernel of `dg_p`.
  have hf : HasStrictFDerivAt g (fderiv ℝ g p) p := hg.hasStrictFDerivAt
  let W : Submodule ℝ (Fin n → ℝ) := (fderiv ℝ g p).ker
  have hcomp : W.ClosedComplemented := by
    simpa [W] using (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin n → ℝ) →L[ℝ] W := Classical.choose hcomp
  have hC : ∀ x : W, C x = x := Classical.choose_spec hcomp
  obtain ⟨γ, V, U, hVopen, _hUopen, h0V, _hpU, hγ0, hγcont, _hγU, hγC, hγzero, _hγsurj⟩ :=
    Work.WilE7.Aux.levelSetChart g p W C hC hf hgp rfl hsurj
  -- `dg_p` is onto `ℝᵏ` with `k < n`, hence its kernel is nontrivial.
  have hpos : 0 < Module.finrank ℝ W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ g p) : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    rw [hsurj, finrank_top] at h1
    simp only [Module.finrank_fin_fun ℝ] at h1
    simp only [W]
    omega
  have hbot : W ≠ ⊥ := by
    intro h
    have h0 : Module.finrank ℝ W = 0 := by rw [h, finrank_bot]
    omega
  obtain ⟨w, hwW, hwne⟩ := (Submodule.ne_bot_iff W).mp hbot
  let w' : W := ⟨w, hwW⟩
  have hw'ne : w' ≠ 0 := by
    intro h
    exact hwne (by simpa [w'] using congr_arg Subtype.val h)
  have hwnorm : 0 < ‖w'‖ := norm_pos_iff.mpr hw'ne
  -- The parameters `v` near `0` whose chart point is a zero of `g` inside the `ε`-ball.
  have hpre : γ ⁻¹' Metric.ball p ε ∈ 𝓝 (0 : W) :=
    hγcont.preimage_mem_nhds (by rw [hγ0]; exact Metric.ball_mem_nhds p hε)
  have hVmem : V ∈ 𝓝 (0 : W) := hVopen.mem_nhds h0V
  have hS : V ∩ γ ⁻¹' Metric.ball p ε ∈ 𝓝 (0 : W) := Filter.inter_mem hVmem hpre
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hS
  -- A small nonzero parameter, hence a zero of `g` different from `p`.
  let v : W := (ρ / (2 * ‖w'‖)) • w'
  have hvne : v ≠ 0 := by
    simp only [v]
    exact smul_ne_zero (by positivity) hw'ne
  have hvball : v ∈ Metric.ball (0 : W) ρ := by
    simp only [v]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hw0 : ‖w'‖ ≠ 0 := ne_of_gt hwnorm
    field_simp
    linarith
  obtain ⟨hvV, hvballp⟩ := hρsub hvball
  refine ⟨γ v, hγzero v hvV, ?_, Metric.mem_ball.mp hvballp⟩
  intro h
  -- `γ v ≠ p` because its chart coordinate is `v ≠ 0 = C (p - p)`.
  have hCv : C (γ v - p) = v := hγC v hvV
  rw [h, sub_self, map_zero] at hCv
  exact hvne hCv.symm

end Work.WilE7.Wit
