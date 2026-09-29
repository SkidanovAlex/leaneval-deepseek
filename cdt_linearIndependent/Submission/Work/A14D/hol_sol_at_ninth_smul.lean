import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.local_structure_at_ninth

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- `PZ` does not vanish on the punctured ball around `1/9` of radius `δ ≤ 1/20`.  (The roots of
`PZ` are `0`, `1`, `1/9` and the two former are at distance `1/9` and `8/9` from `1/9`.) -/
lemma PZ_ne_zero_of_mem_ball_of_ne {δ : ℝ} (hδ : δ ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ Metric.ball ninth δ) (hzne : z ≠ ninth) : PZ z ≠ 0 := by
  have hδ9 : δ ≤ 1 / 9 := by linarith
  rw [PZ_eq_mul_qZ]
  exact mul_ne_zero (sub_ne_zero.mpr hzne) (qZ_ne_zero_of_mem_ball hδ9 hz)

/-- **The holomorphic solution space of `LZ` at `x = 1/9` is one-dimensional.**  Every function
holomorphic on a ball `ball (1/9) δ` annihilated by `LZ` there is a constant multiple of the
distinguished holomorphic solution `y9` (`Work.A14D.Y9`).

The proof is the Wronskian argument: `D = PZ·W` with `W = f·y9' − f'·y9` is holomorphic on the
ball and `D' = 0` because both `f` and `y9` solve the ODE, so `D` is constant and vanishes at the
singular point `1/9` (where `PZ = 0`).  Hence `W = 0` off `1/9`, then everywhere by the identity
theorem, and `f/y9` is constant near `1/9`, whence everywhere by the identity theorem again. -/
theorem hol_sol_at_ninth_smul {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball ninth δ))
    (hode : ∀ z ∈ Metric.ball ninth δ, LZ f z = 0) :
    ∃ c : ℂ, ∀ z ∈ Metric.ball ninth δ, f z = c * y9 z := by
  obtain ⟨hδpos, hδle, hy9d, hy9ne9, hy9ode⟩ := hY
  have hBo : IsOpen (Metric.ball ninth δ) := Metric.isOpen_ball
  have hBp : IsPreconnected (Metric.ball ninth δ) := Metric.isPreconnected_ball
  have h9mem : ninth ∈ Metric.ball ninth δ := Metric.mem_ball_self hδpos
  have hfd : DifferentiableOn ℂ (deriv f) (Metric.ball ninth δ) := hf.deriv hBo
  have hy9dd : DifferentiableOn ℂ (deriv y9) (Metric.ball ninth δ) := hy9d.deriv hBo
  -- the Wronskian `W = f * y9' - f' * y9`
  set Wr : ℂ → ℂ := fun z => f z * deriv y9 z - deriv f z * y9 z with hWr
  have hWrd : DifferentiableOn ℂ Wr (Metric.ball ninth δ) := by
    rw [hWr]
    exact (hf.mul hy9dd).sub (hfd.mul hy9d)
  -- `D = PZ * W` has vanishing derivative
  have hDderiv : Set.EqOn (deriv (fun z => PZ z * Wr z)) 0 (Metric.ball ninth δ) := by
    intro z hz
    simp only [Pi.zero_apply]
    have hz' : Metric.ball ninth δ ∈ 𝓝 z := hBo.mem_nhds hz
    have hfAt : DifferentiableAt ℂ f z := hf.differentiableAt hz'
    have hyAt : DifferentiableAt ℂ y9 z := hy9d.differentiableAt hz'
    have hdfAt : DifferentiableAt ℂ (deriv f) z := hfd.differentiableAt hz'
    have hdyAt : DifferentiableAt ℂ (deriv y9) z := hy9dd.differentiableAt hz'
    have hWrAt : DifferentiableAt ℂ Wr z := hWrd.differentiableAt hz'
    have h1 : deriv (fun z => PZ z * Wr z) z = deriv PZ z * Wr z + PZ z * deriv Wr z :=
      deriv_mul differentiable_PZ.differentiableAt hWrAt
    have hWrval : Wr z = f z * deriv y9 z - deriv f z * y9 z := by rw [hWr]
    have hWrderiv : deriv Wr z = f z * deriv (deriv y9) z - deriv (deriv f) z * y9 z := by
      have hsub : deriv (fun w : ℂ => f w * deriv y9 w - deriv f w * y9 w) z
          = deriv (fun w : ℂ => f w * deriv y9 w) z
            - deriv (fun w : ℂ => deriv f w * y9 w) z :=
        deriv_sub (by fun_prop) (by fun_prop)
      have hm1 : deriv (fun w : ℂ => f w * deriv y9 w) z
          = deriv f z * deriv y9 z + f z * deriv (deriv y9) z := deriv_mul hfAt hdyAt
      have hm2 : deriv (fun w : ℂ => deriv f w * y9 w) z
          = deriv (deriv f) z * y9 z + deriv f z * deriv y9 z := deriv_mul hdfAt hyAt
      rw [hWr, hsub, hm1, hm2]
      ring
    rw [h1, hWrderiv, deriv_PZ_local_structure_at_ninth, hWrval]
    have hfode : PZ z * deriv (deriv f) z + PZ' z * deriv f z + RZ z * f z = 0 := by
      have := hode z hz
      rwa [LZ_def] at this
    have hyode : PZ z * deriv (deriv y9) z + PZ' z * deriv y9 z + RZ z * y9 z = 0 := by
      have := hy9ode z hz
      rwa [LZ_def] at this
    have key : f z * (PZ z * deriv (deriv y9) z + PZ' z * deriv y9 z + RZ z * y9 z)
        - y9 z * (PZ z * deriv (deriv f) z + PZ' z * deriv f z + RZ z * f z)
        = PZ' z * (f z * deriv y9 z - deriv f z * y9 z)
          + PZ z * (f z * deriv (deriv y9) z - deriv (deriv f) z * y9 z) := by ring
    rw [← key, hyode, hfode]
    ring
  obtain ⟨a, ha⟩ := hBo.exists_is_const_of_deriv_eq_zero hBp
    ((differentiable_PZ.differentiableOn).mul hWrd) hDderiv
  have ha0 : a = 0 := by
    have h := ha ninth h9mem
    have hPZ9 : PZ ninth = 0 := by simp only [PZ, ninth]; norm_num
    rw [Pi.mul_apply, hPZ9, zero_mul] at h
    exact h.symm
  have hDzero : ∀ z ∈ Metric.ball ninth δ, PZ z * Wr z = 0 := by
    intro z hz
    have h := ha z hz
    rwa [ha0, Pi.mul_apply] at h
  -- hence `W = 0` off the singular point ...
  have hWr_zero_off : ∀ z ∈ Metric.ball ninth δ, z ≠ ninth → Wr z = 0 := by
    intro z hz hzne
    exact (mul_eq_zero.mp (hDzero z hz)).resolve_left (PZ_ne_zero_of_mem_ball_of_ne hδle hz hzne)
  -- ... and everywhere by the identity theorem
  have hWranalytic : AnalyticOnNhd ℂ Wr (Metric.ball ninth δ) := hWrd.analyticOnNhd hBo
  have hz0mem : ninth + ((δ / 2 : ℝ) : ℂ) ∈ Metric.ball ninth δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : ninth + ((δ / 2 : ℝ) : ℂ) - ninth = ((δ / 2 : ℝ) : ℂ) := by ring
    rw [hsub]
    have hnorm : ‖(((δ / 2 : ℝ)) : ℂ)‖ = δ / 2 := by
      have h2 : ‖(((δ / 2 : ℝ)) : ℂ)‖ ^ 2 = (δ / 2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]
        ring
      have hpos : 0 < δ / 2 := by linarith
      nlinarith [norm_nonneg ((((δ / 2 : ℝ)) : ℂ)), h2, hpos]
    rw [hnorm]
    linarith
  have hWrfull : Set.EqOn Wr 0 (Metric.ball ninth δ) := by
    have hz0ne : ninth + ((δ / 2 : ℝ) : ℂ) ≠ ninth := by
      intro h
      have h2 : ((δ / 2 : ℝ) : ℂ) = 0 := by
        have := congrArg (fun w : ℂ => w - ninth) h
        simpa using this
      have h3 : (δ / 2 : ℝ) = 0 := by exact_mod_cast h2
      linarith
    have hz0 : ninth + ((δ / 2 : ℝ) : ℂ) ∈ Metric.ball ninth δ \ {ninth} :=
      ⟨hz0mem, by simpa [Set.mem_singleton_iff] using hz0ne⟩
    have hopen : IsOpen (Metric.ball ninth δ \ {ninth}) := hBo.sdiff isClosed_singleton
    refine hWranalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBp hz0mem ?_
    filter_upwards [hopen.mem_nhds hz0] with z hz
    exact hWr_zero_off z hz.1 hz.2
  -- a ball around `1/9` on which `y9` does not vanish
  have hcont : ContinuousAt y9 ninth :=
    (hy9d.differentiableAt (Metric.ball_mem_nhds ninth hδpos)).continuousAt
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hy9ne9)
  set ε : ℝ := min ε₁ δ with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos hδpos
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hballsub : Metric.ball ninth ε ⊆ Metric.ball ninth δ := Metric.ball_subset_ball hεδ
  have hyne : ∀ z ∈ Metric.ball ninth ε, y9 z ≠ 0 := fun z hz =>
    hε₁sub (lt_of_lt_of_le (Metric.mem_ball.mp hz) hεε₁)
  -- the quotient `f / y9` is constant near `1/9`
  set φ : ℂ → ℂ := fun z => f z / y9 z with hφ
  have hφd : DifferentiableOn ℂ φ (Metric.ball ninth ε) := by
    rw [hφ]
    exact (hf.mono hballsub).div (hy9d.mono hballsub) hyne
  have hφderiv : Set.EqOn (deriv φ) 0 (Metric.ball ninth ε) := by
    intro z hz
    have hzB : z ∈ Metric.ball ninth δ := hballsub hz
    have hz' : Metric.ball ninth δ ∈ 𝓝 z := hBo.mem_nhds hzB
    have hfAt : DifferentiableAt ℂ f z := hf.differentiableAt hz'
    have hyAt : DifferentiableAt ℂ y9 z := hy9d.differentiableAt hz'
    have hWz : Wr z = 0 := hWrfull hzB
    have hWzv : f z * deriv y9 z - deriv f z * y9 z = 0 := by
      rw [hWr] at hWz
      exact hWz
    rw [hφ]
    have hdiveq : deriv (fun z => f z / y9 z) z
        = (deriv f z * y9 z - f z * deriv y9 z) / y9 z ^ 2 :=
      deriv_div hfAt hyAt (hyne z hz)
    rw [hdiveq]
    have hnum : deriv f z * y9 z - f z * deriv y9 z = 0 := by
      rw [show deriv f z * y9 z - f z * deriv y9 z
          = -(f z * deriv y9 z - deriv f z * y9 z) by ring, hWzv, neg_zero]
    rw [hnum, zero_div]
    rfl
  obtain ⟨cc, hcc⟩ := (Metric.isOpen_ball).exists_is_const_of_deriv_eq_zero
    (Metric.isPreconnected_ball) hφd hφderiv
  -- conclude by the identity theorem for `f - cc * y9`
  refine ⟨cc, ?_⟩
  have hgd : DifferentiableOn ℂ (fun z => f z - cc * y9 z) (Metric.ball ninth δ) :=
    hf.sub (hy9d.const_mul cc)
  have hga : AnalyticOnNhd ℂ (fun z => f z - cc * y9 z) (Metric.ball ninth δ) :=
    hgd.analyticOnNhd hBo
  have hgzero : ∀ z ∈ Metric.ball ninth ε, f z - cc * y9 z = 0 := by
    intro z hz
    have hφz : φ z = cc := hcc z hz
    rw [hφ] at hφz
    have hyz : y9 z ≠ 0 := hyne z hz
    have hfz : f z = cc * y9 z := (div_eq_iff hyz).mp hφz
    rw [hfz, sub_self]
  have hev : (fun z => f z - cc * y9 z) =ᶠ[𝓝 ninth] 0 := by
    filter_upwards [Metric.ball_mem_nhds ninth hεpos] with z hz
    exact hgzero z hz
  have hfin := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBp h9mem hev
  intro z hz
  have h := hfin hz
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end

end Work.A14D
