import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary
import Submission.Commons.Analysis.Complex.Harmonic.max_principle_meanValue
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Converse of the mean value property**: a function continuous on the ball `ball 0 R`
whose circle average over every sufficiently small circle around each interior point equals
its value at the center is harmonic on the whole ball.
Proof: fix `z` with `‖z‖ < R` and let `ρ = (R - ‖z‖)/2 > 0`.  Let `w` be the Dirichlet
solution on `ball z ρ` with boundary data `u ↾ sphere z ρ` (commons `dirichlet_ball`).
Then `v := u - w` is continuous on the closed ball, vanishes on the boundary sphere (by the
gluing continuity of the Dirichlet solution), and has the mean value property at interior
points (both `u` by hypothesis and `w` by the forward mean value theorem
`HarmonicOnNhd.circleAverage_eq` do).  By `max_principle_meanValue` applied to `v` and `-v`,
`v = 0` on the whole ball, so `u = w` near `z`, and `u` is harmonic at `z`
(`harmonicAt_congr_nhds`). -/
theorem harmonic_of_circleAverage {u : ℂ → ℝ} {R : ℝ}
    (hu : ContinuousOn u (ball (0 : ℂ) R))
    (hMV : ∀ p : ℂ, ‖p‖ < R → ∀ r : ℝ, 0 < r → ‖p‖ + r < R →
      Real.circleAverage u p r = u p) :
    InnerProductSpace.HarmonicOnNhd u (ball (0 : ℂ) R) := by
  intro z hz
  have hzR : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
  let ρ : ℝ := (R - ‖z‖) / 2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    nlinarith
  have hρR : ‖z‖ + ρ < R := by
    dsimp [ρ]
    nlinarith
  -- closedBall z ρ ⊆ ball 0 R
  have hclosed_sub : closedBall z ρ ⊆ ball (0 : ℂ) R := by
    intro x hx
    have hxle : ‖x - z‖ ≤ ρ := by
      simpa [dist_eq_norm] using (mem_closedBall.mp hx)
    have hxR : ‖x‖ < R := by
      calc
        ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ρ + ‖z‖ := by nlinarith
        _ < R := by nlinarith [hρR]
    simpa [mem_ball, dist_eq_norm] using hxR
  have huCl : ContinuousOn u (closedBall z ρ) := hu.mono hclosed_sub
  -- Dirichlet solution on ball z ρ with boundary data u
  let g : ℂ → ℝ := fun t => u (z + t)
  let T : ℂ → ℂ := fun t => z + t
  have hTmap : MapsTo T (sphere (0 : ℂ) ρ) (ball (0 : ℂ) R) := by
    intro t ht
    have htρ : ‖t‖ = ρ := by simpa [mem_sphere_iff_norm] using ht
    have hzt : ‖z + t‖ ≤ ‖z‖ + ‖t‖ := by simpa using norm_add_le z t
    have hzts : ‖z + t‖ < R := by
      calc
        ‖z + t‖ ≤ ‖z‖ + ρ := by nlinarith
        _ < R := hρR
    simpa [mem_ball, dist_eq_norm] using hzts
  have hg : ContinuousOn g (sphere (0 : ℂ) ρ) := by
    dsimp [g, T]
    refine ContinuousOn.comp hu (by fun_prop : ContinuousOn (fun t : ℂ => z + t) (sphere (0 : ℂ) ρ)) ?_
    simpa [T] using hTmap
  obtain ⟨P, hP, hPg⟩ := dirichlet_circle_boundary (g := g) (r := ρ) hρpos hg
  let w : ℂ → ℝ := fun x => P (x - z)
  -- w is harmonic on the open ball z ρ
  have hwHarm : HarmonicOnNhd w (ball z ρ) := by
    intro x hx
    dsimp [w]
    have hxnorm : ‖x - z‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hx
    have hPt : HarmonicAt P (x - z) := hP.harmonicOnNhd (x - z) (by simpa [mem_ball, dist_eq_norm] using hxnorm)
    have hf : AnalyticAt ℂ (fun y : ℂ => y - z) x := by
      exact AnalyticAt.sub (𝕜 := ℂ) (f := fun y : ℂ => y) (g := fun _ : ℂ => z) (x := x)
        analyticAt_id (analyticAt_const (v := z) (x := x))
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (u := P)
      (f := fun y : ℂ => y - z) (x := x) hf hPt
  -- w is continuous on the closed ball z ρ
  have hPcl : ContinuousOn P (closedBall (0 : ℂ) ρ) := by
    exact InnerProductSpace.HarmonicContOnCl.continuousOn_ball hP
  have hwCl : ContinuousOn w (closedBall z ρ) := by
    dsimp [w]
    refine ContinuousOn.comp hPcl (by fun_prop : ContinuousOn (fun x : ℂ => x - z) (closedBall z ρ)) ?_
    intro x hx
    have hxle : ‖x - z‖ ≤ ρ := by simpa [dist_eq_norm] using (mem_closedBall.mp hx)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxle
  -- w agrees with u on the boundary sphere
  have hEqSphere : ∀ x : ℂ, ‖x - z‖ = ρ → w x = u x := by
    intro x hx
    dsimp [w]
    calc
      P (x - z) = g (x - z) := hPg (x - z) hx
      _ = u (z + (x - z)) := rfl
      _ = u x := by congr 1; ring
  -- mean value property of w at interior points
  have hwM : ∀ p : ℂ, ‖p - z‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - z‖ + r < ρ →
      Real.circleAverage w p r = w p := by
    intro p hp r hr hcond
    have hwNhd' : HarmonicOnNhd w (closedBall p |r|) := by
      refine hwHarm.mono ?_
      intro x hx
      have hxr : ‖x - p‖ ≤ |r| := by simpa [dist_eq_norm] using (mem_closedBall.mp hx)
      have hxr' : ‖x - p‖ ≤ r := by simpa [abs_of_pos hr] using hxr
      have hxz : ‖x - z‖ < ρ := by
        have htri : ‖x - z‖ ≤ ‖x - p‖ + ‖p - z‖ := by
          simpa [dist_eq_norm] using (dist_triangle x p z)
        nlinarith
      simpa [mem_ball, dist_eq_norm] using hxz
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq (f := w) (c := p) (R := r) hwNhd'
  -- continuity of u and w on small spheres (integrability)
  have hsphere_sub : ∀ p : ℂ, ∀ r : ℝ, ‖p - z‖ + r < ρ → sphere p r ⊆ closedBall z ρ := by
    intro p r hcond x hx
    have hxr : ‖x - p‖ = r := by
      have h₁ := mem_sphere_iff_norm.mp hx
      simpa [dist_eq_norm] using h₁
    have hxz : ‖x - z‖ < ρ := by
      have htri : ‖x - z‖ ≤ ‖x - p‖ + ‖p - z‖ := by
        simpa [dist_eq_norm] using (dist_triangle x p z)
      nlinarith
    have hxzle : ‖x - z‖ ≤ ρ := le_of_lt hxz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxzle
  -- the maximum principle part
  have hvM : ∀ p : ℂ, ‖p - z‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - z‖ + r < ρ →
      Real.circleAverage (u - w) p r = (u - w) p := by
    intro p hp r hr hcond
    have hpR : ‖p‖ < R := by
      have htri : ‖p‖ ≤ ‖p - z‖ + ‖z‖ := by
        simpa using (norm_add_le (p - z) z)
      have h1 : ‖p - z‖ + ‖z‖ < R := by nlinarith
      nlinarith
    have hprR : ‖p‖ + r < R := by
      have htri : ‖p‖ ≤ ‖p - z‖ + ‖z‖ := by
        simpa using (norm_add_le (p - z) z)
      have h1 : ‖p‖ + r ≤ ‖p - z‖ + ‖z‖ + r := by nlinarith
      have h2 : ‖p - z‖ + ‖z‖ + r < ρ + ‖z‖ := by nlinarith
      have h3 : ρ + ‖z‖ < R := by nlinarith [hρR]
      linarith
    have huM : Real.circleAverage u p r = u p := hMV p hpR r hr hprR
    have hwMp : Real.circleAverage w p r = w p := hwM p hp r hr hcond
    have hCu : CircleIntegrable u p r := by
      apply ContinuousOn.circleIntegrable hr.le
      exact huCl.mono (hsphere_sub p r hcond)
    have hCw : CircleIntegrable w p r := by
      apply ContinuousOn.circleIntegrable hr.le
      exact hwCl.mono (hsphere_sub p r hcond)
    calc
      Real.circleAverage (u - w) p r = Real.circleAverage (fun z : ℂ => u z - w z) p r := rfl
      _ = Real.circleAverage u p r - Real.circleAverage w p r := Real.circleAverage_fun_sub hCu hCw
      _ = u p - w p := by rw [huM, hwMp]
  have hbd : ∀ x : ℂ, ‖x - z‖ = ρ → (u - w) x ≤ 0 := by
    intro x hx
    have hEq : w x = u x := hEqSphere x hx
    have h0 : (u - w) x = 0 := by
      simp [hEq]
    exact le_of_eq h0
  have hres1 : ∀ x : ℂ, ‖x - z‖ ≤ ρ → (u - w) x ≤ 0 :=
    max_principle_meanValue (v := u - w) (c := z) (R := ρ) hρpos (huCl.sub hwCl) hvM hbd
  have hvMNeg : ∀ p : ℂ, ‖p - z‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - z‖ + r < ρ →
      Real.circleAverage (-(u - w)) p r = (-(u - w)) p := by
    intro p hp r hr hcond
    have hmain := hvM p hp r hr hcond
    calc
      Real.circleAverage (-(u - w)) p r
          = Real.circleAverage (fun z : ℂ => (-1 : ℝ) • (u - w) z) p r := by
              congr 1
              funext z
              simp
      _ = (-1 : ℝ) • Real.circleAverage (u - w) p r := Real.circleAverage_fun_smul
      _ = (-(u - w)) p := by
        rw [hmain]
        simp
  have hbdNeg : ∀ x : ℂ, ‖x - z‖ = ρ → (-(u - w)) x ≤ 0 := by
    intro x hx
    have hEq : w x = u x := hEqSphere x hx
    have h0 : (u - w) x = 0 := by
      simp [hEq]
    simp [h0]
  have hres2 : ∀ x : ℂ, ‖x - z‖ ≤ ρ → (-(u - w)) x ≤ 0 :=
    max_principle_meanValue (v := -(u - w)) (c := z) (R := ρ) hρpos (huCl.sub hwCl).neg hvMNeg hbdNeg
  -- u = w near z
  have heqOn : ∀ x : ℂ, ‖x - z‖ < ρ → u x = w x := by
    intro x hx
    have hxle : ‖x - z‖ ≤ ρ := le_of_lt hx
    have h₁ : (u - w) x ≤ 0 := hres1 x hxle
    have h₂' : (-(u - w)) x ≤ 0 := hres2 x hxle
    have h₂ : 0 ≤ (u - w) x := by
      have h₂'' : -((u - w) x) ≤ 0 := by simpa using h₂'
      exact neg_nonpos.mp h₂''
    have hzero : (u - w) x = 0 := le_antisymm h₁ h₂
    have hval : u x - w x = 0 := by simpa using hzero
    linarith
  have hEqNhd : u =ᶠ[𝓝 z] w := by
    filter_upwards [Metric.ball_mem_nhds z hρpos] with x hx
    exact heqOn x (by simpa [mem_ball, dist_eq_norm] using hx)
  have hwz : HarmonicAt w z := hwHarm z (by simpa [mem_ball, dist_eq_norm] using hρpos)
  exact (InnerProductSpace.harmonicAt_congr_nhds hEqNhd).mpr hwz

end Commons.Analysis.Complex.Harmonic
