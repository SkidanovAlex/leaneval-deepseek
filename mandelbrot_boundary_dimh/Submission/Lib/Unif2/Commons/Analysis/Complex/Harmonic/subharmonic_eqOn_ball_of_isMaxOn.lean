import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.CompletePartialOrder
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

noncomputable section

open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Strong maximum principle for function with the circle sub-mean-value
inequality on an open ball, in the "maximum attained at the centre" form.**

If `u` is continuous on the open ball `ball c R`, satisfies the circle
sub-mean-value inequality `u p ≤ circleAverage u p r` at every interior point
`p` for every admissible circle, and `u z ≤ u c` for every `z` in the ball,
then `u` is constant equal to `u c` on the whole ball.

Proof: the level set `S = {z ∈ ball c R | u z = u c}` is nonempty (it contains
`c`), open (at a point `z ∈ S` the mean-value inequality on a small circle
around `z` inside the ball forces `u ≡ u c` on that circle, since `u ≤ u c`
everywhere), and its complement in the ball is open by continuity.  The open
ball is preconnected, so `S` is all of it. -/
theorem subharmonic_eqOn_ball_of_isMaxOn {c : ℂ} {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hcont : ContinuousOn u (Metric.ball c R))
    (hmvp : ∀ p ∈ Metric.ball c R, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball c R →
      u p ≤ Real.circleAverage u p r)
    (hmax : ∀ z ∈ Metric.ball c R, u z ≤ u c) :
    ∀ z ∈ Metric.ball c R, u z = u c := by
  classical
  let M : ℝ := u c
  have hmaxM : ∀ z ∈ Metric.ball c R, u z ≤ M := fun z hz => by simpa [M] using hmax z hz
  let S : Set ℂ := {z : ℂ | z ∈ Metric.ball c R ∧ u z = M}
  /- `S` is open: at each of its points `z`, the sub-mean-value inequality on
     a small circle around `z` (inside the ball) pins the average of `u` at
     `M = u z`, so `M - u ≥ 0` on that circle has vanishing average and is
     therefore identically zero there. -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hzS
    rcases hzS with ⟨hzball, huzM⟩
    let d : ℝ := dist z c
    have hdr : d < R := by simpa [d] using (Metric.mem_ball.mp hzball)
    let δ : ℝ := (R - d) / 2
    have hδpos : 0 < δ := by dsimp [δ]; nlinarith
    have hclosed_le : ∀ ρ, ρ ≤ δ → Metric.closedBall z ρ ⊆ Metric.ball c R := by
      intro ρ hρle x hx
      rw [Metric.mem_ball]
      have hxd : dist x z ≤ ρ := Metric.mem_closedBall.mp hx
      have htri : dist x c ≤ dist x z + d := by
        dsimp [d]
        simpa [dist_comm] using (dist_triangle x z c)
      have hδeq : δ = (R - d) / 2 := rfl
      nlinarith [hxd, hρle, htri, hdr, hδeq]
    have hballδ : Metric.ball z δ ⊆ Metric.ball c R :=
      Metric.ball_subset_closedBall.trans (hclosed_le δ le_rfl)
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    refine ⟨hballδ hw, ?_⟩
    by_cases hwz : w = z
    · rw [hwz]
      exact huzM
    · let ρ : ℝ := dist w z
      have hρpos : 0 < ρ := by
        dsimp [ρ]
        exact dist_pos.mpr hwz
      have hρle : ρ ≤ δ := by
        dsimp [ρ]
        exact le_of_lt (Metric.mem_ball.mp hw)
      have hclosedρ : Metric.closedBall z ρ ⊆ Metric.ball c R := hclosed_le ρ hρle
      have hclosedabs : Metric.closedBall z |ρ| ⊆ Metric.ball c R := by
        simpa [abs_of_nonneg hρpos.le] using hclosedρ
      have hsphere_subset : Metric.sphere z |ρ| ⊆ Metric.ball c R :=
        Metric.sphere_subset_closedBall.trans hclosedabs
      have hcontSph : ContinuousOn u (Metric.sphere z |ρ|) := hcont.mono hsphere_subset
      have havg_ge : u z ≤ Real.circleAverage u z ρ := hmvp z hzball ρ hρpos hclosedρ
      have havg_le : Real.circleAverage u z ρ ≤ M :=
        Real.circleAverage_mono_on_of_le_circle (c := z) (R := ρ) (f := u) (a := M)
          (ContinuousOn.circleIntegrable' hcontSph)
          (fun x hx => hmaxM x (hsphere_subset hx))
      have havgM : Real.circleAverage u z ρ = M :=
        le_antisymm havg_le (by rw [← huzM]; exact havg_ge)
      have hgavg : Real.circleAverage (fun x : ℂ => M - u x) z ρ = 0 := by
        have h := Real.circleAverage_fun_sub (f₁ := fun _ : ℂ => M) (f₂ := u)
          (circleIntegrable_const M z ρ) (ContinuousOn.circleIntegrable' hcontSph)
        rw [havgM, Real.circleAverage_const] at h
        simpa using h
      have hgnonneg : ∀ x ∈ Metric.sphere z |ρ|, 0 ≤ (fun x : ℂ => M - u x) x :=
        fun x hx => sub_nonneg.mpr (hmaxM x (hsphere_subset hx))
      have hgz := eq_zero_on_sphere_of_circleAverage_eq_zero (f := fun x : ℂ => M - u x)
        (c := z) (R := ρ) (continuousOn_const.sub hcontSph) hgnonneg hgavg
      have hwmem : w ∈ Metric.sphere z |ρ| := by
        rw [Metric.mem_sphere]
        dsimp [ρ]
        rw [abs_of_nonneg (dist_nonneg : (0 : ℝ) ≤ dist w z)]
      have hzero : M - u w = 0 := hgz w hwmem
      linarith
  /- The complement of `S` in the ball is open: at a point of the ball where
     `u < M`, continuity keeps the values below `M` on a small ball. -/
  have hV_open : IsOpen (Metric.ball c R \ S) := by
    rw [Metric.isOpen_iff]
    intro z hzV
    rcases hzV with ⟨hzball, hznotS⟩
    have hneq : u z ≠ M := by
      intro hzeq
      exact hznotS ⟨hzball, hzeq⟩
    have hlt : u z < M := lt_of_le_of_ne (hmaxM z hzball) hneq
    have hcontAt : ContinuousAt u z := hcont.continuousAt (isOpen_ball.mem_nhds hzball)
    have hevent : ∀ᶠ x in 𝓝 z, u x < M :=
      ContinuousAt.eventually_lt hcontAt continuousAt_const hlt
    rcases (Metric.eventually_nhds_iff.mp hevent) with ⟨ε₂, hε₂pos, hε₂⟩
    rcases (Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzball)) with ⟨ε₁, hε₁pos, hε₁⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
    intro x hx
    have hx₁ : x ∈ Metric.ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hx
    have hx₂ : x ∈ Metric.ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hx
    exact ⟨hε₁ hx₁, fun hxS => (ne_of_lt (hε₂ hx₂)) hxS.2⟩
  /- `S` is a nonempty relatively open-and-closed subset of the preconnected
     open ball, hence it is the whole ball. -/
  have hc_ball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hcS : c ∈ S := ⟨hc_ball, rfl⟩
  have hdisj : Disjoint S (Metric.ball c R \ S) := by
    rw [Set.disjoint_left]
    intro x hxS hxV
    exact hxV.2 hxS
  have hcover : Metric.ball c R ⊆ S ∪ (Metric.ball c R \ S) := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr ⟨hx, hxS⟩
  have hnonempty : (Metric.ball c R ∩ S).Nonempty := ⟨c, hc_ball, hcS⟩
  have hball_sub_S : Metric.ball c R ⊆ S :=
    IsPreconnected.subset_left_of_subset_union hS_open hV_open hdisj hcover hnonempty
      Metric.isPreconnected_ball
  intro z hz
  have hzS : z ∈ S := hball_sub_S hz
  simpa [M] using hzS.2

end Commons.Analysis.Complex.Harmonic