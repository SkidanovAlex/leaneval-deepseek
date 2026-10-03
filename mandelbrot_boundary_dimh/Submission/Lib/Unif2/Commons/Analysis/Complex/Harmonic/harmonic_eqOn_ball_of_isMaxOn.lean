import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Normed.Module.Connected
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

open Set Metric Complex InnerProductSpace
open scoped Topology Real

namespace Commons.Analysis.Complex.Harmonic

/-- **Strong maximum principle for harmonic functions on an open ball.**
If `u` is harmonic on the ball `ball c r` and attains its maximum over the
whole ball at the centre `c`, then `u` is constant on the ball.
(Mean-value property on small circles around a point of `{u = u c}`;
openness/closeness of that level set inside the connected open ball.) -/
theorem harmonic_eqOn_ball_of_isMaxOn {u : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hu : HarmonicOnNhd u (ball c r)) (hmax : ∀ z ∈ ball c r, u z ≤ u c) :
    ∀ z ∈ ball c r, u z = u c := by
  classical
  let M : ℝ := u c
  have hmaxM : ∀ z ∈ ball c r, u z ≤ M := by
    intro z hz
    simpa [M] using hmax z hz
  let S : Set ℂ := {z : ℂ | z ∈ ball c r ∧ u z = M}
  /- S is open: each of its points is surrounded by a ball where u equals M,
     by the mean-value property on small circles (u ≤ M everywhere). -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hzS
    rcases hzS with ⟨hzball, huzM⟩
    let d : ℝ := dist z c
    have hdr : d < r := by
      dsimp [d]
      exact mem_ball.mp hzball
    let δ : ℝ := (r - d) / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      nlinarith [hdr]
    have hclosed_le : ∀ ρ, ρ ≤ δ → closedBall z ρ ⊆ ball c r := by
      intro ρ hρle x hx
      rw [mem_ball]
      have hxd : dist x z ≤ ρ := mem_closedBall.mp hx
      have htri : dist x c ≤ dist x z + d := by
        dsimp [d]
        simpa [dist_comm] using (dist_triangle x z c)
      have hδdef : δ = (r - d) / 2 := rfl
      nlinarith [hxd, hρle, htri, hdr, hδdef]
    have hballδ : ball z δ ⊆ ball c r :=
      (Metric.ball_subset_closedBall.trans (hclosed_le δ le_rfl))
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    constructor
    · exact hballδ hw
    · by_cases hwz : w = z
      · rw [hwz]
        exact huzM
      · let ρ : ℝ := dist w z
        have hρpos : 0 < ρ := by
          dsimp [ρ]
          exact dist_pos.mpr hwz
        have hρleδ : ρ ≤ δ := by
          dsimp [ρ]
          exact le_of_lt (mem_ball.mp hw)
        have hclosed : closedBall z ρ ⊆ ball c r := hclosed_le ρ hρleδ
        have hclosedabs : closedBall z |ρ| ⊆ ball c r := by
          simpa [abs_of_nonneg hρpos.le] using hclosed
        have hsphere_subset : sphere z |ρ| ⊆ ball c r :=
          (Metric.sphere_subset_closedBall.trans hclosedabs)
        have hharmOnClosedAbs : HarmonicOnNhd u (closedBall z |ρ|) := by
          simpa [abs_of_nonneg hρpos.le] using (hu.mono hclosed)
        have havgu : Real.circleAverage u z ρ = u z :=
          InnerProductSpace.HarmonicOnNhd.circleAverage_eq (f := u) (c := z) (R := ρ)
            hharmOnClosedAbs
        have havguM : Real.circleAverage u z ρ = M := havgu.trans huzM
        have hcontOnSphere : ContinuousOn u (sphere z |ρ|) :=
          (InnerProductSpace.HarmonicOnNhd.continuousOn hu).mono hsphere_subset
        have hu_int : CircleIntegrable u z ρ := by
          apply ContinuousOn.circleIntegrable'
          exact hcontOnSphere
        have hconst_int : CircleIntegrable (fun _ : ℂ => M) z ρ := circleIntegrable_const M z ρ
        have havg_g : Real.circleAverage (fun x : ℂ => M - u x) z ρ = 0 := by
          calc
            Real.circleAverage (fun x : ℂ => M - u x) z ρ
                = Real.circleAverage (fun _ : ℂ => M) z ρ - Real.circleAverage u z ρ := by
                    simpa using
                      (Real.circleAverage_fun_sub (f₁ := fun _ : ℂ => M) (f₂ := u)
                        hconst_int hu_int)
            _ = M - M := by
              rw [Real.circleAverage_const, havguM]
            _ = 0 := by ring
        have hg_zero_on_sphere : ∀ x ∈ sphere z |ρ|, (fun x : ℂ => M - u x) x = 0 :=
          eq_zero_on_sphere_of_circleAverage_eq_zero (f := fun x : ℂ => M - u x) (c := z)
            (R := ρ)
            (by
              exact (continuousOn_const.sub hcontOnSphere))
            (by
              intro x hx
              exact sub_nonneg.mpr (hmaxM x (hsphere_subset hx)))
            havg_g
        have hwmemsph : w ∈ sphere z |ρ| := by
          rw [Metric.mem_sphere]
          dsimp [ρ]
          rw [abs_of_nonneg (dist_nonneg : 0 ≤ dist w z)]
        have hwEq : u w = M := by
          have hz0 : (fun x : ℂ => M - u x) w = 0 := hg_zero_on_sphere w hwmemsph
          linarith
        exact hwEq
  /- The complement of S in the ball is open: at points with u < M continuity
     of u keeps values below M on a small ball. -/
  have hV_open : IsOpen (ball c r \ S) := by
    rw [Metric.isOpen_iff]
    intro z hzV
    rcases hzV with ⟨hzball, hznotS⟩
    have hneq : u z ≠ M := by
      intro hzeq
      exact hznotS ⟨hzball, hzeq⟩
    have hlt : u z < M := lt_of_le_of_ne (hmaxM z hzball) hneq
    have hcontAt : ContinuousAt u z := (InnerProductSpace.HarmonicOnNhd.continuousOn hu).continuousAt
      (by exact isOpen_ball.mem_nhds hzball)
    have hevent : ∀ᶠ x in 𝓝 z, u x < M := by
      simpa [M] using
        (ContinuousAt.eventually_lt hcontAt continuousAt_const hlt)
    rcases (Metric.eventually_nhds_iff.mp hevent) with ⟨ε₂, hε₂pos, hε₂⟩
    have hballMem : ball c r ∈ 𝓝 z := isOpen_ball.mem_nhds hzball
    rcases (Metric.mem_nhds_iff.mp hballMem) with ⟨ε₁, hε₁pos, hε₁⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
    intro x hx
    have hx₁ : x ∈ ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hx
    have hx₂ : x ∈ ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hx
    have hxball_c : x ∈ ball c r := hε₁ hx₁
    have hxlt : u x < M := hε₂ hx₂
    exact ⟨hxball_c, by
      intro hxS
      exact (ne_of_lt hxlt) hxS.2⟩
  /- S is a nonempty open-and-closed subset (relative to the ball) of the
     connected ball, so S is the whole ball. -/
  have hc_ball : c ∈ ball c r := mem_ball_self hr
  have hcS : c ∈ S := by
    exact ⟨hc_ball, rfl⟩
  have hdisj : Disjoint S (ball c r \ S) := by
    rw [Set.disjoint_left]
    intro x hxS hxV
    exact hxV.2 hxS
  have hcover : ball c r ⊆ S ∪ (ball c r \ S) := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr ⟨hx, hxS⟩
  have hinter_nonempty : (ball c r ∩ S).Nonempty := ⟨c, hc_ball, hcS⟩
  have hball_sub_S : ball c r ⊆ S :=
    IsPreconnected.subset_left_of_subset_union hS_open hV_open hdisj hcover hinter_nonempty
      isPreconnected_ball
  intro z hz
  have hzS : z ∈ S := hball_sub_S hz
  simpa [M, S] using hzS.2

end Commons.Analysis.Complex.Harmonic
