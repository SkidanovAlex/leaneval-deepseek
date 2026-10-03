import Mathlib.Order.CompletePartialOrder
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_ball_of_isMaxOn

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **Strong maximum principle for harmonic functions on an open ball, at an
arbitrary interior maximum point.**  If `u` is harmonic on `ball c R` and
attains its maximum over the whole ball at `p ∈ ball c R`, then `u` is
constant (equal to `u p`) on the whole ball.  (The level set
`{z ∈ ball c R | u z = u p}` is open by the strong maximum principle on
small balls, and closed inside the ball by continuity of `u`, so it is all
of the preconnected open ball.) -/
private lemma harmonic_eqOn_ball_of_isMaxOn_any {u : ℂ → ℝ} {c p : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball c R)) (hp : p ∈ ball c R)
    (hm : ∀ z ∈ ball c R, u z ≤ u p) : ∀ z ∈ ball c R, u z = u p := by
  classical
  set S : Set ℂ := {z : ℂ | z ∈ ball c R ∧ u z = u p}
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro q hq
    rcases hq with ⟨hqA, hqu⟩
    rcases (Metric.isOpen_iff.mp isOpen_ball q hqA) with ⟨ε, hε0, hball⟩
    have hle : ∀ y ∈ ball q ε, u y ≤ u q := by
      intro y hy
      rw [hqu]
      exact hm y (hball hy)
    have hconst := harmonic_eqOn_ball_of_isMaxOn (c := q) (r := ε) hε0 (hu.mono hball) hle
    refine ⟨ε, hε0, ?_⟩
    intro y hy
    refine ⟨hball hy, ?_⟩
    calc
      u y = u q := hconst y hy
      _ = u p := hqu
  have hS_cl : closure S ∩ ball c R ⊆ S := by
    intro x hx
    rcases hx with ⟨hxcl, hxb⟩
    have hcontAt : ContinuousAt u x :=
      (hu.continuousOn).continuousAt (isOpen_ball.mem_nhds hxb)
    have hmem : u x ∈ closure (u '' S) := mem_closure_image hcontAt hxcl
    have huS : u '' S = {u p} := by
      ext y
      constructor
      · rintro ⟨s, hsS, rfl⟩
        exact hsS.2
      · intro hy
        have hy_eq : y = u p := by simpa using hy
        exact ⟨p, ⟨hp, rfl⟩, hy_eq.symm⟩
    have hcl : closure (u '' S) = {u p} := by
      rw [huS]
      exact isClosed_singleton.closure_eq
    have hup : u x = u p := by
      rw [hcl] at hmem
      simpa using hmem
    exact ⟨hxb, hup⟩
  have hnonempty : (ball c R ∩ S).Nonempty := ⟨p, hp, hp, rfl⟩
  have hsub : ball c R ⊆ S :=
    isPreconnected_ball.subset_of_closure_inter_subset hS_open hnonempty hS_cl
  intro z hz
  exact (hsub hz).2

/-- **Maximum principle for the Dirichlet problem on a disk.**  Let `u` be
harmonic on the open disk `ball c R` and suppose the function
`G(z) := if ‖z - c‖ < R then u z else F z` is continuous on the closed disk
`closedBall c R`.  If the boundary data `F` is bounded above by `M` on the
boundary circle `sphere c R`, then `u z ≤ M` for every `z` in the open disk.
(Proof: `G` attains its maximum `V` on the compact closed disk.  A
maximiser in the interior forces `u` to be constant on the open disk by the
strong maximum principle, and the continuous extension `G` then has value
`V` on the boundary circle, where `F ≤ M`; a maximiser on the boundary
circle is directly bounded by `M`.  Either way `V ≤ M`, hence `u ≤ V ≤ M`.) -/
theorem harmonic_le_of_boundary_le {c : ℂ} {R M : ℝ} (hR : 0 < R) {F : ℂ → ℝ}
    (hFb : ∀ z : ℂ, z ∈ sphere c R → F z ≤ M)
    {u : ℂ → ℝ}
    (hu : ∀ z : ℂ, ‖z - c‖ < R → HarmonicAt u z)
    (huc : ContinuousOn (fun z : ℂ => if ‖z - c‖ < R then u z else F z) (closedBall c R)) :
    ∀ z : ℂ, ‖z - c‖ < R → u z ≤ M := by
  classical
  let G : ℂ → ℝ := fun z => if ‖z - c‖ < R then u z else F z
  have hucG : ContinuousOn G (closedBall c R) := by
    simpa [G] using huc
  have hcl_ne : (closedBall c R).Nonempty := by
    refine ⟨c, ?_⟩
    rw [Metric.mem_closedBall, dist_self]
    exact le_of_lt hR
  obtain ⟨p, hpcl, hpMax⟩ := (isCompact_closedBall c R).exists_isMaxOn hcl_ne hucG
  let V : ℝ := G p
  have huBall : HarmonicOnNhd u (ball c R) := by
    intro z hz
    exact hu z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hp_le_M : V ≤ M := by
    by_cases hp_ball : p ∈ ball c R
    · have hnp : ‖p - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hp_ball
      have hGp_u : G p = u p := by simp [G, hnp]
      have hVup : V = u p := by
        dsimp [V]
        exact hGp_u
      have hmax_ball : ∀ z ∈ ball c R, u z ≤ u p := by
        intro z hz
        have hzn : ‖z - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        calc
          u z = G z := by simp [G, hzn]
          _ ≤ G p := hpMax (ball_subset_closedBall hz)
          _ = u p := hGp_u
      have hconst : ∀ z ∈ ball c R, u z = u p :=
        harmonic_eqOn_ball_of_isMaxOn_any huBall hp_ball hmax_ball
      have hEqBall : Set.EqOn G (fun _ : ℂ => V) (ball c R) := by
        intro z hz
        have hzn : ‖z - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        calc
          G z = u z := by simp [G, hzn]
          _ = u p := hconst z hz
          _ = V := hVup.symm
      have hEqCl : Set.EqOn G (fun _ : ℂ => V) (closedBall c R) :=
        hEqBall.of_subset_closure hucG continuousOn_const ball_subset_closedBall
          (by rw [← closure_ball c hR.ne'])
      let q : ℂ := c + (R : ℂ)
      have hqnorm : ‖q - c‖ = R := by
        dsimp [q]
        rw [show (c + (R : ℂ)) - c = (R : ℂ) by ring]
        rw [norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (le_of_lt hR)
      have hqsphere : q ∈ sphere c R := by
        rw [Metric.mem_sphere]
        simpa [dist_eq_norm] using hqnorm
      have hqcl : q ∈ closedBall c R := by
        rw [Metric.mem_closedBall]
        exact le_of_eq (by simpa [dist_eq_norm] using hqnorm)
      have hqV : G q = V := hEqCl hqcl
      have hqnot : ¬ ‖q - c‖ < R := by
        rw [hqnorm]
        exact (lt_irrefl R)
      have hGqF : G q = F q := by
        dsimp [G]
        rw [if_neg hqnot]
      rw [hqV.symm, hGqF]
      exact hFb q hqsphere
    · have hp_sphere : p ∈ sphere c R := by
        have hdist_le : dist p c ≤ R := Metric.mem_closedBall.mp hpcl
        have hdist_ge : R ≤ dist p c := by
          exact le_of_not_gt (by
            intro hlt
            exact hp_ball (Metric.mem_ball.mpr hlt))
        rw [Metric.mem_sphere]
        exact le_antisymm hdist_le hdist_ge
      have hnpR : ‖p - c‖ = R := by
        simpa [dist_eq_norm] using (Metric.mem_sphere.mp hp_sphere)
      have hnp_not : ¬ ‖p - c‖ < R := by
        rw [hnpR]
        exact (lt_irrefl R)
      have hGpF : G p = F p := by
        dsimp [G]
        rw [if_neg hnp_not]
      have hVp : V = G p := by
        dsimp [V]
      rw [hVp, hGpF]
      exact hFb p hp_sphere
  intro z hz
  have hzball : z ∈ ball c R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  calc
    u z = G z := by simp [G, hz]
    _ ≤ G p := hpMax (ball_subset_closedBall hzball)
    _ = V := rfl
    _ ≤ M := hp_le_M

end Commons.Analysis.Complex.Harmonic