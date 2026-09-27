import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- If `z` lies strictly inside `closedBall c R`, then that closed ball is a
neighbourhood of `z`. -/
private lemma closedBall_mem_nhds_of_lt {c : ℂ} {R : ℝ} {z : ℂ} (hz : ‖z - c‖ < R) :
    closedBall c R ∈ 𝓝 z := by
  let ε : ℝ := (R - ‖z - c‖) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    nlinarith
  refine mem_of_superset (ball_mem_nhds z hε) ?_
  intro x hx
  have hxε : ‖x - z‖ < ε := by simpa [dist_eq_norm] using (mem_ball.mp hx)
  have htri : ‖x - c‖ ≤ ‖x - z‖ + ‖z - c‖ := by
    simpa [dist_eq_norm] using (dist_triangle x z c)
  rw [Metric.mem_closedBall, dist_eq_norm]
  dsimp [ε] at hxε
  nlinarith

/-- **Strong maximum principle for functions with the circle sub-mean-value
inequality on an open ball.**  If `v` is continuous on the closed ball
`closedBall c R`, satisfies the sub-mean-value inequality
`v p ≤ Real.circleAverage v p r` at every interior point on every admissible
circle, and the maximum `M` over the closed ball is attained at an interior
point (`v p = M` with `‖p - c‖ < R`), then `v ≡ M` on the whole open ball.
(The level set `S = {v = M}` inside the ball is nonempty, open by the
sub-mean-value inequality on small circles (the integrand `M - v ≥ 0` has a
nonpositive circle average, and the average of `v` is sandwiched between
`v z = M` and `M`), and its complement is open by continuity; the open ball
is connected.) -/
private lemma eqOn_openBall_of_isMaxOn_sub {v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hcont : ContinuousOn v (closedBall c R))
    (hsub : ∀ p : ℂ, ‖p - c‖ < R → ∀ r : ℝ, 0 < r → ‖p - c‖ + r < R →
      v p ≤ Real.circleAverage v p r)
    {M : ℝ} (hM : ∀ z : ℂ, ‖z - c‖ ≤ R → v z ≤ M) {p : ℂ}
    (hpR : ‖p - c‖ < R) (hpM : v p = M) :
    ∀ z : ℂ, ‖z - c‖ < R → v z = M := by
  classical
  let S : Set ℂ := {z : ℂ | ‖z - c‖ < R ∧ v z = M}
  let A : Set ℂ := {z : ℂ | ‖z - c‖ < R}
  have hA_eq : A = ball c R := by
    ext z
    simp [A, dist_eq_norm]
  have hA_open : IsOpen A := by
    rw [hA_eq]
    exact isOpen_ball
  have hA_pre : IsPreconnected A := by
    rw [hA_eq]
    exact isPreconnected_ball
  /- `S` is open: at each point `z ∈ S` the sub-mean-value inequality on small
     circles centred at `z` forces `v ≡ M` on a neighbourhood of `z`
     (`M - v ≥ 0` on the circle and its circle average vanishes, so it is
     identically zero there). -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hz
    rcases hz with ⟨hzR, hvzM⟩
    let δ : ℝ := (R - ‖z - c‖) / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      nlinarith
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    have hwzδ : ‖w - z‖ < δ := by simpa [dist_eq_norm] using (mem_ball.mp hw)
    have hwR : ‖w - c‖ < R := by
      have htri : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        simpa [dist_eq_norm] using (dist_triangle w z c)
      dsimp [δ] at hwzδ
      nlinarith
    refine ⟨hwR, ?_⟩
    by_cases hwz : w = z
    · rw [hwz]
      exact hvzM
    · let ρ : ℝ := ‖w - z‖
      have hρpos : 0 < ρ := by
        dsimp [ρ]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
      have hρδ : ρ < δ := by
        dsimp [ρ]
        exact hwzδ
      have hcond : ‖z - c‖ + ρ < R := by
        dsimp [δ] at hρδ
        nlinarith
      have hsphere_cl : sphere z |ρ| ⊆ closedBall c R := by
        intro x hx
        have hxz : ‖x - z‖ = |ρ| := mem_sphere_iff_norm.mp hx
        have hxρ : ‖x - z‖ = ρ := by
          rw [hxz]
          exact abs_of_nonneg hρpos.le
        have hxc : ‖x - c‖ ≤ ‖x - z‖ + ‖z - c‖ := by
          simpa [dist_eq_norm] using (dist_triangle x z c)
        rw [Metric.mem_closedBall, dist_eq_norm]
        nlinarith
      have hcontSph : ContinuousOn v (sphere z |ρ|) := hcont.mono hsphere_cl
      /- Subharmonicity at `z` on the circle of radius `ρ`: the circle average of
         `v` is sandwiched between `v z = M` and `M`, hence equals `M`. -/
      have havg_le_M : Real.circleAverage v z ρ ≤ M := by
        refine Real.circleAverage_mono_on_of_le_circle (f := v) (a := M) ?_ ?_
        · exact ContinuousOn.circleIntegrable' hcontSph
        · intro x hx
          have hxcl : ‖x - c‖ ≤ R := by
            have hxB : x ∈ closedBall c R := hsphere_cl hx
            rw [Metric.mem_closedBall, dist_eq_norm] at hxB
            exact hxB
          exact hM x hxcl
      have havg_ge_M : M ≤ Real.circleAverage v z ρ := by
        simpa [hvzM] using (hsub z hzR ρ hρpos hcond)
      have havguM : Real.circleAverage v z ρ = M := le_antisymm havg_le_M havg_ge_M
      have hnonneg : ∀ x ∈ sphere z |ρ|, 0 ≤ (fun x : ℂ => M - v x) x := by
        intro x hx
        have hxcl : ‖x - c‖ ≤ R := by
          have hxB : x ∈ closedBall c R := hsphere_cl hx
          rw [Metric.mem_closedBall, dist_eq_norm] at hxB
          exact hxB
        exact sub_nonneg.mpr (hM x hxcl)
      have hu_int : CircleIntegrable v z ρ := ContinuousOn.circleIntegrable' hcontSph
      have hconst_int : CircleIntegrable (fun _ : ℂ => M) z ρ := circleIntegrable_const M z ρ
      have havg_g : Real.circleAverage (fun x : ℂ => M - v x) z ρ = 0 := by
        calc
          Real.circleAverage (fun x : ℂ => M - v x) z ρ
              = Real.circleAverage (fun _ : ℂ => M) z ρ - Real.circleAverage v z ρ := by
                  simpa using
                    (Real.circleAverage_fun_sub (f₁ := fun _ : ℂ => M) (f₂ := v)
                      hconst_int hu_int)
          _ = M - M := by
            rw [Real.circleAverage_const, havguM]
          _ = 0 := by ring
      have hg_zero : ∀ x ∈ sphere z |ρ|, (fun x : ℂ => M - v x) x = 0 :=
        eq_zero_on_sphere_of_circleAverage_eq_zero (f := fun x : ℂ => M - v x) (c := z)
          (R := ρ)
          (by exact (continuousOn_const.sub hcontSph))
          hnonneg
          havg_g
      have hwSph : w ∈ sphere z |ρ| := by
        rw [Metric.mem_sphere]
        rw [dist_eq_norm]
        dsimp [ρ]
        rw [abs_of_nonneg (norm_nonneg (w - z))]
      have hMv : (fun x : ℂ => M - v x) w = 0 := hg_zero w hwSph
      have : M - v w = 0 := hMv
      linarith

  /- The complement `A \ S` is open: at points of `A` where `v < M`,
     continuity of `v` keeps the values below `M` on a neighbourhood. -/
  have hV_open : IsOpen (A \ S) := by
    rw [Metric.isOpen_iff]
    intro z hzV
    rcases hzV with ⟨hzA, hznotS⟩
    have hzR : ‖z - c‖ < R := by simpa [A] using hzA
    have hznotS' : ¬ (‖z - c‖ < R ∧ v z = M) := by simpa [S] using hznotS
    have hneq : v z ≠ M := by
      intro hzeq
      exact hznotS' ⟨hzR, hzeq⟩
    have hlt : v z < M := lt_of_le_of_ne (hM z (le_of_lt hzR)) hneq
    have hcontz : ContinuousAt v z := hcont.continuousAt (closedBall_mem_nhds_of_lt hzR)
    have hevent : ∀ᶠ w in 𝓝 z, v w < M := by
      simpa using (ContinuousAt.eventually_lt hcontz continuousAt_const hlt)
    have hmemA : A ∈ 𝓝 z := hA_open.mem_nhds hzA
    rcases (Metric.mem_nhds_iff.mp hmemA) with ⟨ε₁, hε₁pos, hε₁⟩
    rcases (Metric.eventually_nhds_iff.mp hevent) with ⟨ε₂, hε₂pos, hε₂⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
    intro w hw
    have hw₁ : w ∈ ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hw
    have hw₂ : w ∈ ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hw
    have hwA : w ∈ A := hε₁ hw₁
    have hwlt : v w < M := hε₂ hw₂
    refine ⟨hwA, ?_⟩
    intro hwS
    have hwS' : ‖w - c‖ < R ∧ v w = M := by simpa [S] using hwS
    exact (ne_of_lt hwlt) hwS'.2

  /- `S` is a nonempty relatively open-and-closed subset of the connected
     open ball `A`, hence `A ⊆ S`. -/
  have hdisj : Disjoint S (A \ S) := by
    rw [Set.disjoint_left]
    intro z hzS hzV
    exact hzV.2 hzS
  have hcover : A ⊆ S ∪ (A \ S) := by
    intro z hzA
    by_cases hzS : z ∈ S
    · exact Or.inl hzS
    · exact Or.inr ⟨hzA, hzS⟩
  have hS_nonempty : (A ∩ S).Nonempty := ⟨p, by simpa [A] using hpR, by
    dsimp [S]
    exact ⟨hpR, hpM⟩⟩
  have hA_sub_S : A ⊆ S :=
    IsPreconnected.subset_left_of_subset_union hS_open hV_open hdisj hcover hS_nonempty hA_pre
  intro z hzR
  have hzS : z ∈ S := hA_sub_S (by simpa [A] using hzR)
  have hzS' : ‖z - c‖ < R ∧ v z = M := by simpa [S] using hzS
  exact hzS'.2

/-- **Maximum principle for continuous subharmonic functions** (circle-average
form: `g p ≤ Real.circleAverage g p r` at every interior point `p` and every
admissible circle radius `r`). If `g ≤ 0` on the boundary sphere, then `g ≤ 0`
on the whole closed ball.

Proof: mirror `max_principle_meanValue` (the level set of the maximum is clopen
in the connected closed ball); at an interior maximizer the subharmonicity gives
`M = g p ≤ avg ≤ M`, hence equality on surrounding circles. -/
theorem max_principle_subharmonic {g : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn g (closedBall c R))
    (hsub : ∀ p : ℂ, ‖p - c‖ < R → ∀ r : ℝ, 0 < r → ‖p - c‖ + r < R →
      g p ≤ Real.circleAverage g p r)
    (hbd : ∀ z : ℂ, ‖z - c‖ = R → g z ≤ 0) :
    ∀ z : ℂ, ‖z - c‖ ≤ R → g z ≤ 0 := by
  classical
  /- `g` attains its maximum `M = g p` on the compact closed ball. -/
  have hne : (closedBall c R).Nonempty := ⟨c, by
    rw [Metric.mem_closedBall, dist_self]
    exact le_of_lt hR⟩
  obtain ⟨p, hpB, hpMax⟩ := (isCompact_closedBall c R).exists_isMaxOn hne hcont
  let M : ℝ := g p
  have hMmax : ∀ z : ℂ, ‖z - c‖ ≤ R → g z ≤ M := by
    intro z hz
    have hzB : z ∈ closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hz
    simpa [M] using (hpMax hzB)
  by_cases hMpos : 0 < M
  · /- if M > 0 the maximiser `p` is interior, and the strong maximum
       principle makes `g ≡ M` on the open ball; continuity extends this to
       the boundary sphere, contradicting `g ≤ 0` there. -/
    have hpR : ‖p - c‖ < R := by
      have hple : ‖p - c‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hpB
      exact lt_of_le_of_ne hple (by
        intro heq
        have hbd_p : g p ≤ 0 := hbd p heq
        linarith)
    have hgM_openBall : ∀ z : ℂ, ‖z - c‖ < R → g z = M :=
      eqOn_openBall_of_isMaxOn_sub hcont hsub hMmax hpR rfl
    let q : ℂ := c + (R : ℂ)
    have hq_cl : q ∈ closedBall c R := by
      rw [Metric.mem_closedBall]
      dsimp [q]
      rw [dist_eq_norm]
      have hnorm : ‖(c + (R : ℂ)) - c‖ = R := by
        rw [show (c + (R : ℂ)) - c = (R : ℂ) by ring]
        rw [norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (le_of_lt hR)
      rw [hnorm]
    have hqR : ‖q - c‖ = R := by
      dsimp [q]
      rw [show (c + (R : ℂ)) - c = (R : ℂ) by ring]
      rw [norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (le_of_lt hR)
    /- extend `g ≡ M` from the open ball to its closure (the closed ball) by
       continuity -/
    have hEqBall : Set.EqOn g (fun _ : ℂ => M) {z : ℂ | ‖z - c‖ < R} := by
      intro z hz
      exact hgM_openBall z hz
    have hEqCl : Set.EqOn g (fun _ : ℂ => M) (closedBall c R) :=
      hEqBall.of_subset_closure hcont continuousOn_const
        (by
          intro z hz
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact le_of_lt hz)
        (by
          rw [show {z : ℂ | ‖z - c‖ < R} = ball c R by
            ext z
            simp [dist_eq_norm]]
          rw [closure_ball c hR.ne'])
    have hgqM : g q = M := hEqCl hq_cl
    have hbd_q : g q ≤ 0 := hbd q hqR
    rw [hgqM] at hbd_q
    linarith
  · /- `M ≤ 0`: every value is at most the maximum. -/
    intro z hz
    exact le_trans (hMmax z hz) (le_of_not_gt hMpos)

end Commons.Analysis.Complex.Harmonic
