import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic
import Submission.Commons.Analysis.Complex.Harmonic.eq_zero_on_sphere_of_circleAverage_eq_zero

open Metric Set Filter
open scoped Topology Real

namespace Commons.Analysis.Complex.Harmonic

/-- If `z` lies strictly inside `closedBall c R`, then that closed ball is a
neighbourhood of `z`. -/
private lemma closedBall_mem_nhds_of_lt' {c : ℂ} {R : ℝ} {z : ℂ} (hz : ‖z - c‖ < R) :
    closedBall c R ∈ 𝓝 z := by
  have hε : 0 < (R - ‖z - c‖) / 2 := by nlinarith
  refine mem_of_superset (ball_mem_nhds z hε) ?_
  intro x hx
  have hxε : ‖x - z‖ < (R - ‖z - c‖) / 2 := by
    simpa [dist_eq_norm] using (mem_ball.mp hx)
  have htri : ‖x - c‖ ≤ ‖x - z‖ + ‖z - c‖ := by
    simpa [dist_eq_norm] using (dist_triangle x z c)
  rw [Metric.mem_closedBall, dist_eq_norm]
  linarith

/-- **Strong maximum principle for a continuous function with a *local* circle
sub-mean-value inequality on an open ball.**  If `g` is continuous on
`closedBall c R`, satisfies the sub-mean-value inequality `g z ≤ Real.circleAverage g z r`
for every sufficiently small `r` (with threshold depending on `z`) at every
interior point `z`, and the maximum `M` over the closed ball is attained at an
interior point (`g p = M` with `‖p - c‖ < R`), then `g ≡ M` on the whole open
ball. -/
private lemma eqOn_openBall_of_isMaxOn_localSub {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hcont : ContinuousOn g (closedBall c R))
    (hloc : ∀ z : ℂ, ‖z - c‖ < R → ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ → g z ≤ Real.circleAverage g z r)
    {M : ℝ} (hM : ∀ z : ℂ, ‖z - c‖ ≤ R → g z ≤ M) {p : ℂ}
    (hpR : ‖p - c‖ < R) (hpM : g p = M) :
    ∀ z : ℂ, ‖z - c‖ < R → g z = M := by
  classical
  let S : Set ℂ := {z : ℂ | ‖z - c‖ < R ∧ g z = M}
  let A : Set ℂ := {z : ℂ | ‖z - c‖ < R}
  have hA_eq : A = ball c R := by
    ext z; simp [A, dist_eq_norm]
  have hA_open : IsOpen A := by rw [hA_eq]; exact isOpen_ball
  have hA_pre : IsPreconnected A := by rw [hA_eq]; exact isPreconnected_ball
  /- `S` is open: at each point `z ∈ S` the local sub-mean-value inequality on
     small circles centred at `z` forces `g ≡ M` on a neighbourhood of `z`. -/
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro z hz
    rcases hz with ⟨hzR, hvzM⟩
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hloc z hzR
    let δ : ℝ := min δ₀ ((R - ‖z - c‖) / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]; exact lt_min hδ₀pos (by nlinarith)
    have hδle₀ : δ ≤ δ₀ := min_le_left _ _
    have hδleR : δ ≤ (R - ‖z - c‖) / 2 := min_le_right _ _
    refine ⟨δ, hδpos, ?_⟩
    intro w hw
    have hwzδ : ‖w - z‖ < δ := by simpa [dist_eq_norm] using (mem_ball.mp hw)
    have hwR : ‖w - c‖ < R := by
      have htri : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        simpa [dist_eq_norm] using (dist_triangle w z c)
      nlinarith [hwzδ, hδleR, hzR]
    refine ⟨hwR, ?_⟩
    by_cases hwz : w = z
    · rw [hwz]; exact hvzM
    · let ρ : ℝ := ‖w - z‖
      have hρpos : 0 < ρ := by
        dsimp [ρ]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
      have hρδ : ρ < δ := by dsimp [ρ]; exact hwzδ
      have hρδ₀ : ρ < δ₀ := lt_of_lt_of_le hρδ hδle₀
      have hsphere_cl : sphere z |ρ| ⊆ closedBall c R := by
        intro x hx
        have hxz : ‖x - z‖ = |ρ| := mem_sphere_iff_norm.mp hx
        have hxρ : ‖x - z‖ = ρ := by rw [hxz, abs_of_nonneg hρpos.le]
        have hxc : ‖x - c‖ ≤ ‖x - z‖ + ‖z - c‖ := by
          simpa [dist_eq_norm] using (dist_triangle x z c)
        rw [Metric.mem_closedBall, dist_eq_norm]
        nlinarith [hxρ, hxc, hρδ, hδleR, hzR]
      have hcontSph : ContinuousOn g (sphere z |ρ|) := hcont.mono hsphere_cl
      have havg_le_M : Real.circleAverage g z ρ ≤ M :=
        Real.circleAverage_mono_on_of_le_circle (f := g) (a := M)
          (ContinuousOn.circleIntegrable' hcontSph)
          (fun x hx => hM x (by
            have := hsphere_cl hx
            rwa [Metric.mem_closedBall, dist_eq_norm] at this))
      have havg_ge_M : M ≤ Real.circleAverage g z ρ := by
        rw [← hvzM]
        exact hδ₀ ρ hρpos hρδ₀
      have havguM : Real.circleAverage g z ρ = M := le_antisymm havg_le_M havg_ge_M
      have hnonneg : ∀ x ∈ sphere z |ρ|, 0 ≤ (fun x : ℂ => M - g x) x := by
        intro x hx
        have hxcl : ‖x - c‖ ≤ R := by
          have := hsphere_cl hx
          rwa [Metric.mem_closedBall, dist_eq_norm] at this
        exact sub_nonneg.mpr (hM x hxcl)
      have hu_int : CircleIntegrable g z ρ := ContinuousOn.circleIntegrable' hcontSph
      have hconst_int : CircleIntegrable (fun _ : ℂ => M) z ρ := circleIntegrable_const M z ρ
      have havg_g : Real.circleAverage (fun x : ℂ => M - g x) z ρ = 0 := by
        calc Real.circleAverage (fun x : ℂ => M - g x) z ρ
            = Real.circleAverage (fun _ : ℂ => M) z ρ - Real.circleAverage g z ρ := by
                simpa using
                  (Real.circleAverage_fun_sub (f₁ := fun _ : ℂ => M) (f₂ := g)
                    hconst_int hu_int)
          _ = M - M := by rw [Real.circleAverage_const, havguM]
          _ = 0 := by ring
      have hg_zero : ∀ x ∈ sphere z |ρ|, (fun x : ℂ => M - g x) x = 0 :=
        eq_zero_on_sphere_of_circleAverage_eq_zero (f := fun x : ℂ => M - g x) (c := z)
          (R := ρ)
          (continuousOn_const.sub hcontSph)
          hnonneg
          havg_g
      have hwSph : w ∈ sphere z |ρ| := by
        rw [Metric.mem_sphere, dist_eq_norm]
        dsimp [ρ]
        rw [abs_of_nonneg (norm_nonneg (w - z))]
      have hMv : (fun x : ℂ => M - g x) w = 0 := hg_zero w hwSph
      have : M - g w = 0 := hMv
      linarith

  /- The complement `A \ S` is open: at points of `A` where `g < M`,
     continuity of `g` keeps the values below `M` on a neighbourhood. -/
  have hV_open : IsOpen (A \ S) := by
    rw [Metric.isOpen_iff]
    intro z hzV
    rcases hzV with ⟨hzA, hznotS⟩
    have hzR : ‖z - c‖ < R := by simpa [A] using hzA
    have hznotS' : ¬ (‖z - c‖ < R ∧ g z = M) := by simpa [S] using hznotS
    have hneq : g z ≠ M := by
      intro hzeq
      exact hznotS' ⟨hzR, hzeq⟩
    have hlt : g z < M := lt_of_le_of_ne (hM z (le_of_lt hzR)) hneq
    have hcontz : ContinuousAt g z := hcont.continuousAt (closedBall_mem_nhds_of_lt' hzR)
    have hevent : ∀ᶠ w in 𝓝 z, g w < M := by
      simpa using (ContinuousAt.eventually_lt hcontz continuousAt_const hlt)
    have hmemA : A ∈ 𝓝 z := hA_open.mem_nhds hzA
    rcases (Metric.mem_nhds_iff.mp hmemA) with ⟨ε₁, hε₁pos, hε₁⟩
    rcases (Metric.eventually_nhds_iff.mp hevent) with ⟨ε₂, hε₂pos, hε₂⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
    intro w hw
    have hw₁ : w ∈ ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hw
    have hw₂ : w ∈ ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hw
    have hwA : w ∈ A := hε₁ hw₁
    have hwlt : g w < M := hε₂ hw₂
    refine ⟨hwA, ?_⟩
    intro hwS
    have hwS' : ‖w - c‖ < R ∧ g w = M := by simpa [S] using hwS
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
  have hzS' : ‖z - c‖ < R ∧ g z = M := by simpa [S] using hzS
  exact hzS'.2

/-- **Maximum principle for continuous functions with a *local* circle
sub-mean-value inequality.**  If `g` is continuous on `closedBall c R`,
satisfies the sub-mean-value inequality `g z ≤ Real.circleAverage g z r` for
every sufficiently small `r` at every interior point `z`, and `g ≤ 0` on the
boundary sphere, then `g ≤ 0` on the whole closed ball. -/
private theorem max_principle_localSub {g : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn g (closedBall c R))
    (hloc : ∀ z : ℂ, ‖z - c‖ < R → ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ → g z ≤ Real.circleAverage g z r)
    (hbd : ∀ z : ℂ, ‖z - c‖ = R → g z ≤ 0) :
    ∀ z : ℂ, ‖z - c‖ ≤ R → g z ≤ 0 := by
  classical
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
  · have hpR : ‖p - c‖ < R := by
      have hple : ‖p - c‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hpB
      exact lt_of_le_of_ne hple (by
        intro heq
        have hbd_p : g p ≤ 0 := hbd p heq
        linarith)
    have hgM_openBall : ∀ z : ℂ, ‖z - c‖ < R → g z = M :=
      eqOn_openBall_of_isMaxOn_localSub hcont hloc hMmax hpR rfl
    let q : ℂ := c + (R : ℂ)
    have hq_cl : q ∈ closedBall c R := by
      rw [Metric.mem_closedBall]
      dsimp [q]
      rw [dist_eq_norm]
      have hnorm : ‖(c + (R : ℂ)) - c‖ = R := by
        rw [show (c + (R : ℂ)) - c = (R : ℂ) by ring]
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (le_of_lt hR)
      rw [hnorm]
    have hqR : ‖q - c‖ = R := by
      dsimp [q]
      rw [show (c + (R : ℂ)) - c = (R : ℂ) by ring]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (le_of_lt hR)
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
  · intro z hz
    exact le_trans (hMmax z hz) (le_of_not_gt hMpos)

theorem circleAverage_ge_of_localSubMeanValue {Ω : Set ℂ} (hΩopen : IsOpen Ω) {w : ℂ → ℝ}
    (hcont : ContinuousOn w Ω)
    (hloc : ∀ p ∈ Ω, ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ Ω ∧
      ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Metric.ball p ε →
        w p ≤ Real.circleAverage w p r) :
    ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      w p ≤ Real.circleAverage w p r := by
  /- Reduce to the comparison criterion for a ball and a harmonic majorant. -/
  have hcmp : ∀ (p : ℂ) (r : ℝ), 0 < r → Metric.closedBall p r ⊆ Ω → ∀ h : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd h (Metric.ball p r) → ContinuousOn h (Metric.closedBall p r) →
      (∀ z ∈ Metric.sphere p r, w z ≤ h z) → ∀ z ∈ Metric.ball p r, w z ≤ h z := by
    intro p r hr hball h hharm hhcont hle
    set g : ℂ → ℝ := fun z => w z - h z with hgdef
    have hgcont : ContinuousOn g (Metric.closedBall p r) := by
      have hw : ContinuousOn w (Metric.closedBall p r) := hcont.mono hball
      exact hw.sub hhcont
    have hloc_g : ∀ z : ℂ, ‖z - p‖ < r → ∃ δ : ℝ, 0 < δ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < δ → g z ≤ Real.circleAverage g z ρ := by
      intro z hzr
      have hzΩ : z ∈ Ω :=
        hball (by rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hzr)
      obtain ⟨ε, hεpos, hεsub, hεineq⟩ := hloc z hzΩ
      refine ⟨min ε ((r - ‖z - p‖) / 2), lt_min hεpos (by nlinarith), ?_⟩
      intro ρ hρpos hρlt
      have hρltε : ρ < ε := lt_of_lt_of_le hρlt (min_le_left _ _)
      have hρltR : ρ < (r - ‖z - p‖) / 2 := lt_of_lt_of_le hρlt (min_le_right _ _)
      have hclsubΩ : Metric.closedBall z ρ ⊆ Metric.ball z ε := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        rw [Metric.mem_ball, dist_eq_norm]
        linarith
      have hclsubΩ' : Metric.closedBall z ρ ⊆ Ω := hclsubΩ.trans hεsub
      have hwge : w z ≤ Real.circleAverage w z ρ := hεineq ρ hρpos hclsubΩ
      have hclsubBall : Metric.closedBall z ρ ⊆ Metric.ball p r := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : ‖x - p‖ ≤ ‖x - z‖ + ‖z - p‖ := by
          simpa [dist_eq_norm] using (dist_triangle x z p)
        nlinarith [hx, h1, hρltR, hzr]
      have hsph_cl : Metric.sphere z |ρ| ⊆ Metric.closedBall z ρ := by
        rw [abs_of_pos hρpos]
        exact Metric.sphere_subset_closedBall
      have hharm_cl : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall z |ρ|) := by
        rw [abs_of_pos hρpos]
        exact hharm.mono hclsubBall
      have hhavg : Real.circleAverage h z ρ = h z :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm_cl
      have hcontSph_w : ContinuousOn w (Metric.sphere z |ρ|) :=
        hcont.mono (fun x hx => hclsubΩ' (hsph_cl hx))
      have hcontSph_h : ContinuousOn h (Metric.sphere z |ρ|) :=
        (InnerProductSpace.HarmonicOnNhd.continuousOn hharm).mono
          (fun x hx => hclsubBall (hsph_cl hx))
      have hint_w : CircleIntegrable w z ρ := hcontSph_w.circleIntegrable'
      have hint_h : CircleIntegrable h z ρ := hcontSph_h.circleIntegrable'
      have hsplit : Real.circleAverage g z ρ
          = Real.circleAverage w z ρ - Real.circleAverage h z ρ := by
        simp only [hgdef]
        exact Real.circleAverage_fun_sub hint_w hint_h
      calc g z = w z - h z := rfl
        _ ≤ Real.circleAverage w z ρ - h z := by linarith
        _ = Real.circleAverage w z ρ - Real.circleAverage h z ρ := by rw [hhavg]
        _ = Real.circleAverage g z ρ := hsplit.symm
    have hbound : ∀ z : ℂ, ‖z - p‖ = r → g z ≤ 0 := by
      intro z hz
      have hzsph : z ∈ Metric.sphere p r := by
        rw [Metric.mem_sphere, dist_eq_norm]; exact hz
      have := hle z hzsph
      show w z - h z ≤ 0
      linarith
    have hmain := max_principle_localSub hr hgcont hloc_g hbound
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : w z - h z ≤ 0 := hmain z (le_of_lt hz)
    linarith
  intro p hp r hr hball
  exact circleAverage_ge_of_le_harmonic hΩopen hcont hcmp hr hball

end Commons.Analysis.Complex.Harmonic
