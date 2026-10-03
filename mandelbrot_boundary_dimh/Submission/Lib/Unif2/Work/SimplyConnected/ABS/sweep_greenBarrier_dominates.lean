import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sweep_domination_aux

/-!
# The sweep of the Green barrier dominates the extremal family

`Work.SimplyConnected.ABS.sweep_greenBarrier_dominates` states that every member `g` of the
extremal family at `x₀` (holomorphic on `X`, `‖g‖ ≤ 1`, `g x₀ = 0`) is dominated by the
exponential of the negative sweep of the clamped logarithmic barrier
`Submission.greenBarrier x₀ ρ` on `univ \ {x₀}`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

theorem sweep_greenBarrier_dominates {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target) :
    ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ →
      ‖g x‖ ≤ Real.exp
        (-(Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x)) := by
  intro g hg x hxne
  classical
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let a : ℂ := c x₀
  let U : Set X := Set.univ \ {x₀}
  let G : X → ℝ := Submission.greenBarrier x₀ ρ
  have hhol : Submission.HolomorphicOnX g Set.univ := hg.1
  have hb : ∀ z : X, ‖g z‖ ≤ 1 := hg.2.1
  have hg0 : g x₀ = 0 := hg.2.2
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hxU : x ∈ U := ⟨mem_univ x, hxne⟩
  have hGzero : ∀ z : X, z ∉ c.source → G z = 0 := by
    intro z hz
    show Submission.greenBarrier x₀ ρ z = 0
    rw [Submission.greenBarrier_apply,
      Submission.chartLogClamp_of_not_mem (fun h => hz h.1)]
  by_cases hgx : g x = 0
  · rw [hgx, norm_zero]
    exact (Real.exp_pos _).le
  by_cases hfam : (Submission.sweepFamily G U).Nonempty
  · -- the main case: exhibit a member of the sweep family
    obtain ⟨ε, hεpos, hiso⟩ := exists_isolated_zero_chart hhol hg0 ⟨x, hgx⟩
    let ν : ℝ := min ε ρ / 2
    have hνpos : 0 < ν := by
      show 0 < min ε ρ / 2
      positivity
    have hνltε : ν < ε := by
      have h1 : min ε ρ ≤ ε := min_le_left _ _
      show min ε ρ / 2 < ε
      linarith
    have hνltρ : ν < ρ := by
      have h1 : min ε ρ ≤ ρ := min_le_right _ _
      show min ε ρ / 2 < ρ
      linarith
    have hν2pos : 0 < ν / 2 := by linarith
    have hν4pos : 0 < ν / 4 := by linarith
    -- the compact annulus and the constant `K`
    let Ann : Set ℂ := Metric.closedBall a ν \ Metric.ball a (ν / 4)
    let A : Set X := c.symm '' Ann
    have htgtν : Metric.closedBall a ν ⊆ c.target := by
      show Metric.closedBall ((chartAt ℂ x₀) x₀) ν ⊆ (chartAt ℂ x₀).target
      exact (Metric.closedBall_subset_closedBall (le_of_lt hνltρ)).trans hsub
    have hclsub : closure (Submission.chartBall c a (ν / 2)) ⊆ c.source := by
      refine ((Submission.closure_chartBall_subset (c := c) (a := a) (ρ := ν / 2) ?_).trans ?_)
      · show Metric.closedBall a (ν / 2) ⊆ c.target
        exact (Metric.closedBall_subset_closedBall (by linarith)).trans htgtν
      · rintro z ⟨w, hw, rfl⟩
        exact c.map_target (htgtν (Metric.closedBall_subset_closedBall (by linarith) hw))
    have hAne : A.Nonempty := by
      refine ⟨c.symm (a + ((ν / 2 : ℝ) : ℂ)), ?_⟩
      refine ⟨a + ((ν / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, rfl⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hν2pos]
        linarith
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hν2pos]
        linarith
    have hAcpt : IsCompact A := by
      refine IsCompact.image_of_continuousOn ?_ ?_
      · exact (isCompact_closedBall a ν).diff Metric.isOpen_ball
      · exact c.continuousOn_symm.mono (fun w hw => htgtν hw.1)
    have hAzf : ∀ z ∈ A, g z ≠ 0 := by
      intro z hz hgz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwt : w ∈ c.target := htgtν hw.1
      have hwsrc : c.symm w ∈ c.source := c.map_target hwt
      have hdist : ‖w - a‖ < ε := by
        have h1 : ‖w - a‖ ≤ ν := by
          have h2 := Metric.mem_closedBall.mp hw.1
          rwa [dist_eq_norm] at h2
        linarith
      have hdist' : ‖(chartAt ℂ x₀) (c.symm w) - (chartAt ℂ x₀) x₀‖ < ε := by
        have h1 : (chartAt ℂ x₀) (c.symm w) = w := c.right_inv hwt
        have h2 : (chartAt ℂ x₀) x₀ = a := rfl
        rw [h1, h2]
        exact hdist
      have hwx : c.symm w = x₀ := hiso (c.symm w) hwsrc hdist' hgz
      have hwa : w = a := by
        rw [← c.right_inv hwt, hwx]
      exact hw.2 (hwa.symm ▸ Metric.mem_ball_self hν4pos)
    have hAcont : ContinuousOn (fun z : X => -Real.log ‖g z‖) A := by
      intro z hz
      exact ((Submission.harmonicOnXAt_neg_log_norm (hhol z (mem_univ z))
        (hAzf z hz)).continuousAt).continuousWithinAt
    obtain ⟨p₀, hp₀A, hp₀max⟩ := hAcpt.exists_isMaxOn hAne hAcont
    let K : ℝ := -Real.log ‖g p₀‖
    have hKnn : 0 ≤ K := by
      show 0 ≤ -Real.log ‖g p₀‖
      exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb p₀))
    have hKann : ∀ z ∈ c.source, ν / 4 ≤ ‖c z - a‖ → ‖c z - a‖ ≤ ν →
        -Real.log ‖g z‖ ≤ K := by
      intro z hzsrc h1 h2
      have hzA : z ∈ A := by
        refine ⟨c z, ⟨?_, ?_⟩, c.left_inv hzsrc⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]; exact h2
        · rw [Metric.mem_ball, dist_eq_norm]; exact not_lt.mpr h1
      exact hp₀max hzA
    -- the value of `K` at the radius `ν/2`
    have hKlog : Real.log (ρ / (ν / 2)) ≤ K := by
      have hwt : a + ((ν / 2 : ℝ) : ℂ) ∈ c.target :=
        htgtν (by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hν2pos]
          linarith)
      have hwsrc : c.symm (a + ((ν / 2 : ℝ) : ℂ)) ∈ c.source := c.map_target hwt
      have hcw : c (c.symm (a + ((ν / 2 : ℝ) : ℂ))) = a + ((ν / 2 : ℝ) : ℂ) :=
        c.right_inv hwt
      have hzA : c.symm (a + ((ν / 2 : ℝ) : ℂ)) ∈ A := by
        refine ⟨a + ((ν / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, rfl⟩
        · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hν2pos]
          linarith
        · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hν2pos]
          linarith
      have hle : -Real.log ‖g (c.symm (a + ((ν / 2 : ℝ) : ℂ)))‖ ≤ K := hp₀max hzA
      have hcdist : ‖c (c.symm (a + ((ν / 2 : ℝ) : ℂ))) - a‖ = ν / 2 := by
        rw [hcw, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν2pos]
      have hsch := norm_le_chartDist_div_of_mem_extremalFamily (x₀ := x₀) (ρ := ρ) hρ hsub hg
        hwsrc (by rw [hcdist]; linarith)
      rw [hcdist] at hsch
      have hgz : g (c.symm (a + ((ν / 2 : ℝ) : ℂ))) ≠ 0 := hAzf _ hzA
      have h1 : Real.log ‖g (c.symm (a + ((ν / 2 : ℝ) : ℂ)))‖ ≤ Real.log ((ν / 2) / ρ) :=
        Real.log_le_log (norm_pos_iff.mpr hgz) hsch
      have h2 : Real.log (ρ / (ν / 2)) = -Real.log ((ν / 2) / ρ) := by
        rw [Real.log_div (ne_of_gt hρ) (by linarith : ν / 2 ≠ 0),
          Real.log_div (by linarith : ν / 2 ≠ 0) (ne_of_gt hρ)]
        ring
      rw [h2]
      linarith
    -- the two domination lemmas
    have hIzf : ∀ z ∈ Submission.chartBall c a (ν / 2), z ≠ x₀ → g z ≠ 0 := by
      intro z hzI hzx hz0
      have hdist : ‖c z - a‖ < ε := by
        have h1 : c z ∈ Metric.ball a (ν / 2) := hzI.2
        rw [Metric.mem_ball, dist_eq_norm] at h1
        linarith
      exact hzx (hiso z hzI.1 hdist hz0)
    have hGle_f : ∀ z ∈ c.source, g z ≠ 0 → G z ≤ -Real.log ‖g z‖ := by
      intro z hzsrc hgz
      by_cases hzρ : ‖c z - a‖ < ρ
      · have hzmem : z ∈ Submission.chartBall c a ρ :=
          ⟨hzsrc, by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hzρ⟩
        have hzne : c z ≠ a := by
          intro h
          have hzx : z = x₀ := c.injOn hzsrc hsrc h
          exact hgz (by rw [hzx]; exact hg0)
        have hczpos : 0 < ‖c z - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
        have hsch := norm_le_chartDist_div_of_mem_extremalFamily (x₀ := x₀) (ρ := ρ) hρ hsub hg
          hzsrc hzρ
        have h1 : Real.log ‖g z‖ ≤ Real.log (‖c z - a‖ / ρ) :=
          Real.log_le_log (norm_pos_iff.mpr hgz) hsch
        have h2 : Real.log (ρ / ‖c z - a‖) = -Real.log (‖c z - a‖ / ρ) := by
          rw [Real.log_div (ne_of_gt hρ) (ne_of_gt hczpos),
            Real.log_div (ne_of_gt hczpos) (ne_of_gt hρ)]
          ring
        have h3 : G z = Real.log (ρ / ‖c z - a‖) := by
          show Submission.greenBarrier x₀ ρ z = Real.log (ρ / ‖c z - a‖)
          rw [Submission.greenBarrier_apply, Submission.chartLogClamp_of_mem hzmem]
        rw [h3, h2]
        linarith
      · have h3 : G z = 0 := by
          show Submission.greenBarrier x₀ ρ z = 0
          rw [Submission.greenBarrier_apply,
            Submission.chartLogClamp_of_not_mem (fun h => hzρ (by
              have h1 : c z ∈ Metric.ball a ρ := h.2
              rwa [Metric.mem_ball, dist_eq_norm] at h1))]
        rw [h3]
        exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb z))
    have hGle_K : ∀ z ∈ c.source, ν / 2 ≤ ‖c z - a‖ → G z ≤ K := by
      intro z hzsrc hzge
      by_cases hzρ : ‖c z - a‖ < ρ
      · have hzmem : z ∈ Submission.chartBall c a ρ :=
          ⟨hzsrc, by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hzρ⟩
        have h3 : G z = Real.log (ρ / ‖c z - a‖) := by
          show Submission.greenBarrier x₀ ρ z = Real.log (ρ / ‖c z - a‖)
          rw [Submission.greenBarrier_apply, Submission.chartLogClamp_of_mem hzmem]
        rw [h3]
        have h4 : Real.log (ρ / ‖c z - a‖) ≤ Real.log (ρ / (ν / 2)) :=
          Real.log_le_log (div_pos hρ (by linarith))
            (div_le_div_of_nonneg_left hρ.le (by linarith) hzge)
        linarith
      · have h3 : G z = 0 := by
          show Submission.greenBarrier x₀ ρ z = 0
          rw [Submission.greenBarrier_apply,
            Submission.chartLogClamp_of_not_mem (fun h => hzρ (by
              have h1 : c z ∈ Metric.ball a ρ := h.2
              rwa [Metric.mem_ball, dist_eq_norm] at h1))]
        rw [h3]
        exact hKnn
    -- the candidate member of the sweep family
    let W : X → ℝ := clampedLogNorm g K
    have hWsup : Submission.SuperharmonicOnX W Set.univ := superharmonicOnX_clampedLogNorm hhol K
    let v : X → ℝ :=
      fun z => if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z
    have hveqf : ∀ p : X, p ∈ Submission.chartBall c a (ν / 2) →
        (fun z : X => -Real.log ‖g z‖) =ᶠ[nhds p] v := by
      intro p hpI
      filter_upwards [(Submission.chartBall_isOpen c a (ν / 2)).mem_nhds hpI] with z hz
      show -Real.log ‖g z‖ =
        (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
      rw [if_pos hz]
    have hveqW : ∀ p : X, p ∉ Submission.chartBall c a (ν / 2) → W =ᶠ[nhds p] v := by
      intro p hpI
      by_cases hpsrc : p ∈ c.source
      · have hpge : ν / 2 ≤ ‖c p - a‖ := by
          by_contra h
          exact hpI ⟨hpsrc, by
            show c p ∈ Metric.ball a (ν / 2)
            rw [Metric.mem_ball, dist_eq_norm]
            exact lt_of_not_ge h⟩
        have hN : {z : X | z ∈ c.source ∧ ν / 4 < ‖c z - a‖} ∈ nhds p := by
          refine inter_mem (c.open_source.mem_nhds hpsrc) ?_
          have hcont : ContinuousAt (fun z : X => ‖c z - a‖) p :=
            ((c.continuousAt hpsrc).sub continuousAt_const).norm
          have hlt : ν / 4 < ‖c p - a‖ := by linarith
          exact hcont.eventually (isOpen_Ioi.mem_nhds hlt)
        filter_upwards [hN] with z hz
        obtain ⟨hzsrc, hzgt⟩ := hz
        by_cases hzI : z ∈ Submission.chartBall c a (ν / 2)
        · have hzlt : ‖c z - a‖ < ν / 2 := by
            have h1 : c z ∈ Metric.ball a (ν / 2) := hzI.2
            rwa [Metric.mem_ball, dist_eq_norm] at h1
          have hzK : -Real.log ‖g z‖ ≤ K := hKann z hzsrc (le_of_lt hzgt) (by linarith)
          have hgz : g z ≠ 0 := hIzf z hzI (by
            intro hzx
            rw [hzx] at hzgt
            have h0 : ‖c x₀ - a‖ = 0 := by
              rw [show c x₀ - a = 0 from sub_self (c x₀), norm_zero]
            rw [h0] at hzgt
            linarith)
          show W z = (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
          rw [if_pos hzI]
          exact clampedLogNorm_of_le hgz hzK
        · show W z = (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
          rw [if_neg hzI]
      · have hpcl : p ∉ closure (Submission.chartBall c a (ν / 2)) := fun h => hpsrc (hclsub h)
        have hN : (closure (Submission.chartBall c a (ν / 2)))ᶜ ∈ nhds p :=
          isClosed_closure.isOpen_compl.mem_nhds hpcl
        filter_upwards [hN] with z hz
        have hzI : z ∉ Submission.chartBall c a (ν / 2) := fun h => hz (subset_closure h)
        show W z = (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
        rw [if_neg hzI]
    have hvcont : ContinuousOn v U := by
      refine continuousOn_of_forall_continuousAt (fun p hp => ?_)
      have hpx : p ≠ x₀ := hp.2
      by_cases hpI : p ∈ Submission.chartBall c a (ν / 2)
      · have hfc : ContinuousAt (fun z : X => -Real.log ‖g z‖) p :=
          (Submission.harmonicOnXAt_neg_log_norm (hhol p (mem_univ p))
            (hIzf p hpI hpx)).continuousAt
        exact hfc.congr (hveqf p hpI)
      · exact ((hWsup.2 p (mem_univ p)).continuousAt).congr (hveqW p hpI)
    have hvsup_at : ∀ p ∈ U, Submission.SuperharmonicOnXAt v p := by
      intro p hp
      have hpx : p ≠ x₀ := hp.2
      by_cases hpI : p ∈ Submission.chartBall c a (ν / 2)
      · have hharm : Submission.HarmonicOnXAt (fun z : X => -Real.log ‖g z‖) p :=
          Submission.harmonicOnXAt_neg_log_norm (hhol p (mem_univ p)) (hIzf p hpI hpx)
        exact Submission.SuperharmonicOnXAt.congr hharm.superharmonic (hveqf p hpI)
      · exact Submission.SuperharmonicOnXAt.congr (hWsup.2 p (mem_univ p)) (hveqW p hpI)
    have hvdom : ∀ z ∈ U, G z ≤ v z := by
      intro z hzU
      have hzx : z ≠ x₀ := hzU.2
      by_cases hzI : z ∈ Submission.chartBall c a (ν / 2)
      · show G z ≤ (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
        rw [if_pos hzI]
        exact hGle_f z hzI.1 (hIzf z hzI hzx)
      · show G z ≤ (if z ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g z‖ else W z)
        rw [if_neg hzI]
        by_cases hgz : g z = 0
        · rw [show W z = K from clampedLogNorm_of_eq_zero hgz]
          by_cases hzsrc : z ∈ c.source
          · have hcge : ε ≤ ‖c z - a‖ := by
              by_contra h
              exact hzx (hiso z hzsrc (lt_of_not_ge h) hgz)
            exact hGle_K z hzsrc (by linarith)
          · rw [hGzero z hzsrc]
            exact hKnn
        · rw [show W z = min (-Real.log ‖g z‖) K from clampedLogNorm_eq_min hgz]
          refine le_min ?_ ?_
          · by_cases hzsrc : z ∈ c.source
            · exact hGle_f z hzsrc hgz
            · rw [hGzero z hzsrc]
              exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb z))
          · by_cases hzsrc : z ∈ c.source
            · have hzge : ν / 2 ≤ ‖c z - a‖ := by
                by_contra h
                exact hzI ⟨hzsrc, by
                  show c z ∈ Metric.ball a (ν / 2)
                  rw [Metric.mem_ball, dist_eq_norm]
                  exact lt_of_not_ge h⟩
              exact hGle_K z hzsrc hzge
            · rw [hGzero z hzsrc]
              exact hKnn
    have hmem : v ∈ Submission.sweepFamily G U := ⟨⟨hvcont, hvsup_at⟩, hvdom⟩
    have hsweep_le : Submission.sweep G U x ≤ v x := Submission.sweep_le_of_mem hmem hxU
    have hvx_le : v x ≤ -Real.log ‖g x‖ := by
      by_cases hxI : x ∈ Submission.chartBall c a (ν / 2)
      · show (if x ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g x‖ else W x)
            ≤ -Real.log ‖g x‖
        rw [if_pos hxI]
      · show (if x ∈ Submission.chartBall c a (ν / 2) then -Real.log ‖g x‖ else W x)
            ≤ -Real.log ‖g x‖
        rw [if_neg hxI]
        exact clampedLogNorm_le_neg_log hgx
    have hlog : Real.log ‖g x‖ ≤ -Submission.sweep G U x := by linarith
    calc ‖g x‖ = Real.exp (Real.log ‖g x‖) := (Real.exp_log (norm_pos_iff.mpr hgx)).symm
      _ ≤ Real.exp (-(Submission.sweep G U x)) := Real.exp_le_exp.mpr hlog
  · -- the sweep family is empty: the sweep vanishes
    have hsweep : Submission.sweep G U x = 0 := by
      have hempty : Submission.sweepFamily G U = ∅ := not_nonempty_iff_eq_empty.mp hfam
      simp [Submission.sweep, Submission.lowerEnvelope, hempty]
    rw [hsweep, neg_zero, Real.exp_zero]
    exact hb x

end Work.SimplyConnected.ABS
