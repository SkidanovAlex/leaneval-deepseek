import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sweep_domination_aux
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.sweep_greenBarrier_dominates
import Submission.Lib.Unif2.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Lib.Unif2.ChartLogClamp
import Submission.Lib.Unif2.SweepMember

/-!
# The sweep of the clamped logarithmic barrier: non-emptiness and the logarithmic pole

This file supplies the two remaining conjuncts of `exists_posHarmonic_logPole_dominating` whose
domination conjunct is `Work.SimplyConnected.ABS.sweep_greenBarrier_dominates`:

* `sweepFamily_greenBarrier_nonempty` — the sweep family of the clamped logarithmic barrier is
  non-empty as soon as the extremal family contains a non-zero member (a member is obtained by
  capping `-log ‖g‖` at a constant outside a small ball around `x₀`; the construction is the one
  used inside the proof of `sweep_greenBarrier_dominates`);
* `exists_posHarmonic_logPole_dominating` — assembling, for `E := sweep (greenBarrier x₀ ρ) U`:
  positivity (`sweep_pos`), harmonicity (`sweep_harmonic`), the logarithmic pole and the domination.

The logarithmic pole: `H := E + log ‖ζ - ζ₀‖` is harmonic on a punctured chart ball and
`H ≥ log ρ` because `E ≥ greenBarrier`; Bôcher's theorem
(`Work.Potential.logCoefficient_of_pos_harmonic`) then writes `H` as `c log‖ζ-ζ₀‖ + h` with
`c ≥ 0`, and `H ≥ log ρ` forces `c ≤ 0`; hence `c = 0` and `H` is bounded near `x₀`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The sweep family of the clamped logarithmic barrier is non-empty** as soon as the extremal
family contains a non-zero member. -/
theorem sweepFamily_greenBarrier_nonempty {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    {f : X → ℂ} (hf : f ∈ Submission.extremalFamily x₀) (hne : ∃ x : X, f x ≠ 0) :
    (Submission.sweepFamily (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀})).Nonempty := by
  classical
  obtain ⟨x, hgx⟩ := hne
  set g : X → ℂ := f with hgdef
  have hg : g ∈ Submission.extremalFamily x₀ := by simpa [hgdef] using hf
  have hhol : Submission.HolomorphicOnX g Set.univ := hg.1
  have hb : ∀ z : X, ‖g z‖ ≤ 1 := hg.2.1
  have hg0 : g x₀ = 0 := hg.2.2
  have hgx' : g x ≠ 0 := by simpa [hgdef] using hgx
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let a : ℂ := c x₀
  let U : Set X := Set.univ \ {x₀}
  let G : X → ℝ := Submission.greenBarrier x₀ ρ
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hGzero : ∀ z : X, z ∉ c.source → G z = 0 := by
    intro z hz
    show Submission.greenBarrier x₀ ρ z = 0
    rw [Submission.greenBarrier_apply,
      Submission.chartLogClamp_of_not_mem (fun h => hz h.1)]
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
  exact ⟨v, ⟨⟨hvcont, hvsup_at⟩, hvdom⟩⟩

/-- **Perron's method for the logarithmic pole, in the form the extremal problem needs.**

If `f` is a non-zero member of the extremal family whose zero at `x₀` is *simple* (the shape in
which the maximiser `f` of the zero-fibre theorem enters, because `hpos` says exactly that), then
`E := sweep (greenBarrier x₀ ρ) (univ \ {x₀})` is positive, harmonic off `x₀`, has a *unit*
logarithmic pole at `x₀` and dominates the whole extremal family.

Both bounds of the logarithmic pole come for free here: `E ≥ greenBarrier` (the barrier is
dominated by every member of the sweep family) and `E ≤ -log‖f‖` (the domination
`sweep_greenBarrier_dominates` with `g = f`), and the simple zero of `f` at `x₀` turns the second
bound into `E + log‖ζ-ζ₀‖ ≤ O(1)`. -/
theorem exists_posHarmonic_logPole_dominating' {x₀ : X} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀) (hne : ∃ x : X, f x ≠ 0)
    (hsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (f ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) :
    ∃ E : X → ℝ,
      (∀ x : X, x ≠ x₀ → 0 < E x) ∧
      Submission.HarmonicOnX E (Set.univ \ {x₀}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E ∧
      (∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖g x‖ ≤ Real.exp (-(E x))) := by
  classical
  obtain ⟨ρ, hρ, hsub⟩ := Submission.exists_chartDisc_radius x₀
  have hUopen : IsOpen (Set.univ \ {x₀} : Set X) := Submission.isOpen_univ_diff_singleton x₀
  have hGsub : Submission.SubharmonicOnX (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) :=
    Submission.subharmonicOnX_greenBarrier hρ hsub
  have hneSF : (Submission.sweepFamily (Submission.greenBarrier x₀ ρ)
      (Set.univ \ {x₀})).Nonempty :=
    sweepFamily_greenBarrier_nonempty hρ hsub hf hne
  -- ## The logarithmic pole
  have hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀
      (Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀})) := by
    obtain ⟨H, hHana, hHne, hHeq⟩ := hsimple
    obtain ⟨ε, hεpos, hiso⟩ := exists_isolated_zero_chart hf.1 hf.2.2 hne
    have hHev : ∀ᶠ w in 𝓝 ((chartAt ℂ x₀) x₀),
        (f ∘ (chartAt ℂ x₀).symm) w = (w - (chartAt ℂ x₀) x₀) * H w := hHeq
    have hHaevent : ∀ᶠ w in 𝓝 ((chartAt ℂ x₀) x₀),
        ‖H ((chartAt ℂ x₀) x₀)‖ / 2 ≤ ‖H w‖ := by
      have hcont : ContinuousAt H ((chartAt ℂ x₀) x₀) := hHana.continuousAt
      have hmem : {u : ℂ | ‖H ((chartAt ℂ x₀) x₀)‖ / 2 < ‖u‖}
          ∈ 𝓝 (H ((chartAt ℂ x₀) x₀)) := by
        refine IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) ?_
        show ‖H ((chartAt ℂ x₀) x₀)‖ / 2 < ‖H ((chartAt ℂ x₀) x₀)‖
        exact half_lt_self (norm_pos_iff.mpr hHne)
      exact (hcont.eventually hmem).mono fun w hw => le_of_lt hw
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hHev.and hHaevent)
    set r : ℝ := min (min ε (ρ / 2)) δ with hrdef
    have hrpos : 0 < r := lt_min (lt_min hεpos (half_pos hρ)) hδpos
    have hrε : r ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
    have hrρ2 : r ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hrδ : r ≤ δ := min_le_right _ _
    have hrρ : r < ρ := lt_of_le_of_lt hrρ2 (half_lt_self hρ)
    refine ⟨|Real.log ρ| + |Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)| + 1,
      Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) r,
      Submission.chartBall_greenBarrier_mem_nhds hrpos, ?_⟩
    intro x hxV hxΩ hxne
    obtain ⟨hxsrc, hxball⟩ := hxV
    have hxdist : dist ((chartAt ℂ x₀) x) ((chartAt ℂ x₀) x₀) < r :=
      Metric.mem_ball.mp hxball
    have hxne' : x ≠ x₀ := hxΩ.2
    have hxU : x ∈ (Set.univ \ {x₀} : Set X) := ⟨mem_univ x, hxne'⟩
    have hcne : (chartAt ℂ x₀) x ≠ (chartAt ℂ x₀) x₀ := by
      intro h
      exact hxne' ((chartAt ℂ x₀).injOn hxsrc (mem_chart_source ℂ x₀) h)
    have hdltρ : ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ < ρ := by
      have h := lt_trans hxdist hrρ
      rwa [dist_eq_norm] at h
    have hdltε : ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ < ε := by
      have h := lt_of_lt_of_le hxdist hrε
      rwa [dist_eq_norm] at h
    -- ## Lower bound: the barrier
    have hclampmem : x ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ := by
      refine ⟨hxsrc, ?_⟩
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
      exact hdltρ
    have hgbval : Submission.greenBarrier x₀ ρ x
        = Real.log (ρ / ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖) := by
      rw [Submission.greenBarrier_apply, Submission.chartLogClamp_of_mem hclampmem]
    have hble : Submission.greenBarrier x₀ ρ x
        ≤ Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x :=
      Submission.barrier_le_sweep hneSF hxU
    have hlower : Real.log ρ
        ≤ Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x
          + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ := by
      have hpos : 0 < ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hcne)
      have h1 : Real.log (ρ / ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖)
          = Real.log ρ - Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ :=
        Real.log_div (ne_of_gt hρ) (ne_of_gt hpos)
      have h2 : Real.log (ρ / ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖)
          ≤ Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x := by
        rw [← hgbval]; exact hble
      linarith
    -- ## Upper bound: the domination with `g = f`
    have hfxne : f x ≠ 0 := by
      intro h0
      exact hxne' (hiso x hxsrc hdltε h0)
    have hdomx : ‖f x‖ ≤ Real.exp
        (-(Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x)) :=
      sweep_greenBarrier_dominates hρ hsub f hf x hxne'
    have hlogdom : Real.log ‖f x‖
        ≤ -(Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x) := by
      have h := Real.log_le_log (norm_pos_iff.mpr hfxne) hdomx
      rwa [Real.log_exp] at h
    have hδx := hδ (lt_of_lt_of_le hxdist hrδ)
    have hfac : f x = ((chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀) * H ((chartAt ℂ x₀) x) := by
      have h1 : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x) = f x := by
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x₀).left_inv hxsrc]
      rw [← h1]
      exact hδx.1
    have hHge : ‖H ((chartAt ℂ x₀) x₀)‖ / 2 ≤ ‖H ((chartAt ℂ x₀) x)‖ := hδx.2
    have hfxnorm : ‖f x‖
        = ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ * ‖H ((chartAt ℂ x₀) x)‖ := by
      rw [hfac, norm_mul]
    have hcxpos : 0 < ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hcne)
    have hHpos : 0 < ‖H ((chartAt ℂ x₀) x)‖ :=
      lt_of_lt_of_le (half_pos (norm_pos_iff.mpr hHne)) hHge
    have hlogfx : Real.log ‖f x‖
        = Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖
          + Real.log ‖H ((chartAt ℂ x₀) x)‖ := by
      rw [hfxnorm, Real.log_mul (ne_of_gt hcxpos) (ne_of_gt hHpos)]
    have hHlow : Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)
        ≤ Real.log ‖H ((chartAt ℂ x₀) x)‖ :=
      Real.log_le_log (half_pos (norm_pos_iff.mpr hHne)) hHge
    have hupper : Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x
        + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖
        ≤ -Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2) := by
      have hlogdom' : Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖
          + Real.log ‖H ((chartAt ℂ x₀) x)‖
          ≤ -(Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}) x) := by
        rw [← hlogfx]; exact hlogdom
      linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le (Real.log ρ),
        abs_nonneg (Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)), (zero_le_one : (0:ℝ) ≤ 1)]
    · linarith [neg_le_abs (Real.log (‖H ((chartAt ℂ x₀) x₀)‖ / 2)),
        abs_nonneg (Real.log ρ), (zero_le_one : (0:ℝ) ≤ 1)]
  refine ⟨Submission.sweep (Submission.greenBarrier x₀ ρ) (Set.univ \ {x₀}), ?_, ?_, hpole, ?_⟩
  · intro x hx
    exact Submission.sweep_greenBarrier_pos hρ hsub hneSF x ⟨mem_univ x, hx⟩
  · exact Submission.sweep_harmonic hUopen hGsub hneSF
  · intro g hg x hx
    exact sweep_greenBarrier_dominates hρ hsub g hg x hx

end Work.SimplyConnected.ABS
