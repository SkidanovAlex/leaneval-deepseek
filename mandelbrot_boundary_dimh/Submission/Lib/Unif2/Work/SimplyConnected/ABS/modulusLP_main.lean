
import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulusLP_branch
import Submission.Lib.Unif2.Work.Modulus.growth_of_unitGreen
import Submission.Lib.Unif2.Work.Modulus.hasTrivialModulusMonodromy_of_periods
import Submission.Lib.Unif2.Work.Modulus.exists_holomorphic_modulus_of_branchOnPunctured
import Submission.Lib.Unif2.Work.Modulus.Main

/-!
# The holomorphic modulus of a logarithmic pole, without decay

Final assembly of the decay-free port of `Work.Modulus`: a function `E` that is harmonic off `z₀`
and has a unit logarithmic pole there has a holomorphic modulus
`Φ = exp (-(E + iE*))` as soon as all periods of the conjugate are multiples of `2π`.  The
conclusion is the `hmod` input of
`Work.SimplyConnected.ABS.extremal_maximizer_zero_fiber_of_inputs'`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Set
open Classical

namespace Work.ModulusLP

open Work.Modulus Work.Modulus.BranchCovering Work.Modulus.BranchCovering.Aux

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The global holomorphic modulus from a branch on the punctured surface** (decay-free form):
a nowhere vanishing holomorphic `Φ` on `X ∖ {z₀}` with modulus `exp (-E)` extends across the pole
(the limit is `0`, since `E → +∞`). -/
theorem exists_holomorphic_modulus_of_branchOnPunctured {z₀ : X} {E : X → ℝ}
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    {Φ : puncturedOpens z₀ → ℂ} (hhol : Submission.HolomorphicOnX Φ Set.univ)
    (hne : ∀ u : puncturedOpens z₀, Φ u ≠ 0)
    (hmod : ∀ u : puncturedOpens z₀, ‖Φ u‖ = Real.exp (-(E u.1))) :
    ∃ Ψ : X → ℂ, Submission.HolomorphicOnX Ψ Set.univ ∧
      (∀ x, x ≠ z₀ → Ψ x ≠ 0) ∧ (∀ x, x ≠ z₀ → ‖Ψ x‖ = Real.exp (-(E x))) := by
  classical
  let Ψ : X → ℂ := fun x => if h : x = z₀ then 0 else Φ ⟨x, h⟩
  have hΨeq : ∀ x (hx : x ≠ z₀), Ψ x = Φ ⟨x, hx⟩ := fun x hx => dif_neg hx
  have hΨ₀ : Ψ z₀ = 0 := dif_pos rfl
  have hΨnorm : ∀ x, x ≠ z₀ → ‖Ψ x‖ = Real.exp (-(E x)) := by
    intro x hx
    rw [hΨeq x hx]
    exact hmod ⟨x, hx⟩
  have hΨne : ∀ x, x ≠ z₀ → Ψ x ≠ 0 := by
    intro x hx
    rw [hΨeq x hx]
    exact hne ⟨x, hx⟩
  have hoff : ∀ x, x ≠ z₀ → Submission.HolomorphicOnXAt Ψ x :=
    fun x hx => holomorphicOnXAt_of_punctured hΨeq hx (hhol ⟨x, hx⟩ (mem_univ _))
  have hΨtend : Tendsto Ψ (𝓝[≠] z₀) (𝓝 0) := by
    have hEtop : Tendsto E (𝓝[≠] z₀) atTop := by
      rw [Filter.tendsto_atTop]
      intro A
      obtain ⟨C₀, V₀, hV₀, hbnd₀⟩ := hpole
      obtain ⟨V, hV, hVE⟩ := growth_of_unitGreen hV₀
        (fun x hx hxne => hbnd₀ x hx ⟨mem_univ x, hxne⟩ hxne) A
      filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with x hxV hxne
      exact (hVE x hxV hxne).le
    have hexp : Tendsto (fun x => Real.exp (-(E x))) (𝓝[≠] z₀) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hEtop
    refine squeeze_zero_norm' (a := fun x => Real.exp (-(E x))) ?_ hexp
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hΨnorm x hx).le
  have hzero : Submission.HolomorphicOnXAt Ψ z₀ := by
    change AnalyticAt ℂ (Ψ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀)
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((chartAt ℂ z₀).open_target.mem_nhds
          ((chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀)))] with w hw hwt
      have hxsrc : (chartAt ℂ z₀).symm w ∈ (chartAt ℂ z₀).source :=
        (chartAt ℂ z₀).map_target hwt
      have hxne : (chartAt ℂ z₀).symm w ≠ z₀ := by
        have hw' : w ≠ (chartAt ℂ z₀) z₀ := hw
        intro hcon
        exact hw' (by rw [← (chartAt ℂ z₀).right_inv hwt, hcon])
      have h := (Submission.HolomorphicOnXAt_iff_chart (f := Ψ) (x := (chartAt ℂ z₀).symm w)
        (y := z₀) hxsrc).mp (hoff _ hxne)
      rw [(chartAt ℂ z₀).right_inv hwt] at h
      exact h.differentiableAt
    · have hsymm : Tendsto (chartAt ℂ z₀).symm (𝓝[≠] ((chartAt ℂ z₀) z₀)) (𝓝[≠] z₀) :=
        tendsto_chartAt_symm_nhdsWithin z₀
      have hga : Ψ ((chartAt ℂ z₀).symm ((chartAt ℂ z₀) z₀)) = 0 := by
        rw [(chartAt ℂ z₀).left_inv (mem_chart_source ℂ z₀)]
        exact hΨ₀
      rw [continuousAt_iff_punctured_nhds]
      simpa only [Function.comp_apply, hga] using hΨtend.comp hsymm
  refine ⟨Ψ, ?_, hΨne, hΨnorm⟩
  intro x _
  by_cases hx : x = z₀
  · rw [hx]; exact hzero
  · exact hoff x hx

/-- **Trivial monodromy of the modulus from the period condition** (decay-free form). -/
theorem hasTrivialModulusMonodromy_of_periods {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hper : ∀ (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀),
      ∃ k : ℤ, greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi)) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ (∀ x, x ≠ z₀ → Φ x ≠ 0) ∧
      (∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) := by
  by_cases hsingle : ∀ x : X, x = z₀
  · exact ⟨fun _ => 0, Submission.holomorphicOnX_const 0, fun x hx => absurd (hsingle x) hx,
      fun x hx => absurd (hsingle x) hx⟩
  · simp only [not_forall] at hsingle
    obtain ⟨x₀, hx₀⟩ := hsingle
    haveI hXlpc : LocallyPathConnectedSpace X :=
      ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
    haveI hUconn : ConnectedSpace (puncturedOpens z₀) := puncturedConnected z₀
    haveI hUlpc : LocallyPathConnectedSpace (puncturedOpens z₀) :=
      (isOpen_punctured z₀).locallyPathConnectedSpace
    haveI hUpc : PathConnectedSpace (puncturedOpens z₀) :=
      PathConnectedSpace.of_locallyPathConnectedSpace
    letI htop : TopologicalSpace ((puncturedOpens z₀) × ℝ) := greenConjTopology z₀ E
    set cov : IsCoveringMap (Prod.fst : (puncturedOpens z₀) × ℝ → (puncturedOpens z₀)) :=
      green_isCoveringMap hEharm with hcovdef
    have hσ : ∀ c : ℝ, Continuous (Submission.conjShift (X := puncturedOpens z₀) c) :=
      fun c => green_continuous_conjShift (z₀ := z₀) (E := E) c
    set u₀ : puncturedOpens z₀ := ⟨x₀, hx₀⟩ with hu₀def
    set e₀ : ↥(Submission.conjFiber u₀) := Submission.conjFiberPt u₀ 0 with he₀def
    have hper' : ∀ δ : FundamentalGroup (puncturedOpens z₀) u₀,
        ∃ k : ℤ, Submission.conjPeriod u₀ e₀ cov δ = k * (2 * Real.pi) := by
      intro δ
      obtain ⟨k, hk⟩ := hper u₀ δ
      refine ⟨k, ?_⟩
      rw [he₀def, hcovdef]
      exact (greenPeriodHom_apply hEharm u₀ δ).symm.trans hk
    have pathTo : (u : puncturedOpens z₀) → Path u₀ u := fun u => PathConnectedSpace.somePath u₀ u
    set Φ : puncturedOpens z₀ → ℂ :=
      fun u => greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).1)
      with hΦdef
    have hΦval : ∀ u : puncturedOpens z₀,
        Φ u = greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).1) :=
      fun u => rfl
    have hcons : ∀ (u : puncturedOpens z₀) (γ γ' : Path u₀ u),
        greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk γ') e₀).1)
          = greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk γ) e₀).1) :=
      fun u γ γ' => greenPhi_monodromy_eq cov hσ e₀ hper' γ γ'
    have hmod : ∀ u : puncturedOpens z₀, ‖Φ u‖ = Real.exp (-(E u.1)) := by
      intro u
      have hx : E (((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).1).1).1 = E u.1 :=
        congrArg (fun v : puncturedOpens z₀ => E v.1)
          ((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).2)
      rw [hΦval u, norm_greenPhi, hx]
    have hne : ∀ u : puncturedOpens z₀, Φ u ≠ 0 := by
      intro u
      rw [hΦval u]
      exact greenPhi_ne_zero _
    have hhol : Submission.HolomorphicOnX Φ Set.univ := by
      intro u₁ _
      set c := chartAt ℂ u₁ with hcdef
      set a : ℂ := c u₁ with hadef
      have hsrc : u₁ ∈ c.source := mem_chart_source ℂ u₁
      have haTgt : a ∈ c.target := c.map_source hsrc
      have hharmAt : InnerProductSpace.HarmonicAt ((greenPunctured z₀ E) ∘ c.symm) a :=
        greenPunctured_harmonic hEharm u₁ (mem_univ u₁)
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.mp
        ((InnerProductSpace.isOpen_setOfPred_harmonicAt
          ((greenPunctured z₀ E) ∘ c.symm)).mem_nhds hharmAt)
      obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds haTgt)
      have hρ : 0 < min r₁ r₂ / 2 := by positivity
      have hρ₁ : min r₁ r₂ / 2 ≤ r₁ := by linarith [min_le_left r₁ r₂]
      have hρ₂ : min r₁ r₂ / 2 ≤ r₂ := by linarith [min_le_right r₁ r₂]
      have hsubT : Metric.ball a (min r₁ r₂ / 2) ⊆ c.target :=
        (Metric.ball_subset_ball hρ₂).trans hr₂sub
      have hharmBall : InnerProductSpace.HarmonicOnNhd ((greenPunctured z₀ E) ∘ c.symm)
          (Metric.ball a (min r₁ r₂ / 2)) :=
        fun w hw => hr₁sub (Metric.ball_subset_ball hρ₁ hw)
      obtain ⟨G, hGana, hGre⟩ :=
        InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharmBall
      set F₀ : puncturedOpens z₀ → ℂ := fun u => G (c u) with hF₀def
      have hF₀hol : Submission.HolomorphicOnX F₀ (Submission.chartBall c a (min r₁ r₂ / 2)) := by
        intro u hu
        rw [Submission.mem_chartBall] at hu
        obtain ⟨husrc, huball⟩ := hu
        rw [Submission.HolomorphicOnXAt_iff_chart (f := F₀) (x := u) (y := u₁) husrc]
        have hev : (F₀ ∘ c.symm) =ᶠ[𝓝 (c u)] G := by
          filter_upwards [Metric.isOpen_ball.mem_nhds huball] with w hw
          simp only [Function.comp_apply, hF₀def]
          rw [c.right_inv (hsubT hw)]
        exact (hGana (c u) huball).congr hev.symm
      have hF₀re : ∀ u ∈ Submission.chartBall c a (min r₁ r₂ / 2),
          (F₀ u).re = greenPunctured z₀ E u := by
        intro u hu
        rw [Submission.mem_chartBall] at hu
        obtain ⟨husrc, huball⟩ := hu
        have h := hGre huball
        rw [Function.comp_apply, c.left_inv husrc] at h
        exact h
      set y₁ : ℝ := (cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u₁)) e₀).1.2 with hy₁def
      set F : puncturedOpens z₀ → ℂ :=
        fun u => F₀ u + Complex.I * (((y₁ - (F₀ u₁).im : ℝ)) : ℂ) with hFdef
      have hadd : Submission.HolomorphicOnX
          (fun u => F₀ u + Complex.I * (((y₁ - (F₀ u₁).im : ℝ)) : ℂ))
          (Submission.chartBall c a (min r₁ r₂ / 2)) ∧
          (∀ u ∈ Submission.chartBall c a (min r₁ r₂ / 2),
            (F₀ u + Complex.I * (((y₁ - (F₀ u₁).im : ℝ)) : ℂ)).re = greenPunctured z₀ E u) :=
        Submission.holomorphicOnX_add_const' hF₀hol hF₀re
          (Complex.I * (((y₁ - (F₀ u₁).im : ℝ)) : ℂ)) (by simp)
      have hFhol : Submission.HolomorphicOnX F (Submission.chartBall c a (min r₁ r₂ / 2)) := by
        simpa only [hFdef] using hadd.1
      have hFre : ∀ u ∈ Submission.chartBall c a (min r₁ r₂ / 2),
          (F u).re = greenPunctured z₀ E u := by
        intro u hu
        simpa only [hFdef] using hadd.2 u hu
      have hFim : (F u₁).im = y₁ := by
        rw [hFdef]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul]
        ring
      have hgraph := continuous_conjGraphMap (h := greenPunctured z₀ E)
        (B := Submission.chartBall c a (min r₁ r₂ / 2)) (F := F)
        (Submission.chartBall_isOpen c a (min r₁ r₂ / 2)) hFhol hFre
      have hlocal : ∀ z ∈ Submission.chartBall c a (min r₁ r₂ / 2), Φ z = Complex.exp (-(F z)) := by
        intro z hz
        obtain ⟨δ, hδ⟩ := exists_path_in_chartBall c hρ hsubT hsrc rfl hz
        rw [hΦval z, ← hcons z (pathTo z) ((pathTo u₁).trans δ)]
        rw [show Path.Homotopic.Quotient.mk ((pathTo u₁).trans δ)
              = (Path.Homotopic.Quotient.mk (pathTo u₁)).trans (Path.Homotopic.Quotient.mk δ)
              from Path.Homotopic.Quotient.mk_trans _ _]
        rw [cov.monodromy_trans_apply]
        have he₁ : cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u₁)) e₀
            = Submission.conjFiberPt u₁ y₁ :=
          Subtype.ext (Prod.ext
            (cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u₁)) e₀).2 hy₁def.symm)
        rw [he₁, monodromy_mk_conjFiberPt_eq cov δ y₁ hgraph hδ hFim.symm]
        rw [greenPhi]
        congr 1
        rw [neg_inj]
        apply Complex.ext <;>
          simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, hFre z hz, greenPunctured,
            Submission.conjFiberPt]
      have hBmem0 : u₁ ∈ Submission.chartBall c a (min r₁ r₂ / 2) := by
        rw [Submission.mem_chartBall]
        exact ⟨hsrc, Metric.mem_ball_self hρ⟩
      have hBmem : Submission.chartBall c a (min r₁ r₂ / 2) ∈ 𝓝 u₁ :=
        (Submission.chartBall_isOpen c a (min r₁ r₂ / 2)).mem_nhds hBmem0
      have hFholAt : Submission.HolomorphicOnXAt F u₁ := hFhol u₁ hBmem0
      have hexpAt : Submission.HolomorphicOnXAt (fun u => Complex.exp (-(F u))) u₁ :=
        hFholAt.cexp_neg
      have hev : (fun u => Complex.exp (-(F u))) =ᶠ[𝓝 u₁] Φ :=
        Filter.eventually_of_mem hBmem fun z hz => (hlocal z hz).symm
      rw [Submission.HolomorphicOnXAt]
      rw [Submission.HolomorphicOnXAt] at hexpAt
      refine AnalyticAt.congr hexpAt ?_
      have htend : Filter.Tendsto c.symm (𝓝 (c u₁)) (𝓝 u₁) := by
        conv_rhs => rw [← c.left_inv hsrc]
        exact c.continuousAt_symm (c.map_source hsrc)
      filter_upwards [htend.eventually hev] with w hw
      exact hw
    exact exists_holomorphic_modulus_of_branchOnPunctured hpole hhol hne hmod

/-- **The holomorphic modulus of a function with a unit logarithmic pole, from the period
condition on all loops of the punctured surface.**  This is the `hmod` input of
`Work.SimplyConnected.ABS.extremal_maximizer_zero_fiber_of_inputs'`. -/
theorem exists_modulus_of_logPole_of_loopsTrivial {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hloop : Work.Modulus.AllLoopsOfPuncturedTrivialInX (X := X) z₀) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Φ z₀ = 0 ∧
      (∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x))) ∧
      (∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ z₀) z₀) ∧ H ((chartAt ℂ z₀) z₀) ≠ 0 ∧
        Filter.EventuallyEq (nhds ((chartAt ℂ z₀) z₀)) (Φ ∘ (chartAt ℂ z₀).symm)
          (fun w : ℂ => (w - (chartAt ℂ z₀) z₀) * H w)) := by
  have hper : ∀ (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀),
      ∃ k : ℤ, greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi) :=
    fun u₀ γ => greenPeriodHom_two_pi_zmultiples hEharm hpole u₀ γ (hloop u₀ γ)
  obtain ⟨Φ, hhol, hne, hmod⟩ := hasTrivialModulusMonodromy_of_periods hEharm hpole hper
  have hp := poleOrderModulus_of_unitGreen hEharm hpole hhol hne hmod
  exact ⟨Φ, hhol, Submission.phi_zero_of_logPole hhol hp, hmod, hp⟩

end Work.ModulusLP
