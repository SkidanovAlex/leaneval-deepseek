import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected
import Submission.Lib.Unif2.Work.Modulus.puncturedHarmonic
import Submission.Lib.Unif2.Work.Modulus.continuous_conjGraphMap
import Submission.Lib.Unif2.Work.Modulus.exists_path_in_chartBall
import Submission.Lib.Unif2.Work.Modulus.monodromy_mk_conjFiberPt_eq
import Submission.Lib.Unif2.Work.Modulus.exists_int_monodromy_eq_conjFiberShift
import Submission.Lib.Unif2.Work.Modulus.exists_holomorphic_modulus_of_branchOnPunctured

/-!
# Trivial monodromy of the modulus from the period condition

Let `X` be a connected complex one-manifold, `z₀ : X`, and `E : X → ℝ` a Green function with pole
`z₀` (`Work.UnitGreen.IsUnitGreenFunctionAt`).  Suppose that every period of the conjugate of `E` over the
punctured surface `U = X ∖ {z₀}` is an integer multiple of `2π`:

`∀ u₀ γ, ∃ k : ℤ, greenPeriodHom hE u₀ γ = k * (2π)`

(`Work.Modulus.greenPeriodHom` is the drift of the harmonic conjugate of `E` along a loop, computed
in the conjugate étale space `greenConjTopology z₀ E` of `Submission.Conjugate`).  Then the
multivalued modulus `Φ = exp (-(E + iE*))` is single valued: there is a holomorphic `Φ` on `X` with
`Φ ≠ 0` off `z₀` and `‖Φ x‖ = exp (-E x)` there.

The construction is the classical one, formalised as follows.  On the punctured surface `U` the
conjugate étale space `(U × ℝ, greenConjTopology z₀ E)` of `E` is a covering space of `U`
(`Work.Modulus.green_isCoveringMap`), and the function `Ψ (u, y) = exp (-(E u + i y))` on it is
invariant under the shifts `y ↦ y + 2π k`.  The period condition says exactly that the monodromy of
the covering around any loop moves the chosen base point `e₀ = (u₀, 0)` by such a shift
(`Work.Modulus.exists_int_monodromy_eq_conjFiberShift`), so `Ψ` of the endpoint of the lift of a
path `u₀ → u` does not depend on the chosen path: this defines a single valued `Φ` on `U`, which is
holomorphic because it agrees locally with `exp (-F)` for a local conjugate `F` of `E`
(`Work.Modulus.monodromy_mk_conjFiberPt_eq` and `Work.Modulus.continuous_conjGraphMap`).  Finally
`Φ` extends across the pole `z₀` (the boundedness comes from `E → +∞`), which is
`Work.Modulus.exists_holomorphic_modulus_of_branchOnPunctured`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The multivalued modulus, evaluated on the conjugate étale space.**  At the point `(u, y)` of
the étale space of the conjugate of `E`, this is `exp (-(E u + i y))`; it has modulus `exp (-E u)`
and is invariant under the shifts `y ↦ y + 2πk`. -/
def greenPhi (z₀ : X) (E : X → ℝ) : (puncturedOpens z₀) × ℝ → ℂ :=
  fun p => Complex.exp (-((E p.1.1 : ℂ) + (p.2 : ℂ) * Complex.I))

theorem norm_greenPhi {z₀ : X} {E : X → ℝ} (p : (puncturedOpens z₀) × ℝ) :
    ‖greenPhi z₀ E p‖ = Real.exp (-(E p.1.1)) := by
  rw [greenPhi, Complex.norm_exp]
  congr 1
  simp

theorem greenPhi_ne_zero {z₀ : X} {E : X → ℝ} (p : (puncturedOpens z₀) × ℝ) :
    greenPhi z₀ E p ≠ 0 :=
  Complex.exp_ne_zero _

/-- `exp (-(E + iE*))` is invariant under the period shifts `y ↦ y + 2πk`. -/
theorem greenPhi_conjFiberShift {z₀ : X} {E : X → ℝ} {u : puncturedOpens z₀}
    (e : ↥(Submission.conjFiber u)) (k : ℤ) :
    greenPhi z₀ E (Submission.conjFiberShift (k * (2 * Real.pi)) e).1 = greenPhi z₀ E e.1 := by
  rw [greenPhi, greenPhi]
  have hsplit : -((E ((Submission.conjFiberShift (k * (2 * Real.pi)) e).1).1.1 : ℂ)
        + (((Submission.conjFiberShift (k * (2 * Real.pi)) e).1).2 : ℂ) * Complex.I)
      = (-((E e.1.1.1 : ℂ) + (e.1.2 : ℂ) * Complex.I))
        + (-(((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)))) := by
    simp only [Submission.conjFiberShift]
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hone : Complex.exp (-((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-k, by push_cast; ring⟩
  rw [hone, mul_one]

/-- **The value of `Ψ` at the endpoint of a lifted path does not depend on the path.**  This is the
period condition in the form used by the construction of the global modulus. -/
theorem greenPhi_monodromy_eq {z₀ : X} {E : X → ℝ}
    [htop : TopologicalSpace ((puncturedOpens z₀) × ℝ)]
    (cov : IsCoveringMap (Prod.fst : (puncturedOpens z₀) × ℝ → (puncturedOpens z₀)))
    (hσ : ∀ c : ℝ, Continuous (Submission.conjShift (X := puncturedOpens z₀) c))
    {u₀ : puncturedOpens z₀} (e₀ : ↥(Submission.conjFiber u₀))
    (hper : ∀ δ : FundamentalGroup (puncturedOpens z₀) u₀,
      ∃ k : ℤ, Submission.conjPeriod u₀ e₀ cov δ = k * (2 * Real.pi))
    {x : puncturedOpens z₀} (γ γ' : Path u₀ x) :
    greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk γ') e₀).1)
      = greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk γ) e₀).1) := by
  obtain ⟨k, hk⟩ := exists_int_monodromy_eq_conjFiberShift (Y := puncturedOpens z₀) cov hσ e₀ γ γ' hper
  rw [hk, greenPhi_conjFiberShift]

/-- **Trivial monodromy of the modulus from the period condition.**  If every period of the
conjugate of the Green function `E` over the punctured surface is a multiple of `2π`, then the
multivalued modulus `exp (-(E + iE*))` is single valued. -/
theorem hasTrivialModulusMonodromy_of_periods
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (hper : ∀ (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀),
      ∃ k : ℤ, greenPeriodHom hE u₀ (Additive.ofMul γ) = k * (2 * Real.pi)) :
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
      green_isCoveringMap hE with hcovdef
    have hσ : ∀ c : ℝ, Continuous (Submission.conjShift (X := puncturedOpens z₀) c) :=
      fun c => green_continuous_conjShift (z₀ := z₀) (E := E) c
    set u₀ : puncturedOpens z₀ := ⟨x₀, hx₀⟩ with hu₀def
    set e₀ : ↥(Submission.conjFiber u₀) := Submission.conjFiberPt u₀ 0 with he₀def
    -- the period condition, in terms of the period of the conjugate covering
    have hper' : ∀ δ : FundamentalGroup (puncturedOpens z₀) u₀,
        ∃ k : ℤ, Submission.conjPeriod u₀ e₀ cov δ = k * (2 * Real.pi) := by
      intro δ
      obtain ⟨k, hk⟩ := hper u₀ δ
      refine ⟨k, ?_⟩
      rw [he₀def, hcovdef]
      exact (greenPeriodHom_apply hE u₀ δ).symm.trans hk
    -- a path from the base point to every point of the punctured surface
    have pathTo : (u : puncturedOpens z₀) → Path u₀ u := fun u => PathConnectedSpace.somePath u₀ u
    -- the single valued modulus on the punctured surface
    set Φ : puncturedOpens z₀ → ℂ :=
      fun u => greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).1)
      with hΦdef
    have hΦval : ∀ u : puncturedOpens z₀,
        Φ u = greenPhi z₀ E ((cov.monodromy (Path.Homotopic.Quotient.mk (pathTo u)) e₀).1) :=
      fun u => rfl
    -- the value does not depend on the chosen path
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
        greenPunctured_harmonic hE u₁ (mem_univ u₁)
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
      -- a local conjugate of `E` on the chart ball
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
      -- adjust the imaginary part so that `F u₁` has imaginary part the `y`-coordinate of the
      -- endpoint of the lift of the chosen path
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
      -- the graph of `F` is continuous in the conjugate topology
      have hgraph := continuous_conjGraphMap (h := greenPunctured z₀ E)
        (B := Submission.chartBall c a (min r₁ r₂ / 2)) (F := F)
        (Submission.chartBall_isOpen c a (min r₁ r₂ / 2)) hFhol hFre
      -- `Φ` agrees with `exp (-F)` near `u₁`
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
      -- holomorphy at `u₁` follows
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
    exact exists_holomorphic_modulus_of_branchOnPunctured hE hhol hne hmod

end Work.Modulus
