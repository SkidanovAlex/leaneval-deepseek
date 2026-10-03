import Mathlib
import Submission.Lib.Unif2.Work.Kernel.pairing_pole_singular_aux
import Submission.Lib.Unif2.Work.Kernel.psmooth_tools
import Submission.Lib.Unif2.Work.Kernel.continuousOn_chartPullback_psi
import Submission.Lib.Unif2.Work.Kernel.contDiffAt_chartPullback_mul_comp_of_harmonic

/-!
# Almost-everywhere strong measurability of the "plateau" pair integrand

The pairing integrand whose measurability this file establishes is

`z ↦ clampedPullback y (σ i) (ψ i) z * ⟪∇(clampedPullback y (ρ i) gB) z,
                                      ∇(clampedPullback y (ρ i) u) z⟫`

(with `y = E.y i` and `u x = if x = a then Θ n (Mb + n) else χ x * Θ n (gA x)`).

Each of the three factors is almost everywhere strongly measurable w.r.t. Lebesgue measure on `ℂ`:

* the weight `clampedPullback y (σ i) (ψ i)` is *continuous* — it is supported in the closed `s i`-ball,
  which sits strictly inside the `σ i`-ball, so the clamping creates no jump
  (`Work.Kernel.continuous_clampedPullback`, using `Work.Kernel.continuousOn_chartPullback_psi`);
* the gradients of the two clamped pullbacks are almost everywhere strongly measurable by
  `Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback'`, whose only input is that the chart
  representative of the pulled-back function is `C¹` off a *single* point:
  * for `gB`, off the pole `b`, this is harmonicity (`IsGreenOn` gives `HarmonicOnX` on `Ω \ {b}`,
    and `InnerProductSpace.HarmonicAt` contains `C²`) transported to the chart by
    `Submission.HarmonicOnXAt_iff_chart`;
  * for `u`, off the pole `a`, this is `Work.Kernel.contDiffAt_chartPullback_mul_comp_of_harmonic`
    for the product `χ · (Θ n ∘ gA)` together with the observation that `u` agrees with that product
    on a neighbourhood of every point different from `a`.

The conclusion then follows from `MeasureTheory.AEStronglyMeasurable.mul` and `.inner`.
-/

open Set MeasureTheory Filter

open scoped Manifold Topology Gradient ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Chart representative of a function harmonic off a point.**  If `u` is harmonic on `Ω \ {x₀}`
and the chart ball of radius `ρ` at `y` is contained in `Ω`, then, off `x₀`, the chart
representative of `u` is `C¹` at every point of that ball. -/
theorem contDiffAt_chartPullback_of_harmonicOn [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {x₀ y : X} {u : X → ℝ} {ρ : ℝ}
    (hu : Submission.HarmonicOnX u (Ω \ {x₀}))
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω) :
    ∀ x ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ, x ≠ x₀ →
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  intro x hx hxne
  have hxsrc : x ∈ (chartAt ℂ y).source := hx.1
  have hharm : Submission.HarmonicOnXAt u x := hu x ⟨hballΩ hx, by simpa using hxne⟩
  exact (((Submission.HarmonicOnXAt_iff_chart (u := u) (x := x) (y := y) hxsrc).mp hharm).1).of_le
    (by norm_num)

/-- **Chart representative of the plateau test function.**  For the function
`v x = if x = a then cst else χ x * Θ (gA x)`, the chart representative is `C¹` at every point of the
chart source different from the pole `a`.  This is the input required by
`Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback'` with `x₀ = a`. -/
theorem contDiffAt_chartPullback_plateau_of_harmonic [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    [DecidableEq X] {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : GreenCover ι Ω K a b)
    {χ gA : X → ℝ} {Θ : ℝ → ℝ} {cst : ℝ}
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχΩ : tsupport χ ⊆ Ω)
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA) (hΘ : ContDiff ℝ 1 Θ) :
    ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source, x ≠ a →
      ContDiffAt ℝ 1 ((fun y : X => if y = a then cst else χ y * Θ (gA y))
        ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x) := by
  classical
  intro k x hx hxa
  have hbase := contDiffAt_chartPullback_mul_comp_of_harmonic E hχc1 hχΩ hgA hΘ k x hx hxa
  refine hbase.congr_of_eventuallyEq ?_
  have htgt : (chartAt ℂ (E.y k)) x ∈ (chartAt ℂ (E.y k)).target :=
    (chartAt ℂ (E.y k)).map_source hx
  have hEq : 𝓝 ((chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) x)) = 𝓝 x :=
    congrArg 𝓝 ((chartAt ℂ (E.y k)).left_inv hx)
  have hcompl : ∀ᶠ w in 𝓝 ((chartAt ℂ (E.y k)).symm ((chartAt ℂ (E.y k)) x)),
      w ∈ ({a}ᶜ : Set X) := by
    rw [hEq]
    exact (isClosed_singleton (x := a)).isOpen_compl.mem_nhds (by simpa using hxa)
  have hsymm : ∀ᶠ w in 𝓝 ((chartAt ℂ (E.y k)) x),
      (chartAt ℂ (E.y k)).symm w ∈ ({a}ᶜ : Set X) :=
    ((chartAt ℂ (E.y k)).continuousAt_symm htgt).eventually hcompl
  filter_upwards [hsymm] with w hw
  simp only [Function.comp_apply]
  rw [if_neg (by simpa using hw)]

theorem aeStronglyMeasurable_pairIntegrand_plateau {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    {gB gA χ : X → ℝ} {Θ : ℕ → ℝ → ℝ} {Mb : ℝ}
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχΩ : tsupport χ ⊆ Ω)
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hΘc1 : ∀ n, ContDiff ℝ 1 (Θ n))
    (i : ι) :
    ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun z : ℂ =>
        Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i) z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z)
          (gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
            (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z))
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  intro n
  -- the weight is continuous (it is clamped strictly outside its support)
  have hAcont : Continuous (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i)) :=
    Work.Kernel.continuous_clampedPullback (x := E.y i) (σ := E.σ i) (s := E.s i) (W := E.ψ i)
      (E.hsσ i)
      (fun w hw => E.htgt i (Metric.ball_subset_ball (E.hσρ i).le hw))
      (Work.Kernel.continuousOn_chartPullback_psi E i)
      (E.hψsupp i)
  have hA : MeasureTheory.AEStronglyMeasurable
      (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i)) MeasureTheory.volume :=
    hAcont.aestronglyMeasurable
  -- the gradient of the clamped pullback of the Green function at `b`
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun z : ℂ => gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gB) z)
      MeasureTheory.volume :=
    Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback'
      (y := E.y i) (ρ := E.ρ i) (u := gB) (x₀ := b) (E.htgt i)
      (contDiffAt_chartPullback_of_harmonicOn (x₀ := b) (y := E.y i) (ρ := E.ρ i) (u := gB)
        hgB.2.1 (E.hballΩ i))
  -- the gradient of the clamped pullback of the plateau test function
  have hG : MeasureTheory.AEStronglyMeasurable
      (fun z : ℂ => gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
        (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z)
      MeasureTheory.volume :=
    Work.Kernel.PS.aeStronglyMeasurable_gradient_clampedPullback'
      (y := E.y i) (ρ := E.ρ i)
      (u := fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x)) (x₀ := a) (E.htgt i)
      (fun x hx hxne =>
        contDiffAt_chartPullback_plateau_of_harmonic (cst := Θ n (Mb + n))
          E hχc1 hχΩ hgA (hΘc1 n) i x hx.1 hxne)
  exact hA.mul (hF.inner hG)

end Work.Kernel
