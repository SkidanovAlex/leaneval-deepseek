import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Pressure.RadialPrim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-!
# Joint `C¹` regularity of the radial primitive

`Work.FTS.Physical.radialPrim G x t = ∫ s in 0..1, ⟪G (s • x) t, x⟫` is the explicit primitive of a
curl-free field used to produce the pressure of the reconstructed Euler solution.  This module
proves that it is jointly `C¹` in `(x,t)` as soon as `G` is jointly `C¹`.

The proof is differentiation under the integral sign: for a jointly `C¹` integrand `K` on a product
`u ×ˢ s` (with `u ∋ [a,b]` and `s` open) the parametric integral `x ↦ ∫ t in a..b, K t x` is `C¹`
on `s`, with derivative `x ↦ ∫ t in a..b, ∂₂K(t,x)`.  The two ingredients are

* `hasFDerivAt_intervalIntegral` — the derivative exists and is the integral of the derivative
  (Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le''`, with the domination bound coming
  from the compactness of `[a,b] × closedBall x₀ ρ`);
* `continuousOn_intervalIntegral_fderiv` — that derivative is continuous in `x`, by dominated
  convergence along the compact strip.

They are assembled in `contDiffOn_intervalIntegral`, and instantiated at `K s (x,t) = ⟪G(s•x,t),x⟫`.

The final theorem is stated with the integral written out, because `Work.FTS.Physical.radialPrim` is
*defined* in the umbrella module `Submission.Work.FTS.Physical.Pressure`, which imports the present
module (it re-exports this lemma as `Work.FTS.Physical.contDiffOn_radialPrim`); importing it here
would create an import cycle.  The two statements are definitionally equal, since `radialPrim` is
definitionally `∫ s in 0..1, ⟪G (s • x) t, x⟫`, so consumers may use either phrasing.
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section General

variable [ProperSpace X]

/-- For `K` jointly `C¹` on the product of open sets `u ×ˢ s`, the partial derivative in the second
variable of `K` (as a function of the whole point) is the full Fréchet derivative composed with
`inr : X →L ℝ × X`. -/
theorem hasFDerivAt_slice {K : ℝ → X → ℝ} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s))
    {t : ℝ} {x : X} (ht : t ∈ u) (hx : x ∈ s) :
    HasFDerivAt (fun y => K t y)
      ((fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) x := by
  have hcd : ContDiffAt ℝ 1 (fun p : ℝ × X => K p.1 p.2) (t, x) :=
    (hK (t, x) ⟨ht, hx⟩).contDiffAt ((hu.prod hs).mem_nhds ⟨ht, hx⟩)
  have hfd : HasFDerivAt (fun p : ℝ × X => K p.1 p.2)
      (fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)) (t, x) :=
    hcd.differentiableAt_one.hasFDerivAt
  have hpair : HasFDerivAt (fun y : X => (t, y)) (ContinuousLinearMap.inr ℝ ℝ X) x := by
    have h : HasFDerivAt (fun y : X => ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ ℝ X)
    have h' : HasFDerivAt (fun y : X => (t, (0 : X)) + ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x := h.const_add (t, (0 : X))
    simpa using h'
  simpa only [Function.comp_def] using hfd.comp x hpair

/-- `(t,x) ↦ ∂₂K(t,x)` is continuous on `u ×ˢ s` when `K` is jointly `C¹` there. -/
theorem continuousOn_fderiv_slice {K : ℝ → X → ℝ} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (u ×ˢ s) := by
  have h1 : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun p : ℝ × X => K p.1 p.2) p) (u ×ˢ s) :=
    hK.continuousOn_fderiv_of_isOpen (hu.prod hs) le_rfl
  have h2 : Continuous fun L : (ℝ × X) →L[ℝ] ℝ => L.comp (ContinuousLinearMap.inr ℝ ℝ X) :=
    (((ContinuousLinearMap.compL ℝ X (ℝ × X) ℝ).flip (ContinuousLinearMap.inr ℝ ℝ X)) :
      ((ℝ × X) →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ)).continuous
  refine (h2.continuousOn.comp h1 (fun p _ => Set.mem_univ _)).congr fun p hp => ?_
  exact (hasFDerivAt_slice hu hs hK hp.1 hp.2).fderiv

/-- **Differentiation under the integral sign.**  For `K` jointly `C¹` on `u ×ˢ s`, with
`[a,b] ⊆ u` and `s` open, the map `x ↦ ∫ t in a..b, K t x` is differentiable at every `x₀ ∈ s` with
derivative the integral of the partial derivative. -/
theorem hasFDerivAt_intervalIntegral {K : ℝ → X → ℝ} {s : Set X} {u : Set ℝ} {a b : ℝ}
    (hs : IsOpen s) (hu : IsOpen u) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s))
    {x₀ : X} (hx₀ : x₀ ∈ s) :
    HasFDerivAt (fun x => ∫ t in a..b, K t x)
      (∫ t in a..b, fderiv ℝ (fun y => K t y) x₀) x₀ := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hρ0 : 0 < ε / 2 := by positivity
  have hρs : Metric.closedBall x₀ (ε / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεs
  have hcont : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (ε / 2)) :=
    (continuousOn_fderiv_slice hu hs hK).mono (Set.prod_mono hsub hρs)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn hcont
  have hsubIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self
  have hslice (x : X) (hx : x ∈ s) : ContinuousOn (fun t : ℝ => K t x) (Set.Icc a b) :=
    hK.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hsub ht, hx⟩)
  have hslice' : ContinuousOn (fun t : ℝ => fderiv ℝ (fun y => K t y) x₀) (Set.Icc a b) :=
    (continuousOn_fderiv_slice hu hs hK).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hsub ht, hx₀⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (x₀ := x₀)
    (s := Metric.ball x₀ (ε / 2) ∩ s)
    (F := fun x t => K t x) (F' := fun x t => fderiv ℝ (fun y => K t y) x) (bound := fun _ => M)
    ?_ ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact inter_mem (Metric.ball_mem_nhds x₀ hρ0) (hs.mem_nhds hx₀)
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact ((hslice x hx).mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hslice x₀ hx₀).intervalIntegrable_of_Icc hab
  · exact (hslice'.mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    exact hM (t, x) ⟨hsubIoc ht, Metric.ball_subset_closedBall hx.1⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    have h := hasFDerivAt_slice hu hs hK (hsub (hsubIoc ht)) hx.2
    simpa only [h.fderiv] using h

/-- **Continuity of the derivative.**  The map `x ↦ ∫ t in a..b, ∂₂K(t,x)` is continuous on `s`. -/
theorem continuousOn_intervalIntegral_fderiv {K : ℝ → X → ℝ} {s : Set X} {u : Set ℝ} {a b : ℝ}
    (hs : IsOpen s) (hu : IsOpen u) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x) s := by
  have hcongr : (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x)
      = fun x => ∫ t in Set.uIoc a b, fderiv ℝ (fun y => K t y) x := by
    funext x
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  rw [hcongr]
  intro x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hρ0 : 0 < ε / 2 := by positivity
  have hρs : Metric.closedBall x₀ (ε / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεs
  have hcont : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (ε / 2)) :=
    (continuousOn_fderiv_slice hu hs hK).mono (Set.prod_mono hsub hρs)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn hcont
  have hsubIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self
  have hint : Integrable (fun _ : ℝ => M) (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (intervalIntegrable_const (c := M) (μ := volume) (a := a) (b := b)).1
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun t : ℝ => fderiv ℝ (fun y => K t y) x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [hs.mem_nhds hx₀] with x hx
    have h1 : ContinuousOn (fun t : ℝ => fderiv ℝ (fun y => K t y) x) (Set.Icc a b) :=
      (continuousOn_fderiv_slice hu hs hK).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hsub ht, hx⟩)
    exact (h1.mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      ‖fderiv ℝ (fun y => K t y) x‖ ≤ (fun _ : ℝ => M) t := by
    filter_upwards [Metric.ball_mem_nhds x₀ hρ0] with x hx
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    exact hM (t, x) ⟨hsubIoc ht, Metric.ball_subset_closedBall hx⟩
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      Tendsto (fun x => fderiv ℝ (fun y => K t y) x) (𝓝 x₀)
        (𝓝 (fderiv ℝ (fun y => K t y) x₀)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    have hslice : ContinuousAt (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (t, x₀) :=
      (continuousOn_fderiv_slice hu hs hK).continuousAt
        ((hu.prod hs).mem_nhds ⟨hsub (hsubIoc ht), hx₀⟩)
    have hline : ContinuousAt (fun x : X => (t, x)) x₀ := continuousAt_const.prodMk continuousAt_id
    simpa only [Function.comp_def] using (hslice.comp hline).tendsto
  have hmain : ContinuousAt (fun x => ∫ t in Set.uIoc a b, fderiv ℝ (fun y => K t y) x) x₀ :=
    tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => M) hmeas hbound hint hlim
  exact hmain.continuousWithinAt

/-- **The parametric interval integral of a `C¹` integrand is `C¹`.** -/
theorem contDiffOn_intervalIntegral {K : ℝ → X → ℝ} {s : Set X} {u : Set ℝ} {a b : ℝ}
    (hs : IsOpen s) (hu : IsOpen u) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in a..b, K t x) s := by
  have key : ContDiffOn ℝ ((0 : ℕ) + 1) (fun x => ∫ t in a..b, K t x) s :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn
      (f := fun x => ∫ t in a..b, K t x) (n := (0 : ℕ))).2
      ⟨fun h => absurd h (by simp),
        fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x,
        (contDiffOn_zero).2 (continuousOn_intervalIntegral_fderiv hs hu hab hsub hK),
        fun x hx => (hasFDerivAt_intervalIntegral hs hu hab hsub hK hx).hasFDerivWithinAt⟩
  exact key

end General

/-! ## The radial primitive of a joint `C¹` field -/

/-- The integrand `(s,(x,t)) ↦ ⟪G(s•x,t),x⟫` of `radialPrim` is `C¹` on `ℝ × (ℝ³ × (0,T))`. -/
theorem contDiffOn_radialPrim_integrand {G : R3 → ℝ → R3} {T : ℝ}
    (hG : ContDiffOn ℝ 1 (fun q : R3 × ℝ => G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × (R3 × ℝ) => inner ℝ (G (p.1 • p.2.1) p.2.2) p.2.1)
      (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioo 0 T)) := by
  have hφ : ContDiffOn ℝ 1 (fun p : ℝ × (R3 × ℝ) => (p.1 • p.2.1, p.2.2))
      (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioo 0 T)) := by fun_prop
  have hmap : MapsTo (fun p : ℝ × (R3 × ℝ) => (p.1 • p.2.1, p.2.2))
      (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioo 0 T)) (Set.univ ×ˢ Set.Ioo 0 T) :=
    fun p hp => ⟨trivial, hp.2.2⟩
  have h1 : ContDiffOn ℝ 1 (fun p : ℝ × (R3 × ℝ) => G (p.1 • p.2.1) p.2.2)
      (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioo 0 T)) := hG.comp hφ hmap
  have h2 : ContDiffOn ℝ 1 (fun p : ℝ × (R3 × ℝ) => p.2.1)
      (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioo 0 T)) := by fun_prop
  exact ContDiffOn.inner ℝ h1 h2

/-- **Joint `C¹` regularity of the radial primitive.**  If `G` is jointly `C¹` on `ℝ³ × (0,T)`,
then so is `(x,t) ↦ radialPrim G x t`. -/
theorem contDiffOn_radialPrim {G : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {T : ℝ} (hG : ContDiffOn ℝ 1 (fun q : Work.FTS.Physical.R3 × ℝ => G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T)) : ContDiffOn ℝ 1 (fun q : Work.FTS.Physical.R3 × ℝ => Work.FTS.Physical.radialPrim G q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 T) := by
  have hK := contDiffOn_radialPrim_integrand (T := T) hG
  have h := contDiffOn_intervalIntegral (X := R3 × ℝ)
    (K := fun s q => inner ℝ (G (s • q.1) q.2) q.1)
    (s := Set.univ ×ˢ Set.Ioo 0 T) (u := Set.univ) (a := 0) (b := 1)
    (isOpen_univ.prod isOpen_Ioo) isOpen_univ (by norm_num) (fun t _ => trivial) hK
  simpa only [Work.FTS.Physical.radialPrim] using h

end Work.FTS.Physical.Pressure
