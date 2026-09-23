import Submission.GapEstimate
import Submission.CornerCut
import Submission.GeodesicExtend
import Submission.CurveField

/-!
# The gap between two curves with the same 2-jet

Two smooth curves through the same point, with the same velocity and the same *covariant
acceleration*, are at Riemannian distance `O(s³)`: in a chart the first two Taylor coefficients of
their difference vanish, and the chart metric is locally bounded.

This is the tool that glues the chart pieces of a piecewise geodesic variation in the global
second-variation argument: on each piece the family is the *quadratic* one
`u t + s η t - (s²/2) Γ(η t)(η t)` (whose intrinsic acceleration in `s` vanishes), and the junction
curves of two adjacent pieces have the same value, velocity and covariant acceleration.

## Contents

* `cov_apply_accel_chart`: the covariant acceleration of a chart curve in coordinates
  (`∇_{γ'}γ' = σ_{w + Γ(v)(σ_v)}`), an immediate rewriting of
  `Submission.Geodesic.cov_apply_eq_frameVector`;
* `derivWithin_tower`: the three derivative levels of a function that is `C³` on an interval;
* **`riemannianEDist_le_cube_of_jet`**: the gap lemma.  The proof changes to the chart at the
  common point `p`, uses the chart formula to convert the equality of the covariant accelerations
  into the equality of the second coordinate derivatives, and then applies
  `Submission.GapEstimate.riemannianEDist_le_cube_of_gap`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartCurv
open Submission.ChartBounds
open Submission.GapEstimate
open Submission.CornerCut
open Submission.GeodesicExtend
open Submission.CurveField
open Submission.ChartConnection

namespace Submission.JetGap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

/-! ## Elementary tools -/

/-- A set that is a neighbourhood of `0` contains an interval `(-ρ, ρ)`. -/
lemma exists_pos_forall_abs_lt_of_mem_nhds {S : Set ℝ} (hS : S ∈ 𝓝 (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, |s| < ρ → s ∈ S := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨ρ, hρ, fun s hs => hsub ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  exact hs

/-- `3` is not the "coerced infinity" of the `C^n` hierarchy. -/
private lemma three_ne_infty : (3 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  intro h
  exact absurd (WithTop.coe_inj.mp h) (ENat.natCast_ne_top 3)

/-- A function that is `C^∞` at `0` is `C³` on a symmetric interval around `0`. -/
lemma exists_pos_contDiffOn_Ioo_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiffAt ℝ ∞ f 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 3 f (Ioo (-ρ) ρ) := by
  have h3 : ContDiffAt ℝ (3 : WithTop ℕ∞) f 0 :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨u, hu, hucd⟩ := (contDiffWithinAt_univ.mpr h3).contDiffOn (m := 3) le_rfl
    (fun h => absurd h three_ne_infty)
  have hu' : u ∈ 𝓝 (0 : ℝ) := by
    have h : insert (0 : ℝ) univ = univ := by ext y; simp
    rwa [h, nhdsWithin_univ] at hu
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hu'
  refine ⟨ρ, hρ, hucd.2.mono (fun s hs => hsub ?_)⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  exact abs_lt.mpr hs

/-- **The covariant acceleration of a chart curve, in coordinates.**  If `γ = e⁻¹ ∘ u` is the curve
of the chart at `x₀` with coordinate curve `u` (`u' = v`, `v' = w`) and `Z` is a smooth section
agreeing with the velocity of `γ` along `γ`, then `∇_{γ'}γ' = σ_{w + Γ(v)(σ_v)}`. -/
theorem cov_apply_accel_chart (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    {u v w : ℝ → E} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ioo a b, HasDerivAt v (w s) s)
    (hstay : ∀ s ∈ Ioo a b, u s ∈ (extChartAt I x₀).target)
    (Z : Π x : M, TangentSpace I x)
    (hZ : CMDiffAt ∞ (T% Z) ((extChartAt I x₀).symm (u t)))
    (hZeq : ∀ s ∈ Ioo a b, Z ((extChartAt I x₀).symm (u s)) =
      curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) s) :
    cov Z ((extChartAt I x₀).symm (u t))
        (curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t)
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (w t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (v t) (v t)) := by
  rw [cov_apply_eq_frameVector cov x₀ ht hu hv hstay Z hZ hZeq, chrB_apply]

/-- **The first three derivative levels of a function that is `C³` on an interval.**  For
`f : ℝ → E` which is `C³` on `Ioo (-ρ) ρ`, the derivative tower `derivWithin f (Ioo (-ρ) ρ)`,
`derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ)`, … exists on the interval. -/
theorem derivWithin_tower {f : ℝ → E} {ρ : ℝ} (hf : ContDiffOn ℝ 3 f (Ioo (-ρ) ρ)) :
    (∀ s ∈ Ioo (-ρ) ρ, HasDerivAt f (derivWithin f (Ioo (-ρ) ρ) s) s) ∧
    (∀ s ∈ Ioo (-ρ) ρ, HasDerivAt (derivWithin f (Ioo (-ρ) ρ))
        (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ) s) s) ∧
    (∀ s ∈ Ioo (-ρ) ρ, HasDerivAt (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ))
        (derivWithin (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ))
          (Ioo (-ρ) ρ) s) s) ∧
    ContDiffOn ℝ 0 (derivWithin (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ))
      (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ) := by
  have hU : UniqueDiffOn ℝ (Ioo (-ρ) ρ) := uniqueDiffOn_Ioo _ _
  have h1 : ContDiffOn ℝ 2 (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ) :=
    hf.derivWithin hU (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have h2 : ContDiffOn ℝ 1 (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ))
      (Ioo (-ρ) ρ) := h1.derivWithin hU (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have h3 : ContDiffOn ℝ 0 (derivWithin (derivWithin (derivWithin f (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ))
      (Ioo (-ρ) ρ)) (Ioo (-ρ) ρ) := h2.derivWithin hU (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)
  refine ⟨?_, ?_, ?_, h3⟩
  · intro s hs
    exact (((hf.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioo hs)).differentiableWithinAt.hasDerivWithinAt).hasDerivAt
      (IsOpen.mem_nhds isOpen_Ioo hs)
  · intro s hs
    exact (((h1.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioo hs)).differentiableWithinAt.hasDerivWithinAt).hasDerivAt
      (IsOpen.mem_nhds isOpen_Ioo hs)
  · intro s hs
    exact (((h2.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (IsOpen.mem_nhds isOpen_Ioo hs)).differentiableWithinAt.hasDerivWithinAt).hasDerivAt
      (IsOpen.mem_nhds isOpen_Ioo hs)


/-! ## The gap lemma -/

/-- **The gap between two curves with the same 2-jet is `O(s³)`.**  If two `C^∞` curves `σ₁`, `σ₂`
have the same value, the same velocity and the same covariant acceleration at `0`, then they are at
Riemannian distance `O(s³)`. -/
theorem riemannianEDist_le_cube_of_jet [Nontrivial E]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) [ContMDiffCovariantDerivative cov ∞]
    {σ₁ σ₂ : ℝ → M} (hσ₁ : ContMDiffAt 𝓘(ℝ) I ∞ σ₁ 0) (hσ₂ : ContMDiffAt 𝓘(ℝ) I ∞ σ₂ 0)
    (hval : σ₁ 0 = σ₂ 0)
    (hvel : curveVelocity (I := I) σ₁ 0 = curveVelocity (I := I) σ₂ 0)
    {Z₁ Z₂ : Π x : M, TangentSpace I x} (hZ₁ : CMDiff ∞ (T% Z₁)) (hZ₂ : CMDiff ∞ (T% Z₂))
    (hev₁ : ∀ᶠ s in 𝓝 (0:ℝ), Z₁ (σ₁ s) = curveVelocity (I := I) σ₁ s)
    (hev₂ : ∀ᶠ s in 𝓝 (0:ℝ), Z₂ (σ₂ s) = curveVelocity (I := I) σ₂ s)
    (hacc : cov Z₁ (σ₁ 0) (curveVelocity (I := I) σ₁ 0)
          = cov Z₂ (σ₂ 0) (curveVelocity (I := I) σ₂ 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in 𝓝 (0:ℝ),
      Manifold.riemannianEDist I (σ₁ s) (σ₂ s) ≤ ENNReal.ofReal (C * |s| ^ 3) := by
  classical
  set p : M := σ₁ 0 with hp
  have hsrc₁ : p ∈ (chartAt H p).source := mem_chart_source H p
  have hsrc₂ : σ₂ 0 ∈ (chartAt H p).source := by rw [← hval]; exact hsrc₁
  set r₁ : ℝ → E := fun s => (extChartAt I p) (σ₁ s) with hr₁def
  set r₂ : ℝ → E := fun s => (extChartAt I p) (σ₂ s) with hr₂def
  have hr₁ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ r₁ 0 := by
    have h := (contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)).comp (0 : ℝ) hσ₁
    simpa only [hr₁def, Function.comp_def] using h
  have hr₂ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ r₂ 0 := by
    have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (↑(extChartAt I p)) (σ₂ 0) := by
      rw [← hval]; exact contMDiffAt_extChartAt (I := I) (x := p) (n := ∞)
    have h := hc.comp (0 : ℝ) hσ₂
    simpa only [hr₂def, Function.comp_def] using h
  -- interval smoothness
  obtain ⟨ρc, hρc, hcd₁, hcd₂⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 3 r₁ (Ioo (-ρ) ρ) ∧
      ContDiffOn ℝ 3 r₂ (Ioo (-ρ) ρ) := by
    obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_pos_contDiffOn_Ioo_of_contDiffAt (F := E)
      (contMDiffAt_iff_contDiffAt.mp hr₁)
    obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_pos_contDiffOn_Ioo_of_contDiffAt (F := E)
      (contMDiffAt_iff_contDiffAt.mp hr₂)
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_⟩
    · exact h₁.mono (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _))
    · exact h₂.mono (Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _))
  have hmemU : Ioo (-ρc) ρc ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
  -- the eventual facts
  obtain ⟨ρe, hρe, hρesub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | σ₁ s ∈ (chartAt H p).source ∧ σ₂ s ∈ (chartAt H p).source ∧
      Z₁ (σ₁ s) = curveVelocity (I := I) σ₁ s ∧ Z₂ (σ₂ s) = curveVelocity (I := I) σ₂ s})
    (by
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₁ s ∈ (chartAt H p).source :=
        hσ₁.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₁)
      have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), σ₂ s ∈ (chartAt H p).source :=
        hσ₂.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hsrc₂)
      filter_upwards [h1, h2, hev₁, hev₂] with s hs1 hs2 hs3 hs4
      exact ⟨hs1, hs2, hs3, hs4⟩)
  set ρ : ℝ := min ρc ρe with hρdef
  have hρ : 0 < ρ := lt_min hρc hρe
  have hρc' : ρ ≤ ρc := min_le_left _ _
  have hρe' : ρ ≤ ρe := min_le_right _ _
  have hsubc : Ioo (-ρ) ρ ⊆ Ioo (-ρc) ρc :=
    Ioo_subset_Ioo (neg_le_neg hρc') hρc'
  have hsube : Ioo (-ρ) ρ ⊆ Ioo (-ρe) ρe :=
    Ioo_subset_Ioo (neg_le_neg hρe') hρe'
  -- the derivative towers
  set A1 : ℝ → E := derivWithin r₁ (Ioo (-ρc) ρc) with hA1def
  set A2 : ℝ → E := derivWithin A1 (Ioo (-ρc) ρc) with hA2def
  set B1 : ℝ → E := derivWithin r₂ (Ioo (-ρc) ρc) with hB1def
  set B2 : ℝ → E := derivWithin B1 (Ioo (-ρc) ρc) with hB2def
  obtain ⟨hdA₁, hdA₂, hdA₃, -⟩ := derivWithin_tower (f := r₁) hcd₁
  obtain ⟨hdB₁, hdB₂, hdB₃, -⟩ := derivWithin_tower (f := r₂) hcd₂
  have hdA₁' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₁ (A1 s) s := fun s hs => by
    simpa only [hA1def] using hdA₁ s (hsubc hs)
  have hdA₂' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt A1 (A2 s) s := fun s hs => by
    simpa only [hA1def, hA2def] using hdA₂ s (hsubc hs)
  have hdB₁' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₂ (B1 s) s := fun s hs => by
    simpa only [hB1def] using hdB₁ s (hsubc hs)
  have hdB₂' : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt B1 (B2 s) s := fun s hs => by
    simpa only [hB1def, hB2def] using hdB₂ s (hsubc hs)
  have hA1cd : ContDiffOn ℝ 2 A1 (Ioo (-ρc) ρc) := by
    simpa only [hA1def] using
      hcd₁.derivWithin (uniqueDiffOn_Ioo _ _) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hB1cd : ContDiffOn ℝ 2 B1 (Ioo (-ρc) ρc) := by
    simpa only [hB1def] using
      hcd₂.derivWithin (uniqueDiffOn_Ioo _ _) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hA1diff : DifferentiableAt ℝ A1 0 :=
    (hA1cd.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  have hB1diff : DifferentiableAt ℝ B1 0 :=
    (hB1cd.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  -- values of the first coordinate derivatives
  have hA1_0 : A1 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
      (curveVelocity (I := I) σ₁ 0) := by
    rw [hA1def, derivWithin_of_mem_nhds hmemU]
    exact deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₁) (t := 0) (hσ₁.mdifferentiableAt (by simp)) hsrc₁
  have hB1_0 : B1 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (σ₂ 0)
      (curveVelocity (I := I) σ₂ 0) := by
    rw [hB1def, derivWithin_of_mem_nhds hmemU]
    exact deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity (I := I)
      (x := p) (γ := σ₂) (t := 0) (hσ₂.mdifferentiableAt (by simp)) hsrc₂
  have hA1B1 : A1 0 = B1 0 := by
    rw [hA1_0, hB1_0, ← hval]
    exact congrArg _ hvel
  -- the curves stay in the chart target
  have htgt₁ : ∀ s ∈ Ioo (-ρ) ρ, r₁ s ∈ (extChartAt I p).target := by
    intro s hs
    have hssrc : σ₁ s ∈ (chartAt H p).source := (hρesub _ (abs_lt.mpr (hsube hs))).1
    simp only [hr₁def]
    exact (extChartAt I p).map_source (by rw [extChartAt_source]; exact hssrc)
  have htgt₂ : ∀ s ∈ Ioo (-ρ) ρ, r₂ s ∈ (extChartAt I p).target := by
    intro s hs
    have hssrc : σ₂ s ∈ (chartAt H p).source := (hρesub _ (abs_lt.mpr (hsube hs))).2.1
    simp only [hr₂def]
    exact (extChartAt I p).map_source (by rw [extChartAt_source]; exact hssrc)
  -- the sections agree with the velocities of the chart curves
  have hZe₁ : ∀ s ∈ Ioo (-ρ) ρ, Z₁ ((extChartAt I p).symm (r₁ s)) =
      curveVelocity (I := I) (fun s => (extChartAt I p).symm (r₁ s)) s := by
    intro s hs
    have habs : |s| < ρe := abs_lt.mpr (hsube hs)
    have hssrc : σ₁ s ∈ (chartAt H p).source := (hρesub _ habs).1
    have hbases : ((extChartAt I p).symm) (r₁ s) = σ₁ s := by
      simp only [hr₁def]
      exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hssrc)
    have hevsrc : ∀ᶠ t in 𝓝 s, σ₁ t ∈ (chartAt H p).source := by
      have h1 : Ioo (-ρe) ρe ∈ 𝓝 s := IsOpen.mem_nhds isOpen_Ioo (hsube hs)
      filter_upwards [h1] with t ht
      exact (hρesub _ (abs_lt.mpr ht)).1
    have hev : (fun t => (extChartAt I p).symm (r₁ t)) =ᶠ[𝓝 s] σ₁ := by
      filter_upwards [hevsrc] with t ht
      simp only [hr₁def]
      exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact ht)
    rw [hbases, curveVelocity_congr_of_eventuallyEq (I := I) hev]
    exact (hρesub _ habs).2.2.1
  have hZe₂ : ∀ s ∈ Ioo (-ρ) ρ, Z₂ ((extChartAt I p).symm (r₂ s)) =
      curveVelocity (I := I) (fun s => (extChartAt I p).symm (r₂ s)) s := by
    intro s hs
    have habs : |s| < ρe := abs_lt.mpr (hsube hs)
    have hssrc : σ₂ s ∈ (chartAt H p).source := (hρesub _ habs).2.1
    have hbases : ((extChartAt I p).symm) (r₂ s) = σ₂ s := by
      simp only [hr₂def]
      exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hssrc)
    have hevsrc : ∀ᶠ t in 𝓝 s, σ₂ t ∈ (chartAt H p).source := by
      have h1 : Ioo (-ρe) ρe ∈ 𝓝 s := IsOpen.mem_nhds isOpen_Ioo (hsube hs)
      filter_upwards [h1] with t ht
      exact (hρesub _ (abs_lt.mpr ht)).2.1
    have hev : (fun t => (extChartAt I p).symm (r₂ t)) =ᶠ[𝓝 s] σ₂ := by
      filter_upwards [hevsrc] with t ht
      simp only [hr₂def]
      exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact ht)
    rw [hbases, curveVelocity_congr_of_eventuallyEq (I := I) hev]
    exact (hρesub _ habs).2.2.2
  have hmemE : Ioo (-ρe) ρe ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
  have hcur₁ : (fun s => (extChartAt I p).symm (r₁ s)) =ᶠ[𝓝 (0:ℝ)] σ₁ := by
    filter_upwards [hmemE] with t ht
    have hssrc : σ₁ t ∈ (chartAt H p).source := (hρesub _ (abs_lt.mpr ht)).1
    simp only [hr₁def]
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hssrc)
  have hcur₂ : (fun s => (extChartAt I p).symm (r₂ s)) =ᶠ[𝓝 (0:ℝ)] σ₂ := by
    filter_upwards [hmemE] with t ht
    have hssrc : σ₂ t ∈ (chartAt H p).source := (hρesub _ (abs_lt.mpr ht)).2.1
    simp only [hr₂def]
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hssrc)
  -- the covariant accelerations in coordinates
  have hbase₁ : ((extChartAt I p).symm) (r₁ 0) = p := by
    show (extChartAt I p).symm ((extChartAt I p) (σ₁ 0)) = p
    rw [(extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc₁), hp]
  have hbase₂ : ((extChartAt I p).symm) (r₂ 0) = p := by
    show (extChartAt I p).symm ((extChartAt I p) (σ₂ 0)) = p
    rw [(extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc₂), hval]
  have hcv₁ : curveVelocity (I := I) (fun s => (extChartAt I p).symm (r₁ s)) 0
      = curveVelocity (I := I) σ₁ 0 :=
    curveVelocity_congr_of_eventuallyEq (I := I) hcur₁
  have hcv₂ : curveVelocity (I := I) (fun s => (extChartAt I p).symm (r₂ s)) 0
      = curveVelocity (I := I) σ₂ 0 :=
    curveVelocity_congr_of_eventuallyEq (I := I) hcur₂
  have hAcc₁ : cov Z₁ p (curveVelocity (I := I) σ₁ 0)
      = frameVector (I := I) p p (A2 0 + chrB cov p p (A1 0) (A1 0)) := by
    have h := cov_apply_accel_chart (cov := cov) p (u := r₁) (v := A1) (w := A2)
      (a := -ρ) (b := ρ) (t := 0) (by simp [hρ]) hdA₁' hdA₂' htgt₁ Z₁
      (hZ₁.contMDiffAt) hZe₁
    rw [hbase₁, hcv₁] at h
    exact h
  have hAcc₂ : cov Z₂ p (curveVelocity (I := I) σ₂ 0)
      = frameVector (I := I) p p (B2 0 + chrB cov p p (B1 0) (B1 0)) := by
    have h := cov_apply_accel_chart (cov := cov) p (u := r₂) (v := B1) (w := B2)
      (a := -ρ) (b := ρ) (t := 0) (by simp [hρ]) hdB₁' hdB₂' htgt₂ Z₂
      (hZ₂.contMDiffAt) hZe₂
    rw [hbase₂, hcv₂] at h
    exact h
  have hacc' := hacc
  rw [hval.symm] at hacc'
  have hKey : frameVector (I := I) p p (A2 0 + chrB cov p p (A1 0) (A1 0))
      = frameVector (I := I) p p (B2 0 + chrB cov p p (B1 0) (B1 0)) := by
    rw [← hAcc₁, hacc', hAcc₂]
  have hA2B2 : A2 0 = B2 0 := by
    have hsub : frameVector (I := I) p p ((A2 0 + chrB cov p p (A1 0) (A1 0))
        - (B2 0 + chrB cov p p (B1 0) (B1 0))) = 0 := by
      rw [frameVector_sub, hKey, sub_self]
    have h0 := (frameVector_eq_zero_iff (I := I) (x₀ := p) (p := p) hsrc₁ _).mp hsub
    rw [hA1B1] at h0
    exact add_right_cancel (sub_eq_zero.mp h0)
  -- the difference of the coordinate curves
  set g : ℝ → E := fun s => r₂ s - r₁ s with hgdef
  have hg3 : ContDiffOn ℝ 3 g (Ioo (-ρc) ρc) := by
    have h := hcd₂.sub hcd₁
    simpa only [hgdef, Pi.sub_apply] using h
  obtain ⟨hdg₁, hdg₂, hdg₃, hg3c⟩ := derivWithin_tower (f := g) hg3
  set D1 : ℝ → E := derivWithin g (Ioo (-ρc) ρc) with hD1def
  set D2 : ℝ → E := derivWithin D1 (Ioo (-ρc) ρc) with hD2def
  set D3 : ℝ → E := derivWithin D2 (Ioo (-ρc) ρc) with hD3def
  have hdg₁r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g (D1 s) s := fun s hs => by
    simpa only [hD1def] using hdg₁ s (hsubc hs)
  have hdg₂r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt D1 (D2 s) s := fun s hs => by
    simpa only [hD1def, hD2def] using hdg₂ s (hsubc hs)
  have hdg₃r : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt D2 (D3 s) s := fun s hs => by
    simpa only [hD1def, hD2def, hD3def] using hdg₃ s (hsubc hs)
  have hdr₁ : DifferentiableAt ℝ r₁ 0 :=
    (hcd₁.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  have hdr₂ : DifferentiableAt ℝ r₂ 0 :=
    (hcd₂.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hmemU
  have hg0 : g 0 = 0 := by
    have h1 : r₁ 0 = (extChartAt I p) p := rfl
    have h2 : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    simp only [hgdef, h1, h2, sub_self]
  have hD1_0 : D1 0 = deriv g 0 := by
    rw [hD1def, derivWithin_of_mem_nhds hmemU]
  have hB1_d : deriv r₂ 0 = B1 0 := by
    rw [hB1def, derivWithin_of_mem_nhds hmemU]
  have hA1_d : deriv r₁ 0 = A1 0 := by
    rw [hA1def, derivWithin_of_mem_nhds hmemU]
  have hg'0 : D1 0 = 0 := by
    rw [hD1_0]
    have h1 : deriv g 0 = deriv r₂ 0 - deriv r₁ 0 := by
      have hgg : g = r₂ - r₁ := by funext s; rfl
      rw [hgg]
      exact deriv_sub hdr₂ hdr₁
    rw [h1, hB1_d, hA1_d]
    exact sub_eq_zero.mpr hA1B1.symm
  have hD2_0 : D2 0 = deriv D1 0 := by
    rw [hD2def, derivWithin_of_mem_nhds hmemU]
  have hD1ev : D1 =ᶠ[𝓝 (0:ℝ)] fun s => B1 s - A1 s := by
    filter_upwards [hmemU] with s hs
    have hsU : Ioo (-ρc) ρc ∈ 𝓝 s := IsOpen.mem_nhds isOpen_Ioo hs
    have hb : B1 s = deriv r₂ s := by rw [hB1def, derivWithin_of_mem_nhds hsU]
    have ha : A1 s = deriv r₁ s := by rw [hA1def, derivWithin_of_mem_nhds hsU]
    rw [hD1def, derivWithin_of_mem_nhds hsU]
    have hgg : g = r₂ - r₁ := by funext s; rfl
    rw [hgg, deriv_sub ((hcd₂.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hsU)
      ((hcd₁.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt hsU),
      hb, ha]
  have hD2_0' : D2 0 = deriv B1 0 - deriv A1 0 := by
    rw [hD2_0, Filter.EventuallyEq.deriv_eq hD1ev]
    have hfun : (fun s => B1 s - A1 s) = B1 - A1 := by funext s; rfl
    rw [hfun, deriv_sub hB1diff hA1diff]
  have hderA1 : deriv A1 0 = A2 0 := by
    rw [hA2def, derivWithin_of_mem_nhds hmemU]
  have hderB1 : deriv B1 0 = B2 0 := by
    rw [hB2def, derivWithin_of_mem_nhds hmemU]
  have hg''0 : D2 0 = 0 := by
    rw [hD2_0', hderA1, hderB1, hA2B2, sub_self]

  -- the metric is bounded near `p`
  obtain ⟨lam, hlam, Lam, hLam, hbnd0⟩ := exists_chartGram_bounds (I := I) p
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hsrc₁)
  obtain ⟨U, hUnh, hUbd⟩ := exists_chartGram_le_nhds (I := I) p (c := 1) (by norm_num)
  obtain ⟨R, hR, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ Metric.ball ((extChartAt I p) p) R ⊆
      (extChartAt I p).target ∩ ((extChartAt I p).symm ⁻¹' U) := by
    have htgt : (extChartAt I p) p ∈ (extChartAt I p).target := mem_extChartAt_target p
    have hcont : ContinuousAt ((extChartAt I p).symm) ((extChartAt I p) p) :=
      continuousAt_extChartAt_symm p
    have h1 : (extChartAt I p).target ∈ 𝓝 ((extChartAt I p) p) :=
      (isOpen_extChartAt_target p).mem_nhds htgt
    have hpt : ((extChartAt I p).symm) ((extChartAt I p) p) = p :=
      (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hsrc₁)
    have h2 : (extChartAt I p).symm ⁻¹' U ∈ 𝓝 ((extChartAt I p) p) := by
      have hUnh' : U ∈ 𝓝 ((extChartAt I p).symm ((extChartAt I p) p)) := by rw [hpt]; exact hUnh
      exact hcont.preimage_mem_nhds hUnh'
    obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
    exact ⟨R, hR, hsub⟩
  have hbound : ∀ z ∈ Metric.ball ((extChartAt I p) p) R, ∀ a : E,
      chartGram (I := I) p ((extChartAt I p).symm z) a a ≤ (2 * Lam) * ‖a‖ ^ 2 := by
    intro z hz a
    have h1 := hUbd ((extChartAt I p).symm z) (hRsub hz).2 a
    have h2 := (hbnd0 p (by simp) a).2
    calc chartGram (I := I) p ((extChartAt I p).symm z) a a
        ≤ (1 + 1) * chartGram (I := I) p p a a := h1
      _ ≤ (1 + 1) * (Lam * ‖a‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = (2 * Lam) * ‖a‖ ^ 2 := by ring
  -- the radii of the two coordinate curves
  have h1c : ContinuousAt r₁ 0 := (hcd₁.continuousOn.continuousAt hmemU)
  have h2c : ContinuousAt r₂ 0 := (hcd₂.continuousOn.continuousAt hmemU)
  have h10 : r₁ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    have h10' : r₁ 0 = (extChartAt I p) p := rfl
    rw [h10', Metric.mem_ball, dist_self]
    exact hR
  have h20 : r₂ 0 ∈ Metric.ball ((extChartAt I p) p) R := by
    have h20' : r₂ 0 = (extChartAt I p) p := by
      show (extChartAt I p) (σ₂ 0) = (extChartAt I p) p
      rw [← hval]
    rw [h20', Metric.mem_ball, dist_self]
    exact hR
  obtain ⟨ρa, hρa, hρasub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₁ s ∈ Metric.ball ((extChartAt I p) p) R})
    (h1c.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h10))
  obtain ⟨ρb, hρb, hρbsub⟩ := exists_pos_forall_abs_lt_of_mem_nhds
    (S := {s : ℝ | r₂ s ∈ Metric.ball ((extChartAt I p) p) R})
    (h2c.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds h20))
  -- the effective radius
  set ρ₀ : ℝ := min (ρc / 2) (min ρ (min ρa ρb)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by linarith) (lt_min hρ (lt_min hρa hρb))
  have hρ0c : ρ₀ ≤ ρc / 2 := min_le_left _ _
  have hρ0ρ : ρ₀ ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ0a : ρ₀ ≤ ρa := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ0b : ρ₀ ≤ ρb := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsubρ₀ : Ioo (-ρ₀) ρ₀ ⊆ Ioo (-ρ) ρ := Ioo_subset_Ioo (neg_le_neg hρ0ρ) hρ0ρ
  -- the derivative facts and the bound
  have h1d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt g (D1 s) s := fun s hs => hdg₁r s (hsubρ₀ hs)
  have h2d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt D1 (D2 s) s := fun s hs => hdg₂r s (hsubρ₀ hs)
  have h3d : ∀ s ∈ Ioo (-ρ₀) ρ₀, HasDerivAt D2 (D3 s) s := fun s hs => hdg₃r s (hsubρ₀ hs)
  obtain ⟨M₀, hM₀, hM₀nn⟩ : ∃ M : ℝ, (∀ s ∈ Ioo (-ρ₀) ρ₀, ‖D3 s‖ ≤ M) ∧ 0 ≤ M := by
    have hD3c : ContinuousOn D3 (Ioo (-ρc) ρc) := by
      simpa only [hD1def, hD2def, hD3def] using hg3c.continuousOn
    have hsub : Icc (-ρ₀) ρ₀ ⊆ Ioo (-ρc) ρc := by
      intro s hs
      exact ⟨by linarith [hρ0c, hρc, hs.1], by linarith [hρ0c, hρc, hs.2]⟩
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc (hD3c.mono hsub)
    exact ⟨max M 0, fun s hs => le_trans (hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩) (le_max_left _ _),
      le_max_right _ _⟩
  have hVin : ∀ s ∈ Ioo (-ρ₀) ρ₀, r₁ s ∈ Metric.ball ((extChartAt I p) p) R := fun s hs =>
    hρasub _ (abs_lt.mpr ⟨by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0a)).1],
      by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0a)).2]⟩)
  have hUVin : ∀ s ∈ Ioo (-ρ₀) ρ₀, r₁ s + g s ∈ Metric.ball ((extChartAt I p) p) R := by
    intro s hs
    have heq : r₁ s + g s = r₂ s := by simp only [hgdef]; abel
    rw [heq]
    exact hρbsub _ (abs_lt.mpr ⟨by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0b)).1],
      by linarith [(abs_lt.mp (lt_of_lt_of_le (abs_lt.mpr hs) hρ0b)).2]⟩)
  obtain ⟨ρ', hρ'pos, hρ'le, hfin⟩ := riemannianEDist_le_cube_of_gap (I := I) (x₀ := p)
    (V := r₁) (g := g) (g' := D1) (g'' := D2) (g''' := D3)
    (K := Metric.ball ((extChartAt I p) p) R) (c := (extChartAt I p) p) (r := R)
    (Λ := 2 * Lam) (M₀ := M₀) (ρ := ρ₀) rfl (by linarith) hρ₀ hg0 hg'0 hg''0
    h1d h2d h3d hM₀ hbound (fun z hz => (hRsub hz).1) hVin hUVin
  refine ⟨Real.sqrt (2 * Lam) * (M₀ / 6),
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hM₀nn (by norm_num)), ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ'pos] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  have hsI : s ∈ Ioo (-ρ) ρ := by
    have h1 : |s| < ρ := lt_of_lt_of_le (lt_of_lt_of_le hs hρ'le) hρ0ρ
    exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
  have hp1 : ((extChartAt I p).symm) (r₁ s) = σ₁ s := by
    show (extChartAt I p).symm ((extChartAt I p) (σ₁ s)) = σ₁ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact (hρesub _ (abs_lt.mpr (hsube hsI))).1)
  have hp2 : ((extChartAt I p).symm) (r₁ s + g s) = σ₂ s := by
    have heq : r₁ s + g s = r₂ s := by simp only [hgdef]; abel
    rw [heq]
    show (extChartAt I p).symm ((extChartAt I p) (σ₂ s)) = σ₂ s
    exact (extChartAt I p).left_inv (by rw [extChartAt_source]; exact (hρesub _ (abs_lt.mpr (hsube hsI))).2.1)
  have h2 := hfin s hs
  rw [hp2, hp1, Manifold.riemannianEDist_comm] at h2
  exact h2.trans (le_of_eq (congrArg ENNReal.ofReal (by ring)))


end

end Submission.JetGap
