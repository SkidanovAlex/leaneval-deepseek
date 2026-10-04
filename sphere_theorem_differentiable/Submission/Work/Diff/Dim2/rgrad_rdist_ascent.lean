import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.rgrad_rdist_eikonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The gradient of the distance function is an ascent direction.**

For `y` with `0 < rdist p y` at which `rdist p ·` is smooth, the gradient `∇(d(p,·))` at `y` makes
an obtuse angle with every shortest unit direction from `y` to `p`.  Indeed, along the minimising
geodesic `γ` from `y` in such a direction `u` (which reaches `p` at time `r = d(y,p)`) we have
`d(p, γ t) = r - t` for `t ∈ [0,r]` by sub-arc minimality, so the directional derivative of
`rdist p ·` at `y` in the direction `u` is `-1`; since `∇(rdist p ·)` is the Riesz representative
of the derivative, `⟪∇(rdist p ·), u⟫ = -1 < 0`.  (No torsion hypothesis is needed: the only
geometric input is that sub-arcs of a minimising geodesic are minimising.) -/
theorem isAscentAt_rgrad_rdist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {p y : M} (hy : 0 < Work.Diff.C.rdist (I := I) (M := M) p y)
    (hsm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) :
    Submission.GSField.IsAscentAt hmet p y
      (Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) := by
  intro r u hr hu hpG hd
  have hrdist_eq : r = Work.Diff.C.rdist (I := I) (M := M) p y := by
    rw [Work.Diff.C.rdist, Manifold.riemannianEDist_comm, hd, ENNReal.toReal_ofReal hr]
  have hrpos : 0 < r := by rw [hrdist_eq]; exact hy
  let γ : ℝ → M := Submission.GlobalExp.geodCurve (cov := cov) hmet r hr y u hu
  obtain ⟨hG0', hvel', hGsm', hGgeo', hGunit'⟩ :=
    Submission.GlobalExp.geodCurve_spec (cov := cov) hmet r hr y u hu
  have hG0 : γ 0 = y := hG0'
  have hvel : Submission.Geodesic.curveVelocity (I := I) γ 0 = u := hvel'
  have hGsm : ContMDiffOn 𝓘(ℝ) I ∞ γ
      (Set.Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (r + Submission.GlobalExp.geodDelta (cov := cov) hmet)) := hGsm'
  have hGexp : Submission.GlobalExp.GExp (cov := cov) hmet y (r • u) = γ r :=
    Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet (x := y) hu (T := r) hr (r := r) hr le_rfl
  have hGr : γ r = p := hGexp.symm.trans hpG.symm
  have hmin : Manifold.riemannianEDist I y (γ r) = ENNReal.ofReal r := by
    rw [hGr]; exact hd
  have hsub := Submission.HingeKey.geodCurve_sub_arc_minimising' (cov := cov) hmet hr hu hr le_rfl hmin
  have hval : ∀ t ∈ Set.Icc (0:ℝ) r,
      Work.Diff.C.rdist (I := I) (M := M) p (γ t) = r - t := by
    intro t ht
    have h1 : Manifold.riemannianEDist I p (γ t) = ENNReal.ofReal (r - t) := by
      rw [Manifold.riemannianEDist_comm, ← hGr]
      exact hsub t ht r ⟨hr, le_rfl⟩ ht.2
    rw [Work.Diff.C.rdist, h1, ENNReal.toReal_ofReal (by linarith [ht.1, ht.2])]
  have hlineq : (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t))
      =ᶠ[𝓝[Set.Ici (0:ℝ)] 0] (fun t : ℝ => r - t) := by
    have hIio : Set.Iio r ∈ 𝓝[Set.Ici (0:ℝ)] 0 := nhdsWithin_le_nhds (Iio_mem_nhds hrpos)
    filter_upwards [self_mem_nhdsWithin, hIio] with t ht htr
    exact hval t ⟨ht, le_of_lt htr⟩
  have hcpmax : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ,ℝ) ∞
      (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t)) 0 := by
    have hdelta := Submission.GlobalExp.geodDelta_pos (cov := cov) hmet
    have hmem : (0:ℝ) ∈ Set.Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (r + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
      ⟨by linarith, by linarith⟩
    have hGsmAt : ContMDiffAt 𝓘(ℝ) I ∞ γ 0 := hGsm.contMDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hFsmAt : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) (γ 0) := by
      rw [hG0]; exact hsm
    exact ContMDiffAt.comp (f := γ)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) (0:ℝ) hFsmAt hGsmAt
  have hderiv : deriv (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t)) 0 = -1 := by
    have hdiff : DifferentiableAt ℝ
        (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t)) 0 :=
      (hcpmax.mdifferentiableAt (by decide)).differentiableAt
    have hlin : HasDerivWithinAt (fun t : ℝ => r - t) (-1) (Set.Ici 0) 0 := by
      have h := (hasDerivWithinAt_const (0:ℝ) (Set.Ici 0) r).sub
        (hasDerivWithinAt_id (0:ℝ) (Set.Ici 0))
      convert h using 1
      · ext t; simp
      · norm_num
    have h0 : (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t)) 0 = r - 0 := by
      show Work.Diff.C.rdist (I := I) (M := M) p (γ 0) = r - 0
      rw [hG0, ← hrdist_eq]
      norm_num
    have hGW : HasDerivWithinAt (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t))
        (-1) (Set.Ici 0) 0 := hlin.congr_of_eventuallyEq hlineq h0
    have h1 := hGW.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h2 := hdiff.derivWithin (uniqueDiffWithinAt_Ici 0)
    rw [h2] at h1
    exact h1
  have hmvf : mvfderiv I (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y u = -1 := by
    have hdelta := Submission.GlobalExp.geodDelta_pos (cov := cov) hmet
    have hmem : (0:ℝ) ∈ Set.Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
        (r + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
      ⟨by linarith, by linarith⟩
    have hγdiff : MDifferentiableAt 𝓘(ℝ) I γ 0 :=
      (hGsm.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).mdifferentiableAt (by decide)
    have hFdiff : MDifferentiableAt I 𝓘(ℝ,ℝ)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) (γ 0) := by
      rw [hG0]; exact hsm.mdifferentiableAt (by decide)
    have hcomp := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) (γ := γ) (t := 0) hFdiff hγdiff
    rw [← Submission.Geodesic.curveVelocity_apply (I := I) γ 0] at hcomp
    rw [hvel] at hcomp
    rw [hG0] at hcomp
    have : deriv ((fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) ∘ γ) 0
        = deriv (fun t : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (γ t)) 0 := rfl
    rw [this, hderiv] at hcomp
    exact hcomp
  rw [Work.Diff.C.inner_rgrad]
  show mvfderiv I (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y u < 0
  rw [hmvf]
  norm_num

/-- **The gradient of the distance function is smooth, unit and an ascent direction**, inside the
ball in which the exponential map at `p` is a diffeomorphism (witnessed by a smooth `Φp` with
`GExp p (Φp y) = y` and `rdist p y = ‖Φp y‖` near `p`).

Conclusion: for `y` near `p` with `0 < rdist p y`, the function `rdist p ·` is smooth at `y`, its
gradient has norm `1` (eikonal), and the gradient is an ascent direction for `d(p,·)` in the sense
of `Submission.GSField.IsAscentAt`: every shortest unit direction from `y` to `p` makes an obtuse
angle with it. -/
theorem rgrad_rdist_ascent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p : M} {Φp : M → TangentSpace I p}
    (hsm : ∀ᶠ y in 𝓝 p, ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y)
    (hinv : ∀ᶠ y in 𝓝 p, Submission.GlobalExp.GExp (cov := cov) hmet p (Φp y) = y)
    (hdist : ∀ᶠ y in 𝓝 p, Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖) :
    ∀ᶠ y in 𝓝 p, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y ∧
      Inner.inner ℝ
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y)
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) = 1 ∧
      Submission.GSField.IsAscentAt hmet p y
        (Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) := by
  classical
  have hP : ∀ᶠ y in 𝓝 p, ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y ∧
      Submission.GlobalExp.GExp (cov := cov) hmet p (Φp y) = y ∧
      Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖ := hsm.and (hinv.and hdist)
  obtain ⟨s, hs, hPs⟩ := hP.exists_mem
  obtain ⟨V, hVsub, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hs
  refine Filter.mem_of_superset (hVopen.mem_nhds hpV) ?_
  intro y hy hypos
  obtain ⟨hysm, hyinv, hydist⟩ := hPs y (hVsub hy)
  have hVmem : V ∈ 𝓝 y := hVopen.mem_nhds hy
  have hPhi_ne : Φp y ≠ 0 := by
    have : 0 < ‖Φp y‖ := by rw [← hydist]; exact hypos
    exact norm_pos_iff.mp this
  have hevdist : (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) =ᶠ[𝓝 y] (fun z => ‖Φp z‖) :=
    Filter.eventually_of_mem hVmem (fun z hz => (hPs z (hVsub hz)).2.2)
  have hnormsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => ‖Φp z‖) y :=
    (contDiffAt_norm ℝ hPhi_ne).comp_contMDiffAt hysm
  have hsm_rdist : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y :=
    (hevdist.contMDiffAt_iff).mpr hnormsm
  refine ⟨hsm_rdist, ?_, ?_⟩
  · exact Work.Diff.C.rgrad_rdist_eikonal (cov := cov) hmet htor (q := p) (x := y)
      (ne_of_gt hypos) hsm_rdist
  · exact isAscentAt_rgrad_rdist (cov := cov) hmet hypos hsm_rdist

end Work.Diff.Dim2
