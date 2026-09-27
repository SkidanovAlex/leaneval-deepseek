import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.ChartBridge

/-!
# The loop and sweep of the germ-route Sard statement

`Submission/Work/Drive/sideGerm_good_exists.lean` asks, for an abstract chart `Q` and an abstract
chart perturbation `Ξ` (`Work.Drive.ChartPert Q m Ξ`), for parameters `t` of arbitrarily small norm
at which the perturbed pair `(Ξ t.1 ∘ Q, w ↦ rotCapping w (Ξ t.2 ∘ Q))` is a `GoodPair`.

This module fixes the two *concrete* maps whose Sard analysis is the content.  Only the **loop's**
chart is perturbed (the sweep stays the unperturbed rotated chart of `Q`):

* `Work.Drive.sgLoop Ξ Q t` — the degenerate **two**-parameter presentation of the core loop of the
  perturbed chart `Ξ t ∘ Q`, `u ↦ coreLoop (Ξ t ∘ Q) (u 0)`: the second coordinate is a *dummy* that
  the map does not see, which is exactly what lets the (2,3)-charted difference machinery
  (`Work.Drive.chartDiff` + `Work.Drive.chartDiff_surjective_iff_range_sup_eq_top`) be used for a
  loop that has only *one* genuine parameter.
* `Work.Drive.sgSweep0 Q c w` — the *fixed* chain: the clamped sweep (cut-off `fun s => 1 - s`,
  level `c`) of the disk presentation of the rotated chart `z ↦ rotCapping w (Q z)`.

Why the *loop* side and not the sweep side: the parameter-derivative of the charted difference system
`z ↦ chartDiff p (sgLoop Ξ Q t) (sgSweep0 Q c w) z` with respect to `t` is the `t`-derivative of the
charted loop value, which `ChartPert` makes *onto everywhere* (`hsurj_sgLoop`); on the sweep side it
would fail at the face `x 2 = 0` of the chain's cube, where `clampScale` collapses the family onto the
level `c` (so that the derivative has rank `≤ 3`).

At `Ξ 0 = id` the pair is `(Q's loop, the sweep of rotCapping w ∘ Q)`, i.e. the parameter pair
`(0, t)` of `Work.Drive.GoodAt Ξ Q c w` is `GoodPair Q (rotCapping w ∘ Q) c`, so `GoodAt` at `(t, 0)`
is the statement the germ route needs.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The loop family**: the degenerate two-parameter presentation of the core loop of the perturbed
chart `Ξ t ∘ Q`.  The second coordinate is a dummy that the map ignores. -/
def sgLoop {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun u => coreLoop (fun z => Ξ t (Q z)) (u 0)

lemma sgLoop_apply {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (u : EuclideanSpace ℝ (Fin 2)) :
    sgLoop Ξ Q t u = coreLoop (fun z => Ξ t (Q z)) (u 0) := rfl

/-- **The fixed chain**: the clamped sweep of the disk presentation of the rotated chart. -/
def sgSweep0 (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) :
    EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  clampedSweep c (fun s => 1 - s) (diskPlane (fun z => rotCapping w (Q z)))

lemma sgSweep0_apply (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (x : EuclideanSpace ℝ (Fin 3)) :
    sgSweep0 Q c w x = clampedSweep c (fun s => 1 - s)
      (diskPlane (fun z => rotCapping w (Q z))) x := rfl


/-! ## Smoothness of the loop family -/

namespace sgAux

open scoped Manifold ContDiff Topology

/-- The exponential parametrisation of the core loop, as a map of the square block. -/
def loopPt (u : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * ((u 0 : ℝ) : ℂ) * Complex.I)

lemma contMDiff_loopPt : ContMDiff (𝓡 2) (𝓘(ℝ,ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞) loopPt := by
  rw [contMDiff_iff_contDiff]
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) =>
    Complex.exp ((Real.pi : ℂ) * Complex.ofRealCLM (u 0) * Complex.I))
  fun_prop

end sgAux

theorem contMDiff_sgLoop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) :
    ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        sgLoop Ξ Q q.1 q.2) := by
  have hfst : ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => q.1) := contMDiff_fst
  have hQ2 : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => Q (sgAux.loopPt u)) :=
    hQ.comp sgAux.contMDiff_loopPt
  have hpair : ContMDiff ((𝓡 m).prod (𝓡 2)) ((𝓡 m).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        (q.1, Q (sgAux.loopPt q.2))) :=
    hfst.prodMk (hQ2.comp contMDiff_snd)
  have hcomp := hΞ.2.1.comp hpair
  simpa [sgLoop, coreLoop, sgAux.loopPt, Function.comp_def] using hcomp



/-! ## The parameter-derivative of the charted loop family is onto -/

/-- **The charted `t`-derivative of the loop family is onto**, at every parameter and every point of
the square block, whenever the value lies in the chart's source: the content is that the composite of
the chart (a local diffeomorphism) with the submersion `t ↦ Ξ t p` (`ChartPert`'s third conjunct) is
onto.  This is the `hsurj` hypothesis of the parametric Sard bricks for the system
`z ↦ chartDiff p (sgLoop Ξ Q t) (sgSweep0 Q c w) z`, whose `t`-derivative is exactly the map below. -/
theorem hsurj_sgLoop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace)
    (hΞ : ChartPert Q m Ξ) (_hQ : IsSmoothChart Q) :
    ∀ (p : CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (u : EuclideanSpace ℝ (Fin 2)),
      pertChart Ξ Q t (Complex.exp ((Real.pi : ℂ) * ((u 0 : ℝ) : ℂ) * Complex.I))
        ∈ (chr p).source →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (pertChart Ξ Q t'
          (Complex.exp ((Real.pi : ℂ) * ((u 0 : ℝ) : ℂ) * Complex.I)))) t) := by
  intro p t u hsrc
  set z₀ : ℂ := Complex.exp ((Real.pi : ℂ) * ((u 0 : ℝ) : ℂ) * Complex.I) with hz₀
  set f : EuclideanSpace ℝ (Fin m) → CappingSpace := fun t' => Ξ t' (Q z₀) with hf
  have hf_eq : ∀ t' : EuclideanSpace ℝ (Fin m), f t' = pertChart Ξ Q t' z₀ := fun _ => rfl
  have hsm : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
  have hsrc' : f t ∈ (chr p).source := by
    rw [hf_eq t]; exact hsrc
  have hsurj_mf : Function.Surjective (mfderiv (𝓡 m) (𝓡 4) f t) :=
    hΞ.2.2 t (Q z₀)
  have hderiv := fderiv_chart_comp f hsm p hsrc'
  have hfun : (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (pertChart Ξ Q t' z₀)) = (fun t' => chr p (f t')) := by
    funext t'; rw [hf_eq t']
  rw [hfun, hderiv]
  have hsrc1 : f t ∈ (extChartAt (𝓡 4) (f t)).source := mem_extChartAt_source (I := 𝓡 4) (f t)
  have hsrc2 : f t ∈ (extChartAt (𝓡 4) p).source := by
    simpa [chr, extChartAt_source] using hsrc'
  -- the change of coordinates is surjective (it has a right inverse), and `mfderiv f t` is onto
  have hsurjT : Function.Surjective
      (tangentCoordChange (𝓡 4) (f t) p (f t)) := by
    intro w
    exact ⟨tangentCoordChange (𝓡 4) p (f t) (f t) w,
      tangentCoordChange_comp_inv (x := p) (y := f t) (z := f t) ⟨hsrc2, hsrc1⟩ w⟩
  intro w
  obtain ⟨v, hv⟩ := hsurj_mf (tangentCoordChange (𝓡 4) p (f t) (f t) w)
  refine ⟨v, ?_⟩
  show tangentCoordChange (𝓡 4) (f t) p (f t) (mfderiv (𝓡 m) (𝓡 4) f t v) = w
  rw [hv]
  exact tangentCoordChange_comp_inv (x := p) (y := f t) (z := f t) ⟨hsrc2, hsrc1⟩ w

end

end Work.Drive
