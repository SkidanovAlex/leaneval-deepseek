import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.Euclidean.TangentField.Setup

/-!
# Tangency of curves in a locally-graph predicate

`Work.ManifoldParity.curve_tangent_chart` requires the curve to take all its values in `K`.  For the
`P`-form of the target theorem the curve only lies in the graph *near* the point, and the graph
condition is stated for the *predicate* `P`.  This file records that local form, and derives from it
that **the chart tangent is intrinsic**: two `P`-charts at the same point give parallel chart
tangents.
-/

namespace Work.Euclidean.TangentField

open scoped ContDiff Topology Manifold
open Set Manifold

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- **A curve which lies in a graph near a point is tangent to that graph.**  This is
`Work.ManifoldParity.curve_tangent_chart` with the global hypothesis `∀ s, γ s ∈ A` weakened to
`∀ᶠ s in 𝓝 t, A (γ s)` and with the graph condition stated for a *predicate* `A`. -/
theorem fderiv_eq_smul_chartField_of_eventually {A : EuclideanSpace ℝ (Fin n) → Prop}
    (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
    (hUo : IsOpen U) (hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hηi : ∀ t, η t i = 0)
    (hgr : ∀ y ∈ U, (A y ↔ y = Work.ManifoldParity.gmap i η (y i)))
    (γ : ℝ → EuclideanSpace ℝ (Fin n)) (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ) {t : ℝ}
    (hγA : ∀ᶠ s in 𝓝 t, A (γ s)) (hγU : γ t ∈ U) (hvel : fderiv ℝ γ t 1 ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧
      fderiv ℝ γ t 1
        = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (γ t i)) (1:ℝ)) := by
  have hγc : Continuous γ := hγ.continuous
  have hγd : DifferentiableAt ℝ γ t := (hγ.contDiffAt).differentiableAt (by simp)
  have hηd : DifferentiableAt ℝ η (γ t i) :=
    (hηsm.contDiffAt).differentiableAt (by simp)
  have hev : ∀ᶠ s in 𝓝 t, γ s = Work.ManifoldParity.gmap i η ((γ s) i) := by
    have h1 : ∀ᶠ s in 𝓝 t, γ s ∈ U := hγc.continuousAt (hUo.mem_nhds hγU)
    filter_upwards [hγA, h1] with s hA hU
    exact (hgr (γ s) hU).mp hA
  set ℓ : ℝ → ℝ := fun s => (γ s) i with hℓ
  have hℓd : DifferentiableAt ℝ ℓ t := by
    have h := (PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp t hγd.hasFDerivAt
    exact h.differentiableAt
  have hchain : HasFDerivAt (fun s => Work.ManifoldParity.gmap i η (ℓ s))
      ((fderiv ℝ (Work.ManifoldParity.gmap i η) (ℓ t)).comp (fderiv ℝ ℓ t)) t := by
    have h := (Work.ManifoldParity.hasFDerivAt_gmap i η (ℓ t) hηd.hasFDerivAt).comp t
      hℓd.hasFDerivAt
    rw [Function.comp_def] at h
    rw [← (Work.ManifoldParity.hasFDerivAt_gmap i η (ℓ t) hηd.hasFDerivAt).fderiv] at h
    exact h
  have heq : fderiv ℝ γ t
      = (fderiv ℝ (Work.ManifoldParity.gmap i η) (ℓ t)).comp (fderiv ℝ ℓ t) := by
    rw [← hchain.fderiv]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hev] with s hs
    simp only [hℓ]
    exact hs
  refine ⟨fderiv ℝ ℓ t 1, ?_, ?_⟩
  · intro hc
    have hzero : fderiv ℝ γ t 1 = 0 := by rw [heq]; simp [hc]
    exact hvel hzero
  · rw [heq]
    simp only [ContinuousLinearMap.comp_apply]
    have hsmul : fderiv ℝ (Work.ManifoldParity.gmap i η) (ℓ t) ((fderiv ℝ ℓ t) 1)
        = ((fderiv ℝ ℓ t) 1) • (fderiv ℝ (Work.ManifoldParity.gmap i η) (ℓ t) (1 : ℝ)) := by
      conv_lhs => rw [show (fderiv ℝ ℓ t) 1 = ((fderiv ℝ ℓ t) 1) • (1 : ℝ) from by simp]
      rw [map_smul]
    rw [hsmul, Work.ManifoldParity.fderiv_gmap i η (ℓ t) hηd.hasFDerivAt]

/-- **The chart tangent is intrinsic.**  If two `P`-charts at a point `x` with `P x` both present
`P` as a graph, then their chart tangents at `x` are non-zero multiples of one another. -/
theorem chartField_parallel_of_PCharts {P : EuclideanSpace ℝ (Fin n) → Prop}
    (p : PChart P) (q : PChart P) {x : EuclideanSpace ℝ (Fin n)} (hx : P x)
    (hxp : x ∈ p.U) (hxq : x ∈ q.U) :
    ∃ c : ℝ, c ≠ 0 ∧
      (EuclideanSpace.single p.i (1:ℝ) + (fderiv ℝ p.η (x p.i)) (1:ℝ))
        = c • (EuclideanSpace.single q.i (1:ℝ) + (fderiv ℝ q.η (x q.i)) (1:ℝ)) := by
  -- the graph curve of `p` through `x`
  have hxeq : x = p.gmap (x p.i) := p.eq_gmap hxp hx
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := p.gmap with hγ
  have hγsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ :=
    Work.ManifoldParity.contDiff_gmap p.hη
  -- near `x p.i`, `γ` lies in `P`
  have hγP : ∀ᶠ s in 𝓝 (x p.i), P (γ s) := by
    have h1 : ∀ᶠ s in 𝓝 (x p.i), γ s ∈ p.U :=
      hγsm.continuous.continuousAt (p.hU.mem_nhds (by rw [← hxeq]; exact hxp))
    filter_upwards [h1] with s hs
    exact p.gmap_mem hs
  -- the velocity of `γ` at `x p.i` is the chart tangent of `p` at `x`
  have hηpd : DifferentiableAt ℝ p.η (x p.i) := (p.hη.contDiffAt).differentiableAt (by simp)
  have hvel : fderiv ℝ γ (x p.i) 1 =
      EuclideanSpace.single p.i (1:ℝ) + (fderiv ℝ p.η (x p.i)) (1:ℝ) := by
    rw [hγ]
    exact Work.ManifoldParity.fderiv_gmap p.i p.η (x p.i) hηpd.hasFDerivAt
  have hcoord : ((fderiv ℝ p.η (x p.i)) (1:ℝ)) p.i = 0 := by
    have h1 : HasFDerivAt (Work.ManifoldParity.coordProj p.i ∘ p.η)
        (((Work.ManifoldParity.coordProj p.i).comp (fderiv ℝ p.η (x p.i))) :
          ℝ →L[ℝ] ℝ) (x p.i) :=
      HasFDerivAt.comp (x p.i)
        (ContinuousLinearMap.hasFDerivAt (Work.ManifoldParity.coordProj p.i)
          (x := p.η (x p.i))) hηpd.hasFDerivAt
    have h2 : HasFDerivAt (Work.ManifoldParity.coordProj p.i ∘ p.η)
        (0 : ℝ →L[ℝ] ℝ) (x p.i) := by
      have hconst : (Work.ManifoldParity.coordProj p.i ∘ p.η) = fun _ : ℝ => (0:ℝ) :=
        funext p.hη0
      rw [hconst]
      exact hasFDerivAt_const (0:ℝ) (x p.i)
    have h3 : ((Work.ManifoldParity.coordProj p.i).comp (fderiv ℝ p.η (x p.i))) = 0 :=
      h1.unique h2
    have h4 := congrArg (fun (L : ℝ →L[ℝ] ℝ) => L (1:ℝ)) h3
    simpa using h4
  have hvelne : fderiv ℝ γ (x p.i) 1 ≠ 0 := by
    rw [hvel]
    intro h0
    have h5 : (EuclideanSpace.single p.i (1:ℝ) + (fderiv ℝ p.η (x p.i)) (1:ℝ)) p.i = 0 := by
      rw [h0]; simp
    rw [PiLp.add_apply, PiLp.single_apply, hcoord, add_zero] at h5
    simp at h5
  -- apply the local tangency with the chart `q`
  have hxq' : γ (x p.i) ∈ q.U := by
    rw [show γ (x p.i) = x from hxeq.symm]
    exact hxq
  obtain ⟨c, hc, hcq⟩ := fderiv_eq_smul_chartField_of_eventually q.i q.U q.η q.hU q.hη q.hη0
    q.hgraph γ hγsm hγP hxq' hvelne
  refine ⟨c, hc, ?_⟩
  rw [← hvel, hcq, show γ (x p.i) = x from hxeq.symm]

end

end Work.Euclidean.TangentField
