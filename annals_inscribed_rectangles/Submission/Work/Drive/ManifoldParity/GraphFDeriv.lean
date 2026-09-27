import Mathlib
import Submission.Work.Drive.ManifoldParity.GraphMap
import Submission.Work.Drive.exists_local_normalForm

/-!
# The derivative of the graph map, and the tangency identity along a graph

Let `ψ : ℝ^{m+1} → ℝ^m` be smooth and let `K = ψ⁻¹(0)` be, near a point, the graph
`u ↦ u • eᵢ + η u` of a map `η` over the `i`-th coordinate.  Then any vector `v ∈ ker (fderiv ψ y)`
at a graph point `y = graphMap i η u` is tangent to the graph, i.e. of the form
`fderiv (graphMap i η) u w` — and taking `i`-th coordinates gives `w = v i`, so

`v = fderiv ℝ (graphMap i η) u (v i)`.

This is the content of `eq_fderiv_graphMap_of_fderiv_eq_zero`.  The dimension count
`ker (fderiv ψ y) = range (fderiv (graphMap i η) u)` uses that `fderiv ψ y` is surjective (the
transversality hypothesis) and that `fderiv (graphMap i η) u` is injective: the coordinate
functional `x ↦ x i` inverts the graph map, so `(fderiv (graphMap i η) u w) i = w`.
-/

namespace Work.Drive.ManifoldParity

open Set Filter
open scoped Topology

noncomputable section

variable {m : ℕ}

/-- The derivative of the graph map. -/
theorem hasFDerivAt_graphMap {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} {u : ℝ}
    (hη : HasFDerivAt η (fderiv ℝ η u) u) :
    HasFDerivAt (graphMap i η)
      ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))) +
        fderiv ℝ η u) u := by
  have h1 : HasFDerivAt (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ))
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))) u := by
    have h := (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt (x := u)
    have hfun : (⇑(ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single i (1 : ℝ)))) = fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ) := by
      ext t
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    rwa [hfun] at h
  rw [show graphMap i η = fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ) + η t from rfl]
  exact h1.add hη

/-- The `i`-th coordinate functional inverts the graph map; differentiating,
`(fderiv (graphMap i η) u w) i = w`. -/
theorem fderiv_graphMap_apply_i {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} {u w : ℝ}
    (hη : DifferentiableAt ℝ η u) (hηi : ∀ t, η t i = 0) :
    (fderiv ℝ (graphMap i η) u w) i = w := by
  have hgd : DifferentiableAt ℝ (graphMap i η) u := differentiableAt_graphMap hη
  have hcomp : HasFDerivAt (fun t : ℝ => (graphMap i η t) i)
      ((Work.Drive.coordL i).comp (fderiv ℝ (graphMap i η) u)) u :=
    (Work.Drive.coordL_hasFDerivAt (m := m) i (graphMap i η u)).comp u hgd.hasFDerivAt
  have hid : (fun t : ℝ => (graphMap i η t) i) = fun t : ℝ => t := funext (graphMap_apply_i hηi)
  have hf : (ContinuousLinearMap.id ℝ ℝ) =
      (Work.Drive.coordL i).comp (fderiv ℝ (graphMap i η) u) := by
    have := hcomp.fderiv
    rw [hid] at this
    simpa using this
  have h1 : (Work.Drive.coordL i) ((fderiv ℝ (graphMap i η) u) w) = w := by
    have := congrArg (fun (f : ℝ →L[ℝ] ℝ) => f w) hf
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using this.symm
  simpa [Work.Drive.coordL_apply] using h1

/-- The derivative of the graph map is injective. -/
theorem injective_fderiv_graphMap {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} {u : ℝ}
    (hη : DifferentiableAt ℝ η u) (hηi : ∀ u, η u i = 0) :
    Function.Injective (fderiv ℝ (graphMap i η) u) := by
  intro w w' hww'
  have := congrArg (fun x : Work.Drive.Amb m => x i) hww'
  rwa [fderiv_graphMap_apply_i hη hηi, fderiv_graphMap_apply_i hη hηi] at this

/-- **The tangency identity along a graph.**  Let `g = graphMap i η` be the graph over the `i`-th
coordinate of the zero set of `ψ` near `g u₀` (i.e. `ψ` vanishes on `g` near `u₀`), let `ψ` be
differentiable at `g u₀` with surjective derivative there, and let `v ∈ ker (fderiv ψ (g u₀))`.  Then
`v` is tangent to the graph: `v = fderiv g u₀ (v i)`. -/
theorem eq_fderiv_graphMap_of_fderiv_eq_zero {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m}
    {ψ : Work.Drive.Amb m → Work.Drive.Tgt m} {u₀ : ℝ} {v : Work.Drive.Amb m}
    (hηd : DifferentiableAt ℝ η u₀) (hηi : ∀ u, η u i = 0)
    (hψd : DifferentiableAt ℝ ψ (graphMap i η u₀))
    (hψvan : ∀ᶠ u in 𝓝 u₀, ψ (graphMap i η u) = 0)
    (hsurj : Function.Surjective (fderiv ℝ ψ (graphMap i η u₀)))
    (hv : fderiv ℝ ψ (graphMap i η u₀) v = 0) :
    v = fderiv ℝ (graphMap i η) u₀ (v i) := by
  have hgd : DifferentiableAt ℝ (graphMap i η) u₀ := differentiableAt_graphMap hηd
  -- the chain rule: `A ∘ B = fderiv (ψ ∘ g) u₀ = 0`, because `ψ ∘ g =ᶠ 0`
  have hcomp : HasFDerivAt (ψ ∘ graphMap i η)
      ((fderiv ℝ ψ (graphMap i η u₀)).comp (fderiv ℝ (graphMap i η) u₀)) u₀ :=
    hψd.hasFDerivAt.comp u₀ hgd.hasFDerivAt
  have hzero : fderiv ℝ (ψ ∘ graphMap i η) u₀ = 0 := by
    have hev : (fun u : ℝ => ψ (graphMap i η u)) =ᶠ[𝓝 u₀]
        (fun _ : ℝ => (0 : Work.Drive.Tgt m)) := by
      filter_upwards [hψvan] with u hu
      simpa using hu
    have h1 : fderiv ℝ (fun u : ℝ => ψ (graphMap i η u)) u₀ =
        fderiv ℝ (fun _ : ℝ => (0 : Work.Drive.Tgt m)) u₀ := hev.fderiv_eq
    simpa [Function.comp_def] using h1
  have hAB : (fderiv ℝ ψ (graphMap i η u₀)).comp (fderiv ℝ (graphMap i η) u₀) = 0 := by
    rw [← hcomp.fderiv, hzero]
  -- so `range B ≤ ker A`
  have hle : (fderiv ℝ (graphMap i η) u₀).range ≤ (fderiv ℝ ψ (graphMap i η u₀)).ker := by
    rintro x ⟨w, rfl⟩
    have h1 : (fderiv ℝ ψ (graphMap i η u₀)) ((fderiv ℝ (graphMap i η) u₀) w) = 0 := by
      have := congrArg (fun (f : ℝ →L[ℝ] Work.Drive.Tgt m) => f w) hAB
      simpa [ContinuousLinearMap.comp_apply] using this
    simpa [LinearMap.mem_ker] using h1
  -- both are one-dimensional
  have hfinB : Module.finrank ℝ (fderiv ℝ (graphMap i η) u₀).range = 1 := by
    rw [LinearMap.finrank_range_of_inj (injective_fderiv_graphMap hηd hηi)]
    simp
  have hfinA : Module.finrank ℝ (fderiv ℝ ψ (graphMap i η u₀)).ker = 1 := by
    have hsurjLin : Function.Surjective
        (fderiv ℝ ψ (graphMap i η u₀) : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m) := by
      simpa using hsurj
    have hr : (fderiv ℝ ψ (graphMap i η u₀)).range = ⊤ := LinearMap.range_eq_top.mpr hsurjLin
    have h1 : Module.finrank ℝ (fderiv ℝ ψ (graphMap i η u₀)).range = m := by
      rw [hr, finrank_top]; simp
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℝ ψ (graphMap i η u₀) : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m)
    have h3 : Module.finrank ℝ (Work.Drive.Amb m) = m + 1 := by simp
    omega
  have heq : (fderiv ℝ (graphMap i η) u₀).range = (fderiv ℝ ψ (graphMap i η u₀)).ker :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfinA, hfinB])
  -- conclude
  have hv' : v ∈ (fderiv ℝ (graphMap i η) u₀).range := by rw [heq]; simpa using hv
  obtain ⟨w, hw⟩ := hv'
  have hw' : fderiv ℝ (graphMap i η) u₀ w = v := by simpa using hw
  have hwi : w = v i := by
    have h1 := congrArg (fun x : Work.Drive.Amb m => x i) hw'
    rw [fderiv_graphMap_apply_i (i := i) hηd hηi] at h1
    exact h1
  rw [show v i = w from hwi.symm, ← hw']

end

end Work.Drive.ManifoldParity
