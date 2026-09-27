import Mathlib
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Embedding.exists_unique_closest_point

/-!
# An immersion is locally injective

The main result of this file, `Work.Embedding.immersion_locally_injective`, is the classical
fact that a smooth immersion `g : M → ℝ^{2n}` of a smooth `n`-manifold is a local embedding: every
point of `M` has an open neighbourhood on which `g` is injective.

The proof has two steps.

* `Work.Embedding.local_injOn_of_injective_fderiv` is the Euclidean statement: if `ψ : ℝ^n → ℝ^N`
  is smooth near `u₀` and its Fréchet derivative there is injective, then `ψ` is injective on some
  neighbourhood of `u₀`.  Choose a continuous linear left inverse `L` of `A = fderiv ℝ ψ u₀`
  (`LinearMap.exists_leftInverse_of_injective`, upgraded to a continuous map using finite
  dimensionality).  Then `L ∘ ψ` has invertible derivative `L ∘ A = id` at `u₀`, so by the inverse
  function theorem (`HasStrictFDerivAt.eventually_left_inverse`) it admits a local left inverse near
  `u₀`, and is therefore injective there; composing with `L` shows that `ψ` is injective there too.
* `Work.Embedding.chartRepN_fderiv_injective` re-proves
  `Work.Embedding.injective_fderiv_chartRep` at the *smooth* regularity level `∞` (the latter is
  stated for analytic maps, a stronger hypothesis), by splitting `mfderiv` through the chart
  (`Work.Projection.mfderiv_chartAt_decomp`).
-/

namespace Work.Embedding

open scoped Manifold ContDiff
open Filter Topology Set

/-- **Local injectivity of a smooth map with injective derivative.**  If `ψ : ℝ^n → ℝ^N` is `C^∞`
on an open set `V` containing `u₀` and `fderiv ℝ ψ u₀` is injective, then `ψ` is injective on some
open neighbourhood of `u₀`. -/
theorem local_injOn_of_injective_fderiv {n N : ℕ}
    {ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)}
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {u₀ : EuclideanSpace ℝ (Fin n)} (hu₀ : u₀ ∈ V)
    (hψ : ContDiffOn ℝ ∞ ψ V)
    (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ u₀ ∈ W ∧ Set.InjOn ψ W := by
  classical
  set A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) := fderiv ℝ ψ u₀ with hA
  -- a continuous linear left inverse `G` of `A`
  have hker : LinearMap.ker A.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := A.toLinearMap.exists_leftInverse_of_injective hker
  let G : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearMap.toContinuousLinearMap g
  have hGA : G ∘L A = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hg v
    simpa [G] using hv
  have hnz : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hψat : ContDiffAt ℝ ∞ ψ u₀ := hψ.contDiffAt (hV.mem_nhds hu₀)
  have hΨcont : ContDiffAt ℝ ∞ (fun u => G (ψ u)) u₀ :=
    G.contDiff.contDiffAt.comp u₀ hψat
  have hΨderiv : HasFDerivAt (fun u => G (ψ u)) (G ∘L A) u₀ :=
    HasFDerivAt.comp u₀ (G.hasFDerivAt (x := ψ u₀)) (hψat.differentiableAt hnz |>.hasFDerivAt)
  have hΨderiv' : HasFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) u₀ := by
    have h := hΨderiv.congr_fderiv hGA
    simpa [ContinuousLinearEquiv.coe_refl] using h
  have hS : HasStrictFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) u₀ :=
    hΨcont.hasStrictFDerivAt' hΨderiv' hnz
  -- the inverse function theorem: `G ∘ ψ` has a local left inverse at `u₀`, hence is locally
  -- injective there
  obtain ⟨S, hSmem, hSinj⟩ := Filter.eventually_iff_exists_mem.mp hS.eventually_left_inverse
  obtain ⟨W, hWsub, hWopen, hu₀W⟩ := mem_nhds_iff.mp hSmem
  refine ⟨W, hWopen, hu₀W, ?_⟩
  intro a ha b hb hab
  have h1 := hSinj a (hWsub ha)
  have h2 := hSinj b (hWsub hb)
  rw [← h1, ← h2, congrArg G hab]

/-- The chart representation `y ↦ e ((chartAt p).symm y)` of a smooth immersion has injective
Fréchet derivative at every point of the chart target.  This is the smooth (rather than analytic)
version of `Work.Embedding.injective_fderiv_chartRep`. -/
theorem chartRepN_fderiv_injective {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (himm : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x))
    (p : M) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    Function.Injective (fderiv ℝ (chartRepN e p) u) := by
  -- the point of `M` of which `u` are the chart coordinates, and the chain rule
  have hxsrc : (chartAt (EuclideanSpace ℝ (Fin n)) p).symm u ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).map_target hu
  have hxmap : (chartAt (EuclideanSpace ℝ (Fin n)) p)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u) = u :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).right_inv hu
  have hdec := Work.Projection.mfderiv_chartAt_decomp e he p
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u) hxsrc
  rw [hxmap] at hdec
  -- the manifold derivative of the chart is surjective, being the derivative of a diffeomorphism
  have hsurj : Function.Surjective
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)) :=
    (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_surjective hxsrc
  intro a b hab
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  refine congrArg (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)) (himm _ ?_)
  rw [hdec]
  exact hab

/-- A smooth map `g : M → ℝ^{2n}` whose derivative is injective at every point (an immersion) is
locally injective: every point has an open neighbourhood on which `g` is injective. -/
theorem immersion_locally_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : M → EuclideanSpace ℝ (Fin (2*n)))
    (hg : ContMDiff (𝓡 n) (𝓡 (2*n)) ∞ g)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n)) g x)) :
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn g U := by
  intro x
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) x with hφ
  have htarget : φ x ∈ φ.target := φ.map_source (mem_chart_source (EuclideanSpace ℝ (Fin n)) x)
  have hsm : ContDiffOn ℝ ∞ (chartRepN g x) φ.target := (contMDiffOn_chartRepN g hg x).contDiffOn
  have hinj : Function.Injective (fderiv ℝ (chartRepN g x) (φ x)) :=
    chartRepN_fderiv_injective g hg himm x htarget
  obtain ⟨W, hWopen, hWmem, hWinj⟩ :=
    local_injOn_of_injective_fderiv φ.open_target htarget hsm hinj
  refine ⟨φ.source ∩ φ ⁻¹' W, φ.isOpen_inter_preimage hWopen,
    ⟨mem_chart_source (EuclideanSpace ℝ (Fin n)) x, hWmem⟩, ?_⟩
  intro a ha b hb hab
  have heq : chartRepN g x (φ a) = chartRepN g x (φ b) := by
    rw [chartRepN_chart g x a ha.1, chartRepN_chart g x b hb.1, hab]
  exact φ.injOn ha.1 hb.1 (hWinj ha.2 hb.2 heq)

end Work.Embedding
