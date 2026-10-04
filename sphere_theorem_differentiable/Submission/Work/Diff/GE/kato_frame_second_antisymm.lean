import Mathlib
import Submission.Diff.Interfaces
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false

/-- A function on a manifold which is eventually equal to a constant near a point has vanishing
`mvfderiv` there.  (Mathlib only has the `mfderiv` version, `Filter.EventuallyEq.mfderiv_eq`.) -/
private lemma mvfderiv_eq_zero_of_eventuallyEq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {c : F} {x : M} (h : f =ᶠ[𝓝 x] fun _ => c) : d% f x = 0 := by
  have hmf : mfderiv I (𝓘(ℝ, F)) f x = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq (f₁ := f) (f := fun _ => c) h, mfderiv_const]
    ext v
    simp
  rw [show d% f x = (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
      (mfderiv I (𝓘(ℝ, F)) f x) from rfl, hmf, ContinuousLinearMap.comp_zero]

/-- `mvfderiv` only depends on the germ of the function. -/
private lemma mvfderiv_congr_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : M → F} {x : M} (h : f =ᶠ[𝓝 x] g) : d% f x = d% g x := by
  have h1 : mfderiv I (𝓘(ℝ, F)) f x
      = (↑(tangentSpaceCast 𝓘(ℝ, F) (g x) (f x))) ∘SL mfderiv I (𝓘(ℝ, F)) g x :=
    Filter.EventuallyEq.mfderiv_eq (f := g) (f₁ := f) h
  rw [show d% f x = (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
        (mfderiv I (𝓘(ℝ, F)) f x) from rfl,
      show d% g x = (NormedSpace.fromTangentSpace (g x)).toContinuousLinearMap ∘L
        (mfderiv I (𝓘(ℝ, F)) g x) from rfl, h1]
  ext v
  rfl

/-- **Antisymmetry of the second derivative of a geodesic orthonormal frame.**  If the smooth fields
`W i` are orthonormal for `g` near `x` and geodesic at `x` (`∇_{W m x} W j = 0` for all `m j`), then the
vectors `Aᵐ_γ := ∇_{W m x}(∇_{W m} W γ)` at `x` are antisymmetric when paired with the frame:
`⟨Aᵐ_γ, W β x⟩ = -⟨Aᵐ_β, W γ x⟩` for all `m γ β`.  Proof: for the metric-compatible `lcOf g` one has
`X ⟨∇_X W γ, W β⟩ = ⟨Aᵐ_γ, W β⟩ + ⟨∇_X W γ, ∇_X W β⟩` on the one hand and, using
`⟨W γ, W β⟩ = const` near `x`, `= -X ⟨W γ, ∇_X W β⟩ = -⟨∇_X W γ, ∇_X W β⟩ - ⟨W γ, Aᵐ_β⟩` on the other;
at `x` the middle products vanish by the geodesic condition. -/
theorem kato_frame_second_antisymm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (x : M) (hW : ∀ i, CMDiff ∞ (T% (W i)))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y))
    (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0) :
    ∀ m γ β, g.inner x (lcOf g (fun p : M ↦ lcOf g (W γ) p (W m p)) x (W m x)) (W β x)
      = - g.inner x (lcOf g (fun p : M ↦ lcOf g (W β) p (W m p)) x (W m x)) (W γ x) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcovne, -, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcovne
  -- the open neighbourhood of `x` on which the frame is orthonormal
  obtain ⟨V, hVmem, hVeq⟩ := Filter.eventually_iff_exists_mem.mp hON
  obtain ⟨U, hUV, hUopen, hxU⟩ := mem_nhds_iff.mp hVmem
  intro m γ β
  -- the fields appearing in the statement
  let X : Π y : M, TangentSpace I y := W m
  let Y : Π y : M, TangentSpace I y := W γ
  let Z : Π y : M, TangentSpace I y := W β
  let S : Π y : M, TangentSpace I y := fun p => lcOf g Y p (X p)
  let T : Π y : M, TangentSpace I y := fun p => lcOf g Z p (X p)
  let S' : Π y : M, TangentSpace I y := fun p => lcOf g S p (X p)
  let T' : Π y : M, TangentSpace I y := fun p => lcOf g T p (X p)
  let φ : M → ℝ := fun p => inner ℝ (S p) (Z p)
  let ψ : M → ℝ := fun p => inner ℝ (Y p) (T p)
  -- the geodesic condition at `x`
  have hzeroS : S x = 0 := hgeo m γ
  have hzeroT : T x = 0 := hgeo m β
  -- smoothness of the fields
  have hX_sm : CMDiff ∞ (T% X) := by simpa only [X] using hW m
  have hY_sm : CMDiff ∞ (T% Y) := by simpa only [Y] using hW γ
  have hZ_sm : CMDiff ∞ (T% Z) := by simpa only [Z] using hW β
  have hS_sm : CMDiff ∞ (T% S) := by
    simpa only [S, X, Y] using
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply (lcOf g) hcov
        (Z := W γ) (Y := W m) (hW γ) (hW m)
  have hT_sm : CMDiff ∞ (T% T) := by
    simpa only [T, X, Z] using
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply (lcOf g) hcov
        (Z := W β) (Y := W m) (hW β) (hW m)
  -- (1) metric compatibility: the first derivative of the pairing of the two frame fields
  have hmetpair : ∀ y : M, mvfderiv I (fun p : M => inner ℝ (Y p) (Z p)) y (X y)
      = inner ℝ (S y) (Z y) + inner ℝ (Y y) (T y) := by
    intro y
    simpa only [S, T, X, Y, Z] using hmet Y Z hY_sm hZ_sm y (X y)
  -- (2) the pairing `⟨W γ, W β⟩` is constant near `x`, so its derivative vanishes there
  have hpair_ev : ∀ᶠ y in 𝓝 x, mvfderiv I (fun p : M => inner ℝ (Y p) (Z p)) y (X y) = 0 := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    have hev : (fun p : M => inner ℝ (Y p) (Z p))
        =ᶠ[𝓝 y] fun _ : M => (if γ = β then (1 : ℝ) else 0) := by
      filter_upwards [hUopen.mem_nhds hy] with q hq
      have hf := hVeq q (hUV hq)
      simp only [IsONFrame] at hf
      exact hf γ β
    rw [mvfderiv_eq_zero_of_eventuallyEq_const hev]
    simp
  -- (3) hence `φ + ψ` vanishes identically near `x`
  have hpoint : (φ + ψ) =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [hpair_ev] with y hy
    have h1 : (φ + ψ) y = mvfderiv I (fun p : M => inner ℝ (Y p) (Z p)) y (X y) := by
      rw [show (φ + ψ) y = inner ℝ (S y) (Z y) + inner ℝ (Y y) (T y) by
        simp only [Pi.add_apply, φ, ψ]]
      exact (hmetpair y).symm
    rw [h1, hy]
  -- (4) hence `φ = -ψ` near `x`, and therefore the same for the derivatives
  have hneg : φ =ᶠ[𝓝 x] (-ψ) := by
    filter_upwards [hpoint] with y hy
    have hy' : φ y + ψ y = 0 := hy
    exact eq_neg_of_add_eq_zero_left hy'
  have hdφ : d% φ x = -(d% ψ x) := by
    rw [mvfderiv_congr_eventuallyEq hneg, mvfderiv_neg]
  -- (5) the two first-order products, by metric compatibility at `x`
  have hφ_deriv : (d% φ x) (X x) = inner ℝ (S' x) (Z x) := by
    simpa only [φ, S', hzeroS, inner_zero_left, add_zero] using hmet S Z hS_sm hZ_sm x (X x)
  have hψ_deriv : (d% ψ x) (X x) = inner ℝ (Y x) (T' x) := by
    simpa only [ψ, T', hzeroT, inner_zero_right, zero_add] using hmet Y T hY_sm hT_sm x (X x)
  -- (6) assemble
  have hkey : inner ℝ (S' x) (Z x) + inner ℝ (Y x) (T' x) = 0 := by
    have h1 : (d% φ x) (X x) = -((d% ψ x) (X x)) := by
      simpa using congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L (X x)) hdφ
    rw [hφ_deriv, hψ_deriv] at h1
    linarith
  have hconv : ∀ a b : TangentSpace I x, inner ℝ a b = g.inner x a b := fun _ _ => rfl
  have hkey' : g.inner x (S' x) (Z x) + g.inner x (T' x) (Y x) = 0 := by
    have hcomm : inner ℝ (Y x) (T' x) = inner ℝ (T' x) (Y x) := real_inner_comm _ _
    have h1 : inner ℝ (S' x) (Z x) + inner ℝ (T' x) (Y x) = 0 := by rw [← hcomm]; exact hkey
    rwa [hconv (S' x) (Z x), hconv (T' x) (Y x)] at h1
  show g.inner x (S' x) (Z x) = -g.inner x (T' x) (Y x)
  linarith [hkey']

end Work.Diff.GE
