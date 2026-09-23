import Mathlib

namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Bundle
open Filter

/-- **Local-frame expansion at a vanishing vector** (Hausdorff case).  If a smooth vector
field `X` on a Hausdorff manifold vanishes at `x`, then near `x` it is a finite combination
`∑ i, f i • Y i` of smooth *globally defined* vector fields `Y i` with smooth coefficient
functions `f i`, all vanishing at `x`.

Suggested proof: take the trivialization `e := trivializationAt E (TangentSpace I) x`, a
basis `b := Module.finBasis ℝ E` and the associated local frame `e.localFrame b` with
coefficients `e.localFrameCoeff b`.  The frame expansion `e.eventually_eq_localFrame_sum_coeff_smul`
writes `X =ᶠ[nhds x] ∑ i, c i • e.localFrame b i` on `e.baseSet`, with `c i` smooth on
`e.baseSet`.  Pick a smooth bump `ψ` with `ψ =ᶠ[nhds x] 1` and
`tsupport ψ ⊆ e.baseSet` (`SmoothBumpFunction.nhds_basis_tsupport`, using `[T2Space M]`), and
set `f i := ψ * c i`, `Y i := ψ • e.localFrame b i`.  Both are globally `C^∞` (they are zero
outside `tsupport ψ ⊆ e.baseSet`, where the frame and its coefficients are smooth), and
`f i x = c i x = 0` because `X x = 0` and the coefficients are linear in `X x`.
When `finrank ℝ E = 0` the sum is empty and `X =ᶠ 0` since the fibers are trivial. -/
theorem exists_frame_decomposition_of_apply_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {X : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hXx : X x = 0) :
    ∃ (f : Fin (Module.finrank ℝ E) → M → ℝ)
      (Y : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x),
      (∀ i, CMDiff ∞ (f i)) ∧ (∀ i, CMDiff ∞ (T% (Y i))) ∧ (∀ i, f i x = 0) ∧
      (X =ᶠ[nhds x] ∑ i, f i • Y i) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I) → M) :=
    trivializationAt E (TangentSpace I (M := M)) x
  have hxmem : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I (M := M)) x
  have hbase : e.baseSet = (chartAt H x).source := TangentBundle.trivializationAt_baseSet x
  have hnb : e.baseSet ∈ nhds x :=
    hbase ▸ (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hnb
  let c : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun i => (LinearMap.piApply (e.localFrameCoeff I b i)) X
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun i => fun y => ψ y • c i y
  let Y : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => (ψ : M → ℝ) • e.localFrame b i
  refine ⟨f, Y, ?_, ?_, ?_, ?_⟩
  · intro i
    have hc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (c i) (chartAt H x).source := by
      have h := contMDiffOn_localFrameCoeff (t := e.baseSet) b e.open_baseSet (subset_refl _)
        hX.contMDiffOn i
      rw [← hbase]
      simpa only [c] using h
    simpa only [f] using ψ.contMDiff_smul hc
  · intro i
    have hs : CMDiff[e.baseSet] ∞ (T% (e.localFrame b i)) :=
      e.contMDiffOn_localFrame_baseSet (I := I) ∞ b i
    have hψon : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ e.baseSet := ψ.contMDiff.contMDiffOn
    have hres := hψon.smul_section_of_tsupport e.open_baseSet hψts hs
    simpa only [Y] using hres
  · intro i
    have hcx : c i x = 0 := by
      simp only [c, LinearMap.piApply_apply, hXx, map_zero]
    simp only [f, ψ.eq_one, hcx, one_smul]
  · have hframe : X =ᶠ[nhds x]
        (fun y => ∑ i, (e.localFrameCoeff I b i y) (X y) • e.localFrame b i y) :=
      e.eventually_eq_localFrame_sum_coeff_smul (I := I) (s := X) b hxmem
    have hψ1 : (ψ : M → ℝ) =ᶠ[nhds x] 1 := ψ.eventuallyEq_one
    have h2 : (fun y => ∑ i, (e.localFrameCoeff I b i y) (X y) • e.localFrame b i y) =ᶠ[nhds x]
        (fun y => ∑ i, (f i • Y i) y) := by
      filter_upwards [hψ1] with y hψy
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [f, Y, Pi.smul_apply', c, LinearMap.piApply_apply, hψy, Pi.one_apply, one_smul]
      rfl
    have h3 : (fun y => ∑ i, (f i • Y i) y) = (∑ i, f i • Y i) := by
      funext y
      exact (Finset.sum_apply y Finset.univ (fun i => f i • Y i)).symm
    exact hframe.trans (h2.trans (Filter.EventuallyEq.of_eq h3))

end Commons.Geometry.Manifold.VectorField
