import Mathlib
import Submission.Commons.Geometry.Manifold.exists_isMIntegralCurveOn_nhds
import Submission.Commons.Geometry.Manifold.exists_uniform_local_flow_box
import Submission.Commons.Topology.continuous_uncurry_of_flow

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

namespace Commons.Geometry.Manifold

set_option autoImplicit false
set_option linter.style.haveILetI false

/-! ## The core construction -/

/-- Given a uniform local existence statement for the `C^∞` vector field `v`, there is a global
flow: a map `φ : M → ℝ → M` with `φ x 0 = x`, with `φ x` a global integral curve of `v`, and
satisfying the semigroup law `φ (φ x s) t = φ x (s + t)`. -/
theorem exists_global_flow_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε)) :
    ∃ φ : M → ℝ → M, (∀ x : M, φ x 0 = x) ∧ (∀ x : M, IsMIntegralCurve (φ x) v) ∧
      (∀ x : M, ∀ s t : ℝ, φ (φ x s) t = φ x (s + t)) := by
  have hv1 : ContMDiff I I.tangent 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (WithTop.coe_le_coe.mpr (le_top : (1:ℕ∞) ≤ ⊤) :
      ((1:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞))
  choose φ hφ using fun x : M => exists_isMIntegralCurve_of_isMIntegralCurveOn hv1 hε h x
  have hφ0 : ∀ x : M, φ x 0 = x := fun x => (hφ x).1
  have hφint : ∀ x : M, IsMIntegralCurve (φ x) v := fun x => (hφ x).2
  refine ⟨φ, hφ0, hφint, ?_⟩
  intro x s t
  have heq : φ (φ x s) = φ x ∘ (· + s) := by
    refine isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := (0:ℝ)) hv1
      (hφint (φ x s)) ((hφint x).comp_add s) ?_
    simp [hφ0]
  have := congrFun heq t
  simp only [Function.comp_apply] at this
  rw [this, add_comm]

/-! ## The main theorem -/

/-- **Existence of the global flow of a smooth vector field on a compact boundaryless manifold.**

For a `C^∞` vector field `v` on a compact manifold `M` without boundary there is a map
`φ : M → ℝ → M` such that `φ x` is the (global) integral curve of `v` starting at `x`, the flow
law `φ (φ x s) t = φ x (s + t)` holds, and `(x, t) ↦ φ x t` is continuous. -/
theorem exists_global_flow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [CompactSpace M] {v : (x : M) → TangentSpace I x} (hv : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => (⟨x, v x⟩ : TangentBundle I M))) : ∃ φ : M → ℝ → M, (∀ x : M, φ x 0 = x) ∧ (∀ x : M, IsMIntegralCurve (φ x) v) ∧ (∀ x : M, ∀ s t : ℝ, φ (φ x s) t = φ x (s + t)) ∧ Continuous (fun p : M × ℝ => φ p.1 p.2) := by
  obtain ⟨ε, hε, hbox⟩ := exists_uniform_local_flow_box hv
  have hloc0 : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
    intro x
    obtain ⟨U, hUopen, hxU, γ, hγ0, hγi, hγc⟩ := hbox x
    exact ⟨γ x, hγ0 x hxU, hγi x hxU⟩
  obtain ⟨φ, hφ0, hφint, hadd⟩ := exists_global_flow_core hv hε hloc0
  refine ⟨φ, hφ0, hφint, hadd, ?_⟩
  have hv1 : ContMDiff I I.tangent 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (WithTop.coe_le_coe.mpr le_top)
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (WithTop.coe_le_coe.mpr (le_top : (1:ℕ∞) ≤ ⊤) :
      ((1:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞))
  have hloc : ∀ x : M, ∀ t : ℝ, |t| < ε → ContinuousAt (fun p : M × ℝ => φ p.1 p.2) (x, t) := by
    intro x t ht
    obtain ⟨U, hUopen, hxU, γ, hγ0, hγi, hγc⟩ := hbox x
    have hmem0 : (0:ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    have hagree : ∀ y ∈ U, ∀ s ∈ Ioo (-ε) ε, γ y s = φ y s := by
      intro y hy s hs
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := (0:ℝ)) hmem0 hv1
        (hγi y hy) ((hφint y).isMIntegralCurveOn _) (by rw [hγ0 y hy, hφ0 y]) hs
    have hst : (x, t) ∈ U ×ˢ Ioo (-ε) ε := ⟨hxU, abs_lt.mp ht⟩
    have hopen : IsOpen (U ×ˢ Ioo (-ε) ε) := hUopen.prod isOpen_Ioo
    have hγat : ContinuousAt (fun p : M × ℝ => γ p.1 p.2) (x, t) :=
      hγc.continuousAt (hopen.mem_nhds hst)
    have hev : (fun p : M × ℝ => γ p.1 p.2) =ᶠ[𝓝 (x, t)] (fun p : M × ℝ => φ p.1 p.2) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨U ×ˢ Ioo (-ε) ε, hopen.mem_nhds hst, fun p hp => hagree p.1 hp.1 p.2 hp.2⟩
    exact hγat.congr hev
  exact Commons.Topology.continuous_uncurry_of_flow hε hφ0 hadd hloc

end Commons.Geometry.Manifold
