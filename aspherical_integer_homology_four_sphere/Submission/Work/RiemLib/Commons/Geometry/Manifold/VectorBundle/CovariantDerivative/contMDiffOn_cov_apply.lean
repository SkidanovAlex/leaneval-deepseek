import Mathlib
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

open scoped _root_.Manifold _root_.ContDiff Topology
open _root_.VectorField Set _root_.CovariantDerivative Bundle Filter

theorem contMDiffOn_cov_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
    {u : Set M} (hu : IsOpen u)
    {Z Y : Π x : M, TangentSpace I x}
    (hZ : CMDiff[u] ∞ (T% Z)) (hY : CMDiff[u] ∞ (T% Y)) :
    CMDiff[u] ∞ (T% (fun y : M => cov Z y (Y y))) := by
  intro x hx
  -- A smooth bump function supported in `u` and equal to `1` near `x`.
  obtain ⟨f, hf_tsupp, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) (s := u)
      (hu.mem_nhds hx)).mem_iff.mp (hu.mem_nhds hx)
  have hf_one : (f : M → ℝ) =ᶠ[𝓝 x] (1 : M → ℝ) := f.eventuallyEq_one
  -- The sections `f • Z` and `f • Y` are globally smooth and agree with `Z`, `Y` near `x`.
  have hZ_smooth : CMDiff ∞ (T% ((f : M → ℝ) • Z)) :=
    ContMDiffOn.smul_section_of_tsupport (I := I) (F := E) (V := TangentSpace I)
      (f.contMDiff.contMDiffOn) hu hf_tsupp hZ
  have hY_smooth : CMDiff ∞ (T% ((f : M → ℝ) • Y)) :=
    ContMDiffOn.smul_section_of_tsupport (I := I) (F := E) (V := TangentSpace I)
      (f.contMDiff.contMDiffOn) hu hf_tsupp hY
  have hmain : CMDiff ∞ (T% (fun y : M => cov ((f : M → ℝ) • Z) y (((f : M → ℝ) • Y) y))) :=
    contMDiff_cov_apply cov hcov hZ_smooth hY_smooth
  -- On the open set `V`, contained in `u`, where `f` is locally equal to `1`, the two
  -- expressions agree pointwise.
  set V : Set M := interior {y : M | (f : M → ℝ) y = 1} ∩ u with hVdef
  have hV_open : IsOpen V := isOpen_interior.inter hu
  have hxV : x ∈ V := by
    refine ⟨?_, hx⟩
    rw [mem_interior_iff_mem_nhds]
    exact hf_one
  have hpoint : ∀ y ∈ V, cov ((f : M → ℝ) • Z) y (((f : M → ℝ) • Y) y) = cov Z y (Y y) := by
    intro y hy
    obtain ⟨hyint, hyu⟩ := hy
    have hy1 : (f : M → ℝ) =ᶠ[𝓝 y] (1 : M → ℝ) := by
      filter_upwards [isOpen_interior.mem_nhds hyint] with z hz
      simpa using interior_subset hz
    have hZy : ((f : M → ℝ) • Z) =ᶠ[𝓝 y] Z := by
      filter_upwards [hy1] with z hz
      show (f : M → ℝ) z • Z z = Z z
      simp only [hz, Pi.one_apply, one_smul]
    have hYy : ((f : M → ℝ) • Y) =ᶠ[𝓝 y] Y := by
      filter_upwards [hy1] with z hz
      show (f : M → ℝ) z • Y z = Y z
      simp only [hz, Pi.one_apply, one_smul]
    have h1 : cov ((f : M → ℝ) • Z) y = cov Z y :=
      (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq
        ((hZ_smooth y).mdifferentiableAt (by simp))
        ((hZ.contMDiffAt (hu.mem_nhds hyu)).mdifferentiableAt (by simp))
        Filter.univ_mem hZy
    have h2 : (((f : M → ℝ) • Y) y) = Y y := hYy.eq_of_nhds
    rw [h1, h2]
  have hG_on : CMDiff[V] ∞ (T% (fun y : M => cov Z y (Y y))) :=
    (hmain.contMDiffOn (s := V)).congr fun y hy => congrArg (TotalSpace.mk' E y) (hpoint y hy).symm
  exact (hG_on.contMDiffAt (hV_open.mem_nhds hxV)).contMDiffWithinAt

end Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
