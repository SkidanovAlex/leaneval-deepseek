import Mathlib
import Submission.Work.SSGRoute.PTW.RegularRep
import Submission.Work.SSGRoute.PTW.avgOp_regRep
import Submission.Work.SSGRoute.PTW.Spectral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The nontriviality step for the spectral argument

If `A = avgOp ξ` and `regRep y` moves `ξ`, then some nonzero eigenspace of `A` carries a vector
moved by `regRep y`.  This is the step that produces the finite-dimensional invariant subspace
with nontrivial `y`-action (see `Spectral.lean` for the surrounding plan).
-/

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- Nontriviality step: if `A = avgOp ξ`, `regRep y` moves `ξ`, the kernel of `A` is orthogonal to
the orbit of `ξ`, and the range of `A` lies in the closure of the span of the nonzero eigenspaces of
`A`, then some nonzero eigenspace of `A` contains a vector moved by `regRep y`. -/
theorem exists_eigenspace_regRep_ne_one (ξ : Lp ℂ 2 μ) (y : Q)
    (hyst : regRep (μ := μ) y ξ ≠ ξ)
    (hker : ∀ η : Lp ℂ 2 μ, avgOp (μ := μ) ξ η = 0 →
      ∀ g : Q, inner ℂ (regRep (μ := μ) g ξ) η = 0)
    (hrange : (avgOp (μ := μ) ξ).range ≤
      (⨆ (lam : {m : ℂ // m ≠ 0}), Module.End.eigenspace
        ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam.1).topologicalClosure) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∃ v : Lp ℂ 2 μ,
      v ∈ Module.End.eigenspace
        ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam ∧
      v ≠ 0 ∧ regRep (μ := μ) y v ≠ v := by
  by_contra hcon
  have htriv : ∀ lam : ℂ, lam ≠ 0 → ∀ v : Lp ℂ 2 μ,
      v ∈ Module.End.eigenspace
        ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam →
      regRep (μ := μ) y v = v := by
    intro lam hlam v hv
    by_contra hvne
    have hv0 : v ≠ 0 := fun h0 => hvne (by rw [h0]; simp)
    exact hcon ⟨lam, hlam, v, hv, hv0, hvne⟩
  -- the operator `regRep y - 1` vanishes on the span of the nonzero eigenspaces, hence on its closure
  have hsub : (⨆ (lam : {m : ℂ // m ≠ 0}), Module.End.eigenspace
        ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam.1) ≤
      (regRep (μ := μ) y - 1).ker := by
    refine iSup_le fun lam => ?_
    intro v hv
    change (regRep (μ := μ) y) v - v = 0
    rw [sub_eq_zero]
    exact htriv lam.1 lam.2 v hv
  have hvan : ∀ w : Lp ℂ 2 μ, w ∈ (⨆ (lam : {m : ℂ // m ≠ 0}), Module.End.eigenspace
        ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam.1).topologicalClosure →
      regRep (μ := μ) y w = w := by
    intro w hw
    have hcl : IsClosed (((regRep (μ := μ) y - 1).ker : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
      ContinuousLinearMap.isClosed_ker _
    have hmem : w ∈ (regRep (μ := μ) y - 1).ker :=
      Submodule.topologicalClosure_minimal _ hsub hcl hw
    change (regRep (μ := μ) y) w - w = 0 at hmem
    exact sub_eq_zero.mp hmem
  have hA : ∀ η : Lp ℂ 2 μ, avgOp (μ := μ) ξ ((regRep (μ := μ) y - 1) η) = 0 := by
    intro η
    change avgOp (μ := μ) ξ ((regRep (μ := μ) y) η - η) = 0
    rw [map_sub, sub_eq_zero, avgOp_regRep]
    exact hvan _ (hrange ⟨η, rfl⟩)
  have hξ0 : inner ℂ (regRep (μ := μ) y ξ) ((regRep (μ := μ) y - 1) ξ) = 0 := hker _ (hA ξ) y
  have hξ1 : inner ℂ ξ ((regRep (μ := μ) y - 1) ξ) = 0 := by
    have h := hker _ (hA ξ) 1
    simpa [regRep_one] using h
  have h1 : inner ℂ ξ (regRep (μ := μ) y ξ) = ((‖ξ‖ : ℂ)) ^ 2 := by
    have h := hξ1
    change inner ℂ ξ ((regRep (μ := μ) y) ξ - ξ) = 0 at h
    rw [inner_sub_right, sub_eq_zero, inner_self_eq_norm_sq_to_K] at h
    exact h
  have h2 : inner ℂ (regRep (μ := μ) y ξ) ξ = ((‖ξ‖ : ℂ)) ^ 2 := by
    have h := hξ0
    change inner ℂ (regRep (μ := μ) y ξ) ((regRep (μ := μ) y) ξ - ξ) = 0 at h
    rw [inner_sub_right, sub_eq_zero] at h
    rw [inner_self_eq_norm_sq_to_K, norm_regRep_apply] at h
    exact h.symm
  -- Equality in Cauchy--Schwarz forces `regRep y ξ = ξ`, contradicting `hyst`.
  have h5 : ‖regRep (μ := μ) y ξ - ξ‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (regRep (μ := μ) y ξ - ξ)]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (regRep (μ := μ) y ξ), norm_regRep_apply,
      h2, h1, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ξ]
    simp
  have h6 : regRep (μ := μ) y ξ - ξ = 0 := by
    have hz' : ‖regRep (μ := μ) y ξ - ξ‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
    simpa using hz'
  exact hyst (eq_of_sub_eq_zero h6)

end Work.SSGRoute.PTW
