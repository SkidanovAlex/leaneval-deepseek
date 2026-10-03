import Mathlib

namespace Work.Pert.Ksub2

/-- A holomorphic function on an open set is Lipschitz on every compact subset of that set.

Proof: `f` is complex differentiable on the open set `D`, hence analytic, hence `C^1` over `ℝ`
on `D`. Every point of `D` therefore has a neighbourhood on which `f` is Lipschitz, so `f` is
locally Lipschitz on `V`. A locally Lipschitz function on a compact set is globally Lipschitz
(`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`). -/
theorem exists_lipschitzOn_of_compact {f : ℂ → ℂ} {D V : Set ℂ} (hD : IsOpen D) (hVc : IsCompact V)
    (hVD : V ⊆ D) (hf : DifferentiableOn ℂ f D) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ V, ∀ z' ∈ V, ‖f z - f z'‖ ≤ L * ‖z - z'‖ := by
  -- `f` is `C^1` over `ℝ` on the open set `D`
  have hcd : ContDiffOn ℝ 1 f D := ContDiffOn.restrict_scalars ℝ (hf.contDiffOn hD)
  -- hence locally Lipschitz on `V`
  have hloc : LocallyLipschitzOn V f := fun x hx => by
    have hx' : ContDiffAt ℝ 1 f x := (hcd x (hVD hx)).contDiffAt (hD.mem_nhds (hVD hx))
    obtain ⟨K, t, ht, hK⟩ := hx'.exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩
  -- locally Lipschitz on a compact set is globally Lipschitz
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hVc
  refine ⟨(K : ℝ), K.coe_nonneg, fun z hz z' hz' => ?_⟩
  have h := hK.dist_le_mul z hz z' hz'
  simpa [dist_eq_norm] using h

end Work.Pert.Ksub2
