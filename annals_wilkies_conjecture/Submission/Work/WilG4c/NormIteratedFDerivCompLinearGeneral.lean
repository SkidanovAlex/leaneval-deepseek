import Mathlib

open scoped Topology

namespace Work.WilG4c

/-- Chain rule for the `s`-th Fréchet derivative of a composition with a continuous linear map
on the right, in the case where the source and target of the linear map have different
dimensions: if `Φ` is `C^s` at `L x` then the `s`-th derivative of `Φ ∘ L` at `x` is the
`s`-th derivative of `Φ` at `L x` composed with `L` in every variable, whence its operator
norm is at most `‖D^s Φ (L x)‖ * ‖L‖^s`.

This is the `N`-source `M`-target instance of
`Work.WilG4c.norm_iteratedFDeriv_comp_linear_le` (which only treats square dimensions and
target an open subset of a normed space). -/
theorem NormIteratedFDerivCompLinearGeneral {N M : ℕ}
    (L : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)) (Φ : (Fin M → ℝ) → ℝ) (x : Fin N → ℝ) (s : ℕ)
    (hΦ : ContDiffAt ℝ s Φ (L x)) :
    ‖iteratedFDeriv ℝ s (fun y : Fin N → ℝ => Φ (L y)) x‖ ≤
      ‖iteratedFDeriv ℝ s Φ (L x)‖ * ‖L‖ ^ s := by
  -- `Φ` is `C^s` on an open neighbourhood `v` of `L x`.
  obtain ⟨u, hu, hΦu⟩ := hΦ.contDiffOn le_rfl (by simp)
  rcases mem_nhds_iff.mp hu with ⟨v, hvu, hv_open, hLv⟩
  have hv_cont : ContDiffOn ℝ s Φ v := hΦu.mono hvu
  -- The chain rule for the iterated derivative of `Φ ∘ L` on the open set `L ⁻¹' v`.
  have h_comp : iteratedFDerivWithin ℝ s (fun y : Fin N → ℝ => Φ (L y)) (L ⁻¹' v) x =
      (iteratedFDerivWithin ℝ s Φ v (L x)).compContinuousLinearMap (fun _ : Fin s => L) :=
    L.iteratedFDerivWithin_comp_right hv_cont hv_open.uniqueDiffOn
      (hv_open.preimage L.continuous).uniqueDiffOn hLv (le_refl (s : WithTop ℕ∞))
  have hmem_pre : L ⁻¹' v ∈ 𝓝 x := (hv_open.preimage L.continuous).mem_nhds hLv
  -- Replace the `Within` derivatives by the ordinary ones (both sets are open).
  have h1 : iteratedFDerivWithin ℝ s Φ v (L x) = iteratedFDeriv ℝ s Φ (L x) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hv_open.uniqueDiffOn hΦ hLv
  have h2 : iteratedFDerivWithin ℝ s (fun y : Fin N → ℝ => Φ (L y)) (L ⁻¹' v) x =
      iteratedFDeriv ℝ s (fun y : Fin N → ℝ => Φ (L y)) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv (hv_open.preimage L.continuous).uniqueDiffOn
      ((hv_cont.comp_continuousLinearMap L).contDiffAt hmem_pre) hLv
  have key : iteratedFDeriv ℝ s (fun y : Fin N → ℝ => Φ (L y)) x =
      (iteratedFDeriv ℝ s Φ (L x)).compContinuousLinearMap (fun _ : Fin s => L) := by
    rw [← h2, h_comp, h1]
  -- Norm bound for composing a multilinear map with a constant family of linear maps.
  have hb : ‖(iteratedFDeriv ℝ s Φ (L x)).compContinuousLinearMap (fun _ : Fin s => L)‖ ≤
      ‖iteratedFDeriv ℝ s Φ (L x)‖ * ‖L‖ ^ s := by
    calc ‖(iteratedFDeriv ℝ s Φ (L x)).compContinuousLinearMap (fun _ : Fin s => L)‖
        ≤ ‖iteratedFDeriv ℝ s Φ (L x)‖ * ∏ _i : Fin s, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ s Φ (L x)‖ * ‖L‖ ^ s := by simp
  rw [key]
  exact hb

end Work.WilG4c
