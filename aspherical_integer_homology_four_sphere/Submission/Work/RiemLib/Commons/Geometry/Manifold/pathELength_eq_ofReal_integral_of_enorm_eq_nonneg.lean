import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold

theorem pathELength_eq_ofReal_integral_of_enorm_eq_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [(x : M) → ENorm (TangentSpace I x)] [(x : M) → ENormSMulClass ℝ (TangentSpace I x)]
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Icc a b) MeasureTheory.volume)
    (hfnn : ∀ t ∈ Set.Icc a b, 0 ≤ f t)
    (h : ∀ t ∈ Set.Icc a b,
      ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I γ t) (1 : ℝ)‖ₑ = ENNReal.ofReal (f t)) :
    Manifold.pathELength I γ a b = ENNReal.ofReal (∫ t in a..b, f t) := by
  have hfnn' : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hfnn t ht
  calc Manifold.pathELength I γ a b
      = ∫⁻ t in Set.Icc a b,
          ‖(mfderiv (modelWithCornersSelf ℝ ℝ) I γ t) (1 : ℝ)‖ₑ :=
        Manifold.pathELength_eq_lintegral_mfderiv_Icc
    _ = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (f t) :=
        MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun t ht => h t ht)
    _ = ENNReal.ofReal (∫ t, f t ∂MeasureTheory.volume.restrict (Set.Icc a b)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf hfnn').symm
    _ = ENNReal.ofReal (∫ t in a..b, f t) := by
        congr 1
        rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

end Commons.Geometry.Manifold