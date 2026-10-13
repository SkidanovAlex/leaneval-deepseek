import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

theorem box_integral_eq {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc c d, g p.1 p.2 = ∫ z in a..b, ∫ θ in c..d, g z θ := by
  -- The integrand is continuous on the (compact) rectangle, hence integrable there.
  have hf : MeasureTheory.IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc c d) :=
    ContinuousOn.integrableOn_compact (IsCompact.prod isCompact_Icc isCompact_Icc) hg
  -- Fubini for set integrals over a product of sets.
  refine (MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => g p.1 p.2) hf).trans ?_
  -- Turn the iterated set integrals over `Icc` into interval integrals:
  -- `∫ in a..b = ∫ in Ioc a b` and `Ioc a b =ᵐ Icc a b`.
  simp only [intervalIntegral.integral_of_le, hab, hcd,
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (α := ℝ)
      (μ := MeasureTheory.volume))]

end Work.FTS.StrongEps.LocUnif.D5
