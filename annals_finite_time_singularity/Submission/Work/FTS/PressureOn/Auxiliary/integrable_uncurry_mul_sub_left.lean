import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem integrable_uncurry_mul_sub_left (a b ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hρ : Continuous ρ)
    (hac : HasCompactSupport a) (hρc : HasCompactSupport ρ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (x t : EuclideanSpace ℝ (Fin 3)) => ρ t * a x * b (x - t))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- The integrand is continuous and supported in `tsupport a ×ˢ tsupport ρ`, a compact set.
  have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ρ p.2 * a p.1 * b (p.1 - p.2)) :=
    ((hρ.comp continuous_snd).mul (ha.comp continuous_fst)).mul
      (hb.comp (continuous_fst.sub continuous_snd))
  have hsupp : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3) => ρ p.2 * a p.1 * b (p.1 - p.2)) := by
    have hle : Function.support (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          a p.1 * ρ p.2) ⊆ Function.support a ×ˢ Function.support ρ := by
      intro p hp
      simp only [Function.mem_support, Set.mem_prod] at hp ⊢
      exact ⟨fun h => hp (by rw [h, zero_mul]), fun h => hp (by rw [h, mul_zero])⟩
    have hA : HasCompactSupport (fun p : EuclideanSpace ℝ (Fin 3) ×
        EuclideanSpace ℝ (Fin 3) => a p.1 * ρ p.2) := by
      refine (hac.isCompact.prod hρc.isCompact).of_isClosed_subset (isClosed_tsupport _) ?_
      calc tsupport (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
              a p.1 * ρ p.2)
          = closure (Function.support fun p : EuclideanSpace ℝ (Fin 3) ×
              EuclideanSpace ℝ (Fin 3) => a p.1 * ρ p.2) := rfl
        _ ⊆ closure (Function.support a ×ˢ Function.support ρ) := closure_mono hle
        _ = closure (Function.support a) ×ˢ closure (Function.support ρ) := closure_prod_eq
        _ = tsupport a ×ˢ tsupport ρ := rfl
    refine hA.mono (fun p hp => ?_)
    rw [Function.mem_support] at hp ⊢
    intro h
    exact hp (by rw [mul_comm (ρ p.2) (a p.1), h, zero_mul])
  exact hcont.integrable_of_hasCompactSupport hsupp

end Work.FTS.PressureOn.Auxiliary
