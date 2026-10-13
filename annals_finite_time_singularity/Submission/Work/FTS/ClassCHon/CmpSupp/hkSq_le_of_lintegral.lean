import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp

/-- `∫⁻` of `ofReal` of the `H^k`-integrand, compared with the real-valued iterated
integral `HkSq`: the two agree because the integrand is nonnegative and integrable
(`HkMem`).  Stated on the half-line `Ioi 0` (which differs from `Iz = Ici 0` by the
null set `{0}`). -/
theorem lintegral_HkIntegrand_eq {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k Ψ) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k Ψ z θ) := by
  have hinner : (fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k Ψ z θ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun z => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hmem.1 z ?_) (Filter.Eventually.of_forall fun θ => ?_)
    · rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
    · exact Work.Spaces.HkIntegrand_nonneg α k Ψ z θ
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have hInt : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k Ψ z θ)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [hIoi_eq_Iz]
    exact hmem.2
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) :=
    Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ
  rw [← MeasureTheory.lintegral_congr_ae hinner]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm

theorem hkSq_le_of_lintegral {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmem : Work.Spaces.HkMem α 0 Ψ)
    (hfin : (∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Ψ z θ)) ≤ ENNReal.ofReal C) :
    Work.Spaces.HkSq α 0 Ψ ≤ C := by
  have hEq := lintegral_HkIntegrand_eq (k := 0) hmem
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have h1 : ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 Ψ z θ) ≤ ENNReal.ofReal C := by
    rw [← hEq]
    exact hfin
  have hle : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 Ψ z θ) ≤ C :=
    (ENNReal.ofReal_le_ofReal_iff hC).mp h1
  calc Work.Spaces.HkSq α 0 Ψ
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Ψ z θ := rfl
    _ = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Ψ z θ := by rw [← hIoi_eq_Iz]
    _ ≤ C := hle

end Work.FTS.ClassCHon.CmpSupp
