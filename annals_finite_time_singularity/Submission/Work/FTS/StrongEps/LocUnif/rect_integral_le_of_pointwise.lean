import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

/-- If `g²` is dominated pointwise on the rectangle `[a,b] × [c,d]` (`⊆ (0,∞) × (0,π/2)`) by
`K` times the `ℋ⁶`-integrand of `F`, then the iterated integral of `g²` over the rectangle is
dominated by `K` times the squared `ℋ⁶`-norm of `F`.

The proof is pure monotonicity of the integral: the rectangle is contained in `Iz × Iθ`, the
`ℋ⁶`-integrand is a sum of squares and hence nonnegative, and the only integrability needed is
the one supplied by `HkMem α 6 F`. -/
theorem rect_integral_le_of_pointwise {a b c d K α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hd : d < Real.pi / 2) {F g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 6 F) (hK : 0 ≤ K)
    (hpt : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (g z θ) ^ 2 ≤ K * Work.Spaces.HkIntegrand α 6 F z θ) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2) ≤ K * Work.Spaces.HkSq α 6 F := by
  have hsubz : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans ha.le hz.1
  have hsubθ : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans hc.le hθ.1, le_trans hθ.2 hd.le⟩
  -- (1) the angular integral at a fixed `z ∈ [a,b]`
  have hinner : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hsubz hz
    have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 F z θ) (Set.Icc c d) :=
      (hmem.1 z hzIz).mono_set hsubθ
    have hInt2 : IntegrableOn
        (fun θ => K * Work.Spaces.HkIntegrand α 6 F z θ) (Set.Icc c d) := hInt.const_mul _
    have hstep1 : (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α 6 F z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => sq_nonneg _) hInt2
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          fun θ hθ => hpt z hz θ hθ)
    have hstep2 : (∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α 6 F z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ :=
      setIntegral_mono_set (hmem.1 z hzIz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ)
        (Eventually.of_forall fun θ hθ => hsubθ hθ)
    calc (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α 6 F z θ := hstep1
      _ = K * ∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α 6 F z θ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ :=
          mul_le_mul_of_nonneg_left hstep2 hK
  -- (2) the radial integral
  have houter : (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
      ≤ K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 F z θ := by
    have hInt : IntegrableOn
        (fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ)
        (Set.Icc a b) := (hmem.2.mono_set hsubz).const_mul _
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ z in Set.Icc a b, K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 F z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              fun z hz => hinner z hz)
      _ = K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 F z θ := MeasureTheory.integral_const_mul _ _
  -- (3) enlarging `[a,b]` to `Iz`
  have hlast : (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 F z θ) ≤ Work.Spaces.HkSq α 6 F := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_mono_set hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ)
      (Eventually.of_forall fun z hz => hsubz hz)
  exact le_trans houter (mul_le_mul_of_nonneg_left hlast hK)

end Work.FTS.StrongEps.LocUnif
