import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-- **Elgindi, bound on the good term of the `H^4` product rule.**

If `(U z θ)^2 ≤ M` and `(V z θ · W_t(θ))^2 ≤ HkIntegrand α 4 h z θ` on the domain, then
the squared product `(U·V·W_t)^2` is integrable on every angular slice, its `z`-integral
is integrable over `Iz`, and the double integral is bounded by `M · |h|²_{H^4}`.

The proof is a one-step domination: pointwise on the domain
`(U·V·W_t)^2 = U^2 · (V·W_t)^2 ≤ M · HkIntegrand α 4 h`, and all the integrability
statements come from `HkMem α 4 h` together with the two measurability hypotheses. -/
theorem GoodTermSqBound (α : ℝ) (U V h : ℝ → ℝ → ℝ) (M : ℝ)
    (hh : Work.Spaces.HkMem α 4 h)
    (hUb : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, (U z θ) ^ 2 ≤ M)
    (hVsq : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (V z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ)
    (hslice_meas : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (U p.1 p.2 * V p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
          (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2)
          Work.Spaces.Iz
      ∧ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ M * Work.Spaces.HkSq α 4 h := by
  have hIz_meas : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- `M` is nonnegative: `z = θ = 0` lies in the domain.
  have hM : 0 ≤ M := by
    have h0 := hUb 0 Work.Spaces.zero_mem_Iz 0 Work.Spaces.zero_mem_Iθ
    nlinarith [sq_nonneg (U 0 0)]
  -- Pointwise domination of the squared good term by `M · HkIntegrand`.
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := by
    intro z hz θ hθ
    have h1 := hUb z hz θ hθ
    have h2 := hVsq z hz θ hθ
    have hfeq : (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
        = (U z θ) ^ 2 * (V z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    rw [hfeq]
    calc (U z θ) ^ 2 * (V z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ M * (V z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_le_mul_of_nonneg_left h2 hM
  -- Integrability of every angular slice.
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hHint : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 h z θ) Work.Spaces.Iθ := hh.1 z hz
    have hbig : MeasureTheory.Integrable
        (fun θ => M * Work.Spaces.HkIntegrand α 4 h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hHint.const_mul M
    refine MeasureTheory.Integrable.mono' hbig (hslice_meas z hz) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg (U z θ * V z θ * Work.Spaces.Wt α z θ))]
    exact hbound z hz θ hθ
  -- Measurability of the `z`-slice integral, from the joint measurability.
  have hmeasG : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hjoint
  have hK_int : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hh.2
  have hsliceK : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α 4 h z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun z hz => hh.1 z hz
  -- Dominated bound for the inner integral at a fixed `z`.
  have hinner : ∀ z ∈ Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ M * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ := by
    intro z hz
    calc ∫ θ in Work.Spaces.Iθ, (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, M * Work.Spaces.HkIntegrand α 4 h z θ := by
          refine integral_mono_ae (hslice z hz) ((hsliceK z hz).const_mul M) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
          exact hbound z hz θ hθ
      _ = M * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ := by
          rw [integral_const_mul]
  -- Integrability over `Iz` of the `z`-slice integral.
  have hG_int : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hK_int.const_mul M) hmeasG ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz_meas] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact hinner z hz
  -- The numerical bound.
  have hfinal : ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ M * Work.Spaces.HkSq α 4 h := by
    have hmono : ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
          (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz,
            M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ) := by
      refine integral_mono_ae hG_int (hK_int.const_mul M) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hIz_meas] with z hz
      exact hinner z hz
    calc ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (U z θ * V z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ ∫ z in Work.Spaces.Iz,
            M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h z θ) := hmono
      _ = M * Work.Spaces.HkSq α 4 h := by rw [integral_const_mul]; rfl
  exact ⟨hslice, hG_int, hfinal⟩

end Work.Spaces
