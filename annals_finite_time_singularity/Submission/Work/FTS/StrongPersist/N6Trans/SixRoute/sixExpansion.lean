import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.GoodOpenBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open MeasureTheory Set Filter
open scoped Real Topology

/-- The open quadrant `(0,∞) × (0,π/2)` has full measure for the product of the two restricted
Lebesgue measures `(volume|Iz).prod (volume|Iθ)`. -/
theorem ae_mem_Q0_prod :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2 ∧ p.2 < π / 2 := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    fun p hp => hp

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as it appears throughout the flat
pairing estimates. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

theorem sixExpansion {α : ℝ} {f g : ℝ → ℝ → ℝ} (a b : ℕ) (ρ : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hterm : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- Step 1: the slot pairing is the product-measure integral of the uncurried integrand.
  have hprod : Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
      = ∫ p, ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2 ∂IPM := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hXY).symm
  rw [hprod]
  -- Step 2: Leibniz expansion of `D_z^b D_θ^a (f · D_z g)`, a.e. on the open quadrant.
  have hpt : (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[IPM] (fun p : ℝ × ℝ =>
          ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2)) := by
    filter_upwards [ae_mem_Q0_prod] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    rw [Work.FTS.TransportS.mixed_mul_Dz_open b a f g hf hg p.1 p.2 hz hθ0 hθ1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    ring
  rw [MeasureTheory.integral_congr_ae hpt]
  -- Step 3: exchange the integral with the (finite) double sum.
  have key : ∀ a₁ ≤ a, ∀ b₁ ≤ b,
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2)) IPM :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ ha₁ b₁ hb₁).const_mul _
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun a₁ ha₁ => ?_
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun b₁ hb₁ => ?_
      exact MeasureTheory.integral_const_mul _ _
    · intro b₁ hb₁
      exact key a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
  · intro a₁ ha₁
    exact MeasureTheory.integrable_finsetSum _ fun b₁ hb₁ =>
      key a₁ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)) b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))

end Work.FTS.StrongPersist.N6Trans.SixRoute
