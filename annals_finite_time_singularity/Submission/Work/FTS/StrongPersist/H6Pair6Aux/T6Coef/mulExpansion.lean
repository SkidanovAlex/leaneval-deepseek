import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open scoped Real Topology
open MeasureTheory Set Filter

set_option quotPrecheck false in
/-- The product of the two restricted Lebesgue measures, as it appears throughout the flat
pairing estimates. -/
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

theorem mulExpansion {f g : ℝ → ℝ → ℝ} (a b : ℕ) (ρ : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hterm : ∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
      = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                * Work.Spaces.mixed b a g p.1 p.2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- Step 1: the slot pairing is the product-measure integral of the uncurried integrand.
  have hprod : Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
      = ∫ p, ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2 ∂IPM := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hXY).symm
  rw [hprod]
  -- Step 2: the Leibniz expansion of `D_z^bD_θ^a (f · g)`, a.e. on the open quadrant.
  have hpt : (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
      =ᵐ[IPM] (fun p : ℝ × ℝ =>
          ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2)) := by
    filter_upwards [Work.FTS.StrongPersist.N6Trans.SixRoute.ae_mem_Q0_prod] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f g hf hg p.1 p.2 hz hθ0 hθ1]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    ring
  rw [MeasureTheory.integral_congr_ae hpt]
  -- Step 3: exchange the integral with the (finite) double sum.
  have key : ∀ a₁ ≤ a, ∀ b₁ ≤ b,
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
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

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
