import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarAssembly
import Submission.Work.FIArea4.Vflip.Vfd.farW_divisor_sum_le

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem far_sum_numerics (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R:ℝ)*(S:ℝ)/(D:ℝ))^((1:ℝ)/3) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2*R ∧ S < s ∧ s ≤ 2*S) →
      (∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
        if m ∣ c then
          (Real.log (2*H)+1)^2 * (Real.log (2*(cR c R : ℝ))+1) *
            ( (m * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))))^(-(1:ℝ)/2) * ((cR c R:ℝ)*(S:ℝ))
              + ((R:ℝ)*(S:ℝ))^(ε/4)
                * ( m * (16*(R:ℝ)*(S:ℝ)/((c:ℝ)*(D:ℝ))) * Real.sqrt ((cR c R:ℝ)*(S:ℝ))
                    + (Real.log (160*H)+1) * ((cR c R:ℝ)*(S:ℝ)^((3:ℝ)/4)
                        + (S:ℝ)*(cR c R:ℝ)^((3:ℝ)/4)) ) )
            * Work.FIArea4.p14L2 (cR c R) S (redA c α)
        else 0)
      ≤ C * ((Real.log (2*H)+1)^2 * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^2
                * ((D:ℝ)*H*(R:ℝ)*(S:ℝ))^((1:ℝ)/2)
            + (Real.log (2*H)+1)^4 * ((R:ℝ)*(S:ℝ))^(ε/2)
                * (((R:ℝ)*(S:ℝ))^((3:ℝ)/2)/(D:ℝ)
                    + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)))
            * Work.FIArea4.p14Ener R S α := by
  obtain ⟨Cw, hCw, hW⟩ := farW_divisor_sum_le ε hε
  obtain ⟨C, hC, hC'⟩ := far_sum_numerics_aux ε hε Cw hCw hW
  refine ⟨C, hC, ?_⟩
  intro D R S H α h1 h2 h3 h4 h5 h6 h7
  change (∑ m ∈ Finset.range (2 * R + 1), ∑ c ∈ Finset.range (2 * R + 1),
        if m ∣ c then farW D R S H ε m c * Work.FIArea4.p14L2 (cR c R) S (redA c α) else 0)
      ≤ C * farB D R S H ε * Work.FIArea4.p14Ener R S α
  exact hC' D R S H α h1 h2 h3 h4 h5 h6 h7

end

end Work.FIArea4.Vflip.Vfd
