import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLComp.USCBasic

/-!
# Close returns to a compact set of positive measure (Poincaré recurrence)

Given a measure-preserving `T` on `X₃`, a compact set `K` of positive measure and a scale `δ`, there
is a point `x ∈ K` whose `T`-orbit returns to `K` with displacement in `V δ`.  This is the "finite
cover by small balls plus Poincaré recurrence" step of ROUTE_LEAD L9.4 (in EKL it is implicit in
"by Poincaré recurrence", `B_δ(x)`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.EKLNonExc

open MeasureTheory Filter Topology
open Work.EKLContract
open Work.EKLComp (ball mem_ball self_mem_ball isOpen_ball)

noncomputable section

theorem exists_close_return (μ : Measure X3) [IsProbabilityMeasure μ] (T : X3 → X3)
    (hT : MeasurePreserving T μ μ) (K : Set X3) (hK : IsCompact K) (hμK : 0 < μ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hV : ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ V ε, ∀ h ∈ V ε, h * g⁻¹ ∈ V δ) :
    ∃ x ∈ K, ∃ n : ℕ, 0 < n ∧ T^[n] x ∈ K ∧ ∃ g ∈ V δ, T^[n] x = g • x := by
  obtain ⟨ε, hε0, hεV⟩ := hV
  have hcov : K ⊆ ⋃ z ∈ (Set.univ : Set K), ball ε (z : X3) := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨⟨x, hx⟩, trivial, self_mem_ball hε0 x⟩
  obtain ⟨b', _, hb'fin, hb'cov⟩ :=
    hK.elim_finite_subcover_image (b := Set.univ) (c := fun z : K => ball ε (z : X3))
      (fun i _ => isOpen_ball ε (i : X3)) hcov
  obtain ⟨z, hz, hzpos⟩ : ∃ z : K, z ∈ b' ∧ 0 < μ (K ∩ ball ε (z : X3)) := by
    by_contra hcon
    push_neg at hcon
    haveI : Countable b' := hb'fin.countable.to_subtype
    have h2 : ∑' w : b', μ (K ∩ ball ε ((w : K) : X3)) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro w
      exact le_antisymm (hcon w.1 w.2) zero_le
    have h1 : μ K ≤ ∑' w : b', μ (K ∩ ball ε ((w : K) : X3)) := by
      calc μ K ≤ μ (⋃ w : b', (K ∩ ball ε ((w : K) : X3))) := by
            apply measure_mono
            intro x hx
            rcases Set.mem_iUnion₂.mp (hb'cov hx) with ⟨w, hwb, hwx⟩
            exact Set.mem_iUnion.mpr ⟨⟨w, hwb⟩, ⟨hx, hwx⟩⟩
        _ ≤ ∑' w : b', μ (K ∩ ball ε ((w : K) : X3)) := measure_iUnion_le _
    have h3 : μ K = 0 := le_antisymm (h2 ▸ h1) zero_le
    exact (lt_irrefl (0 : ENNReal)) (h3 ▸ hμK)
  have hmeas : NullMeasurableSet (K ∩ ball ε (z : X3)) μ := by
    rw [Set.inter_comm]
    exact ((isOpen_ball ε (z : X3)).measurableSet.inter hK.measurableSet).nullMeasurableSet
  obtain ⟨x, hxS, m, hm0, hmS⟩ := hT.exists_mem_iterate_mem hmeas (ne_of_gt hzpos)
  obtain ⟨g, hg, hgx⟩ := mem_ball.mp hxS.2
  obtain ⟨h, hh, hhy⟩ := mem_ball.mp hmS.2
  refine ⟨x, hxS.1, m, Nat.pos_of_ne_zero hm0, hmS.1, h * g⁻¹, hεV g hg h hh, ?_⟩
  have hz_eq : (z : X3) = g⁻¹ • x := by
    rw [← hgx, ← mul_smul, inv_mul_cancel, one_smul]
  rw [← hhy, hz_eq, mul_smul]

end

end Work.EKLNonExc
