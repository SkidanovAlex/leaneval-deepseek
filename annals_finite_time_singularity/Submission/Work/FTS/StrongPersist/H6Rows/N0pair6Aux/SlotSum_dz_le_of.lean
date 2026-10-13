import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.TransportS.ip4SlotDomFixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! The `D_z`-shift of the slot pairing and of the slot sum, with the pointwise identity
`D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on the open quadrant taken as a hypothesis instead of
being derived from `SmoothOpen` (`Work.FTS.TransportS.mixed_dz_eqOn`). -/

/-- **The slot pairing shifts along `D_z`**, given the pointwise identity on `Q0`. -/
theorem slotPairing_dz_of (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = Work.FTS.TransportS.slotPairing ρ a (b + 1) u v := by
  unfold Work.FTS.TransportS.slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  have h1 := hu hp
  have h2 := hv hp
  simp only [Function.uncurry] at h1 h2
  rw [h1, h2]

/-- **The slot term shifts along `D_z`**, given the pointwise identity on `Q0`. -/
theorem SlotTerm_dz_le_of (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      ≤ Work.FTS.TransportS.SlotTerm α a (b + 1) u v := by
  unfold Work.FTS.TransportS.SlotTerm
  rw [slotPairing_dz_of Work.FTS.TransportS.leafEta a b hu hv,
    slotPairing_dz_of Work.FTS.TransportS.leafOne a b hu hv,
    slotPairing_dz_of (Work.FTS.TransportS.leafGam α) a b hu hv]

/-- The `D_z`-shift of the slot sum at finite order: the proved `Work.FTS.TransportS.SlotSum_dz_le`
is the instance where the pointwise identity `D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on the open
quadrant is supplied by `Work.FTS.TransportS.mixed_dz_eqOn` from `SmoothOpen`; here that identity
is a hypothesis, so the statement is a strict generalisation and hence true. -/
theorem SlotSum_dz_le_of {α : ℝ} {n : ℕ} {u v : ℝ → ℝ → ℝ}
    (hu : ∀ a b : ℕ, a + b ≤ n →
      Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
        (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : ∀ a b : ℕ, a + b ≤ n →
      Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
        (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      ≤ Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  rw [Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm,
    Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b hb =>
            SlotTerm_dz_le_of α a b
              (hu a b (by
                simp only [Finset.mem_range] at ha hb
                omega))
              (hv a b (by
                simp only [Finset.mem_range] at ha hb
                omega))))
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - a),
          Work.FTS.TransportS.SlotTerm α a b u v := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        by_cases ha : a ≤ n + 1
        · rw [show n + 2 - a = (n + 1 - a) + 1 from by omega]
          conv_rhs => rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right
            (show (0 : ℝ) ≤ Work.FTS.TransportS.SlotTerm α a 0 u v from
              Work.FTS.TransportS.SlotTerm_nonneg α a 0 u v)
        · rw [show n + 1 - a = 0 from by omega]
          simp only [Finset.range_zero, Finset.sum_empty]
          exact Finset.sum_nonneg (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α a b u v)
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          Work.FTS.TransportS.SlotTerm α a' b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg
            (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
