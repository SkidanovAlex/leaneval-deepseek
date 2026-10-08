import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

open Subgroup

theorem sq_commute {G : Type*} [Group G] {s : G} {I R : Subgroup G}
    (hI : Work.GW2.Inverts s I) (hR : Work.GW2.Inverts s R)
    (hRI : R ≤ Subgroup.normalizer (I : Set G))
    {k : G} (hk : k ∈ R) {x : G} (hx : x ∈ I) : Commute (k ^ 2) x := by
  have hkI : k ∈ Subgroup.normalizer (I : Set G) := hRI hk
  have hkx : k * x * k⁻¹ ∈ I := ((Subgroup.mem_normalizer_iff).mp hkI x).mp hx
  have hk2 : k⁻¹ ∈ R := R.inv_mem hk
  have hinvR : s * k * s⁻¹ = k⁻¹ := hR k hk
  have hinvR' : s * k⁻¹ * s⁻¹ = k := by have := hR k⁻¹ hk2; simpa using this
  have hinvI : s * x * s⁻¹ = x⁻¹ := hI x hx
  have hraw : s * (k * x * k⁻¹) * s⁻¹ = (k * x * k⁻¹)⁻¹ := hI (k * x * k⁻¹) hkx
  have key : k⁻¹ * x⁻¹ * k = k * x⁻¹ * k⁻¹ := by
    calc k⁻¹ * x⁻¹ * k = (s * k * s⁻¹) * (s * x * s⁻¹) * (s * k⁻¹ * s⁻¹) := by
          rw [hinvR, hinvI, hinvR']
      _ = s * (k * x * k⁻¹) * s⁻¹ := by group
      _ = (k * x * k⁻¹)⁻¹ := hraw
      _ = k * x⁻¹ * k⁻¹ := by group
  have h2 : x⁻¹ * k ^ 2 = k ^ 2 * x⁻¹ := by
    have := congrArg (fun t => k * t * k) key
    simpa [sq, mul_assoc] using this
  have hc : Commute x (k ^ 2) := by
    have h0 : Commute x⁻¹ (k ^ 2) := h2
    simpa using Commute.inv_left h0
  exact hc.symm

end Work.CORE4
