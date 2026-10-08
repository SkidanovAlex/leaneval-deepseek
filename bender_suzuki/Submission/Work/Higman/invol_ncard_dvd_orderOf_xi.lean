import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- In a Suzuki 2-group `P`, the involutions form a single orbit under the cyclic group
`⟨ξ⟩`; hence their number divides `orderOf ξ`. -/
theorem invol_ncard_dvd_orderOf_xi {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    (Work.Higman.Invol P).ncard ∣ orderOf h.xi := by
  -- Fix an involution `u`; `K = ⟨ξ⟩` acts on `P` by evaluation.
  obtain ⟨u, -, hu2, -, -⟩ := h.manyInvol
  set K : Subgroup (MulAut P) := Subgroup.zpowers h.xi with hK
  -- `ξ` preserves involutions, and `h.trans` says it is transitive on them:
  -- so the involutions are exactly the orbit of `u` under `K`.
  have horbit : (MulAction.orbit K u : Set P) = Invol P := by
    ext z
    rw [MulAction.mem_orbit_iff, mem_Invol]
    constructor
    · rintro ⟨g, rfl⟩
      show orderOf (g • u) = 2
      rw [show g • u = (g : MulAut P) u from rfl, MulEquiv.orderOf_eq, hu2]
    · intro hz
      obtain ⟨k, hk⟩ := h.trans u z hu2 hz
      have hmem : h.xi ^ k ∈ K := by
        rw [hK]
        exact Subgroup.pow_mem (Subgroup.zpowers h.xi) (Subgroup.mem_zpowers h.xi) k
      exact ⟨⟨h.xi ^ k, hmem⟩, hk⟩
  -- Orbit-stabiliser in `K`: `|orbit| * |stabiliser| = |K| = orderOf ξ`.
  have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K u)
  rw [Nat.card_prod, hK, Nat.card_zpowers] at hos
  have hcard : (Invol P).ncard = Nat.card (MulAction.orbit K u) := by
    rw [Nat.card_coe_set_eq, horbit]
  exact ⟨Nat.card ↥(MulAction.stabilizer K u), by rw [hcard]; exact hos.symm⟩

end Work.Higman
