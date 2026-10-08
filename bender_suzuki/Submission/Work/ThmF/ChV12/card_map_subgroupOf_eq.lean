import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of `P ≤ V` under a homomorphism injective on `P`

Let `V = centD H t` and `W = W H t ≤ V`, and let `ρ : V →* M` be a homomorphism whose kernel
is `W` (as a subgroup of `V`).  If `P ≤ V` meets `W` trivially, then `ρ` is injective on
`P.subgroupOf V`, so the image `(P.subgroupOf V).map ρ` has the same cardinality as `P`.

This is the cardinality computation in Ch. V §3 step (1) of the Bender–Suzuki development: for
the action `ρ : V →* (F ≃+* F)` of `V` on the field `F` with kernel `W`
(Ch. V §1 Prop. 3), a subgroup `P ≤ V` of prime order with `P ∩ W = 1` has image of order `|P|`
in `Aut F`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- The image of `P ≤ V` under a homomorphism whose kernel (which is `W` by hypothesis) meets
`P` trivially has the same cardinality as `P`. -/
theorem card_map_subgroupOf_eq {G : Type} [Group G] (H : Subgroup G) (t : G) (P : Subgroup G)
    (hPV : P ≤ Submission.Blueprint.centD H t) (hPW : P ⊓ W H t = ⊥)
    {M : Type} [Group M] (ρ : ↥(Submission.Blueprint.centD H t) →* M)
    (hker : ρ.ker = (W H t).subgroupOf (Submission.Blueprint.centD H t)) :
    Nat.card ↥(Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t))) = Nat.card ↥P := by
  -- `ρ` has trivial kernel on `P.subgroupOf V`
  have hinj : ∀ v : ↥(P.subgroupOf (Submission.Blueprint.centD H t)), ρ v = 1 → v = 1 := by
    intro v h1
    have hmem : (v : ↥(Submission.Blueprint.centD H t)) ∈ ρ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have h2 : ((v : ↥(Submission.Blueprint.centD H t)) : G) ∈ P ⊓ W H t := ⟨v.2, hmem⟩
    rw [hPW, Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  have hbij : Function.Bijective (fun v : ↥(P.subgroupOf (Submission.Blueprint.centD H t)) =>
      (⟨ρ v, Subgroup.mem_map_of_mem ρ v.2⟩ :
        ↥(Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t))))) := by
    constructor
    · intro v w hvw
      have h2 : ρ (v : ↥(Submission.Blueprint.centD H t))
          = ρ (w : ↥(Submission.Blueprint.centD H t)) := congrArg Subtype.val hvw
      have h1 : ρ ((v : ↥(Submission.Blueprint.centD H t))
          * (w : ↥(Submission.Blueprint.centD H t))⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      have h3 : v * w⁻¹ = 1 := hinj (v * w⁻¹) h1
      exact mul_inv_eq_one.mp h3
    · intro y
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩
  have h1 : Nat.card ↥(P.subgroupOf (Submission.Blueprint.centD H t))
      = Nat.card ↥(Subgroup.map ρ (P.subgroupOf (Submission.Blueprint.centD H t))) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  -- the identity map identifies `P.subgroupOf V` with `P` when `P ≤ V`
  have h2 : Nat.card ↥(P.subgroupOf (Submission.Blueprint.centD H t)) = Nat.card ↥P :=
    Nat.card_congr
      { toFun := fun v => (⟨v.1.1, v.2⟩ : ↥P)
        invFun := fun g =>
          (⟨⟨(g : G), hPV g.2⟩, g.2⟩ : ↥(P.subgroupOf (Submission.Blueprint.centD H t)))
        left_inv := fun v => Subtype.ext (Subtype.ext rfl)
        right_inv := fun g => Subtype.ext rfl }
  exact h1.symm.trans h2

end Work.ThmF.ChV12
