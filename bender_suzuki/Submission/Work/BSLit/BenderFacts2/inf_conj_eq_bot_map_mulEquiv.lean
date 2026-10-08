import Mathlib
import Submission.Work.BSLit.BenderFacts2.threePointAPI

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- **The group-theoretic three-point condition transports along a `MulEquiv`.**  The condition `∀ x y, x ∉ H → y ∉ H → x⁻¹ * y ∉ H → H ⊓ x H x⁻¹ ⊓ y H y⁻¹ = ⊥` holds for `H ≤ G` iff it holds for the image `H.map e` in `G'`.  Route: a subgroup of `G'` is in the image of `Subgroup.map e` iff it is `K.map e`; use `Subgroup.map_inf` and `Work.BSLit.BenderFacts2.conj_map_mulEquiv` (`(x H x⁻¹)^e = (e x) H^e (e x)⁻¹`) to compute the image of the intersection, and `Subgroup.mem_map_iff_mem` for the three membership conditions. -/
theorem inf_conj_eq_bot_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
    (e : G ≃* G') :
    (∀ x y : G, x ∉ H → y ∉ H → x⁻¹ * y ∉ H →
      H ⊓ Submission.Blueprint.conj x H ⊓ Submission.Blueprint.conj y H = ⊥) ↔
    (∀ x y : G', x ∉ H.map e.toMonoidHom → y ∉ H.map e.toMonoidHom →
      x⁻¹ * y ∉ H.map e.toMonoidHom →
      H.map e.toMonoidHom ⊓ Submission.Blueprint.conj x (H.map e.toMonoidHom) ⊓
        Submission.Blueprint.conj y (H.map e.toMonoidHom) = ⊥) := by
  have hf : Function.Injective (e.toMonoidHom : G →* G') := e.injective
  constructor
  · intro hG x y hx hy hxy
    have haH : e.symm x ∉ H := fun hm =>
      hx (by rw [← e.apply_symm_apply x]; exact Subgroup.mem_map_of_mem e.toMonoidHom hm)
    have hbH : e.symm y ∉ H := fun hm =>
      hy (by rw [← e.apply_symm_apply y]; exact Subgroup.mem_map_of_mem e.toMonoidHom hm)
    have habH : (e.symm x)⁻¹ * (e.symm y) ∉ H := fun hm =>
      hxy (by
        rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, ← map_inv, ← map_mul]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hm)
    have h := hG (e.symm x) (e.symm y) haH hbH habH
    have key : (H ⊓ Submission.Blueprint.conj (e.symm x) H ⊓
          Submission.Blueprint.conj (e.symm y) H).map e.toMonoidHom =
        H.map e.toMonoidHom ⊓ Submission.Blueprint.conj x (H.map e.toMonoidHom) ⊓
          Submission.Blueprint.conj y (H.map e.toMonoidHom) := by
      rw [Subgroup.map_inf _ _ _ hf, Subgroup.map_inf _ _ _ hf,
        conj_map_mulEquiv H e (e.symm x), conj_map_mulEquiv H e (e.symm y),
        e.apply_symm_apply x, e.apply_symm_apply y]
    rw [← key, h, Subgroup.map_bot]
  · intro hG' a b ha hb hab
    have hx : e a ∉ H.map e.toMonoidHom := fun hm => ha ((Subgroup.mem_map_iff_mem hf).mp hm)
    have hy : e b ∉ H.map e.toMonoidHom := fun hm => hb ((Subgroup.mem_map_iff_mem hf).mp hm)
    have hxy : (e a)⁻¹ * e b ∉ H.map e.toMonoidHom := fun hm => hab (by
      rw [← map_inv, ← map_mul] at hm
      exact (Subgroup.mem_map_iff_mem hf).mp hm)
    have h := hG' (e a) (e b) hx hy hxy
    have key : (H ⊓ Submission.Blueprint.conj a H ⊓
          Submission.Blueprint.conj b H).map e.toMonoidHom =
        H.map e.toMonoidHom ⊓ Submission.Blueprint.conj (e a) (H.map e.toMonoidHom) ⊓
          Submission.Blueprint.conj (e b) (H.map e.toMonoidHom) := by
      rw [Subgroup.map_inf _ _ _ hf, Subgroup.map_inf _ _ _ hf,
        conj_map_mulEquiv H e a, conj_map_mulEquiv H e b]
    have hmap : (H ⊓ Submission.Blueprint.conj a H ⊓
          Submission.Blueprint.conj b H).map e.toMonoidHom = ⊥ := by rw [key, h]
    exact (Subgroup.map_injective hf) (by rw [hmap, Subgroup.map_bot])

end Work.BSLit.BenderFacts2
