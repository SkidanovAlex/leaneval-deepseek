import Mathlib.Tactic.Group
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Product

theorem prod_comp_eq_pow_card_ker {A B : Type*} [Group A] [Fintype A] [CommGroup B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) (g : B → ℂ) :
    ∏ a : A, g (f a) = (∏ b : B, g b) ^ Nat.card f.ker := by
  classical
  -- Each fibre of `f` over a point `b` is in bijection with `ker f`, hence has
  -- cardinality `Nat.card f.ker` (surjectivity supplies a base point).
  have hcard : ∀ b : B, (Finset.univ.filter (fun a : A => f a = b)).card = Nat.card f.ker := by
    intro b
    obtain ⟨a₀, ha₀⟩ := hf b
    let e : {a : A // f a = b} ≃ f.ker :=
      { toFun := fun a => ⟨a₀⁻¹ * a.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ha₀, a.2, inv_mul_cancel]⟩
        invFun := fun k => ⟨a₀ * k.1, by
          rw [map_mul, ha₀, k.2, mul_one]⟩
        left_inv := fun a => by
          apply Subtype.ext
          simp only
          group
        right_inv := fun k => by
          apply Subtype.ext
          simp only
          group }
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype (fun a : A => f a = b)]
    exact Fintype.card_congr e
  -- Split the product over `A` into the fibres of `f`.
  calc ∏ a : A, g (f a)
      = ∏ b : B, ∏ a ∈ Finset.univ.filter (fun a : A => f a = b), g (f a) :=
          (Finset.prod_fiberwise Finset.univ (fun a : A => f a) (fun a : A => g (f a))).symm
    _ = ∏ b : B, (g b) ^ (Finset.univ.filter (fun a : A => f a = b)).card := by
          refine Finset.prod_congr rfl ?_
          intro b _
          rw [Finset.prod_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
            Finset.prod_const]
    _ = ∏ b : B, (g b) ^ Nat.card f.ker :=
          Finset.prod_congr rfl (fun b _ => by rw [hcard b])
    _ = (∏ b : B, g b) ^ Nat.card f.ker := Finset.prod_pow Finset.univ _ g

end NK.HeckeL.Product
