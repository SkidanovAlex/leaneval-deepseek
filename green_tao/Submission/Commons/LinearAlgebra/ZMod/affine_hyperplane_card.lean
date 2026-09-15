import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.PicardGroup

namespace Commons.LinearAlgebra.ZMod

/-- The number of solutions `x : Fin t → ZMod p` of a nontrivial affine linear equation
`∑ j, L j * x j = b` with `L ≠ 0` is exactly `p ^ (t - 1)` (the kernel of a nonzero linear
functional on `(ZMod p)^t` has cardinality `p ^ (t-1)`). -/
theorem affine_hyperplane_card {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 1 ≤ t)
    (L : Fin t → ZMod p) (hL : L ≠ 0) (b : ZMod p) :
    ((Finset.univ : Finset (Fin t → ZMod p)).filter
      (fun x => ∑ j, L j * x j = b)).card = p ^ (t - 1) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hL
  -- the linear functional `x ↦ ∑ j, L j * x j`
  let f : (Fin t → ZMod p) →ₗ[ZMod p] ZMod p :=
    { toFun := fun x => ∑ j, L j * x j
      map_add' := by
        intro x y
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring) }
  have hf : ∀ x : Fin t → ZMod p, f x = ∑ j, L j * x j := fun _ => rfl
  -- `f` is surjective, using `L i ≠ 0`
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨fun j => if j = i then c / L i else 0, ?_⟩
    rw [hf, Fintype.sum_eq_single i (fun j hj => by simp [hj])]
    rw [if_pos rfl, ← mul_div_assoc, mul_div_cancel_left₀ c hi]
  -- a point `x0` with `f x0 = b`
  let x0 : Fin t → ZMod p := fun j => if j = i then b / L i else 0
  have hx0 : f x0 = b := by
    change f (fun j => if j = i then b / L i else 0) = b
    rw [hf, Fintype.sum_eq_single i (fun j hj => by simp [hj])]
    rw [if_pos rfl, ← mul_div_assoc, mul_div_cancel_left₀ b hi]
  -- the dimension of the kernel is `t - 1`
  have hfin : Module.finrank (ZMod p) (LinearMap.ker f) = t - 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hR : Module.finrank (ZMod p) (LinearMap.range f) = 1 := by
      rw [hrange, finrank_top]
      exact Module.finrank_self (ZMod p)
    have hV : Module.finrank (ZMod p) (Fin t → ZMod p) = t := Module.finrank_fin_fun (ZMod p)
    rw [hR, hV] at hrn
    omega
  have hker : Nat.card (LinearMap.ker f) = p ^ (t - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker f),
      Nat.card_eq_fintype_card, ZMod.card p, hfin]
  -- the solution set is a translate of the kernel
  have hequiv :
      Nat.card {x : Fin t → ZMod p // ∑ j, L j * x j = b} = Nat.card (LinearMap.ker f) :=
    (Nat.card_congr
      { toFun := fun y => ⟨x0 + y.1, by
          rw [← hf (x0 + y.1), map_add, hx0, LinearMap.mem_ker.mp y.2, add_zero]⟩
        invFun := fun z => ⟨z.1 - x0, by
          rw [LinearMap.mem_ker, map_sub, hf z.1, z.2, hx0, sub_self]⟩
        left_inv := fun y => Subtype.ext (add_sub_cancel_left x0 y.1)
        right_inv := fun z => Subtype.ext (add_sub_cancel x0 z.1) }).symm
  rw [← Fintype.card_subtype (fun x : Fin t → ZMod p => ∑ j, L j * x j = b),
    ← Nat.card_eq_fintype_card, hequiv, hker]

end Commons.LinearAlgebra.ZMod