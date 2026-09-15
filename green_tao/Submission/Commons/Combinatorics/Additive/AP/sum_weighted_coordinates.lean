import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Additive.AP

open Finset

theorem sum_weighted_coordinates {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n)
    (c : Fin n → ZMod p) (hc : ∃ i, c i ≠ 0) (g : ZMod p → ℝ) :
    (∑ y : Fin n → ZMod p, g (∑ i, c i * y i)) = (p : ℝ)^(n-1) * ∑ x : ZMod p, g x := by
  obtain ⟨i0, hi0⟩ := hc
  -- the linear functional `y ↦ ∑ i, c i * y i` as an additive monoid homomorphism
  let φ : (Fin n → ZMod p) →+ ZMod p :=
    { toFun := fun y => ∑ i, c i * y i
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ y, φ y = ∑ i, c i * y i := fun _ => rfl
  -- `φ` is surjective because the coordinate `i0` has a nonzero (hence invertible) coefficient
  have hsurj : Function.Surjective φ := by
    intro x
    refine ⟨(Function.update 0 i0 ((c i0)⁻¹ * x)), ?_⟩
    rw [hφ]
    rw [Finset.sum_eq_single i0]
    · rw [Function.update_self, ← mul_assoc, mul_inv_cancel₀ hi0, one_mul]
    · intro j _ hj
      rw [Function.update_of_ne hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ i0) h
  -- all fibres of `φ` have the same cardinality
  have hfibeq : ∀ z : ZMod p,
      Fintype.card {y : Fin n → ZMod p // φ y = z}
        = Fintype.card {y : Fin n → ZMod p // φ y = 0} := by
    intro z
    rw [Fintype.card_subtype (fun y => φ y = z),
      Fintype.card_subtype (fun y => φ y = 0)]
    exact AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj z) ⟨0, map_zero φ⟩
  -- and that common cardinality is `p ^ (n - 1)`
  have hK : Fintype.card {y : Fin n → ZMod p // φ y = 0} = p ^ (n - 1) := by
    have hsum1 : ∑ x : ZMod p, Fintype.card {y : Fin n → ZMod p // φ y = x}
        = Fintype.card (Fin n → ZMod p) := by
      have h := Fintype.sum_fiberwise φ (fun _ : Fin n → ZMod p => (1 : ℕ))
      simpa using h
    have hsum2 : ∑ x : ZMod p, Fintype.card {y : Fin n → ZMod p // φ y = x}
        = Fintype.card (ZMod p) * Fintype.card {y : Fin n → ZMod p // φ y = 0} := by
      have hcongr : ∑ x : ZMod p, Fintype.card {y : Fin n → ZMod p // φ y = x}
          = ∑ _x : ZMod p, Fintype.card {y : Fin n → ZMod p // φ y = 0} :=
        Finset.sum_congr rfl (fun z _ => hfibeq z)
      rw [hcongr, Finset.sum_const, Finset.card_univ]
      simp
    have heq : Fintype.card (ZMod p) * Fintype.card {y : Fin n → ZMod p // φ y = 0}
        = Fintype.card (Fin n → ZMod p) := hsum2 ▸ hsum1
    rw [ZMod.card p, Fintype.card_fun, Fintype.card_fin, ZMod.card p] at heq
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hpn : p ^ n = p * p ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ, mul_comm]
    rw [hpn] at heq
    exact Nat.mul_left_cancel hp heq
  have hcard : ∀ x : ZMod p, Fintype.card {y : Fin n → ZMod p // φ y = x} = p ^ (n - 1) :=
    fun x => by rw [hfibeq x, hK]
  calc (∑ y : Fin n → ZMod p, g (∑ i, c i * y i))
      = ∑ y : Fin n → ZMod p, g (φ y) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hφ y]
    _ = ∑ x : ZMod p, ∑ y : {y : Fin n → ZMod p // φ y = x}, g x :=
        (Fintype.sum_fiberwise' φ g).symm
    _ = ∑ x : ZMod p, (p : ℝ)^(n-1) * g x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard x, Nat.cast_pow]
    _ = (p : ℝ)^(n-1) * ∑ x : ZMod p, g x := by rw [Finset.mul_sum]

end Commons.Combinatorics.Additive.AP