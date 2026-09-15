import Mathlib

namespace Commons.Combinatorics.Additive.AP

open Finset

/-- A counting identity for two linear forms over `ZMod p`:  if the map
`y ↦ (∑ i, c i * y i, ∑ i, d i * y i)` from `(Fin n → ZMod p)` onto
`ZMod p × ZMod p` is surjective, then every fibre of this map has
`p ^ (n - 2)` elements, so summing `g` over the image of the map equals
`p ^ (n - 2)` times the sum of `g` over all of `ZMod p × ZMod p`. -/
theorem sum_of_two_linear_forms {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 2 ≤ n)
    (c d : Fin n → ZMod p)
    (hsurj : Function.Surjective (fun y : Fin n → ZMod p => (∑ i, c i * y i, ∑ i, d i * y i)))
    (g : ZMod p × ZMod p → ℝ) :
    (∑ y : Fin n → ZMod p, g (∑ i, c i * y i, ∑ i, d i * y i))
      = (p : ℝ) ^ (n - 2) * ∑ z : ZMod p × ZMod p, g z := by
  classical
  -- Package the two linear forms as an additive homomorphism.
  let F : (Fin n → ZMod p) →+ (ZMod p × ZMod p) :=
    { toFun := fun y => (∑ i, c i * y i, ∑ i, d i * y i)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;>
          · rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring }
  have hFfun : ∀ y : Fin n → ZMod p, F y = (∑ i, c i * y i, ∑ i, d i * y i) := fun _ => rfl
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨y, hy⟩ := hsurj z
    exact ⟨y, by rw [hFfun y]; exact hy⟩
  -- The common cardinality of the fibres.
  set m : ℕ := Fintype.card {y : Fin n → ZMod p // F y = 0} with hm
  have hcard : ∀ z : ZMod p × ZMod p,
      Fintype.card {y : Fin n → ZMod p // F y = z} = m := by
    intro z
    have h := AddMonoidHom.card_fiber_eq_of_mem_range F
      (x := (0 : ZMod p × ZMod p)) (y := z) ⟨0, map_zero F⟩ (hFsurj z)
    rw [← Fintype.card_subtype (fun y => F y = 0),
        ← Fintype.card_subtype (fun y => F y = z)] at h
    rw [hm]
    exact h.symm
  -- Sum of the fibre cardinalities is the cardinality of the source.
  have hsum : (∑ z : ZMod p × ZMod p, Fintype.card {y : Fin n → ZMod p // F y = z})
      = Fintype.card (Fin n → ZMod p) := by
    have h := Fintype.sum_fiberwise' (M := ℕ) F (fun _ : ZMod p × ZMod p => (1 : ℕ))
    simpa using h
  have hsum_eq : (∑ z : ZMod p × ZMod p, Fintype.card {y : Fin n → ZMod p // F y = z})
      = Fintype.card (ZMod p × ZMod p) * m := by
    simp only [hcard]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcardG : Fintype.card (Fin n → ZMod p) = p ^ n := by
    rw [Fintype.card_fun]
    simp [ZMod.card]
  have hcardP : Fintype.card (ZMod p × ZMod p) = p ^ 2 := by
    rw [Fintype.card_prod]
    simp [ZMod.card, pow_two]
  have hp2m : p ^ 2 * m = p ^ n := by
    have h := hsum_eq.symm.trans hsum
    rw [hcardP, hcardG] at h
    exact h
  have hn2 : 2 + (n - 2) = n := by omega
  have hm_eq : m = p ^ (n - 2) := by
    have hpown : p ^ n = p ^ 2 * p ^ (n - 2) := by
      conv_lhs => rw [← hn2]
      rw [pow_add]
    have h2 : p ^ 2 * m = p ^ 2 * p ^ (n - 2) := by rw [hp2m, hpown]
    exact Nat.eq_of_mul_eq_mul_left (by have hp : 0 < p := (Fact.out : p.Prime).pos; positivity) h2
  -- Decompose the sum into fibres.
  have hsplit : (∑ y : Fin n → ZMod p, g (F y))
      = ∑ z : ZMod p × ZMod p,
          (Fintype.card {y : Fin n → ZMod p // F y = z} : ℝ) * g z := by
    rw [← Fintype.sum_fiberwise' (M := ℝ) (g := F) (f := g)]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hconst : (∑ z : ZMod p × ZMod p,
        (Fintype.card {y : Fin n → ZMod p // F y = z} : ℝ) * g z)
      = (m : ℝ) * ∑ z : ZMod p × ZMod p, g z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [hcard z]
  have hmR : (m : ℝ) = (p : ℝ) ^ (n - 2) := by
    rw [hm_eq, Nat.cast_pow]
  change (∑ y : Fin n → ZMod p, g (F y)) = (p : ℝ) ^ (n - 2) * ∑ z : ZMod p × ZMod p, g z
  rw [hsplit, hconst, hmR]

end Commons.Combinatorics.Additive.AP
