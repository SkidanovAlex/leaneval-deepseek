import Mathlib

namespace Work.Peluse.SwapC

theorem prodProdEraseEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [CommMonoid M] (a : ι) (F : ι → ι → M)
    (h : ∀ x y, x ≠ a → y ≠ a → F x y = 1) :
    (∏ x : ι, ∏ y : ι, F x y)
      = F a a * (∏ x ∈ (Finset.univ : Finset ι).erase a, F x a)
          * (∏ y ∈ (Finset.univ : Finset ι).erase a, F a y) := by
  classical
  -- Peel the inner product at `y = a` for each `x`.
  have hx : ∀ x : ι, (∏ y : ι, F x y)
      = F x a * ∏ y ∈ (Finset.univ : Finset ι).erase a, F x y := fun x =>
    (Finset.mul_prod_erase (Finset.univ : Finset ι) (fun y => F x y) (Finset.mem_univ a)).symm
  -- Peel the outer product at `x = a`.
  have houter : (∏ x : ι, F x a)
      = F a a * ∏ x ∈ (Finset.univ : Finset ι).erase a, F x a :=
    (Finset.mul_prod_erase (Finset.univ : Finset ι) (fun x => F x a) (Finset.mem_univ a)).symm
  -- For `y ≠ a`, the sum over all `x` collapses to the `x = a` term.
  have hy : ∀ y ∈ (Finset.univ : Finset ι).erase a, (∏ x : ι, F x y) = F a y := by
    intro y hy
    have hya : y ≠ a := Finset.ne_of_mem_erase hy
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι) (fun x => F x y) (Finset.mem_univ a)]
    rw [Finset.prod_eq_one (fun x hx' => h x y (Finset.ne_of_mem_erase hx') hya), mul_one]
  -- Swap the order of summation over the off-diagonal part.
  have hinner : (∏ x : ι, ∏ y ∈ (Finset.univ : Finset ι).erase a, F x y)
      = ∏ y ∈ (Finset.univ : Finset ι).erase a, F a y := by
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl hy
  calc (∏ x : ι, ∏ y : ι, F x y)
      = ∏ x : ι, (F x a * ∏ y ∈ (Finset.univ : Finset ι).erase a, F x y) :=
        Finset.prod_congr rfl (fun x _ => hx x)
    _ = (∏ x : ι, F x a) * (∏ x : ι, ∏ y ∈ (Finset.univ : Finset ι).erase a, F x y) :=
        Finset.prod_mul_distrib
    _ = F a a * (∏ x ∈ (Finset.univ : Finset ι).erase a, F x a)
          * (∏ y ∈ (Finset.univ : Finset ι).erase a, F a y) := by
        rw [houter, hinner]

end Work.Peluse.SwapC
