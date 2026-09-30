import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Double counting: the number of ordered pairs `(x, y)` with `key x = key y` equals the sum
over the image of `key` of the square of the fibre size. -/
theorem fiber_pairs_sq_sum {Ω κ : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq κ] (key : Ω → κ) :
    (((Finset.univ : Finset Ω).product (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => key q.1 = key q.2)).card =
      ∑ k ∈ (Finset.univ : Finset Ω).image key,
        ((Finset.univ : Finset Ω).filter (fun x => key x = k)).card ^ 2 := by
  classical
  let f : κ → ℕ := fun k => ((Finset.univ : Finset Ω).filter (fun x => key x = k)).card
  have key_mem : ∀ a ∈ (Finset.univ : Finset Ω), key a ∈ (Finset.univ : Finset Ω).image key :=
    fun a _ => Finset.mem_image_of_mem key (Finset.mem_univ a)
  have hfkey : ∀ a : Ω,
      ((Finset.univ : Finset Ω).filter (fun b => key a = key b)).card = f (key a) := by
    intro a
    have h : (Finset.univ : Finset Ω).filter (fun b => key a = key b)
        = (Finset.univ : Finset Ω).filter (fun b => key b = key a) :=
      Finset.filter_congr (fun b _ => eq_comm)
    rw [h]
  calc
    (((Finset.univ : Finset Ω).product (Finset.univ : Finset Ω)).filter
        (fun q : Ω × Ω => key q.1 = key q.2)).card
        = ∑ a ∈ (Finset.univ : Finset Ω), f (key a) := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter,
              show (Finset.univ : Finset Ω).product Finset.univ
                  = ((Finset.univ : Finset Ω) ×ˢ Finset.univ) from rfl, Finset.sum_product]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_boole]
          exact hfkey a
    _ = ∑ k ∈ (Finset.univ : Finset Ω).image key,
        ((Finset.univ : Finset Ω).filter (fun x => key x = k)).card ^ 2 := by
          rw [← Finset.sum_fiberwise_of_maps_to' key_mem f]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_const_nat (fun x hx => rfl), pow_two]

end Work.BMF
