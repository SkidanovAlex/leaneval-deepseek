import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- **Fibre decomposition of the discrepancy count.**  For a map `f : S → V` into an additive
commutative group, the number of pairs `(x,y)` with `f x - f y = d` equals the sum, over all
values `v` of `f`, of the product of the fibre counts at `v` and at `v + d`. -/
theorem card_sub_eq_sum_fiber {S V : Type*} [Fintype S] [AddCommGroup V] [DecidableEq V]
    (f : S → V) (d : V) :
    ((Finset.univ : Finset (S × S)).filter (fun p => f p.1 - f p.2 = d)).card =
      ∑ v ∈ (Finset.univ : Finset S).image f,
        ((Finset.univ : Finset S).filter (fun x => f x = v)).card *
        ((Finset.univ : Finset S).filter (fun y => f y = v + d)).card := by
  classical
  -- Write `A` for the set of pairs counted on the left and `I` for the image of `f`.
  set A : Finset (S × S) :=
    (Finset.univ : Finset (S × S)).filter (fun p => f p.1 - f p.2 = d) with hA
  set I : Finset V := (Finset.univ : Finset S).image f with hI
  -- The second coordinate of a counted pair always lies in the image of `f`.
  have hmap : Set.MapsTo (fun p : S × S => f p.2) (↑A : Set (S × S)) (↑I : Set V) := by
    intro p hp
    simp only [Finset.mem_coe, hI, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨p.2, rfl⟩
  -- The fibre of `A` over a value `b` is the product of the fibres at `b + d` and at `b`.
  have hfib : ∀ b : V, A.filter (fun a : S × S => f a.2 = b) =
      ((Finset.univ : Finset S).filter (fun x => f x = b + d)) ×ˢ
      ((Finset.univ : Finset S).filter (fun y => f y = b)) := by
    intro b
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, hA]
    constructor
    · rintro ⟨hpd, hyb⟩
      rw [sub_eq_iff_eq_add'] at hpd
      exact ⟨by rw [hpd, hyb], hyb⟩
    · rintro ⟨hxb, hyb⟩
      exact ⟨by rw [sub_eq_iff_eq_add', hxb, hyb], hyb⟩
  -- Count `A` by its fibres over the second coordinate, then identify each fibre.
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hfib b, Finset.card_product, mul_comm]

end Work.BMF.recursion
