import Mathlib

namespace Work.Peluse.LadderP

/-- The number of `A : Fin j → Fin M` satisfying a single linear equation `∑ k, w k * A k = t`, whose coefficient at some index `i₀` is `1`, is at most `M ^ (j - 1)`. -/
theorem cardLinEqLe {j M : ℕ} (w : Fin j → ℤ) (i₀ : Fin j) (hi : w i₀ = 1) (t : ℤ) :
    (Finset.univ.filter (fun A : Fin j → Fin M => ∑ k, w k * (A k : ℤ) = t)).card ≤ M ^ (j - 1) := by
  classical
  -- The solution set of the equation.
  set S : Finset (Fin j → Fin M) :=
    Finset.univ.filter (fun A : Fin j → Fin M => ∑ k, w k * (A k : ℤ) = t) with hS
  -- `Fin j` minus one point has `j - 1` elements.
  have hcompl : Fintype.card {k : Fin j // k ≠ i₀} = j - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin]
  -- Forgetting the `i₀`-th coordinate is injective on the solution set: two solutions agreeing
  -- away from `i₀` agree at `i₀` too, because the equation determines it (`w i₀ = 1`).
  have hinj : Set.InjOn (fun A : Fin j → Fin M => (fun k : {k : Fin j // k ≠ i₀} => A k.1)) ↑S := by
    intro A hA B hB hAB
    have hA' : ∑ k, w k * (A k : ℤ) = t := by
      have := hA; rw [hS] at this; exact (Finset.mem_filter.mp this).2
    have hB' : ∑ k, w k * (B k : ℤ) = t := by
      have := hB; rw [hS] at this; exact (Finset.mem_filter.mp this).2
    funext k
    by_cases hk : k = i₀
    · subst k
      have hzero : ∑ q : Fin j, (w q * (A q : ℤ) - w q * (B q : ℤ)) = 0 := by
        rw [Finset.sum_sub_distrib, hA', hB', sub_self]
      have hsingle : ∑ q : Fin j, (w q * (A q : ℤ) - w q * (B q : ℤ))
          = w i₀ * (A i₀ : ℤ) - w i₀ * (B i₀ : ℤ) := by
        refine Finset.sum_eq_single i₀ ?_ ?_
        · intro b _ hb
          have hb' : A b = B b := congrFun hAB ⟨b, hb⟩
          rw [hb', sub_self]
        · intro h; exact absurd (Finset.mem_univ i₀) h
      have hwnz : w i₀ ≠ 0 := by rw [hi]; exact one_ne_zero
      have hcast : (A i₀ : ℤ) = (B i₀ : ℤ) :=
        mul_left_cancel₀ hwnz (sub_eq_zero.mp (hsingle ▸ hzero))
      exact Fin.ext (by exact_mod_cast hcast)
    · exact congrFun hAB ⟨k, hk⟩
  calc S.card
      = (S.image (fun A : Fin j → Fin M =>
          (fun k : {k : Fin j // k ≠ i₀} => A k.1))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card ({k : Fin j // k ≠ i₀} → Fin M) := Finset.card_le_univ _
    _ = M ^ (j - 1) := by rw [Fintype.card_fun, Fintype.card_fin, hcompl]

end Work.Peluse.LadderP
