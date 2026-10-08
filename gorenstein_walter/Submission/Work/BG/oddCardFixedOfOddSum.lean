import Mathlib

namespace Work.BG

/-- **Parity of the fixed-point count of an involution.**
Let `X` be a finite type with an involution `f` (`f (f x) = x`) and let `m : X → ℕ` be
`f`-invariant (`m (f x) = m x`). If the total sum `Σ_x m x` is odd, then the number of `f`-fixed
points at which `m` is odd is odd: `Odd #{x | f x = x ∧ Odd (m x)}`.
Route: the non-fixed points of `X` pair up under `f` with equal weight, so their contribution to
`Σ_x m x` is even (`Finset.sum_involution` in `ZMod 2`); hence `Σ_x m x ≡ Σ_{f x = x} m x`, and
`Σ_{f x = x} m x ≡ #{f x = x : Odd (m x)}` mod 2 (`Finset.odd_sum_iff_odd_card_odd`). -/
theorem oddCardFixedOfOddSum {X : Type} [Fintype X] (f : X → X)
    (hf : ∀ x, f (f x) = x) (m : X → ℕ) (hm : ∀ x, m (f x) = m x)
    (hodd : Odd (∑ x : X, m x)) :
    Odd (Nat.card {x : X // f x = x ∧ Odd (m x)}) := by
  classical
  let φ : X → ZMod 2 := fun x => (m x : ZMod 2)
  let F : Finset X := Finset.univ.filter (fun x => f x = x)
  let N : Finset X := Finset.univ.filter (fun x => ¬ f x = x)
  -- The total sum, read in `ZMod 2`, is `1`.
  have hsum_cast : ((∑ x : X, m x : ℕ) : ZMod 2) = ∑ x : X, φ x := by
    rw [Nat.cast_sum]
  have htotal : ∑ x : X, φ x = 1 := by
    rw [← hsum_cast]
    exact ZMod.natCast_eq_one_iff_odd.mpr hodd
  -- Non-fixed points pair up, so their total contribution vanishes.
  have hN_sum : ∑ x ∈ N, φ x = 0 := by
    refine Finset.sum_involution (s := N) (f := φ) (g := fun x _ => f x) ?_ ?_ ?_ ?_
    · intro x hx
      have hfx : φ (f x) = φ x := by simp [φ, hm x]
      rw [hfx, CharTwo.add_self_eq_zero]
    · intro x hx _
      exact (Finset.mem_filter.mp hx).2
    · intro x hx
      have hx' : ¬ (f x = x) := (Finset.mem_filter.mp hx).2
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hf x, eq_comm] using hx'
    · intro x hx
      exact hf x
  -- Hence the total sum equals the sum over fixed points.
  have hsplit : ∑ x : X, φ x = ∑ x ∈ F, φ x := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = x) φ
    rw [← h]
    rw [show (Finset.univ.filter (fun x => f x = x)) = F from rfl,
        show (Finset.univ.filter (fun x => ¬ f x = x)) = N from rfl,
        hN_sum, add_zero]
  have hfixed : ∑ x ∈ F, φ x = 1 := by
    rw [← hsplit]
    exact htotal
  -- On the fixed point set, the sum counts the points with odd weight.
  have hFsum : ∑ x ∈ F, φ x = (({x ∈ F | Odd (m x)} : Finset X).card : ZMod 2) := by
    rw [← Finset.sum_boole (fun x => Odd (m x)) F]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases h : Odd (m x)
    · rw [if_pos h]
      exact ZMod.natCast_eq_one_iff_odd.mpr h
    · rw [if_neg h]
      exact ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h)
  have hcard_cast : (({x ∈ F | Odd (m x)} : Finset X).card : ZMod 2) = 1 := by
    rw [← hFsum]
    exact hfixed
  have hcard_odd : Odd ({x ∈ F | Odd (m x)} : Finset X).card :=
    ZMod.natCast_eq_one_iff_odd.mp hcard_cast
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa [F, Finset.filter_filter] using hcard_odd

end Work.BG
