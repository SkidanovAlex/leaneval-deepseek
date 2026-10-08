import Mathlib
import Submission.Work.DSTR.D16Aux

namespace Work.DSTR.D16

/-- **In a `2`-group every nontrivial element has a power of order `2`.**  Proof: `IsPGroup.iff_card`
gives `Nat.card H = 2 ^ n` for `H = Subgroup.zpowers g` (`IsPGroup.to_subgroup`), so
`orderOf g = Nat.card (Subgroup.zpowers g) = 2 ^ k` (`Nat.card_zpowers` / `Fintype.card_zpowers`);
`g ≠ 1` gives `k ≠ 0`, and then `x := g ^ 2 ^ (k - 1)` has `orderOf x = 2` by `orderOf_pow` and the
`Nat.gcd` computation, with `x ∈ Subgroup.zpowers g`.  This is the shared-library fact behind
"a nontrivial normal `2`-subgroup meets the centre in an involution" (Bender 1.6(b)).

Useful names: `IsPGroup.to_subgroup`, `IsPGroup.iff_card`, `Nat.card_zpowers`,
`orderOf_pow` (`orderOf (g ^ n) = orderOf g / Nat.gcd (orderOf g) n`), `Subgroup.pow_mem`. -/
theorem exists_zpowers_orderOf_eq_two {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {g : G} (hg : g ≠ 1) : ∃ x ∈ Subgroup.zpowers g, orderOf x = 2 := by
  -- `IsPGroup.iff_orderOf` turns the `2`-group hypothesis into `orderOf g = 2 ^ k`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := G)).mp hG g
  -- `g ≠ 1` forces `k ≠ 0`, since `orderOf g = 1` would give `g = 1`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hk
    exact hg (orderOf_eq_one_iff.mp hk)
  -- hence `orderOf g` is even,
  have h2dvd : 2 ∣ orderOf g := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  -- and the `(orderOf g / 2)`-th power of `g` is an involution inside `⟨g⟩`.
  exact ⟨g ^ (orderOf g / 2),
    Subgroup.pow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) _,
    orderOf_pow_orderOf_div (orderOf_pos g).ne' h2dvd⟩

end Work.DSTR.D16
