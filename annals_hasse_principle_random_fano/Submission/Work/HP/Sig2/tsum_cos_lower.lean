import Mathlib

namespace Work.HP.Sig2

/-- A tsum lower bound: if `a ≥ 0` is summable on `α`, `c` takes the value `1` at `z` and satisfies
`-1 ≤ c x ≤ 1` everywhere, then `2 a z - ∑' x, a x ≤ ∑' x, a x * c x`.  (Used with
`a x = exp(-π s² ‖x‖²) ≥ 0` and `c x = cos (2π ⟨x,t⟩) ∈ [-1,1]`, `c 0 = 1`.) -/
theorem tsum_cos_lower {α : Type*} (a c : α → ℝ) (z : α)
    (ha : Summable a) (hpos : ∀ x, 0 ≤ a x) (hz : c z = 1)
    (hlow : ∀ x, -1 ≤ c x) (hhigh : ∀ x, c x ≤ 1) :
    2 * a z - ∑' x, a x ≤ ∑' x, a x * c x := by
  -- `a * c` is summable, since `|a x * c x| ≤ a x`.
  have hsum_ac : Summable (fun x => a x * c x) := by
    refine Summable.of_norm_bounded (g := a) ha (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos x)]
    calc a x * |c x| ≤ a x * 1 :=
          mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hlow x, hhigh x⟩) (hpos x)
      _ = a x := by ring
  -- `a * (c + 1)` is summable, being a sum of summable functions.
  have hsum_d : Summable (fun x => a x * (c x + 1)) := by
    have := hsum_ac.add ha
    simpa [mul_add, mul_one] using this
  -- The summand at `z` alone is `2 a z`.
  have hzterm : a z * (c z + 1) = 2 * a z := by rw [hz]; ring
  have key : a z * (c z + 1) ≤ ∑' x, a x * (c x + 1) :=
    hsum_d.le_tsum z (fun x _ => mul_nonneg (hpos x) (by linarith [hlow x]))
  rw [hzterm] at key
  -- Split the sum: `∑ (a (c+1)) = ∑ (a c) + ∑ a`.
  have hsplit : ∑' x, a x * (c x + 1) = ∑' x, a x * c x + ∑' x, a x := by
    have h1 : (fun x => a x * (c x + 1)) = fun x => a x * c x + a x := by
      funext x; ring
    rw [h1, Summable.tsum_add hsum_ac ha]
  rw [hsplit] at key
  linarith

end Work.HP.Sig2
