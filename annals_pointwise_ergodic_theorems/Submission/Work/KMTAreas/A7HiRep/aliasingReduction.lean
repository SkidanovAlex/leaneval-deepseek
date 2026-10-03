import Mathlib
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunPosAux
import Submission.Work.KMTAreas.A7HiRep.chainPartSubAdd
import Submission.Work.KMTAreas.A7HiRep.chainPartPrefixZero

namespace Work.KMTAreas.A7HiRep

set_option maxHeartbeats 1000000

/-! ## The aliasing of the good major arcs is free

The target `Work.KMTAreas.A7HiRep.chainPartSqFunPos` assumes only `GoodMajorArcs ρ Cρ₀ l₁ (-(m₀))`
with `2 ≤ Cρ₀`, i.e. `m₀ ≥ 2·2^{ρ l₁}`; in that regime the Ionescu--Wainger arcs
`(α + ℝ_{≤-(m₀)})_{α ∈ (ℚ/ℤ)_{≤l₁}}` need **not** be disjoint (the non-aliasing threshold
`GoodMajorArcs ρ Cρ l₁ (-(m₀))` with the large constant `Cρ` of `exists_goodMajorArcs_nonAliasing`
is genuinely stronger).

The theorem below shows that this apparent extra difficulty costs *nothing*: any `(l₁, m₀)`
satisfying the target's hypothesis splits, after the *constant* number `J = J(ρ)` of scales (with
`J` as produced by `nonAliasingShift`), into a "coarse" part and a "fine" part, where the fine part
is non-aliased.  Concretely, writing `T_m = lpf ρ l₁ m₀ m`,

  `chainPart r (m ↦ T_m f) ≤ chainPart r (m ↦ T_{min m J} f) + chainPart r (m ↦ T_{m+J} f)`,

the first summand is the chain part of the *frozen* walk, which is at most `J^{1-1/r}·sqFun`
pointwise (`chainPartFrozenSqFun`: the chain has at most `J` effective jumps, and `ℓ^r ⊆ ℓ²` on a
`J`-dimensional vector — this consumes the `r > 2` slack), and the second summand is the walk at the
*shifted* base level `m₀ + J`, which is non-aliased (`nonAliasingShift`) and whose square function is
a sub-sum of the square function at `m₀` (`sqFun_shift_le`).

So the only input needed is the chain/square-function bound **in the non-aliased regime**, with a
constant *uniform* in `(l₁, m₀)`. -/

/-- **The prefix-zero/tail comparison for the chain part.**  The walk `m ↦ b m − b (min m J)`
(whose increments vanish for `m < J` and are the increments `Δ_m b` afterwards) is dominated by
the *shifted* walk `m ↦ b (m+J)`: its increments are the increments of `b (m+J)`, prefixed by `J`
zeros. -/
theorem chainPart_prefixZero_tail (r : NNReal) (hr : 1 ≤ r) (J : ℕ) (b : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => b m - b (min m J))
      ≤ Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => b (m + J)) := by
  have hw : (fun m : ℕ => b m - b (min m J))
      = fun m : ℕ => (-(b J)) + (if m ≤ J then b J else b m) := by
    funext m
    by_cases hm : m ≤ J
    · rw [if_pos hm, min_eq_left hm]; ring
    · rw [if_neg hm, min_eq_right (le_of_lt (not_le.mp hm))]; ring
  rw [hw, chainPart_add_const]
  have hpre : (fun m : ℕ => if m ≤ J then b J else b m)
      = fun m : ℕ => if m ≤ J then (fun k : ℕ => b (k + J)) 0
          else (fun k : ℕ => b (k + J)) (m - J) := by
    funext m
    by_cases hm : m ≤ J
    · simp only [if_pos hm, Nat.zero_add]
    · simp only [if_neg hm, show m - J + J = m from by omega]
  rw [hpre]
  exact chainPartPrefixZero r hr J (fun k : ℕ => b (k + J))

end Work.KMTAreas.A7HiRep
