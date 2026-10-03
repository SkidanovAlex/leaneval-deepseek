import Mathlib

/-!
# Weighted power inequality for weights of total mass at most one

For a finite set `s`, nonnegative weights `w` with `∑ i ∈ s, w i ≤ 1`, nonnegative reals `x`
and an exponent `p ≥ 1`,

  `(∑ i ∈ s, w i * x i) ^ p ≤ ∑ i ∈ s, w i * x i ^ p`.

This is Jensen's inequality for the convex function `y ↦ y ^ p` on `[0, ∞)`, applied with the
additional point `0` carrying the leftover weight `1 - ∑ i ∈ s, w i ≥ 0`; the extra term vanishes
because `p ≥ 1`.  No normalisation (division by the total weight) is needed.
-/

namespace Work.Peluse.PetLinear

/-- **Weighted power inequality.** For nonnegative weights of total mass `≤ 1`, the `p`-th power
of the weighted average is at most the weighted average of the `p`-th powers, for `p ≥ 1`. -/
theorem weighted_sum_pow_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) (hws : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, w i * x i) ^ p ≤ ∑ i ∈ s, w i * x i ^ p := by
  have hp0 : p ≠ 0 := by omega
  -- Jensen applied to the convex function `y ↦ y ^ p` on `[0,∞)`, with the extra point `0`
  -- carrying the leftover mass `1 - ∑ w` (the second setting of the instruction is implicit:
  -- `q := 0` is the distinguished element, `v := 1 - ∑ w` its weight, and `h₁` says the total
  -- mass is `1`).
  have hmain := (convexOn_pow (𝕜 := ℝ) p).map_add_sum_le
      (s := Set.Ici (0:ℝ)) (t := s) (w := w) (p := x) (f := fun y : ℝ => y ^ p)
      (v := 1 - ∑ i ∈ s, w i) (q := 0) hw (by rw [sub_add_cancel]) (fun i hi => hx i hi)
      (sub_nonneg.mpr hws) (Set.mem_Ici.mpr le_rfl)
  simpa [hp0] using hmain

end Work.Peluse.PetLinear
