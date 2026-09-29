import Mathlib

namespace Work.TMC16Core.Assembly

/-- Arithmetic core of the resonant-zone assembly.

Given `100 ≤ Q`, an integer `m` with `Q/5 ≤ m ≤ 4Q/5`, and a natural `d` with
`d ≤ m` and `d ≤ Q - m`, there exist integers `a ≤ m ≤ b` bracketing `m` with
`a ≥ (Q-1)/20 + 3` and `b ≤ 95(Q-1)/100 - 3`, and such that the distance from
`m` to the nearer of the two ends is at least `d - ((Q-1)/20 + 5)`.

Concretely we take `a = ⌈(Q-1)/20⌉ + 3` and `b = ⌊95(Q-1)/100 - 3⌋`. -/
theorem res_zone_arith {Q : ℕ} (hQ : 100 ≤ Q) {m : ℤ} {d : ℕ}
    (hm1 : (Q : ℝ) / 5 ≤ (m : ℝ)) (hm2 : 5 * (m : ℝ) ≤ 4 * (Q : ℝ))
    (hd1 : (d : ℝ) ≤ (m : ℝ)) (hd2 : (d : ℝ) ≤ (Q : ℝ) - (m : ℝ)) :
    ∃ a b : ℤ,
      (((Q - 1 : ℕ) : ℝ)) / 20 + 3 ≤ (a : ℝ) ∧
      (b : ℝ) ≤ 95 * (((Q - 1 : ℕ) : ℝ)) / 100 - 3 ∧
      a ≤ m ∧ m ≤ b ∧
      (d : ℝ) - ((((Q - 1 : ℕ) : ℝ)) / 20 + 4) ≤
        ((min (m - a) (b - m) : ℤ) : ℝ) + 1 := by
  have hQ1 : 1 ≤ Q := by omega
  set q : ℕ := Q - 1 with hq
  set x : ℝ := (q : ℝ) / 20 with hx
  set y : ℝ := 95 * (q : ℝ) / 100 - 3 with hy
  -- real-valued normalisation of the natural `q = Q - 1`
  have hqR : (q : ℝ) = (Q : ℝ) - 1 := by
    rw [hq, Nat.cast_sub hQ1]; norm_num
  have hQr : (100 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  -- `x` sits well below `Q/5`, so `a := ⌈x⌉ + 3` is still `≤ m`
  have hxQ : x + 4 ≤ (Q : ℝ) / 5 := by rw [hx, hqR]; linarith
  -- `y - 1` sits well above `4Q/5`, so `b := ⌊y⌋` is still `≥ m`
  have hyQ : 4 * (Q : ℝ) / 5 ≤ y - 1 := by rw [hy, hqR]; linarith
  -- the exact identity `y - 1 = Q - x - 5`
  have hyx : y - 1 = (Q : ℝ) - x - 5 := by rw [hy, hx, hqR]; ring
  refine ⟨⌈x⌉ + 3, ⌊y⌋, ?_, ?_, ?_, ?_, ?_⟩
  · -- `x + 3 ≤ ⌈x⌉ + 3`
    have h := Int.le_ceil x
    push_cast
    linarith
  · -- `⌊y⌋ ≤ y`
    linarith [Int.floor_le y]
  · -- `⌈x⌉ + 3 ≤ m`
    have hc := Int.ceil_lt_add_one x
    have : (((⌈x⌉ + 3 : ℤ) : ℝ)) ≤ (m : ℝ) := by
      push_cast at hc ⊢
      linarith [hxQ, hm1]
    exact_mod_cast this
  · -- `m ≤ ⌊y⌋`
    have hf := Int.lt_floor_add_one y
    have : (m : ℝ) ≤ (((⌊y⌋ : ℤ) : ℝ)) := by
      linarith [hyQ, hm2]
    exact_mod_cast this
  · -- the `min` distance bound
    have hmin : ((min (m - (⌈x⌉ + 3)) (⌊y⌋ - m) : ℤ) : ℝ)
        = min ((m : ℝ) - ((⌈x⌉ + 3 : ℤ) : ℝ)) (((⌊y⌋ : ℤ) : ℝ) - (m : ℝ)) := by
      rw [Int.cast_min]; push_cast; ring_nf
    rw [hmin]
    have h1 : (d : ℝ) - x - 5 ≤ (m : ℝ) - ((⌈x⌉ + 3 : ℤ) : ℝ) := by
      have hc := Int.ceil_lt_add_one x
      push_cast at hc ⊢
      linarith [hd1]
    have h2 : (d : ℝ) - x - 5 ≤ ((⌊y⌋ : ℤ) : ℝ) - (m : ℝ) := by
      have hf := Int.lt_floor_add_one y
      linarith [hd2, hyx]
    linarith [le_min h1 h2]

end Work.TMC16Core.Assembly
