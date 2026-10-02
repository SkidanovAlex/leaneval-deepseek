import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

/-- The slit plane `ℂ \ (−∞, v − 1/2]` cut along the real half-line `(−∞, v − 1/2]`, intersected
with a right half-plane `{Re w > a}`, is star-shaped with respect to every real point `p` with
`p > v − 1/2` and `p > a`. -/
theorem starConvex_slitAt (v p a : ℝ) (hp : v - 1 / 2 < p) (ha : a < p) :
    StarConvex ℝ (p : ℂ)
      ({w : ℂ | ¬ (w.im = 0 ∧ w.re ≤ v - 1 / 2)} ∩ {w : ℂ | a < w.re}) := by
  -- A convex combination `s • p + t • y` of the real base point `p` and a point `y` of the set
  -- stays in the set.  Write `z` for that combination.
  intro y hy s t hs ht hst
  rw [Set.mem_inter_iff] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have him : (s • (p : ℂ) + t • y).im = t * y.im := by
    simp [Complex.add_im, Complex.ofReal_im]
  have hre : (s • (p : ℂ) + t • y).re = s * p + t * y.re := by
    simp [Complex.add_re, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · -- The slit condition `¬ (z.im = 0 ∧ z.re ≤ v - 1/2)`.
    rw [Set.mem_ofPred_eq, him, hre]
    rcases eq_or_ne y.im 0 with hyim | hyim
    · -- If `y` is real then `y.re > v - 1/2`, and the same holds along the segment.
      rw [hyim, mul_zero]
      rintro ⟨h0, hle⟩
      have hyre : v - 1 / 2 < y.re := by
        by_contra hcon
        exact hy1 ⟨hyim, le_of_not_gt hcon⟩
      have hgt : v - 1 / 2 < s * p + t * y.re :=
        (convex_Ioi (r := v - 1 / 2)) hp hyre hs ht hst
      linarith
    · -- If `y` is non-real then the segment is non-real except possibly at `p`.
      rintro ⟨heq, hle⟩
      have ht0 : t = 0 := by
        rcases mul_eq_zero.mp heq with h | h
        · exact h
        · exact absurd h hyim
      have hs1 : s = 1 := by linarith
      have hpe : s * p + t * y.re = p := by rw [ht0, hs1]; ring
      linarith
  · -- The half-plane condition `a < z.re`.
    rw [Set.mem_ofPred_eq, hre]
    exact (convex_Ioi (r := a)) ha hy2 hs ht hst

end Work.GATE2.PL
