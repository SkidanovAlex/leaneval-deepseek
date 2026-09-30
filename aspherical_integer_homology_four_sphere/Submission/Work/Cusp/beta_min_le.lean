import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The coordinate offset `off t = 1/2 − |frac t − 1/2|` is nonnegative: `frac t ∈ [0,1)`, so
`frac t − 1/2 ∈ [−1/2, 1/2)`, i.e. its absolute value is at most `1/2`. -/
private lemma off_nonneg (t : ℝ) : 0 ≤ off t := by
  rw [off]
  have h1 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h2 : Int.fract t < 1 := Int.fract_lt_one t
  have h3 : |Int.fract t - 1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- The coordinate offset is at most `1/2`: it is `1/2` minus a nonnegative quantity. -/
private lemma off_le_half (t : ℝ) : off t ≤ 1/2 := by
  rw [off]
  have h := abs_nonneg (Int.fract t - 1/2)
  linarith

/-- **The ceiling `β` is bounded below by `βMin = √(3/2)`.**  Each of the three coordinate offsets
`off (x i)` lies in `[0, 1/2]`, so `Σ (off (x i))² ≤ 3 · (1/2)² = 3/4` and the radicand
`9/4 − Σ (off (x i))²` of `β x` is at least `9/4 − 3/4 = 3/2`; monotonicity of `√·` gives the
claim.  (The bound is attained at `x = (1/2, 1/2, 1/2)`, the centre of a cube face.) -/
theorem beta_min_le (x : E3) : betaMin ≤ beta x := by
  have hS : (∑ i : Fin 3, (off (x i)) ^ 2) ≤ 3/4 := by
    calc (∑ i : Fin 3, (off (x i)) ^ 2) ≤ ∑ _i : Fin 3, (1/4 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [off_nonneg (x i), off_le_half (x i)]
      _ = 3/4 := by rw [Fin.sum_univ_three]; norm_num
  rw [betaMin, beta]
  apply Real.sqrt_le_sqrt
  linarith

end Work.Cusp
