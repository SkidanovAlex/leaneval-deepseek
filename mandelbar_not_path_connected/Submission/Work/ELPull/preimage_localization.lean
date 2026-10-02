import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The two preimages of a regular value of `Tantibar c`

`Tantibar c z = (conj z)^2 + c` is an antiholomorphic quadratic map; its only critical point is
`z = 0`, with critical value `c`.  For `y ≠ c` the value `y` is regular, the two preimages
`u`, `-u` are distinct, and the *product of the distances* to them measures the distance of the
image from `y`:

  `Tantibar c z - y = conj((z - u) * (z + u))`,   hence   `‖Tantibar c z - y‖ = ‖z-u‖ * ‖z+u‖`.

That identity is what makes the localization statement elementary: the preimage of the ball of
radius `ε^2` about `y` is contained in the union of the `ε`-balls about the two preimages. -/

/-- The algebraic heart of the localization: writing `y = w * w + c` for a square root `w` of
`y - c`, the deviation of `Tantibar c z` from `y` is the conjugate of `(z - conj w)(z + conj w)`. -/
private lemma Tantibar_sub_mul (c w z : ℂ) :
    Tantibar c z - (w * w + c)
      = starRingEnd ℂ ((z - starRingEnd ℂ w) * (z + starRingEnd ℂ w)) := by
  simp only [Tantibar, map_mul, map_sub, map_add, starRingEnd_apply]
  rw [star_star]
  ring

/-- The consequence of `Tantibar_sub_mul` used in the proof: the norm of the deviation is the
product of the distances to the two preimages. -/
private lemma norm_Tantibar_sub (c w z : ℂ) :
    ‖Tantibar c z - (w * w + c)‖
      = ‖z - starRingEnd ℂ w‖ * ‖z + starRingEnd ℂ w‖ := by
  rw [Tantibar_sub_mul, Complex.norm_conj, norm_mul]

/-- The two preimages of a value `y ≠ c` of `Tantibar c` are the only ones, and they separate
locally: every neighbourhood of them captures all preimages of a small enough neighbourhood
of `y`. -/
theorem preimage_localization {c y : ℂ} (hy : y ≠ c) {ε : ℝ} (hε : 0 < ε) :
    ∃ u v : ℂ, LeanEval.ComplexAnalysis.Tantibar c u = y ∧ LeanEval.ComplexAnalysis.Tantibar c v = y ∧
      u ≠ v ∧ (∀ z : ℂ, LeanEval.ComplexAnalysis.Tantibar c z = y → z = u ∨ z = v) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖LeanEval.ComplexAnalysis.Tantibar c z - y‖ < δ →
        ‖z - u‖ < ε ∨ ‖z - v‖ < ε := by
  -- A square root `w` of the regular value's offset `y - c`; the two preimages are
  -- `u = conj w` and `v = -u = -conj w`.
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (y - c)
  have hyw : y = w * w + c := by rw [← hw]; ring
  refine ⟨starRingEnd ℂ w, -starRingEnd ℂ w, ?_, ?_, ?_, ?_, ε ^ 2, pow_pos hε 2, ?_⟩
  · -- `Tantibar c u = y`
    rw [Tantibar, Complex.conj_conj, sq, ← hw]; ring
  · -- `Tantibar c v = y`
    rw [Tantibar, map_neg, Complex.conj_conj]
    have : (-w) ^ 2 = w * w := by ring
    rw [this, ← hw]; ring
  · -- the two preimages are distinct, since otherwise `w = 0` and `y = c`
    intro h
    have h2 : starRingEnd ℂ w = 0 := by
      have hsum : starRingEnd ℂ w + starRingEnd ℂ w = 0 := by linear_combination h
      have : (2 : ℂ) * starRingEnd ℂ w = 0 := by rw [two_mul]; exact hsum
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    have hw0 : w = 0 := by
      have := congrArg (starRingEnd ℂ) h2
      rwa [Complex.conj_conj, map_zero] at this
    exact hy (sub_eq_zero.mp (by rw [hw, hw0, mul_zero]))
  · -- and they are the only preimages: `(conj z)^2 = w^2` forces `conj z = ±w`
    intro z hz
    have hsq : (starRingEnd ℂ z) ^ 2 = w * w := by
      rw [Tantibar] at hz
      rw [← hw]
      linear_combination hz
    have hfac : (starRingEnd ℂ z - w) * (starRingEnd ℂ z + w) = 0 := by
      have : (starRingEnd ℂ z - w) * (starRingEnd ℂ z + w)
          = (starRingEnd ℂ z) ^ 2 - w * w := by ring
      rw [this, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      have := congrArg (starRingEnd ℂ) (sub_eq_zero.mp h1)
      simpa using this
    · right
      have := congrArg (starRingEnd ℂ) (add_eq_zero_iff_eq_neg.mp h1)
      simpa using this
  · -- localization: the ball of radius `ε^2` about `y` has its preimage inside the `ε`-balls
    intro z hz
    by_contra hcon
    push Not at hcon
    have hnorm : ‖Tantibar c z - y‖ = ‖z - starRingEnd ℂ w‖ * ‖z + starRingEnd ℂ w‖ := by
      rw [hyw, norm_Tantibar_sub]
    have h2 : ε ≤ ‖z + starRingEnd ℂ w‖ := by
      have := hcon.2
      rwa [sub_neg_eq_add] at this
    have hle : ε * ε ≤ ‖Tantibar c z - y‖ := by
      rw [hnorm]
      exact mul_le_mul hcon.1 h2 (le_of_lt hε) (norm_nonneg _)
    have heps : ε ^ 2 = ε * ε := by ring
    linarith

end Work.ELPull
