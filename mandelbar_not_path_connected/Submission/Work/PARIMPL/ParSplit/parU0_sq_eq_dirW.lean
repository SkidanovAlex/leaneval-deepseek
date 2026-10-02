/-
# `Work.PARIMPL.ParSplit.parU0_sq_eq_dirW`

A pure algebra lemma used in the phase analysis of the normal-form germ of the tricorn's second
return map.  Writing `W := 2 (m c - F c (m c)) / E c` and using `Gc = (E/2)²`, the quantity
`(Gc/‖Gc‖) · ρ² / ‖ρ‖²` occurring in `parLam · parRho²/‖parRho‖²` equals the normalized square
`(W/‖W‖)²`, because `W = (E/2)·ρ`.

Concretely: if `G ≠ 0`, `ρ ≠ 0`, `G = (E/2)²` and `D = G ρ`, then `2 D / E = (E/2) ρ`, and

  `(G/‖G‖) · ρ² / ‖ρ‖² = ((2 D / E)/‖2 D / E‖)²`.

Both sides reduce to `((u/‖u‖)·(ρ/‖ρ‖))²` with `u = E/2`, which is the normalized square of
`u·ρ = 2D/E`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- The product of two normalized complex numbers is the normalization of their product. -/
lemma div_norm_mul (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (z / (‖z‖ : ℂ)) * (w / (‖w‖ : ℂ)) = (z * w) / (‖z * w‖ : ℂ) := by
  have hz' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hw' : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  rw [norm_mul, Complex.ofReal_mul]
  field_simp

/-- Normalized-square form of the main identity, with `u = E/2`. -/
lemma parU0_dirW_key (u ρ : ℂ) (hu : u ≠ 0) (hρ : ρ ≠ 0) :
    u ^ 2 / (‖u ^ 2‖ : ℂ) * ρ ^ 2 / ((‖ρ‖ : ℂ)) ^ 2
      = ((u * ρ) / (‖u * ρ‖ : ℂ)) ^ 2 := by
  have hA : u ^ 2 / (‖u ^ 2‖ : ℂ) = (u / (‖u‖ : ℂ)) ^ 2 := by
    rw [norm_pow, Complex.ofReal_pow, div_pow]
  have hB : ρ ^ 2 / ((‖ρ‖ : ℂ)) ^ 2 = (ρ / (‖ρ‖ : ℂ)) ^ 2 := by
    rw [div_pow]
  rw [mul_div_assoc, hA, hB, ← mul_pow, div_norm_mul u ρ hu hρ]

theorem parU0_sq_eq_dirW {E G ρ D : ℂ} (hG : G ≠ 0) (hρ : ρ ≠ 0) (hGE : G = (E / 2) ^ 2)
    (hD : D = G * ρ) :
    (G / (‖G‖ : ℂ)) * ρ ^ 2 / ((‖ρ‖ : ℂ)) ^ 2
      = ((2 * D / E) / ((‖2 * D / E‖ : ℂ))) ^ 2 := by
  have hE : E ≠ 0 := by
    rintro rfl
    exact hG (by rw [hGE]; norm_num)
  have hE2 : (E / 2) ≠ 0 := div_ne_zero hE two_ne_zero
  have hDE : 2 * D / E = (E / 2) * ρ := by
    rw [hD, hGE]
    field_simp
  rw [hGE, hDE, parU0_dirW_key (E / 2) ρ hE2 hρ]

end Work.PARIMPL.ParSplit
